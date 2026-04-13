# ============================================================
# Offline Google Trends → Price Backtester (no terminal args)
# ============================================================

import os
import re
import numpy as np
import pandas as pd
import yfinance as yf
from datetime import datetime, timedelta, timezone

# ============================================================
# ----------- USER SETTINGS: EDIT THESE ONLY -----------------
# ============================================================

TICKERS = ['GMT','ONDS','MDB','DUOL','AEYE','AESI','ALKT','TNYA','KC','INTR','ENPH','RN','SEDG','GDS']                            # e.g. ["OPEN", "AESI", "DUOL"]
TERM_MAP = {"OPEN": "opendoor"}               # optional mapping {ticker: term}
START_DATE = "2025-10-10"
END_DATE = "2026-01-10"
GEO = "US"

# Signal settings
MULTIPLIER = 1.1
LOOKBACK_DAYS = 7
REGEN_DAYS = 10.5
ALERT_FREEZE_DAYS = 7
HORIZONS = [1, 2, 3, 4, 5]
PRELOOKBACK = 5

# Alert thresholds
THRESHOLDS = {
    "popularity": 10.1,
    "weighed_popularity": 10.1,
    "significance": 10.1,
    "balanced_significance": 1.2,
}

# --- Trade management rules ---
STOP_LOSS_PCT = 0.0518        # 5.18% stop (fraction)
EXIT_ON_GAIN_REDUCTION = False  # sell on first day the gain vs entry is lower than previous day


# Trend data folder and output file
TRENDS_DIR = "/Users/hsiangyuchu/trends_data"         # <---- put your Google Trends CSVs here
OUTPUT_FILE = "Backtest_results_offline3.csv"

# ============================================================


# -------------------- Metrics --------------------

def popularity_list(x, average_initial):
    if average_initial == 0:
        return [0.0] * max(0, len(x) - 1)
    out, s = [], 0.0
    for i in range(len(x) - 1):
        s += x[i] / average_initial
        out.append(round(s, 2))
    return out

def weighed_popularity_list(x, average_initial):
    pl = popularity_list(x, average_initial)
    return [round(pl[i] / (1 + i), 2) for i in range(len(pl))]

def significance_list(x, average_initial):
    if not x: return []
    d = [x[i + 1] - x[i] for i in range(len(x) - 1)]
    base = average_initial if average_initial else 0.0
    res = [round(x[0] - base, 2)]
    for a in range(len(d)):
        pos = [d[b] for b in range(a + 1) if d[b] > 0]
        res.append(round(sum(pos) / len(pos), 2) if pos else 0.0)
    return res

def balanced_significance_list(x, average_initial):
    if not x: return []
    denom = average_initial if average_initial else 1.0
    d = [x[i + 1] - x[i] for i in range(len(x) - 1)]
    res = [round((x[0] - denom) / denom, 2)]
    for a in range(len(d)):
        pos = [d[b] for b in range(a + 1) if d[b] > 0]
        res.append(round((sum(pos) / len(pos)) / denom, 2) if pos else 0.0)
    return res

# -------------------- Helper --------------------

def ensure_utc_index(s):
    s = s.copy()
    s.index = pd.to_datetime(s.index, errors="coerce")
    s = s[~s.index.isna()]
    if s.index.tz is None:
        s.index = s.index.tz_localize("UTC")
    else:
        s.index = s.index.tz_convert("UTC")
    return s.sort_index()

# -------------------- Local Trends Loader --------------------
import csv, io, re

def load_trends_from_csv(term, directory, start, end):
    """
    Super-robust loader for your Google Trends files.
    File name must be <term>.csv (case-insensitive) inside `directory`.
    Data assumed to start where column A looks like a date; A=date, B=value from that row downward.
    Returns a pandas Series (UTC index). Never returns None.
    """
    def _empty():
        return pd.Series(dtype=float)

    # --- locate file
    if not os.path.isdir(directory):
        print(f"[ERROR] Trends folder not found: {directory}")
        return _empty()

    target = None
    for f in os.listdir(directory):
        if f.lower().endswith(".csv") and os.path.splitext(f)[0].lower() == term.lower():
            target = os.path.join(directory, f)
            break
    if target is None:
        print(f"[WARN] No CSV found for term '{term}' in {directory}")
        return _empty()

    # --- detect if it's actually an Excel workbook (xlsx/zip magic 'PK')
    try:
        with open(target, "rb") as fh:
            head = fh.read(4)
        if head.startswith(b"PK"):
            try:
                df = pd.read_excel(target, header=None)
            except Exception as e:
                print(f"[WARN] read_excel failed for {target}: {e}")
                return _empty()
            # convert dataframe -> text-like table (two cols) below
            raw_rows = df.values.tolist()
            # normalize to strings
            lines = []
            for row in raw_rows:
                a = "" if len(row) < 1 or pd.isna(row[0]) else str(row[0])
                b = "" if len(row) < 2 or pd.isna(row[1]) else str(row[1])
                lines.append([a, b])
            # fall through to picking first date-like row
            return _series_from_lines(lines, start, end)
    except Exception as e:
        print(f"[WARN] Could not peek file {target}: {e}")

    # --- read as text (CSV). Try multiple encodings; keep the first that yields non-empty text
    text = None
    for enc in ("utf-8-sig", "utf-8", "utf-16", "latin1"):
        try:
            with open(target, "r", encoding=enc, errors="strict") as fh:
                txt = fh.read()
                if txt and len(txt.strip()) > 0:
                    text = txt
                    break
        except Exception:
            continue
    if text is None:
        print(f"[WARN] Unable to read CSV {target} using common encodings.")
        return _empty()

    # --- detect delimiter
    try:
        dialect = csv.Sniffer().sniff(text[:2048], delimiters=",;\t")
        delim = dialect.delimiter
    except Exception:
        # fallback: guess by presence order
        if text.count(";") > text.count(",") and text.count(";") >= text.count("\t"):
            delim = ";"
        elif text.count("\t") > text.count(","):
            delim = "\t"
        else:
            delim = ","

    # parse with csv.reader
    reader = csv.reader(io.StringIO(text), delimiter=delim)
    rows = [row for row in reader if any(cell.strip() for cell in row)]
    if not rows:
        print(f"[WARN] CSV {target} appears empty after parsing.")
        return _empty()

    # build list of first two columns as strings
    lines = []
    for row in rows:
        a = row[0].strip() if len(row) > 0 else ""
        b = row[1].strip() if len(row) > 1 else ""
        lines.append([a, b])

    # convert to series
    return _series_from_lines(lines, start, end)


# ---- helper to convert parsed "lines" into a Series
def _series_from_lines(lines, start, end):
    """
    lines: list of [colA, colB] strings
    Finds first row where colA looks like a date, then uses rows from there down.
    Converts all dates to timezone-aware (UTC) before slicing.
    """
    import re
    import pandas as pd

    def looks_like_date(s: str) -> bool:
        s = s.strip()
        return (
            re.match(r"^\d{1,2}/\d{1,2}/\d{4}$", s) or    # dd/mm/yyyy or mm/dd/yyyy
            re.match(r"^\d{4}-\d{2}-\d{2}$", s) or       # yyyy-mm-dd
            re.match(r"^\d{4}/\d{2}/\d{2}$", s)          # yyyy/mm/dd
        )

    # --- find first date-like line ---
    start_idx = None
    for i, (a, _) in enumerate(lines):
        if looks_like_date(a):
            start_idx = i
            break
    if start_idx is None:
        print("[WARN] No date-like rows found in parsed lines (expect dd/mm/yyyy or yyyy-mm-dd).")
        return pd.Series(dtype=float)

    # --- take from start_idx onward ---
    dates, vals = [], []
    for a, b in lines[start_idx:]:
        if not looks_like_date(a):
            # you can stop when non-date rows appear, or continue
            # break
            continue
        dates.append(a)
        vals.append(b)

    if not dates:
        return pd.Series(dtype=float)

    # --- build DataFrame ---
    df = pd.DataFrame({"date": dates, "value": vals})

    # Try dayfirst, then fallback
    d1 = pd.to_datetime(df["date"], dayfirst=True, errors="coerce")
    d2 = pd.to_datetime(df["date"], dayfirst=False, errors="coerce")
    df["date"] = d1 if d1.notna().sum() >= d2.notna().sum() else d2

    df["value"] = pd.to_numeric(df["value"], errors="coerce")
    df = df.dropna(subset=["date", "value"])
    if df.empty:
        return pd.Series(dtype=float)

    s = df.set_index("date")["value"].astype(float)

    # --- ensure UTC before comparing ---
    if s.index.tz is None:
        s.index = s.index.tz_localize("UTC")
    else:
        s.index = s.index.tz_convert("UTC")

    # also ensure start/end are UTC-aware
    if getattr(start, "tzinfo", None) is None:
        start_utc = pd.Timestamp(start).tz_localize("UTC")
    else:
        start_utc = start.tz_convert("UTC")

    if getattr(end, "tzinfo", None) is None:
        end_utc = pd.Timestamp(end).tz_localize("UTC")
    else:
        end_utc = end.tz_convert("UTC")

    # --- slice by date window ---
    s = s[(s.index >= start_utc) & (s.index <= end_utc)]
    if s.empty:
        return pd.Series(dtype=float)

    return s.sort_index()





# -------------------- Prices & Backtest Core --------------------

# Map your logical tickers → Yahoo symbols (edit as you like)
YF_TICKER_MAP = {
    # "GMT": "GMT-USD",     # if you meant the crypto STEPN on USD
    # "GMT": "GMT.L",       # if you meant a London-listed equity
}

def yf_prices(ticker, start, end):
    """
    Safe wrapper around yfinance. Tries mapping first; if nothing, tries the raw.
    Returns an empty Series on any error (never None).
    """
    def _empty():
        return pd.Series(dtype=float)

    yf_sym = YF_TICKER_MAP.get(ticker, ticker)
    try_syms = [yf_sym]
    if yf_sym != ticker:
        try_syms.append(ticker)  # also try original, just in case

    for sym in try_syms:
        try:
            start_str = start.strftime("%Y-%m-%d")
            end_str = (end + pd.Timedelta(days=2)).strftime("%Y-%m-%d")
            df = yf.download(sym, start=start_str, end=end_str, progress=False, auto_adjust=True)
            if df is None or df.empty or "Close" not in df.columns:
                continue
            s = df["Close"].astype(float)
            s.index = pd.to_datetime(s.index, errors="coerce")
            s = s[~s.index.isna()]
            if s.empty:
                continue
            s = s.tz_localize("UTC")
            return s.sort_index()
        except Exception as e:
            print(f"[WARN] {ticker} ({sym}): yfinance error: {e}")

    print(f"[WARN] No price data for {ticker} (tried {try_syms})")
    return _empty()


def simulate_exit_with_rules(prices, event_dt, stop_loss_frac=STOP_LOSS_PCT, exit_on_gain_reduction=EXIT_ON_GAIN_REDUCTION):
    """
    Returns a dict with:
      entry_time, entry_price, exit_time, exit_price, exit_reason, realized_exit_logret, realized_exit_pct
    Entry = first price strictly AFTER event_dt.
    Exit rules (checked daily, in order):
      1) Stop-loss: price <= entry * (1 - stop_loss_frac)
      2) Gain reduction: today's return vs entry < yesterday's return vs entry
    If neither triggers before series ends, exit at the last available price.
    """
    result = {
        "entry_time": None, "entry_price": None,
        "exit_time": None,  "exit_price": None,
        "exit_reason": None,
        "realized_exit_logret": None, "realized_exit_pct": None,
    }
    if prices.empty: 
        return result

    fut = prices[prices.index > event_dt]
    if fut.empty:
        return result

    entry_time = fut.index[0]
    entry_price = float(fut.iloc[0])

    stop_price = entry_price * (1.0 - float(stop_loss_frac))
    prev_ret = None  # yesterday's return vs entry

    # iterate from the day after entry (inclusive)
    for ts, px in fut.iloc[0:].items():
        px = float(px)

        # Rule 1: stop-loss
        if px <= stop_price:
            result.update({
                "entry_time": entry_time,
                "entry_price": entry_price,
                "exit_time": ts,
                "exit_price": px,
                "exit_reason": "stop_loss",
                "realized_exit_logret": float(np.log(px / entry_price)),
                "realized_exit_pct": float(px / entry_price - 1.0),
            })
            return result

        # Rule 2: gain reduction vs previous day
        if exit_on_gain_reduction:
            cur_ret = px / entry_price - 1.0
            if prev_ret is not None and cur_ret < prev_ret:
                result.update({
                    "entry_time": entry_time,
                    "entry_price": entry_price,
                    "exit_time": ts,
                    "exit_price": px,
                    "exit_reason": "gain_reduction",
                    "realized_exit_logret": float(np.log(px / entry_price)),
                    "realized_exit_pct": float(cur_ret),
                })
                return result
            prev_ret = cur_ret

    # If we never exited, close at last available price
    last_ts = fut.index[-1]
    last_px = float(fut.iloc[-1])
    result.update({
        "entry_time": entry_time,
        "entry_price": entry_price,
        "exit_time": last_ts,
        "exit_price": last_px,
        "exit_reason": "time_exit",
        "realized_exit_logret": float(np.log(last_px / entry_price)),
        "realized_exit_pct": float(last_px / entry_price - 1.0),
    })
    return result


def forward_returns(prices, event_dt, horizons):
    out = {h: None for h in horizons}
    if prices.empty:
        return out
    fut = prices[prices.index > event_dt]
    if fut.empty:
        return out
    entry = fut.iloc[0]
    entry_loc = prices.index.get_loc(fut.index[0])
    for h in horizons:
        idx = entry_loc + h
        if idx < len(prices):
            exit_p = prices.iloc[idx]
            out[h] = float(np.log(exit_p / entry))
    return out

def price_increasing_before(prices, event_dt, prelookback, up_ratio=0.6):
    if prices.empty:
        return False
    hist = prices[prices.index < event_dt].tail(prelookback + 1)
    if len(hist) < prelookback + 1:
        return False
    rets = np.diff(hist.values)
    net_up = hist.values[-1] > hist.values[0]
    up_days = (rets > 0).mean() if len(rets) else 0.0
    return bool(net_up and up_days >= up_ratio)

def average_initial_7day_at(trends, i):
    start = max(0, i - 6)
    slice_ = trends.iloc[start:i + 1]
    return float(slice_.mean()) if not slice_.empty else float(trends.iloc[i])

# -------------------- Main Backtest --------------------

def backtest_one(ticker, term, start, end):
    trends = load_trends_from_csv(term, TRENDS_DIR, start, end)
    prices = yf_prices(ticker, start, end)
    if trends.empty or prices.empty:
        print(f"[WARN] Missing data for {ticker}")
        return pd.DataFrame(), {}

    alerts = []
    current_avg_initial = None
    last_signal_at = None
    last_alert_at = None
    regen_delta = pd.Timedelta(days=REGEN_DAYS)
    alert_freeze_delta = pd.Timedelta(days=ALERT_FREEZE_DAYS)

    for i in range(LOOKBACK_DAYS, len(trends)):
        t = trends.index[i]
        val_t = float(trends.iloc[i])
        prev = trends.iloc[i - LOOKBACK_DAYS:i]
        if prev.empty: continue
        prev_max = float(prev.max())

        if prev_max > 0 and val_t >= MULTIPLIER * prev_max:
            if (last_signal_at is None) or (t - last_signal_at >= regen_delta) or (current_avg_initial is None):
                current_avg_initial = average_initial_7day_at(trends, i)
            last_signal_at = t

            x_vals = [float(v) for v in trends.iloc[max(0, i - 14): i + 1].tolist()]
            pl = popularity_list(x_vals, current_avg_initial)
            wpl = weighed_popularity_list(x_vals, current_avg_initial)
            sl = significance_list(x_vals, current_avg_initial)
            bsl = balanced_significance_list(x_vals, current_avg_initial)

            latest_pop = pl[-1] if pl else 0
            latest_wpop = wpl[-1] if wpl else 0
            latest_sig = sl[-1] if sl else 0
            latest_bsig = bsl[-1] if bsl else 0

            is_alert = (
                latest_pop > THRESHOLDS["popularity"] or
                latest_wpop > THRESHOLDS["weighed_popularity"] or
                latest_sig > THRESHOLDS["significance"] or
                latest_bsig > THRESHOLDS["balanced_significance"]
            )
            if is_alert:
                if last_alert_at is not None and (t - last_alert_at) < alert_freeze_delta:
                    continue

                fwd = forward_returns(prices, t, HORIZONS)
                pre_up = price_increasing_before(prices, t, PRELOOKBACK)

                row = {
                    "ticker": ticker,
                    "term": term,
                    "alert_time_utc": t.isoformat(),
                    "trend_value": val_t,
                    "prev_window_max": prev_max,
                    "average_initial": current_avg_initial,
                    "popularity": latest_pop,
                    "weighed_popularity": latest_wpop,
                    "significance": latest_sig,
                    "balanced_significance": latest_bsig,
                    "pretrend_increasing": pre_up,
                }
                for h in HORIZONS:
                    row[f"fwd_logret_{h}d"] = fwd[h]
                    row[f"win_{h}d"] = (fwd[h] is not None) and (fwd[h] > 0)

                alerts.append(row)
                last_alert_at = t

    alerts_df = pd.DataFrame(alerts)
    if alerts_df.empty:
        return alerts_df, {}

    win_rates = {}
    for h in HORIZONS:
        wcol = f"win_{h}d"
        win_rates[h] = alerts_df[wcol].mean() if wcol in alerts_df.columns else 0.0

    return alerts_df, win_rates


# -------------------- Runner --------------------

def main():
    # Convert string dates into pandas timestamps with UTC
    start_dt = pd.Timestamp(START_DATE).tz_localize("UTC")
    end_dt = pd.Timestamp(END_DATE).tz_localize("UTC")


    all_alerts = []
    for tk in TICKERS:
        term = TERM_MAP.get(tk, tk)
        print(f"\n=== Backtesting {tk} (term '{term}') ===")
        alerts_df, win_rates = backtest_one(tk, term, start_dt, end_dt)
        if alerts_df.empty:
            print("  No alerts.")
            continue

        print(f"  Alerts: {len(alerts_df)}")
        for h, wr in win_rates.items():
            print(f"   +{h}d win rate: {wr*100:.1f}%")

        all_alerts.append(alerts_df)

    if all_alerts:
        out_df = pd.concat(all_alerts, ignore_index=True)
        out_df.to_csv(OUTPUT_FILE, index=False)
        print(f"\nSaved {len(out_df)} alerts → {OUTPUT_FILE}")
    else:
        print("\nNo alerts generated for any ticker.")

if __name__ == "__main__":
    main()
