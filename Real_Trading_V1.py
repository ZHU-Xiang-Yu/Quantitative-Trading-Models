#!/usr/bin/env python3
# trend_monitor_daily_trading.py
#
# Daily (9:30 PM America/New_York) Google Trends scan (daily resolution)
# + rate limiting/backoff batching
# + alert cooldown + delayed baseline regen
# + Tiger Brokers (paper/live) order at next RTH open

import threading
import queue
import time
import random
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo
import pandas as pd
from pytrends.request import TrendReq
import tkinter as tk
from tkinter.scrolledtext import ScrolledText
import os
import warnings

# ==== Tiger Open API ====
# pip install tigeropen
from tigeropen.tiger_open_config import TigerOpenClientConfig
from tigeropen.common.util.signature_utils import read_private_key
from tigeropen.trade.trade_client import TradeClient
from tigeropen.common.util.contract_utils import stock_contract
from tigeropen.common.util.order_utils import market_order

# Quiet noisy warnings
warnings.filterwarnings("ignore", category=FutureWarning)
warnings.filterwarnings("ignore", category=UserWarning)

# ================== CONFIG ==================
KEYWORDS = ["AMC", "GME", "ONDS", "MDB", "DUOL", "AEYE", "AESI",
            "ALKT", "TNYA", "RUN", "KC", "INTR", "ENPH", "RN", "SEDG", "GDS"]
CSV_OUTPUT = "trend_alerts.csv"

# Trends fetch config (daily resolution)
TRENDS_TIMEFRAME = "today 1-m"     # daily points for last ~30 days
TRENDS_GEO = "US"
MAX_GROUP_SIZE = 5                 # up to 5 terms per request

# Signal & thresholds
SIGNAL_JUMP_MULTIPLIER = 1.10      # newest >= 1.10 * max of prior-day window
PREV_WINDOW_DAYS = 1               # compare vs previous 1 day (yesterday)
ALERT_COOLDOWN_DAYS = 7.0          # suppress alerts for 7 days after an alert
AVG_REGEN_AFTER_DAYS = 10.5        # regenerate baseline 10.5 days after alert
AVG_REGEN_WINDOW_DAYS = 7.0        # baseline from the next 7 days after alert

# Metric thresholds
ALERT_POPULARITY = 10.1
ALERT_WEIGHED_POPULARITY = 10.1
ALERT_SIGNIFICANCE = 10.1
ALERT_BALANCED_SIGNIFICANCE = 1.2

# History buffer (we keep more than 30 days locally by appending runs)
HISTORY_DAYS_TO_KEEP = 120

# Rate limiting / backoff (polite, ToS-friendly)
MIN_SECS_BETWEEN_REQUESTS = 3      # minimum spacing between Google requests
MAX_JITTER_SECS = 2                # add random jitter [0..MAX_JITTER_SECS]
BACKOFF_START = 8                  # seconds on first failure
MAX_BACKOFF_SECS = 600             # cap exponential backoff at 10 minutes
MAX_RETRIES = 5

# Schedule: run once per day at 23:30 America/New_York
RUN_TZ = ZoneInfo("America/New_York")
RUN_HOUR = 23
RUN_MINUTE = 30

# Trading Account 
USE_PAPER = True  # True for paper, False for live (⚠️ be careful)
TIGER_ID = "YOUR_TIGER_ID"
TIGER_ACCOUNT = "YOUR_ACCOUNT_ID"      # paper or live account id
PRIVATE_KEY_PEM_PATH = "/path/to/your/tiger_private_key.pem"
DEFAULT_BUY_QTY = 1                           # change the default buy quantity here.

# Map keyword -> stock symbol
KEYWORD_TO_SYMBOL = {
    "AMC": "AMC",
    "GME": "GME",
    "ONDS": "ONDS",
    "MDB": "MDB",
    "DUOL": "DUOL",
    "AEYE": "AEYE",
    "AESI": "AESI",
    "ALKT": "ALKT",
    "TNYA": "TNYA",
    "RUN": "RUN",
    "KC": "KC",
    "INTR": "INTR",
    "ENPH": "ENPH",
    "RN": "RN",
    "SEDG": "SEDG",
    "GDS": "GDS",
}
# ============================================

# ---------- Helpers ----------
def ensure_utc_index(s: pd.Series) -> pd.Series:
    s = s.copy()
    s.index = pd.to_datetime(s.index, errors='coerce')
    if s.index.tz is None:
        s.index = s.index.tz_localize('UTC')
    else:
        s.index = s.index.tz_convert('UTC')
    return s.sort_index()

def chunks(lst, n):
    for i in range(0, len(lst), n):
        yield lst[i:i+n]

def next_run_dt_utc(now_utc: datetime) -> datetime:
    """Compute next 21:30 America/New_York in UTC."""
    now_local = now_utc.astimezone(RUN_TZ)
    target_local = now_local.replace(hour=RUN_HOUR, minute=RUN_MINUTE, second=0, microsecond=0)
    if target_local <= now_local:
        target_local = target_local + timedelta(days=1)
    return target_local.astimezone(timezone.utc)

def next_us_rth_open_utc(after_dt_utc: datetime) -> datetime:
    """
    Compute next US regular trading session open (09:30 ET) AFTER a given UTC time.
    This is simplistic (no holiday calendar). It rolls forward to next weekday if weekend.
    """
    dt_local = after_dt_utc.astimezone(RUN_TZ)
    # next 09:30 local
    target = dt_local.replace(hour=9, minute=30, second=0, microsecond=0)
    if target <= dt_local:
        target += timedelta(days=1)
    # skip weekends
    while target.weekday() >= 5:  # 5=Sat, 6=Sun
        target += timedelta(days=1)
    return target.astimezone(timezone.utc)

# ---------- Metric functions ----------
def popularity(x, average_initial):
    if average_initial == 0 or len(x) <= 1:
        return 0.0
    return sum(x[it] / average_initial for it in range(len(x) - 1))

def popularity_list(x, average_initial):
    populist, sume = [], 0.0
    if average_initial == 0:
        return [0.0] * max(0, len(x) - 1)
    for it in range(len(x) - 1):
        sume += x[it] / average_initial
        populist.append(round(sume, 2))
    return populist

def weighed_popularity_list(x, average_initial):
    populist, sume = [], 0.0
    if average_initial == 0:
        return [0.0] * max(0, len(x) - 1)
    for it in range(len(x) - 1):
        sume += x[it] / average_initial
        populist.append(round(sume, 2))
    return [round(populist[it] / (1 + it), 2) for it in range(len(populist))]

def significance_list(x, average_initial):
    if not x:
        return []
    deri_list = [x[it + 1] - x[it] for it in range(len(x) - 1)]
    base = average_initial if average_initial else 0.0
    weighed_sig_list = [round(x[0] - base, 2)]
    for a in range(len(deri_list)):
        pos = [deri_list[b] for b in range(a + 1) if deri_list[b] > 0]
        weighed_sig_list.append(round(sum(pos) / len(pos), 2) if pos else 0.0)
    return weighed_sig_list

def balanced_significance_list(x, average_initial):
    if not x:
        return []
    denom = average_initial if average_initial else 1.0
    b_deri_list = [x[it + 1] - x[it] for it in range(len(x) - 1)]
    b_weighed_sig_list = [round((x[0] - denom) / denom, 2)]
    for a in range(len(b_deri_list)):
        pos = [b_deri_list[b] for b in range(a + 1) if b_deri_list[b] > 0]
        b_weighed_sig_list.append(round((sum(pos) / len(pos)) / denom, 2) if pos else 0.0)
    return b_weighed_sig_list

# ---------- Tiger API ----------
class TigerTrader:
    def __init__(self, log_fn):
        self.log = log_fn
        self.client = None
        try:
            cfg = TigerOpenClientConfig(sandbox_debug=USE_PAPER)
            cfg.private_key = read_private_key(PRIVATE_KEY_PEM_PATH)
            cfg.tiger_id = TIGER_ID
            cfg.account = TIGER_ACCOUNT
            self.client = TradeClient(cfg)
            self.log(f"Tiger API: TradeClient initialized (paper={USE_PAPER}).")
        except Exception as e:
            self.log(f"Tiger API init error: {repr(e)}")

    def place_market_buy(self, symbol: str, qty: int = DEFAULT_BUY_QTY) -> bool:
        """Submit a DAY market BUY during regular hours (outside_rth=False)."""
        if not self.client:
            self.log("Tiger API not ready; skipping trade.")
            return False
        try:
            c = stock_contract(symbol=symbol, currency='USD')
            o = market_order(account=TIGER_ACCOUNT, contract=c, action='BUY', quantity=max(1, int(qty)))
            o.time_in_force = 'DAY'
            o.outside_rth = False
            self.client.place_order(o)
            self.log(f"Tiger API: Submitted MKT BUY {qty} {symbol}. order_id={getattr(o, 'id', None)}")
            return True
        except Exception as e:
            self.log(f"Tiger API order error for {symbol}: {repr(e)}")
            return False

# ---------- Background: executes queued trades at next RTH open ----------
class TradeExecutor(threading.Thread):
    def __init__(self, log_fn, trader: TigerTrader, stop_event: threading.Event):
        super().__init__(daemon=True)
        self.log = log_fn
        self.trader = trader
        self.stop_event = stop_event
        self.pending = []  # list of dicts: {symbol, qty, execute_at_utc}
        self.lock = threading.Lock()

    def queue_trade(self, symbol: str, qty: int, execute_at_utc: datetime):
        with self.lock:
            self.pending.append({"symbol": symbol, "qty": qty, "execute_at_utc": execute_at_utc})
        self.log(f"Queued trade: BUY {qty} {symbol} at next open ({execute_at_utc.isoformat()}).")

    def run(self):
        while not self.stop_event.is_set():
            now = datetime.now(timezone.utc)
            to_exec = []
            with self.lock:
                remain = []
                for t in self.pending:
                    if t["execute_at_utc"] <= now:
                        to_exec.append(t)
                    else:
                        remain.append(t)
                self.pending = remain
            for t in to_exec:
                self.log(f"Executing queued trade: BUY {t['qty']} {t['symbol']} now.")
                ok = self.trader.place_market_buy(t["symbol"], t["qty"])
                if not ok:
                    # if fail, retry 2 minutes later
                    retry_at = now + timedelta(minutes=2)
                    self.log(f"Trade failed; will retry at {retry_at.isoformat()}.")
                    self.queue_trade(t["symbol"], t["qty"], retry_at)
            # check every 30 seconds
            for _ in range(30):
                if self.stop_event.is_set():
                    break
                time.sleep(1)

# ---------- Trends Monitor: one run per day at 21:30 ET ----------
class TrendsMonitor(threading.Thread):
    def __init__(self, log_q, stop_event):
        super().__init__(daemon=True)
        self.log_q = log_q
        self.stop_event = stop_event

        # Polite, explicit request settings
        self.pytrends = TrendReq(
            hl='en-US', tz=0, retries=0, backoff_factor=0, requests_args={"timeout": (10, 30)}
        )

        self.trend_history = {kw: pd.Series(dtype=float) for kw in KEYWORDS}
        self.avg_init = {kw: None for kw in KEYWORDS}
        self.last_alert_at = {kw: None for kw in KEYWORDS}
        self.alert_cooldown_until = {kw: None for kw in KEYWORDS}
        self.pending_regen_after_alert = {kw: None for kw in KEYWORDS}

        # rate limiter
        self._next_allowed_time = datetime.now(timezone.utc)

        # trading
        self.trader = TigerTrader(self.log)
        self.trade_exec = TradeExecutor(self.log, self.trader, self.stop_event)
        self.trade_exec.start()

    # --------------- Logging ---------------
    def log(self, msg):
        ts_utc = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
        ts_et  = datetime.now(timezone.utc).astimezone(RUN_TZ).strftime("%Y-%m-%d %H:%M:%S ET")
        self.log_q.put(f"[{ts_utc} | {ts_et}] {msg}")

    # --------------- Rate limiter ---------------
    def _sleep_until_allowed(self):
        now = datetime.now(timezone.utc)
        if now < self._next_allowed_time:
            to_sleep = (self._next_allowed_time - now).total_seconds()
            slept = 0.0
            while slept < to_sleep and not self.stop_event.is_set():
                chunk = min(0.25, to_sleep - slept)
                time.sleep(chunk)
                slept += chunk
        delay = MIN_SECS_BETWEEN_REQUESTS + random.uniform(0, MAX_JITTER_SECS)
        self._next_allowed_time = datetime.now(timezone.utc) + timedelta(seconds=delay)

    def _fetch_group_daily(self, group):
        """
        Fetch daily-resolution interest_over_time for a group of up to 5 keywords with backoff.
        Returns DataFrame with keyword columns (and possibly 'isPartial').
        """
        self._sleep_until_allowed()
        delay = BACKOFF_START
        for attempt in range(1, MAX_RETRIES + 1):
            try:
                self.pytrends.build_payload(group, cat=0, timeframe=TRENDS_TIMEFRAME, geo=TRENDS_GEO, gprop='')
                df = self.pytrends.interest_over_time()
                return df
            except Exception as e:
                self.log(f"[RATE-LIMIT/ERROR] {group} attempt {attempt}: {repr(e)}")
                sleep_s = min(delay, MAX_BACKOFF_SECS) + random.uniform(0, 1.5)
                slept = 0.0
                while slept < sleep_s and not self.stop_event.is_set():
                    chunk = min(0.5, sleep_s - slept)
                    time.sleep(chunk)
                    slept += chunk
                delay = min(delay * 2, MAX_BACKOFF_SECS)
        return None

    # --------------- Baseline regen check ---------------
    def _maybe_regen_average_initial(self, kw, now_utc):
        alert_time = self.pending_regen_after_alert[kw]
        if alert_time is None:
            return
        regen_time = alert_time + timedelta(days=AVG_REGEN_AFTER_DAYS)
        if now_utc < regen_time:
            return
        # compute baseline from next 7 days after alert
        win_start = alert_time
        win_end = alert_time + timedelta(days=AVG_REGEN_WINDOW_DAYS)
        series = self.trend_history[kw]
        if series.empty:
            self.log(f"{kw}: baseline regen skipped (no data).")
            self.pending_regen_after_alert[kw] = None
            return
        window = series[(series.index >= win_start) & (series.index < win_end)]
        if window.empty:
            self.log(f"{kw}: baseline regen window had no points; keeping prior baseline.")
            self.pending_regen_after_alert[kw] = None
            return
        new_avg = float(window.mean())
        self.avg_init[kw] = new_avg
        self.pending_regen_after_alert[kw] = None
        self.log(f"{kw}: average_initial regenerated at +{AVG_REGEN_AFTER_DAYS}d using next {AVG_REGEN_WINDOW_DAYS}d: {round(new_avg, 4)}")

    # --------------- One scan (called at 21:30 ET daily) ---------------
    def run_daily_scan(self):
        self.log(f"Starting daily Trends scan (timeframe={TRENDS_TIMEFRAME}, geo={TRENDS_GEO}).")
        groups = list(chunks(KEYWORDS, MAX_GROUP_SIZE))
        random.shuffle(groups)  # avoid always hitting same group first

        now = datetime.now(timezone.utc)

        for group in groups:
            if self.stop_event.is_set():
                break

            df = self._fetch_group_daily(group)
            if df is None or df.empty:
                self.log(f"{group}: no data returned.")
                continue

            # Drop 'isPartial' if present
            if "isPartial" in df.columns:
                df = df.drop(columns=["isPartial"])

            # Coerce index to UTC once (df index is timestamps/dates)
            df.index = pd.to_datetime(df.index, errors='coerce')
            # These are date-like (no timezone); treat as naive dates at 00:00 UTC
            df.index = df.index.tz_localize('UTC')

            # For each keyword column, merge into local history and evaluate
            for kw in group:
                if kw not in df.columns:
                    self.log(f"{kw}: column missing in returned data.")
                    continue

                new_col = df[kw].astype(float)
                if self.trend_history[kw].empty:
                    merged = ensure_utc_index(new_col)
                else:
                    prior = ensure_utc_index(self.trend_history[kw].astype(float))
                    merged = pd.concat([prior, ensure_utc_index(new_col)])

                # Dedup dates, keep last
                merged = merged[~merged.index.duplicated(keep='last')]

                # Keep last N days
                cutoff = now - timedelta(days=HISTORY_DAYS_TO_KEEP)
                merged = merged[merged.index >= cutoff]
                self.trend_history[kw] = merged

                # Maybe regenerate delayed baseline
                self._maybe_regen_average_initial(kw, now)

                if len(merged) < (PREV_WINDOW_DAYS + 2):
                    self.log(f"{kw}: not enough history yet ({len(merged)} days).")
                    continue

                # Latest daily value (today or yesterday depending on Google availability)
                last_value = float(merged.iloc[-1])

                # Previous window (yesterday, or N days)
                prev_slice = merged.iloc[-(PREV_WINDOW_DAYS + 1):-1]
                max_prev = float(prev_slice.max()) if not prev_slice.empty else 0.0

                self.log(f"{kw}: latest={last_value}, prev_window_max={max_prev}")

                # Signal: newest >= multiplier * prev-window max
                if max_prev > 0 and last_value >= SIGNAL_JUMP_MULTIPLIER * max_prev:
                    # Respect alert cooldown
                    cooldown_until = self.alert_cooldown_until[kw]
                    if cooldown_until is not None and now < cooldown_until:
                        self.log(f"{kw}: signal detected but alert suppressed until {cooldown_until.isoformat()}.")
                        continue

                    # Baseline for metrics
                    x = [float(v) for v in merged.tolist()]
                    if self.avg_init[kw] is None:
                        self.avg_init[kw] = (sum(x) / len(x)) if len(x) > 0 else 1.0
                        self.log(f"{kw}: average_initial initialized = {round(self.avg_init[kw], 4)}")
                    else:
                        self.log(f"{kw}: using existing average_initial = {round(self.avg_init[kw], 4)}")

                    average_initial = self.avg_init[kw]

                    pop_list = popularity_list(x, average_initial)
                    w_pop_list = weighed_popularity_list(x, average_initial)
                    sig_list = significance_list(x, average_initial)
                    bal_sig_list = balanced_significance_list(x, average_initial)

                    latest_pop = pop_list[-1] if pop_list else 0.0
                    latest_w_pop = w_pop_list[-1] if w_pop_list else 0.0
                    latest_sig = sig_list[-1] if sig_list else 0.0
                    latest_bal_sig = bal_sig_list[-1] if bal_sig_list else 0.0

                    metrics = {
                        "popularity": latest_pop,
                        "weighed_popularity": latest_w_pop,
                        "significance": latest_sig,
                        "balanced_significance": latest_bal_sig
                    }

                    # Thresholds
                    if (latest_pop > ALERT_POPULARITY or
                        latest_w_pop > ALERT_WEIGHED_POPULARITY or
                        latest_sig > ALERT_SIGNIFICANCE or
                        latest_bal_sig > ALERT_BALANCED_SIGNIFICANCE):

                        # Fire alert
                        block = (
                            "\n" + "=" * 56 + "\n" +
                            f"🚨 ALERT TRIGGERED for {kw} 🚨\n"
                            f"Popularity: {metrics['popularity']}\n"
                            f"Weighed Popularity: {metrics['weighed_popularity']}\n"
                            f"Significance: {metrics['significance']}\n"
                            f"Balanced Significance: {metrics['balanced_significance']}\n" +
                            "=" * 56 + "\n"
                        )
                        self.log(block)

                        # Record timing + cooldown + schedule baseline regen later
                        self.last_alert_at[kw] = now
                        self.alert_cooldown_until[kw] = now + timedelta(days=ALERT_COOLDOWN_DAYS)
                        self.pending_regen_after_alert[kw] = now

                        # Append to CSV
                        row = {
                            "timestamp_utc": now.isoformat(),
                            "timestamp_et": now.astimezone(RUN_TZ).isoformat(),
                            "keyword": kw,
                            "average_initial_used": round(float(average_initial), 6),
                            "alert_cooldown_until": self.alert_cooldown_until[kw].isoformat(),
                            "baseline_regen_due_at": (now + timedelta(days=AVG_REGEN_AFTER_DAYS)).isoformat(),
                            **metrics
                        }
                        df_alert = pd.DataFrame([row])
                        if not os.path.exists(CSV_OUTPUT):
                            df_alert.to_csv(CSV_OUTPUT, index=False)
                        else:
                            df_alert.to_csv(CSV_OUTPUT, mode='a', header=False, index=False)

                        # === Queue trade for next RTH open ===
                        symbol = KEYWORD_TO_SYMBOL.get(kw)
                        if not symbol:
                            self.log(f"No ticker mapping for keyword '{kw}'. Skipping trade.")
                        else:
                            execute_at = next_us_rth_open_utc(after_dt_utc=now)
                            self.trade_exec.queue_trade(symbol, DEFAULT_BUY_QTY, execute_at)
                    else:
                        # No alert; nothing else
                        pass

        self.log("Daily scan complete.")

    # --------------- Main loop: run at 21:30 ET each day ---------------
    def run(self):
        while not self.stop_event.is_set():
            now_utc = datetime.now(timezone.utc)
            target_utc = next_run_dt_utc(now_utc)
            wait_s = (target_utc - now_utc).total_seconds()
            self.log(f"Next scan scheduled at {target_utc.isoformat()} (UTC) / {target_utc.astimezone(RUN_TZ).strftime('%Y-%m-%d %H:%M:%S')} ET.")

            # Sleep until next run, but wake cooperatively
            slept = 0.0
            while slept < wait_s and not self.stop_event.is_set():
                chunk = min(1.0, wait_s - slept)
                time.sleep(chunk)
                slept += chunk

            if self.stop_event.is_set():
                break

            # Run one daily scan
            try:
                self.run_daily_scan()
            except Exception as e:
                self.log(f"Error in daily scan: {repr(e)}")
                # brief pause before re-scheduling next day
                for _ in range(10):
                    if self.stop_event.is_set():
                        break
                    time.sleep(1)

# ---------- Tkinter GUI ----------
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Daily Google Trends Monitor (9:30 PM ET) + Tiger Trading")
        self.geometry("900x600")

        top = tk.Frame(self)
        top.pack(fill="x", padx=10, pady=10)

        self.start_btn = tk.Button(top, text="Start", command=self.start_monitor)
        self.start_btn.pack(side="left", padx=5)

        self.stop_btn = tk.Button(top, text="Stop", state="disabled", command=self.stop_monitor)
        self.stop_btn.pack(side="left", padx=5)

        cfg = f"Paper={USE_PAPER} • Timeframe={TRENDS_TIMEFRAME} (daily) • Cooldown={ALERT_COOLDOWN_DAYS}d • Baseline regen at +{AVG_REGEN_AFTER_DAYS}d (next {AVG_REGEN_WINDOW_DAYS}d)"
        self.info_label = tk.Label(top, text=cfg)
        self.info_label.pack(side="left", padx=15)

        self.log_area = ScrolledText(self, wrap="word", height=28)
        self.log_area.pack(fill="both", expand=True, padx=10, pady=10)

        self.log_q = queue.Queue()
        self.stop_event = threading.Event()
        self.worker = None

        self.after(200, self.drain_log_queue)
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def start_monitor(self):
        if self.worker and self.worker.is_alive():
            return
        self.stop_event.clear()
        self.worker = TrendsMonitor(self.log_q, self.stop_event)
        self.worker.start()
        self.start_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        self.append_log("Started daily scheduler.")

    def stop_monitor(self):
        if self.worker:
            self.stop_event.set()
            self.worker = None
        self.start_btn.config(state="normal")
        self.stop_btn.config(state="disabled")
        self.append_log("Stopped.")

    def drain_log_queue(self):
        try:
            while True:
                line = self.log_q.get_nowait()
                self.append_log(line)
        except queue.Empty:
            pass
        self.after(200, self.drain_log_queue)

    def append_log(self, text):
        self.log_area.insert("end", text + "\n")
        self.log_area.see("end")

    def on_close(self):
        self.stop_monitor()
        self.destroy()

if __name__ == "__main__":
    app = App()
    app.mainloop()
