"""
Solana meme signal bot - Render-safe public API version.

What this version fixes:
- Render Web Service timeout: starts a small HTTP health server on PORT.
- PumpPortal WebSocket reconnects automatically and has a recv timeout.
- New tokens go into a bounded worker queue instead of spawning unlimited threads.
- DEX Screener data is retried after launch because indexing can lag PumpPortal.
- Later-momentum scans are queued instead of doing blocking API work inline.
- Exact rejection reasons are logged.
- TP monitoring runs independently from launch scanning.
- Graceful handling of Telegram/API failures.

Public-data limitation:
This code does NOT pretend to know sniper/bundler/dev/smart-money status.
Those fields remain UNKNOWN unless a dedicated provider is connected.
"""

import html
import json
import logging
import os
import threading
import time
from collections import defaultdict, deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from queue import Empty, PriorityQueue
from urllib.parse import urlparse

import requests
import websocket
from dotenv import load_dotenv

load_dotenv()

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
)
log = logging.getLogger("meme-signal-bot")

# ============================================================
# CONFIG
# ============================================================

TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()
PUMP_API_KEY = os.getenv("PUMP_API_KEY", "").strip()
JUPITER_API_KEY = os.getenv("JUPITER_API_KEY", "").strip()

# Fixed strategy settings. Change these here if required.
DEX_POLL_SECONDS = 20
PROVIDER_TIMEOUT_SECONDS = 8
PROVIDER_COOLDOWN_SECONDS = 60

NEW_MAX_AGE_MINUTES = 15
LATER_MIN_AGE_MINUTES = 15
LATER_MAX_AGE_HOURS = 72

NEW_MIN_SCORE = 70
LATER_MIN_SCORE = 75

MIN_LIQUIDITY_USD = 8000
MIN_VOLUME_5M_USD = 5000
MIN_TXNS_5M = 30
MIN_BUY_RATIO = 0.55

MAX_TRACKED = 500
SIGNAL_COOLDOWN_SECONDS = 3600

TP1_X = 1.7
TP2_X = 2.0
FINAL_TARGET_X = 5.0

# Runtime controls
WORKER_COUNT = 2
NEW_RETRY_COUNT = 10
NEW_RETRY_DELAY_SECONDS = 12
GENERAL_RETRY_COUNT = 4
HEARTBEAT_SECONDS = 60
MAX_LATER_QUEUE_PER_CYCLE = 25

# APIs
DEX_URL = "https://api.dexscreener.com/tokens/v1/solana/"
GECKO_URL = "https://api.geckoterminal.com/api/v2/networks/solana/tokens/{mint}/pools"
JUPITER_URL = "https://api.jup.ag/price/v3"
SOLANA_RPC_URL = "https://api.mainnet-beta.solana.com"
PUMP_WS_URL = "wss://pumpportal.fun/api/data"

SESSION = requests.Session()
SESSION.headers.update({"User-Agent": "public-solana-meme-signal-bot/2.0"})

# ============================================================
# STATE
# ============================================================

tokens = {}                  # mint -> PumpPortal metadata
last_signal = {}             # mint -> unix timestamp
entry_price = {}             # mint -> signal price
tp_state = {}                # mint -> 0/1/2/3
price_history = defaultdict(lambda: deque(maxlen=30))
provider_fail_until = defaultdict(float)

state_lock = threading.RLock()
queue_lock = threading.Lock()
pending_jobs = set()

# Priority queue: (run_at, sequence, kind, mint, attempt)
job_queue = PriorityQueue(maxsize=2000)
job_sequence = 0

# Stats for heartbeat
stats = defaultdict(int)


def now_ts():
    return time.time()


def safe_float(value, default=0.0):
    try:
        if value is None or value == "":
            return default
        return float(value)
    except (TypeError, ValueError):
        return default


def safe_int(value, default=0):
    try:
        if value is None or value == "":
            return default
        return int(float(value))
    except (TypeError, ValueError):
        return default


def html_escape(value):
    return html.escape(str(value), quote=True)


def age_minutes(created_at):
    if not created_at:
        return 999999.0
    return max(0.0, (now_ts() - created_at) / 60.0)


def target_percent(target_x):
    # Keep the user's requested display convention: 5X -> +500%.
    return round(target_x * 100)


def target_label(target_x):
    return f"{target_x:g}X (+{target_percent(target_x)}%)"

# ============================================================
# HEALTH SERVER - IMPORTANT FOR RENDER WEB SERVICES
# ============================================================

class HealthHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        path = urlparse(self.path).path
        if path not in ("/", "/health", "/healthz"):
            self.send_response(404)
            self.end_headers()
            return

        with state_lock:
            token_count = len(tokens)
            signal_count = len(last_signal)

        body = json.dumps({
            "ok": True,
            "service": "solana-meme-signal-bot",
            "tokens_tracked": token_count,
            "signals": signal_count,
            "queue": job_queue.qsize(),
            "time": int(now_ts()),
        }).encode("utf-8")

        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, fmt, *args):
        return


def start_health_server():
    port = safe_int(os.getenv("PORT", "10000"), 10000)
    server = ThreadingHTTPServer(("0.0.0.0", port), HealthHandler)
    log.info("Health server listening on 0.0.0.0:%d", port)
    threading.Thread(target=server.serve_forever, daemon=True).start()

# ============================================================
# TELEGRAM
# ============================================================

def telegram_url(method):
    return f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/{method}"


def send_telegram(text, photo_url=None):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        log.error("Telegram credentials missing; message not delivered.")
        print("\n" + text + "\n")
        return False

    try:
        if photo_url:
            r = SESSION.post(
                telegram_url("sendPhoto"),
                data={
                    "chat_id": TELEGRAM_CHAT_ID,
                    "photo": photo_url,
                    "caption": text[:1024],
                    "parse_mode": "HTML",
                },
                timeout=PROVIDER_TIMEOUT_SECONDS,
            )
        else:
            r = SESSION.post(
                telegram_url("sendMessage"),
                data={
                    "chat_id": TELEGRAM_CHAT_ID,
                    "text": text[:4096],
                    "parse_mode": "HTML",
                    "disable_web_page_preview": False,
                },
                timeout=PROVIDER_TIMEOUT_SECONDS,
            )
        r.raise_for_status()
        result = r.json()
        if not result.get("ok", False):
            raise RuntimeError(result)
        return True
    except Exception as exc:
        log.error("Telegram send failed: %s", exc)
        stats["telegram_errors"] += 1
        return False

# ============================================================
# PROVIDER HELPERS
# ============================================================

def provider_available(name):
    return now_ts() >= provider_fail_until[name]


def mark_provider_failure(name):
    provider_fail_until[name] = now_ts() + PROVIDER_COOLDOWN_SECONDS
    stats[f"{name}_fail"] += 1


def get_dex_data(mint):
    """Primary market provider. Returns the best Solana pair."""
    if not provider_available("dexscreener"):
        return None
    try:
        r = SESSION.get(
            DEX_URL + mint,
            timeout=PROVIDER_TIMEOUT_SECONDS,
        )
        r.raise_for_status()
        data = r.json()
        pairs = data if isinstance(data, list) else data.get("pairs", [])
        sol_pairs = [p for p in pairs if p.get("chainId") == "solana"]
        if not sol_pairs:
            sol_pairs = pairs
        if not sol_pairs:
            return None
        sol_pairs.sort(
            key=lambda p: safe_float((p.get("liquidity") or {}).get("usd")),
            reverse=True,
        )
        stats["dex_ok"] += 1
        return sol_pairs[0]
    except Exception as exc:
        mark_provider_failure("dexscreener")
        log.warning("DEX Screener failed for %s: %s", mint, exc)
        return None


def get_gecko_data(mint):
    """Secondary provider. Used for price/liquidity if DEX Screener is unavailable.
    GeckoTerminal generally does not expose the same 5m buckets, so it cannot
    by itself satisfy the complete signal dataset.
    """
    if not provider_available("geckoterminal"):
        return None
    try:
        r = SESSION.get(
            GECKO_URL.format(mint=mint),
            timeout=PROVIDER_TIMEOUT_SECONDS,
        )
        r.raise_for_status()
        data = r.json().get("data", [])
        if not data:
            return None
        rows = []
        for item in data:
            a = item.get("attributes") or {}
            rows.append((safe_float(a.get("reserve_in_usd")), item))
        rows.sort(key=lambda x: x[0], reverse=True)
        stats["gecko_ok"] += 1
        return rows[0][1] if rows else None
    except Exception as exc:
        mark_provider_failure("geckoterminal")
        log.warning("GeckoTerminal failed for %s: %s", mint, exc)
        return None


def get_jupiter_price(mint):
    """Tertiary provider for a current price only."""
    if not JUPITER_API_KEY or not provider_available("jupiter"):
        return None
    try:
        r = SESSION.get(
            JUPITER_URL,
            params={"ids": mint},
            headers={"x-api-key": JUPITER_API_KEY},
            timeout=PROVIDER_TIMEOUT_SECONDS,
        )
        r.raise_for_status()
        data = r.json()
        row = data.get(mint) or {}
        price = safe_float(row.get("usdPrice") or row.get("price"))
        if price > 0:
            stats["jupiter_ok"] += 1
            return price
        return None
    except Exception as exc:
        mark_provider_failure("jupiter")
        log.warning("Jupiter failed for %s: %s", mint, exc)
        return None


def verify_mint_rpc(mint):
    """Final lightweight on-chain existence check."""
    try:
        r = SESSION.post(
            SOLANA_RPC_URL,
            json={
                "jsonrpc": "2.0",
                "id": 1,
                "method": "getAccountInfo",
                "params": [mint, {"encoding": "base64"}],
            },
            timeout=PROVIDER_TIMEOUT_SECONDS,
        )
        r.raise_for_status()
        data = r.json()
        return bool((data.get("result") or {}).get("value"))
    except Exception as exc:
        log.debug("Solana RPC verification failed for %s: %s", mint, exc)
        return False


def normalize_dex_pair(pair):
    txns = pair.get("txns") or {}
    volume = pair.get("volume") or {}
    change = pair.get("priceChange") or {}
    liq = pair.get("liquidity") or {}
    base = pair.get("baseToken") or {}
    info = pair.get("info") or {}

    tx5 = txns.get("m5") or {}
    vol5 = safe_float(volume.get("m5"))
    buys = safe_int(tx5.get("buys"))
    sells = safe_int(tx5.get("sells"))
    total_tx = buys + sells
    buy_ratio = buys / total_tx if total_tx else 0.0

    return {
        "name": base.get("name") or "Unknown",
        "symbol": base.get("symbol") or "???",
        "price": safe_float(pair.get("priceUsd")),
        "liquidity": safe_float(liq.get("usd")),
        "volume_5m": vol5,
        "buys_5m": buys,
        "sells_5m": sells,
        "txns_5m": total_tx,
        "buy_ratio": buy_ratio,
        "price_change_5m": safe_float(change.get("m5")),
        "price_change_1h": safe_float(change.get("h1")),
        "price_change_6h": safe_float(change.get("h6")),
        "price_change_24h": safe_float(change.get("h24")),
        "market_cap": safe_float(pair.get("marketCap")),
        "fdv": safe_float(pair.get("fdv")),
        "pair_created_at": safe_float(pair.get("pairCreatedAt")) / 1000.0 if pair.get("pairCreatedAt") else None,
        "dex_url": pair.get("url") or f"https://dexscreener.com/solana/{pair.get('pairAddress', '')}",
        "image": info.get("imageUrl"),
        "pair_address": pair.get("pairAddress"),
    }


def get_market_data(mint):
    """Try providers in order. Only DEX Screener currently provides the
    complete 5m dataset required by the strategy. Other providers prevent
    total price-data loss and are logged, but do not fabricate 5m metrics.
    """
    pair = get_dex_data(mint)
    if pair:
        d = normalize_dex_pair(pair)
        if d["price"] > 0:
            return d, "DEX_SCREENER"

    # Fallback providers are intentionally not converted into fake 5m data.
    gecko = get_gecko_data(mint)
    if gecko:
        attrs = gecko.get("attributes") or {}
        price = safe_float(attrs.get("base_token_price_usd"))
        liquidity = safe_float(attrs.get("reserve_in_usd"))
        log.info("FALLBACK GeckoTerminal %s price=%s liquidity=%s (5m data unavailable)", mint, price, liquidity)

    j_price = get_jupiter_price(mint)
    if j_price:
        log.info("FALLBACK Jupiter %s price=%s (5m data unavailable)", mint, j_price)

    return None, "NO_COMPLETE_MARKET_DATA"

# ============================================================
# SCORING
# ============================================================

def score_market(d):
    liq = d["liquidity"]
    vol = d["volume_5m"]
    tx = d["txns_5m"]
    br = d["buy_ratio"]

    if d["price"] <= 0:
        return None, "NO_PRICE"
    if liq < MIN_LIQUIDITY_USD:
        return None, f"LOW_LIQUIDITY ${liq:,.0f} < ${MIN_LIQUIDITY_USD:,.0f}"
    if vol < MIN_VOLUME_5M_USD:
        return None, f"LOW_5M_VOLUME ${vol:,.0f} < ${MIN_VOLUME_5M_USD:,.0f}"
    if tx < MIN_TXNS_5M:
        return None, f"LOW_5M_TXNS {tx} < {MIN_TXNS_5M}"
    if br < MIN_BUY_RATIO:
        return None, f"WEAK_BUY_PRESSURE {br * 100:.1f}% < {MIN_BUY_RATIO * 100:.0f}%"

    score = 0.0
    score += min(20.0, (liq / MIN_LIQUIDITY_USD) * 8.0)
    score += min(25.0, (vol / MIN_VOLUME_5M_USD) * 8.0)
    score += min(15.0, (tx / MIN_TXNS_5M) * 5.0)
    score += min(20.0, max(0.0, (br - MIN_BUY_RATIO) / (1.0 - MIN_BUY_RATIO)) * 20.0)

    p5 = d["price_change_5m"]
    p1 = d["price_change_1h"]
    if p5 > 0:
        score += min(10.0, p5 * 1.5)
    if p1 > 0:
        score += min(10.0, p1 * 0.5)

    return round(min(100.0, score), 1), None

# ============================================================
# SIGNAL LOGIC
# ============================================================

def signal_allowed(mint):
    return now_ts() - last_signal.get(mint, 0) >= SIGNAL_COOLDOWN_SECONDS


def remember_price(mint, price):
    if price > 0:
        price_history[mint].append((now_ts(), price))


def momentum_accelerating(mint):
    h = list(price_history[mint])
    if len(h) < 3:
        return False
    old_p = h[0][1]
    last_p = h[-1][1]
    return old_p > 0 and last_p > old_p


def build_signal(kind, mint, d, score):
    symbol = html_escape(d["symbol"])
    name = html_escape(d["name"])
    price = d["price"]
    liq = d["liquidity"]
    vol = d["volume_5m"]
    tx = d["txns_5m"]
    buys = d["buys_5m"]
    sells = d["sells_5m"]
    ratio = d["buy_ratio"] * 100
    p5 = d["price_change_5m"]
    p1 = d["price_change_1h"]
    mc = d["market_cap"]

    return (
        f"<b>{'🆕 NEW LAUNCH' if kind == 'NEW' else '🔥 LATER MOMENTUM'}</b>\n\n"
        f"<b>{symbol}</b> — {name}\n"
        f"<code>{html_escape(mint)}</code>\n\n"
        f"📊 <b>Score:</b> {score}/100\n"
        f"💵 <b>Price:</b> ${price:.10f}\n"
        f"💧 <b>Liquidity:</b> ${liq:,.0f}\n"
        f"📈 <b>5m Volume:</b> ${vol:,.0f}\n"
        f"🔄 <b>5m Txns:</b> {tx} (🟢 {buys} / 🔴 {sells})\n"
        f"🟢 <b>Buy pressure:</b> {ratio:.1f}%\n"
        f"🚀 <b>5m:</b> {p5:+.2f}% | <b>1h:</b> {p1:+.2f}%\n"
        f"💰 <b>Market Cap:</b> ${mc:,.0f}\n\n"
        f"<b>TP Plan</b>\n"
        f"• {target_label(TP1_X)} → book 25%\n"
        f"• {target_label(TP2_X)} → book 50% of remaining\n"
        f"• {target_label(FINAL_TARGET_X)} → book 100% of remaining\n\n"
        f"⚠️ Holder/sniper/bundler/dev/smart-money checks: <b>UNKNOWN</b>\n\n"
        f"📉 <a href=\"{html_escape(d['dex_url'])}\">Open chart / DEX Screener</a>\n"
        f"⚠️ <i>Momentum screen only; not a profit or safety guarantee.</i>"
    )


def evaluate(kind, mint, attempt=0):
    with state_lock:
        meta = tokens.get(mint)
    if not meta:
        return "DONE"

    age = age_minutes(meta.get("created_at"))
    if kind == "NEW":
        if age > NEW_MAX_AGE_MINUTES:
            return "DONE"
        min_score = NEW_MIN_SCORE
    else:
        if age < LATER_MIN_AGE_MINUTES or age > LATER_MAX_AGE_HOURS * 60:
            return "DONE"
        min_score = LATER_MIN_SCORE

    d, provider = get_market_data(mint)
    if not d:
        stats["no_market_data"] += 1
        log.info("WAIT | %s | %s | attempt=%d/%d", kind, mint, attempt, NEW_RETRY_COUNT if kind == "NEW" else GENERAL_RETRY_COUNT)
        return "RETRY"

    remember_price(mint, d["price"])

    if kind == "LATER" and d["price_change_5m"] <= 0 and not momentum_accelerating(mint):
        log.info("REJECT | LATER | %s | no positive momentum", mint)
        return "DONE"

    score, reject = score_market(d)
    if score is None:
        stats["rejected"] += 1
        log.info("REJECT | %s | %s | %s", kind, mint, reject)
        return "DONE"

    if score < min_score:
        stats["rejected"] += 1
        log.info("REJECT | %s | %s | score %.1f < %.1f", kind, mint, score, min_score)
        return "DONE"

    if not signal_allowed(mint):
        log.info("REJECT | %s | %s | duplicate cooldown", kind, mint)
        return "DONE"

    # Verify the mint immediately before signaling. Failure is retryable for NEW.
    if not verify_mint_rpc(mint):
        log.info("WAIT | %s | %s | Solana RPC verification unavailable", kind, mint)
        return "RETRY"

    with state_lock:
        last_signal[mint] = now_ts()
        entry_price[mint] = d["price"]
        tp_state[mint] = 0

    text = build_signal(kind, mint, d, score)
    delivered = send_telegram(text, d.get("image"))
    stats["signals"] += 1
    log.info("SIGNAL | %s | %s | score=%.1f | provider=%s | telegram=%s", kind, mint, score, provider, delivered)
    return "DONE"

# ============================================================
# JOB QUEUE
# ============================================================

def enqueue_job(kind, mint, attempt=0, delay=0):
    global job_sequence
    key = (kind, mint)
    with queue_lock:
        if key in pending_jobs:
            return False
        pending_jobs.add(key)
        job_sequence += 1
        try:
            job_queue.put_nowait((now_ts() + max(0, delay), job_sequence, kind, mint, attempt))
            return True
        except Exception:
            pending_jobs.discard(key)
            stats["queue_full"] += 1
            return False


def worker_loop(worker_id):
    while True:
        try:
            run_at, _, kind, mint, attempt = job_queue.get(timeout=5)
            wait = run_at - now_ts()
            if wait > 0:
                time.sleep(min(wait, 5))
                # Put it back if it is still not due.
                if run_at > now_ts():
                    with queue_lock:
                        pending_jobs.discard((kind, mint))
                    enqueue_job(kind, mint, attempt, run_at - now_ts())
                    job_queue.task_done()
                    continue

            with queue_lock:
                pending_jobs.discard((kind, mint))

            result = evaluate(kind, mint, attempt)
            max_attempts = NEW_RETRY_COUNT if kind == "NEW" else GENERAL_RETRY_COUNT
            if result == "RETRY" and attempt < max_attempts:
                delay = NEW_RETRY_DELAY_SECONDS * (attempt + 1) if kind == "NEW" else 20
                enqueue_job(kind, mint, attempt + 1, delay)
            elif result == "RETRY":
                log.info("GIVEUP | %s | %s | market data/RPC did not become available", kind, mint)

            job_queue.task_done()
        except Empty:
            continue
        except Exception:
            log.exception("Worker %s error", worker_id)
            time.sleep(1)

# ============================================================
# TP MONITOR
# ============================================================

def monitor_positions():
    while True:
        try:
            with state_lock:
                active = list(entry_price.items())

            for mint, entry in active:
                if entry <= 0:
                    continue
                d, _ = get_market_data(mint)
                if not d or d["price"] <= 0:
                    continue

                price = d["price"]
                multiple = price / entry
                with state_lock:
                    state = tp_state.get(mint, 0)

                if state < 1 and multiple >= TP1_X:
                    send_telegram(
                        f"🎯 <b>TP1 HIT — {html_escape(d['symbol'])}</b>\n"
                        f"Entry: ${entry:.10f}\nCurrent: ${price:.10f}\n"
                        f"Multiple: <b>{multiple:.2f}X</b>\n\n📌 Book <b>25%</b>."
                    )
                    with state_lock:
                        tp_state[mint] = 1

                elif state < 2 and multiple >= TP2_X:
                    send_telegram(
                        f"🎯 <b>TP2 HIT — {html_escape(d['symbol'])}</b>\n"
                        f"Entry: ${entry:.10f}\nCurrent: ${price:.10f}\n"
                        f"Multiple: <b>{multiple:.2f}X</b>\n\n📌 Book <b>50% of remaining</b>."
                    )
                    with state_lock:
                        tp_state[mint] = 2

                elif state < 3 and multiple >= FINAL_TARGET_X:
                    send_telegram(
                        f"🏁 <b>FINAL TARGET — {html_escape(d['symbol'])}</b>\n"
                        f"Entry: ${entry:.10f}\nCurrent: ${price:.10f}\n"
                        f"Multiple: <b>{multiple:.2f}X</b>\n\n📌 Book <b>100% of remaining</b>."
                    )
                    with state_lock:
                        tp_state[mint] = 3

                if d["liquidity"] < MIN_LIQUIDITY_USD * 0.65:
                    send_telegram(
                        f"🚨 <b>LIQUIDITY WARNING — {html_escape(d['symbol'])}</b>\n"
                        f"Liquidity now: ${d['liquidity']:,.0f}\n"
                        f"Review position immediately.\n"
                        f"📉 <a href=\"{html_escape(d['dex_url'])}\">Chart</a>"
                    )

            time.sleep(DEX_POLL_SECONDS)
        except Exception:
            log.exception("TP monitor error")
            time.sleep(DEX_POLL_SECONDS)

# ============================================================
# PUMPPORTAL
# ============================================================

def parse_new_token(msg):
    mint = msg.get("mint") or msg.get("token") or msg.get("address")
    if not mint:
        return None

    created = msg.get("createdAt") or msg.get("timestamp")
    if created:
        created = safe_float(created)
        if created > 10_000_000_000:
            created /= 1000.0
    else:
        created = now_ts()

    return {
        "mint": mint,
        "name": msg.get("name") or "Unknown",
        "symbol": msg.get("symbol") or "???",
        "created_at": created,
        "uri": msg.get("uri"),
        "raw": msg,
    }


def store_token(token):
    mint = token["mint"]
    with state_lock:
        tokens[mint] = token
        if len(tokens) > MAX_TRACKED:
            oldest = min(tokens.items(), key=lambda kv: kv[1].get("created_at", now_ts()))[0]
            tokens.pop(oldest, None)

    stats["tokens_seen"] += 1
    log.info("New token: %s (%s) %s", token["symbol"], token["name"], mint)

    # Retry because DEX Screener may need several seconds to index the pair.
    enqueue_job("NEW", mint, 0, 5)


def pump_ws_loop():
    while True:
        ws = None
        try:
            url = PUMP_WS_URL
            if PUMP_API_KEY:
                url += "?api-key=" + PUMP_API_KEY

            log.info("Connecting to PumpPortal...")
            ws = websocket.create_connection(
                url,
                timeout=20,
                enable_multithread=True,
            )
            ws.settimeout(20)
            ws.send(json.dumps({"method": "subscribeNewToken"}))
            ws.send(json.dumps({"method": "subscribeMigration"}))
            log.info("PumpPortal connected.")
            stats["ws_connected"] += 1

            while True:
                try:
                    raw = ws.recv()
                except websocket.WebSocketTimeoutException:
                    # A timeout is not a crash. Ping and continue; reconnect if ping fails.
                    ws.ping()
                    log.debug("PumpPortal heartbeat ping")
                    continue

                if not raw:
                    raise RuntimeError("PumpPortal returned empty frame")

                try:
                    msg = json.loads(raw)
                except json.JSONDecodeError:
                    continue

                token = parse_new_token(msg)
                if token:
                    store_token(token)

        except Exception as exc:
            stats["ws_errors"] += 1
            log.warning("PumpPortal disconnected: %s; reconnecting in 3s...", exc)
            try:
                if ws:
                    ws.close()
            except Exception:
                pass
            time.sleep(3)

# ============================================================
# LATER MOMENTUM
# ============================================================

def later_momentum_loop():
    while True:
        try:
            with state_lock:
                items = list(tokens.items())

            queued = 0
            # Process newest tokens first; cap each cycle to avoid API bursts.
            items.sort(key=lambda kv: kv[1].get("created_at", 0), reverse=True)
            for mint, meta in items:
                if queued >= MAX_LATER_QUEUE_PER_CYCLE:
                    break
                age = age_minutes(meta.get("created_at"))
                if LATER_MIN_AGE_MINUTES <= age <= LATER_MAX_AGE_HOURS * 60:
                    if enqueue_job("LATER", mint, 0, 0):
                        queued += 1

            log.info("SCAN | later queued=%d tracked=%d queue=%d", queued, len(items), job_queue.qsize())
            time.sleep(DEX_POLL_SECONDS)
        except Exception:
            log.exception("Later momentum scanner error")
            time.sleep(10)

# ============================================================
# HEARTBEAT / CONFIG
# ============================================================

def heartbeat_loop():
    while True:
        try:
            with state_lock:
                tc = len(tokens)
                sc = len(last_signal)
            log.info(
                "HEARTBEAT | alive=YES | tokens=%d | signals=%d | queue=%d | ws=%d | rejected=%d | market_wait=%d",
                tc,
                sc,
                job_queue.qsize(),
                stats["ws_connected"],
                stats["rejected"],
                stats["no_market_data"],
            )
            time.sleep(HEARTBEAT_SECONDS)
        except Exception:
            time.sleep(HEARTBEAT_SECONDS)


def validate_config():
    if not TELEGRAM_BOT_TOKEN:
        log.warning("TELEGRAM_BOT_TOKEN is empty")
    if not TELEGRAM_CHAT_ID:
        log.warning("TELEGRAM_CHAT_ID is empty")
    if not JUPITER_API_KEY:
        log.info("JUPITER_API_KEY empty: Jupiter fallback disabled")

    log.info(
        "Config: NEW<=%.1fm | LATER %.1fm-%.1fh | liquidity>=$%.0f | volume5m>=$%.0f | txns5m>=%d | buy>=%.0f%% | TP=%s/%s/%s",
        NEW_MAX_AGE_MINUTES,
        LATER_MIN_AGE_MINUTES,
        LATER_MAX_AGE_HOURS,
        MIN_LIQUIDITY_USD,
        MIN_VOLUME_5M_USD,
        MIN_TXNS_5M,
        MIN_BUY_RATIO * 100,
        target_label(TP1_X),
        target_label(TP2_X),
        target_label(FINAL_TARGET_X),
    )


def main():
    validate_config()
    start_health_server()

    # Start workers first so the WS can immediately enqueue tokens.
    for i in range(WORKER_COUNT):
        threading.Thread(target=worker_loop, args=(i + 1,), daemon=True, name=f"scanner-{i+1}").start()

    threading.Thread(target=pump_ws_loop, daemon=True, name="pumpportal-ws").start()
    threading.Thread(target=later_momentum_loop, daemon=True, name="later-scanner").start()
    threading.Thread(target=monitor_positions, daemon=True, name="tp-monitor").start()
    threading.Thread(target=heartbeat_loop, daemon=True, name="heartbeat").start()

    log.info("Public API meme signal bot started and Render health endpoint is active.")

    # Keep the main process alive forever. Render can now see the PORT listener.
    while True:
        time.sleep(3600)


if __name__ == "__main__":
    main()
