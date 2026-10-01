"""
Public/free Solana meme signal bot
----------------------------------
Data:
  - PumpPortal WebSocket: free subscribeNewToken / subscribeMigration
  - DEX Screener public API: token/pair market data
  - Telegram Bot API: signal delivery

Important:
  This version deliberately does NOT claim to detect sniper/bundler/dev/smart-money
  unless a dedicated provider is connected. Those fields are marked UNKNOWN.
  It is a momentum screener, not a guarantee of safety or profit.

Run:
  1. pip install -r requirements.txt
  2. copy .env.example values into .env
  3. python bot.py
"""

import json
import logging
import os
import threading
import time
from collections import defaultdict, deque
from datetime import datetime, timezone

import requests
import websocket
from dotenv import load_dotenv

load_dotenv()

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
)
log = logging.getLogger("meme-signal-bot")


# ---------------- CONFIG ----------------

TELEGRAM_BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()

# PumpPortal's new-token stream is free. API key is optional for this
# particular subscription, but can be supplied if you have one.
PUMP_API_KEY = os.getenv("PUMP_API_KEY", "").strip()

DEX_POLL_SECONDS = int(os.getenv("DEX_POLL_SECONDS", "20"))
NEW_MAX_AGE_MINUTES = float(os.getenv("NEW_MAX_AGE_MINUTES", "15"))
LATER_MIN_AGE_MINUTES = float(os.getenv("LATER_MIN_AGE_MINUTES", "15"))
LATER_MAX_AGE_HOURS = float(os.getenv("LATER_MAX_AGE_HOURS", "72"))

NEW_MIN_SCORE = float(os.getenv("NEW_MIN_SCORE", "70"))
LATER_MIN_SCORE = float(os.getenv("LATER_MIN_SCORE", "75"))

MIN_LIQUIDITY_USD = float(os.getenv("MIN_LIQUIDITY_USD", "8000"))
MIN_VOLUME_5M_USD = float(os.getenv("MIN_VOLUME_5M_USD", "5000"))
MIN_TXNS_5M = int(os.getenv("MIN_TXNS_5M", "30"))
MIN_BUY_RATIO = float(os.getenv("MIN_BUY_RATIO", "0.55"))

MAX_TRACKED = int(os.getenv("MAX_TRACKED", "500"))
SIGNAL_COOLDOWN_SECONDS = int(os.getenv("SIGNAL_COOLDOWN_SECONDS", "3600"))

TP1_X = float(os.getenv("TP1_X", "1.7"))
TP2_X = float(os.getenv("TP2_X", "2.0"))
FINAL_TARGET_X = float(os.getenv("FINAL_TARGET_X", "3.0"))

# DEX Screener documents 300 req/min for token/pair endpoints.
# We stay far below that by polling one batch of tokens each cycle.
DEX_URL = "https://api.dexscreener.com/tokens/v1/solana/"


# ---------------- STATE ----------------

tokens = {}                  # mint -> token metadata
last_signal = {}             # mint -> unix time
entry_price = {}             # mint -> signal price
tp_state = {}                # mint -> 0/1/2/3
price_history = defaultdict(lambda: deque(maxlen=20))
lock = threading.Lock()


# ---------------- HELPERS ----------------

def now_ts():
    return time.time()


def age_minutes(created_at):
    if not created_at:
        return 999999.0
    return max(0.0, (now_ts() - created_at) / 60.0)


def safe_float(value, default=0.0):
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def safe_int(value, default=0):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def html_escape(s):
    return (
        str(s)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
    )


# ---------------- TELEGRAM ----------------

def telegram_url(method):
    return f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/{method}"


def send_telegram(text, photo_url=None):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        log.warning("Telegram credentials missing; signal printed only.")
        print("\n" + text + "\n")
        return False

    try:
        if photo_url:
            r = requests.post(
                telegram_url("sendPhoto"),
                data={
                    "chat_id": TELEGRAM_CHAT_ID,
                    "photo": photo_url,
                    "caption": text[:1024],
                    "parse_mode": "HTML",
                },
                timeout=15,
            )
        else:
            r = requests.post(
                telegram_url("sendMessage"),
                data={
                    "chat_id": TELEGRAM_CHAT_ID,
                    "text": text[:4096],
                    "parse_mode": "HTML",
                    "disable_web_page_preview": False,
                },
                timeout=15,
            )

        r.raise_for_status()
        return True
    except Exception as exc:
        log.exception("Telegram error: %s", exc)
        return False


# ---------------- DEX SCREENER ----------------

def get_dex_data(mint):
    """Return the best Solana pair for a token."""
    try:
        r = requests.get(
            DEX_URL + mint,
            timeout=10,
            headers={"User-Agent": "public-solana-meme-signal-bot/1.0"},
        )
        r.raise_for_status()
        data = r.json()

        pairs = data if isinstance(data, list) else data.get("pairs", [])
        if not pairs:
            return None

        sol_pairs = [p for p in pairs if p.get("chainId") == "solana"]
        if not sol_pairs:
            sol_pairs = pairs

        # Prefer the pair with the largest USD liquidity.
        sol_pairs.sort(
            key=lambda p: safe_float((p.get("liquidity") or {}).get("usd")),
            reverse=True,
        )
        return sol_pairs[0]
    except Exception as exc:
        log.debug("DEX lookup failed for %s: %s", mint, exc)
        return None


def normalize_pair(pair):
    txns = pair.get("txns") or {}
    volume = pair.get("volume") or {}
    change = pair.get("priceChange") or {}
    liq = pair.get("liquidity") or {}
    base = pair.get("baseToken") or {}
    info = pair.get("info") or {}

    # DEX Screener normally exposes 5m values when that bucket exists.
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
        "pair_created_at": safe_float(pair.get("pairCreatedAt")) / 1000.0
        if pair.get("pairCreatedAt") else None,
        "dex_url": pair.get("url") or f"https://dexscreener.com/solana/{pair.get('pairAddress', '')}",
        "image": info.get("imageUrl"),
        "pair_address": pair.get("pairAddress"),
    }


# ---------------- SCORING ----------------

def score_market(d):
    """
    Public-data momentum score.
    Max = 100.

    Hard rejection:
      - no/very low liquidity
      - insufficient 5m volume
      - insufficient transactions
      - weak buy ratio
    """
    liq = d["liquidity"]
    vol = d["volume_5m"]
    tx = d["txns_5m"]
    br = d["buy_ratio"]

    if liq < MIN_LIQUIDITY_USD:
        return None, "LOW_LIQUIDITY"
    if vol < MIN_VOLUME_5M_USD:
        return None, "LOW_5M_VOLUME"
    if tx < MIN_TXNS_5M:
        return None, "LOW_5M_TXNS"
    if br < MIN_BUY_RATIO:
        return None, "WEAK_BUY_PRESSURE"

    score = 0.0

    # Liquidity: 0-20
    score += min(20.0, (liq / MIN_LIQUIDITY_USD) * 8.0)

    # Volume: 0-25
    score += min(25.0, (vol / MIN_VOLUME_5M_USD) * 8.0)

    # Transactions: 0-15
    score += min(15.0, (tx / MIN_TXNS_5M) * 5.0)

    # Buy pressure: 0-20
    score += min(20.0, max(0.0, (br - MIN_BUY_RATIO) / (1.0 - MIN_BUY_RATIO)) * 20.0)

    # Price momentum: 0-20
    p5 = d["price_change_5m"]
    p1 = d["price_change_1h"]

    if p5 > 0:
        score += min(10.0, p5 * 1.5)
    if p1 > 0:
        score += min(10.0, p1 * 0.5)

    return round(min(100.0, score), 1), None


# ---------------- SIGNALS ----------------

def signal_allowed(mint):
    return now_ts() - last_signal.get(mint, 0) >= SIGNAL_COOLDOWN_SECONDS


def remember_price(mint, price):
    if price > 0:
        price_history[mint].append((now_ts(), price))


def momentum_accelerating(mint):
    h = list(price_history[mint])
    if len(h) < 3:
        return False

    # Simple public-data acceleration check:
    # latest price should be above the oldest tracked price and recent delta positive.
    old_t, old_p = h[0]
    _, last_p = h[-1]
    if old_p <= 0:
        return False
    return last_p > old_p


def build_signal(kind, mint, meta, d, score):
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

    safety_note = (
        "⚠️ Holder/sniper/bundler/dev checks: <b>UNKNOWN</b> "
        "(public-data version)"
    )

    return (
        f"<b>{'🆕 NEW LAUNCH' if kind == 'NEW' else '🔥 LATER MOMENTUM'}</b>\n\n"
        f"<b>{symbol}</b> — {name}\n"
        f"<code>{mint}</code>\n\n"
        f"📊 <b>Score:</b> {score}/100\n"
        f"💵 <b>Price:</b> ${price:.10f}\n"
        f"💧 <b>Liquidity:</b> ${liq:,.0f}\n"
        f"📈 <b>5m Volume:</b> ${vol:,.0f}\n"
        f"🔄 <b>5m Txns:</b> {tx}  (🟢 {buys} / 🔴 {sells})\n"
        f"🟢 <b>Buy pressure:</b> {ratio:.1f}%\n"
        f"🚀 <b>5m:</b> {p5:+.2f}% | <b>1h:</b> {p1:+.2f}%\n"
        f"💰 <b>Market Cap:</b> ${mc:,.0f}\n\n"
        f"<b>TP Plan</b>\n"
        f"• {TP1_X}X → book 25%\n"
        f"• {TP2_X}X → book 50% of remaining\n"
        f"• {FINAL_TARGET_X}X → book 100% of remaining\n\n"
        f"{safety_note}\n\n"
        f"📉 <a href=\"{html_escape(d['dex_url'])}\">Open chart / DEX Screener</a>\n"
        f"⚠️ <i>Signal is a momentum screen, not a profit guarantee.</i>"
    )


def maybe_signal(kind, mint):
    with lock:
        meta = tokens.get(mint)
    if not meta:
        return

    d_raw = get_dex_data(mint)
    if not d_raw:
        return

    d = normalize_pair(d_raw)
    remember_price(mint, d["price"])

    age = age_minutes(meta.get("created_at"))

    if kind == "NEW":
        if age > NEW_MAX_AGE_MINUTES:
            return
        min_score = NEW_MIN_SCORE
    else:
        if age < LATER_MIN_AGE_MINUTES or age > LATER_MAX_AGE_HOURS * 60:
            return
        # Later momentum requires positive recent momentum.
        if d["price_change_5m"] <= 0 and not momentum_accelerating(mint):
            return
        min_score = LATER_MIN_SCORE

    score, reject = score_market(d)
    if score is None or score < min_score:
        return

    if not signal_allowed(mint):
        return

    with lock:
        last_signal[mint] = now_ts()
        entry_price[mint] = d["price"]
        tp_state[mint] = 0

    text = build_signal(kind, mint, meta, d, score)
    send_telegram(text, d.get("image"))
    log.info("SIGNAL %s %s score=%s", kind, mint, score)


# ---------------- TP MONITOR ----------------

def monitor_positions():
    while True:
        try:
            with lock:
                active = list(entry_price.items())

            for mint, entry in active:
                if entry <= 0:
                    continue

                d_raw = get_dex_data(mint)
                if not d_raw:
                    continue

                d = normalize_pair(d_raw)
                price = d["price"]
                if price <= 0:
                    continue

                multiple = price / entry

                with lock:
                    state = tp_state.get(mint, 0)

                if state < 1 and multiple >= TP1_X:
                    send_telegram(
                        f"🎯 <b>TP1 HIT — {html_escape(d['symbol'])}</b>\n"
                        f"Entry: ${entry:.10f}\n"
                        f"Current: ${price:.10f}\n"
                        f"Multiple: <b>{multiple:.2f}X</b>\n\n"
                        f"📌 Book <b>25%</b>."
                    )
                    with lock:
                        tp_state[mint] = 1

                elif state < 2 and multiple >= TP2_X:
                    send_telegram(
                        f"🎯 <b>TP2 HIT — {html_escape(d['symbol'])}</b>\n"
                        f"Entry: ${entry:.10f}\n"
                        f"Current: ${price:.10f}\n"
                        f"Multiple: <b>{multiple:.2f}X</b>\n\n"
                        f"📌 Book <b>50% of remaining</b>."
                    )
                    with lock:
                        tp_state[mint] = 2

                elif state < 3 and multiple >= FINAL_TARGET_X:
                    send_telegram(
                        f"🏁 <b>FINAL TARGET — {html_escape(d['symbol'])}</b>\n"
                        f"Entry: ${entry:.10f}\n"
                        f"Current: ${price:.10f}\n"
                        f"Multiple: <b>{multiple:.2f}X</b>\n\n"
                        f"📌 Book <b>100% of remaining</b>."
                    )
                    with lock:
                        tp_state[mint] = 3

                # Public DEX data can also indicate a sharp liquidity collapse.
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


# ---------------- PUMPPORTAL WS ----------------

def parse_new_token(msg):
    """
    PumpPortal creation messages commonly contain mint/name/symbol/uri.
    We accept multiple field spellings to be tolerant of API changes.
    """
    mint = msg.get("mint") or msg.get("token") or msg.get("address")
    if not mint:
        return None

    name = msg.get("name") or "Unknown"
    symbol = msg.get("symbol") or "???"

    # PumpPortal's creation timestamp may be absent; use receipt time.
    created = msg.get("createdAt") or msg.get("timestamp")
    if created:
        created = safe_float(created)
        # Convert milliseconds if necessary.
        if created > 10_000_000_000:
            created /= 1000.0
    else:
        created = now_ts()

    return {
        "mint": mint,
        "name": name,
        "symbol": symbol,
        "created_at": created,
        "uri": msg.get("uri"),
        "raw": msg,
    }


def pump_ws_loop():
    while True:
        try:
            url = "wss://pumpportal.fun/api/data"
            if PUMP_API_KEY:
                url += "?api-key=" + PUMP_API_KEY

            log.info("Connecting to PumpPortal...")
            ws = websocket.create_connection(url, timeout=30)

            # Free new-token stream.
            ws.send(json.dumps({"method": "subscribeNewToken"}))

            # Migration stream is also free and helps us notice tokens
            # reaching a DEX pool.
            ws.send(json.dumps({"method": "subscribeMigration"}))

            log.info("PumpPortal connected.")

            while True:
                raw = ws.recv()
                if not raw:
                    continue

                try:
                    msg = json.loads(raw)
                except json.JSONDecodeError:
                    continue

                token = parse_new_token(msg)
                if not token:
                    continue

                mint = token["mint"]

                with lock:
                    tokens[mint] = token

                    # Prevent unlimited memory growth.
                    if len(tokens) > MAX_TRACKED:
                        oldest = min(
                            tokens.items(),
                            key=lambda kv: kv[1].get("created_at", now_ts()),
                        )[0]
                        tokens.pop(oldest, None)

                log.info(
                    "New token: %s (%s) %s",
                    token["symbol"],
                    token["name"],
                    mint,
                )

                # Give DEX Screener a moment to index the pair.
                threading.Thread(
                    target=delayed_new_check,
                    args=(mint,),
                    daemon=True,
                ).start()

        except Exception as exc:
            log.warning("PumpPortal disconnected: %s; reconnecting...", exc)
            time.sleep(3)


def delayed_new_check(mint):
    time.sleep(5)
    maybe_signal("NEW", mint)


# ---------------- LATER MOMENTUM SCAN ----------------

def later_momentum_loop():
    while True:
        try:
            with lock:
                items = list(tokens.items())

            for mint, meta in items:
                age = age_minutes(meta.get("created_at"))
                if LATER_MIN_AGE_MINUTES <= age <= LATER_MAX_AGE_HOURS * 60:
                    maybe_signal("LATER", mint)

            time.sleep(max(DEX_POLL_SECONDS, 20))
        except Exception:
            log.exception("Later momentum scanner error")
            time.sleep(20)


# ---------------- MAIN ----------------

def validate_config():
    if not TELEGRAM_BOT_TOKEN:
        log.warning("TELEGRAM_BOT_TOKEN is empty.")
    if not TELEGRAM_CHAT_ID:
        log.warning("TELEGRAM_CHAT_ID is empty.")

    log.info(
        "Config: NEW<=%.1fm | LATER %.1fm-%.1fh | "
        "min liquidity=$%.0f | min 5m volume=$%.0f | min txns=%d",
        NEW_MAX_AGE_MINUTES,
        LATER_MIN_AGE_MINUTES,
        LATER_MAX_AGE_HOURS,
        MIN_LIQUIDITY_USD,
        MIN_VOLUME_5M_USD,
        MIN_TXNS_5M,
    )


def main():
    validate_config()

    threading.Thread(target=pump_ws_loop, daemon=True).start()
    threading.Thread(target=later_momentum_loop, daemon=True).start()
    threading.Thread(target=monitor_positions, daemon=True).start()

    log.info("Public API meme signal bot started.")

    while True:
        time.sleep(3600)


if __name__ == "__main__":
    main()
