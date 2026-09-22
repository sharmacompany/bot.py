
import os
import asyncio
import json
import time
import logging
from datetime import datetime, timezone, timedelta
from io import BytesIO
from collections import defaultdict, deque
from urllib.parse import quote

try:
    import asyncpg
except ImportError:
    asyncpg = None

import aiohttp
from aiohttp import web
from dotenv import load_dotenv
from aiogram import Bot, Dispatcher, F
from aiogram.dispatcher.middlewares.base import BaseMiddleware
from aiogram.filters import Command
from aiogram.types import (
    Message, BufferedInputFile, InlineKeyboardMarkup,
    InlineKeyboardButton, CallbackQuery
)
from PIL import Image, ImageDraw, ImageFont

load_dotenv()
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO").upper()

# Global API reliability controls. These values are used by the HTTP/RPC
# request helpers below; they are not just informational .env settings.
API_MAX_RETRIES = max(0, int(os.getenv("API_RETRY_COUNT", os.getenv("API_MAX_RETRIES", "3"))))
API_RETRY_BACKOFF_SECONDS = max(0.1, float(os.getenv("API_RETRY_BACKOFF_SECONDS", "1.0")))
PROVIDER_MIN_INTERVAL_SECONDS = max(0.0, float(os.getenv("PROVIDER_MIN_INTERVAL_SECONDS", "0.05")))
PROVIDER_LATENCY_WARN_SECONDS = max(0.1, float(os.getenv("PROVIDER_LATENCY_WARN_SECONDS", "3.0")))
PROVIDER_HEALTH_WINDOW = max(3, int(os.getenv("PROVIDER_HEALTH_WINDOW", "20")))
HELIUS_SAFE_DAILY_RESERVE = max(0.0, float(os.getenv("HELIUS_SAFE_DAILY_RESERVE", "250")))
HELIUS_SAFE_MONTHLY_RESERVE = max(0.0, float(os.getenv("HELIUS_SAFE_MONTHLY_RESERVE", "5000")))

# ============================================================
# HELIUS HARD USAGE GUARD
# ============================================================
# Conservative accounting: the bot will reserve credits BEFORE every Helius
# HTTP/RPC attempt. The shared monthly ceiling is 950,000 credits.
HELIUS_MONTHLY_CREDIT_CAP = 950_000.0
# Combined Helius API + RPC + WSS daily ceiling.
HELIUS_DAILY_CREDIT_CAP = 31_000.0
HELIUS_RPS_CAP = max(1.0, min(8.0, float(os.getenv("HELIUS_RPS_CAP", "7.0"))))
HELIUS_HTTP_DEFAULT_COST = 10.0
HELIUS_ENHANCED_COST = 100.0
HELIUS_WSS_CREDITS_PER_MB = 20.0
HELIUS_USAGE_WARN = 0.80
HELIUS_USAGE_CRITICAL = 0.90
HELIUS_HARD_CAP_REQUIRE_DB = os.getenv("HELIUS_HARD_CAP_REQUIRE_DB", "true").lower() in {"1", "true", "yes", "on"}
_helius_usage_lock = asyncio.Lock()
_helius_month_used = 0.0
_helius_month_key = None
_helius_day_key = None
_helius_day_used = 0.0
_helius_rps_times = deque()


# ============================================================
# CONFIG
# ============================================================

BOT_TOKEN = os.getenv("BOT_TOKEN", "")
FREE_CHANNEL_ID = os.getenv("FREE_CHANNEL_ID", "")
PREMIUM_CHANNEL_ID = os.getenv("PREMIUM_CHANNEL_ID", "")
ADMIN_IDS = {int(x) for x in os.getenv("ADMIN_IDS", "").split(",") if x.strip().isdigit()}

# Use your own private provider endpoint/key. Do not commit these to GitHub.
HELIUS_API_KEY = os.getenv("HELIUS_API_KEY", "")
HELIUS_RPC_URL = (
    os.getenv("HELIUS_RPC_URL")
    or (f"https://mainnet.helius-rpc.com/?api-key={HELIUS_API_KEY}"
        if HELIUS_API_KEY else "")
)
HELIUS_WSS_URL = (
    os.getenv("HELIUS_WSS_URL")
    or (f"wss://mainnet.helius-rpc.com/?api-key={HELIUS_API_KEY}"
        if HELIUS_API_KEY else "")
)

ALCHEMY_RPC = os.getenv("ALCHEMY_RPC", "")
QUICKNODE_RPC = os.getenv("QUICKNODE_RPC", "")
QUICKNODE_WSS = os.getenv("QUICKNODE_WSS", "")
# Backward-compatible aliases for the longer variable names.
ALCHEMY_SOLANA_RPC_URL = os.getenv("ALCHEMY_SOLANA_RPC_URL", "") or ALCHEMY_RPC
QUICKNODE_RPC_URL = os.getenv("QUICKNODE_RPC_URL", "") or QUICKNODE_RPC
QUICKNODE_WSS_URL = os.getenv("QUICKNODE_WSS_URL", "") or QUICKNODE_WSS

# ============================================================
# PROVIDER FAILOVER ORDER
# ============================================================
# Helius is intentionally FIRST. When its hard daily/monthly credit guard
# blocks a request (for example after the 31k daily cap), rpc_call/http
# failover continues into the public pool below. Public endpoints are shared
# and rate-limited, so they are a fallback pool, not an unlimited quota.
DEFAULT_PUBLIC_RPC_URLS = [
    # Verified public Solana mainnet endpoints. Keep questionable/
    # provider-specific URLs out of the default pool so a bad DNS name
    # cannot repeatedly poison failover. Add more through RPC_SLOT_1..5.
    "https://api.mainnet-beta.solana.com",
    "https://rpc.publicnode.com",
    "https://solana.api.onfinality.io/public",
]
DEFAULT_PUBLIC_WSS_URLS = [
    "wss://api.mainnet-beta.solana.com",
    "wss://solana-rpc.publicnode.com",
    "wss://solana.api.onfinality.io/public-ws",
]

# Optional extra public endpoints can be supplied in .env; the three defaults
# above always remain first unless duplicates are removed.
_extra_free_rpc = [x.strip() for x in os.getenv("FREE_RPC_URLS", "").split(",") if x.strip()]
_extra_free_wss = [x.strip() for x in os.getenv("FREE_WSS_URLS", "").split(",") if x.strip()]

# Optional provider slots for additional RPC/WSS failover endpoints.
_PROVIDER_RPC_SLOTS = [os.getenv(f"RPC_SLOT_{i}", "").strip() for i in range(1, 6)]
_PROVIDER_WSS_SLOTS = [os.getenv(f"WSS_SLOT_{i}", "").strip() for i in range(1, 6)]
# RPC_SLOT_1..5 / WSS_SLOT_1..5 may be used for additional public or private failover URLs.
_extra_free_rpc.extend(x for x in _PROVIDER_RPC_SLOTS if x)
_extra_free_wss.extend(x for x in _PROVIDER_WSS_SLOTS if x)

def _unique_urls(items):
    out = []
    for item in items:
        if item and item not in out:
            out.append(item)
    return out

FREE_RPC_PROVIDERS = _unique_urls(DEFAULT_PUBLIC_RPC_URLS + _extra_free_rpc)
FREE_WSS_PROVIDERS = _unique_urls(DEFAULT_PUBLIC_WSS_URLS + _extra_free_wss)

PRIVATE_RPC_PROVIDERS = _unique_urls([
    HELIUS_RPC_URL,
    ALCHEMY_SOLANA_RPC_URL,
    QUICKNODE_RPC_URL,
])
PRIVATE_WSS_PROVIDERS = _unique_urls([
    HELIUS_WSS_URL,
    QUICKNODE_WSS_URL,
])

# Final strict order: Helius FIRST, then 5 public RPC / public WSS fallbacks,
# then any additional private providers configured in .env.
# This is what makes the Helius 31k/day guard an actual failover trigger.
_HELIUS_RPC_FIRST = [u for u in [HELIUS_RPC_URL] if u]
_HELIUS_WSS_FIRST = [u for u in [HELIUS_WSS_URL] if u]
RPC_URLS = (
    _unique_urls(_HELIUS_RPC_FIRST + FREE_RPC_PROVIDERS)
    + [u for u in PRIVATE_RPC_PROVIDERS if u not in _HELIUS_RPC_FIRST and u not in FREE_RPC_PROVIDERS]
)
WSS_PROVIDERS = (
    _unique_urls(_HELIUS_WSS_FIRST + FREE_WSS_PROVIDERS)
    + [u for u in PRIVATE_WSS_PROVIDERS if u not in _HELIUS_WSS_FIRST and u not in FREE_WSS_PROVIDERS]
)
WSS_URL = WSS_PROVIDERS[0] if WSS_PROVIDERS else ""

# Program IDs can be extended in .env.
PUMPFUN_PROGRAM_ID = os.getenv("PUMPFUN_PROGRAM_ID", "").strip()
WATCH_PROGRAM_IDS = [
    x.strip() for x in os.getenv("WATCH_PROGRAM_IDS", "").split(",") if x.strip()
]

# Comma-separated wallets that YOU designate as smart-money wallets.
SMART_MONEY_WALLETS = {
    x.strip() for x in os.getenv("SMART_MONEY_WALLETS", "").split(",") if x.strip()
}

DAILY_SIGNAL_HOUR_UTC = int(os.getenv("DAILY_SIGNAL_HOUR_UTC", "12"))
DAILY_SIGNAL_MINUTE_UTC = int(os.getenv("DAILY_SIGNAL_MINUTE_UTC", "0"))

# Free channel: one daily signal.
# Premium channel: scanner runs at this interval.
PREMIUM_SCAN_SECONDS = int(os.getenv("PREMIUM_SCAN_SECONDS", "30"))
RESULT_SCAN_SECONDS = int(os.getenv("RESULT_SCAN_SECONDS", "30"))
AUTO_DISCOVERY_ENABLED = os.getenv("AUTO_DISCOVERY_ENABLED", "true").lower() in {"1", "true", "yes", "on"}
DISCOVERY_SCAN_SECONDS = int(os.getenv("DISCOVERY_SCAN_SECONDS", "20"))
HELIUS_ENHANCED_ENABLED = bool(HELIUS_API_KEY)
PRICE_MAX_AGE_SECONDS = int(os.getenv("PRICE_MAX_AGE_SECONDS", "60"))

# Scan protection: avoid repeated provider calls when users submit the same
# token repeatedly. This is a cache/rate-limit layer, not a data source.
SCAN_CACHE_SECONDS = max(3, int(os.getenv("SCAN_CACHE_SECONDS", "15")))
USER_SCAN_COOLDOWN_SECONDS = max(1, int(os.getenv("USER_SCAN_COOLDOWN_SECONDS", "3")))
MAX_SCAN_CACHE_ITEMS = max(50, int(os.getenv("MAX_SCAN_CACHE_ITEMS", "500")))


# Optional Helius program addresses for automatic discovery. Keep PUMPFUN_PROGRAM_ID
# empty unless you have verified the current official program id.
DISCOVERY_PROGRAM_IDS = [x.strip() for x in os.getenv("DISCOVERY_PROGRAM_IDS", "").split(",") if x.strip()]

MIN_LIQUIDITY_USD = float(os.getenv("MIN_LIQUIDITY_USD", "30000"))
MIN_SCORE = int(os.getenv("MIN_SCORE", "75"))

TP1_PCT = float(os.getenv("TP1_PCT", "10"))
TP2_PCT = float(os.getenv("TP2_PCT", "20"))
TP3_PCT = float(os.getenv("TP3_PCT", "30"))
SL_PCT = float(os.getenv("SL_PCT", "10"))

FREE_RESULT_MINUTES = int(os.getenv("FREE_RESULT_MINUTES", "60"))
PREMIUM_MAX_ACTIVE_SIGNALS = int(os.getenv("PREMIUM_MAX_ACTIVE_SIGNALS", "50"))

# Premium CTA
PREMIUM_URL = os.getenv("PREMIUM_URL", "https://t.me/YOUR_PREMIUM_CHANNEL")
DATABASE_URL = os.getenv("DATABASE_URL", "")
PAYMENT_WALLET = os.getenv("PAYMENT_WALLET", "")
PLAN_PRICES_USD = {"weekly": 1.99, "monthly": 4.99, "yearly": 19.99}
PLAN_DAYS = {"weekly": 7, "monthly": 30, "yearly": 365}
SOL_USD_RATE = float(os.getenv("SOL_USD_RATE", "150"))
SOL_USD_PRICE_URL = os.getenv(
    "SOL_USD_PRICE_URL",
    "https://api.binance.com/api/v3/ticker/price?symbol=SOLUSDT"
)
PAYMENT_CHECK_SECONDS = int(os.getenv("PAYMENT_CHECK_SECONDS", "60"))
FREE_HIDE_LOGO = os.getenv("FREE_HIDE_LOGO", "false").lower() in {"1","true","yes","on"}
FREE_HIDE_ADDRESS = os.getenv("FREE_HIDE_ADDRESS", "false").lower() in {"1","true","yes","on"}
# Direct bot link. Leave empty to auto-build it from the bot username.
BOT_USERNAME = os.getenv("BOT_USERNAME", "YOUR_BOT_USERNAME").lstrip("@").strip()
BOT_URL = os.getenv("BOT_URL", "").strip()
BRAND_NAME = os.getenv("BRAND_NAME", "Solana Intelligence")
REFERRAL_REWARD_DAYS = int(os.getenv("REFERRAL_REWARD_DAYS", "7"))
WATCHLIST_MAX = int(os.getenv("WATCHLIST_MAX", "20"))
TRIAL_DAYS = max(1, int(os.getenv("TRIAL_DAYS", "5")))
TRIAL_ENABLED = False  # All user intelligence features are paid; no free trial.
EARLY_WATCH_SCORE = int(os.getenv("EARLY_WATCH_SCORE", "75"))
ALERT_COOLDOWN_SECONDS = int(os.getenv("ALERT_COOLDOWN_SECONDS", "300"))
LOGO_PATH = os.getenv("LOGO_PATH", "")

# Optional explicit token watchlist. This is useful without a market-data
# aggregator: put addresses here and the bot will continuously analyze them.
WATCH_TOKENS = {
    x.strip() for x in os.getenv("WATCH_TOKENS", "").split(",") if x.strip()
}

# ============================================================
# V5 MARKET INTELLIGENCE / USER ALERT CONFIG
# ============================================================

# ============================================================
# V6 USER SAFETY / ALERTS / ADMIN CONTROL
# ============================================================

RUG_LIQUIDITY_DROP_PCT = float(os.getenv("RUG_LIQUIDITY_DROP_PCT", "30"))
RUG_PRICE_DROP_PCT = float(os.getenv("RUG_PRICE_DROP_PCT", "25"))
WHALE_DUMP_SOL = float(os.getenv("WHALE_DUMP_SOL", "100"))
ALERT_REPEAT_SECONDS = int(os.getenv("ALERT_REPEAT_SECONDS", "300"))
PAPER_TRADING_ENABLED = os.getenv("PAPER_TRADING_ENABLED", "true").lower() in {"1","true","yes","on"}

# Production-friendly runtime controls. These can be overridden in .env.
CACHE_ENABLED = os.getenv("CACHE_ENABLED", "true").lower() in {"1","true","yes","on"}
API_RETRY_COUNT = max(1, int(os.getenv("API_RETRY_COUNT", "3")))
API_TIMEOUT_SECONDS = max(3, int(os.getenv("API_TIMEOUT_SECONDS", "10")))
MAX_CONCURRENT_SCANS = max(1, int(os.getenv("MAX_CONCURRENT_SCANS", "4")))
# Runtime protection: global provider concurrency, short circuit-breaker, and
# per-user command throttling. These reduce duplicate API pressure without
# hiding provider failures.
PROVIDER_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_SCANS)
PROVIDER_FAILURE_LIMIT = max(2, int(os.getenv("PROVIDER_FAILURE_LIMIT", "5")))
PROVIDER_COOLDOWN_SECONDS = max(10, int(os.getenv("PROVIDER_COOLDOWN_SECONDS", "30")))
USER_SCAN_RATE_SECONDS = max(1, int(os.getenv("USER_SCAN_RATE_SECONDS", "3")))
_provider_failures = defaultdict(int)
_provider_open_until = defaultdict(float)
_provider_last_request = defaultdict(float)
_provider_latency = defaultdict(lambda: deque(maxlen=PROVIDER_HEALTH_WINDOW))
_provider_requests = defaultdict(int)
_provider_errors = defaultdict(int)
_provider_health_lock = asyncio.Lock()
_seen_signatures = set()
_seen_signatures_order = deque(maxlen=5000)
_user_scan_last = {}
PAPER_TRADE_SIZE_USD = float(os.getenv("PAPER_TRADE_SIZE_USD", "100"))
MAX_USER_WATCHLIST = int(os.getenv("MAX_USER_WATCHLIST", "20"))

# Token lifecycle state: NEW -> EARLY -> MOMENTUM -> LATE -> MONITOR -> INVALIDATED
token_lifecycle = {}
user_last_alert = defaultdict(dict)
paper_trades = {}

V6_ALERT_TYPES = {
    "new_launch", "smart_money", "whale", "rug",
    "volume_acceleration", "price_move", "invalidation"
}


# Optional free/public market-data source. The bot still refuses to
# fabricate data when this source is unavailable.
DEXSCREENER_API_URL = os.getenv(
    "DEXSCREENER_API_URL",
    "https://api.dexscreener.com/latest/dex/tokens/"
)
MARKET_DATA_ENABLED = os.getenv("MARKET_DATA_ENABLED", "true").lower() in {"1","true","yes","on"}
MARKET_REFRESH_SECONDS = int(os.getenv("MARKET_REFRESH_SECONDS", "20"))
TOKEN_SNAPSHOT_SECONDS = int(os.getenv("TOKEN_SNAPSHOT_SECONDS", "60"))

# Meme lifecycle filters. These are screening thresholds, not profit guarantees.
NEW_LAUNCH_MAX_SECONDS = int(os.getenv("NEW_LAUNCH_MAX_SECONDS", "180"))
EARLY_ALERT_MAX_SECONDS = int(os.getenv("EARLY_ALERT_MAX_SECONDS", "900"))
LATE_MEME_MAX_SECONDS = int(os.getenv("LATE_MEME_MAX_SECONDS", "7200"))
MIN_BUY_SELL_RATIO = float(os.getenv("MIN_BUY_SELL_RATIO", "1.70"))
MIN_BUY_SHARE_PCT = float(os.getenv("MIN_BUY_SHARE_PCT", "65"))
MIN_LIQUIDITY_EARLY_USD = float(os.getenv("MIN_LIQUIDITY_EARLY_USD", "30000"))
MIN_LIQUIDITY_PREFERRED_USD = float(os.getenv("MIN_LIQUIDITY_PREFERRED_USD", "50000"))
TOP10_WARNING_PCT = float(os.getenv("TOP10_WARNING_PCT", "30"))
DEV_WARNING_PCT = float(os.getenv("DEV_WARNING_PCT", "4"))
BUNDLED_WARNING_PCT = float(os.getenv("BUNDLED_WARNING_PCT", "12"))

# Advanced intelligence controls
ADVANCED_SCORE_ENABLED = os.getenv("ADVANCED_SCORE_ENABLED", "true").lower() in {"1","true","yes","on"}
SIGNAL_TP1_PCT = float(os.getenv("SIGNAL_TP1_PCT", str(TP1_PCT)))
SIGNAL_TP2_PCT = float(os.getenv("SIGNAL_TP2_PCT", str(TP2_PCT)))
SIGNAL_TP3_PCT = float(os.getenv("SIGNAL_TP3_PCT", str(TP3_PCT)))
SIGNAL_SL_PCT = float(os.getenv("SIGNAL_SL_PCT", str(SL_PCT)))
MAX_TIMELINE_EVENTS = int(os.getenv("MAX_TIMELINE_EVENTS", "30"))


# Alert controls.
GLOBAL_ALERT_COOLDOWN_SECONDS = int(os.getenv("GLOBAL_ALERT_COOLDOWN_SECONDS", "300"))
MAX_DISCOVERY_ALERTS_PER_HOUR = int(os.getenv("MAX_DISCOVERY_ALERTS_PER_HOUR", "20"))
SMART_MONEY_ALERT_MIN_WALLETS = int(os.getenv("SMART_MONEY_ALERT_MIN_WALLETS", "2"))
WHALE_ALERT_SOL = float(os.getenv("WHALE_ALERT_SOL", "50"))

# Optional wallet labels: WALLET=LABEL,WALLET2=LABEL2
SMART_MONEY_LABELS = {}
for _item in os.getenv("SMART_MONEY_LABELS", "").split(","):
    if "=" in _item:
        _w, _label = _item.split("=", 1)
        if _w.strip():
            SMART_MONEY_LABELS[_w.strip()] = _label.strip() or "Tracked Wallet"

# Runtime V5 state.
market_cache = {}
token_snapshots = defaultdict(lambda: deque(maxlen=120))
token_alert_state = {}
alert_hour_bucket = deque(maxlen=200)
user_alert_cache = {}
last_market_refresh = {}
scan_report_cache = {}
user_scan_last_at = {}

async def cached_enriched_report(mint: str):
    """Return a short-lived cached report to reduce duplicate API/RPC calls."""
    now = time.time()
    item = scan_report_cache.get(mint)
    if item and now - item[0] < SCAN_CACHE_SECONDS:
        return item[1]
    report = await enriched_report(mint)
    if report:
        if len(scan_report_cache) >= MAX_SCAN_CACHE_ITEMS:
            oldest = min(scan_report_cache.items(), key=lambda kv: kv[1][0])[0]
            scan_report_cache.pop(oldest, None)
        scan_report_cache[mint] = (now, report)
    return report

def user_scan_allowed(user_id: int):
    now = time.time()
    last = user_scan_last_at.get(user_id, 0.0)
    if now - last < USER_SCAN_COOLDOWN_SECONDS:
        return False
    user_scan_last_at[user_id] = now
    return True



logging.basicConfig(
    level=getattr(logging, LOG_LEVEL, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(message)s"
)

dp = Dispatcher()


class PaidAccessMiddleware(BaseMiddleware):
    """Require active Premium for every non-admin user feature.

    Only onboarding/payment routes remain public: /start, /premium and
    /verify. Admins bypass the paywall completely.
    """
    PUBLIC_COMMANDS = {"/start", "/premium", "/verify"}
    PUBLIC_CALLBACKS = {"premium"}

    async def __call__(self, handler, event, data):
        user = getattr(event, "from_user", None)
        if not user:
            return await handler(event, data)

        uid = user.id
        if uid in ADMIN_IDS:
            return await handler(event, data)

        if isinstance(event, Message):
            text = (event.text or event.caption or "").strip()
            command = text.split(maxsplit=1)[0].split("@")[0].lower() if text else ""
            if command in self.PUBLIC_COMMANDS:
                return await handler(event, data)
            await event.answer(
                "🔒 <b>Premium access required</b>\n\n"
                "All scanner, intelligence, alerts, wallet, portfolio and trading tools are available to active Premium members.\n\n"
                "Use /premium to choose a plan.",
                parse_mode="HTML"
            )
            return

        if isinstance(event, CallbackQuery):
            callback = event.data or ""
            if callback in self.PUBLIC_CALLBACKS or callback.startswith("plan:"):
                return await handler(event, data)
            await event.answer("🔒 Premium access required. Use Premium to continue.", show_alert=True)
            return

        return await handler(event, data)


dp.message.outer_middleware(PaidAccessMiddleware())
dp.callback_query.outer_middleware(PaidAccessMiddleware())

# Runtime state
active_signals = {}
free_sent_today = None
recent_signatures = deque(maxlen=1000)
wallet_events = defaultdict(deque)
last_wallet_scan = {}
last_signal_time = {}


# ============================================================
# DATABASE / MEMBERSHIP
# ============================================================
DB = None

async def db_init():
    """Initialize PostgreSQL without allowing a temporary DB/DNS failure to kill the bot."""
    global DB
    try:
        await _db_init_once()
        if DB:
            logging.info("PostgreSQL connected and schema initialized.")
            return True
    except Exception as exc:
        logging.exception("PostgreSQL initialization failed; bot will continue and retry: %s", exc)
        try:
            if DB:
                await DB.close()
        except Exception:
            pass
        DB = None
    return False


async def db_reconnect_loop():
    """Retry PostgreSQL in the background so a transient Render/Supabase DNS outage is recoverable."""
    while True:
        try:
            if DB is None and DATABASE_URL and asyncpg is not None:
                await db_init()
                if DB:
                    await adv8_db_init()
                    await v9_db_init()
        except Exception:
            logging.exception("PostgreSQL reconnect loop failed")
        await asyncio.sleep(max(15, int(os.getenv("DB_RETRY_SECONDS", "30"))))

async def _db_init_once():
    global DB
    if not DATABASE_URL or asyncpg is None:
        logging.warning("PostgreSQL disabled: set DATABASE_URL and install asyncpg.")
        return
    DB = await asyncpg.create_pool(DATABASE_URL, min_size=1, max_size=5)
    async with DB.acquire() as c:
        await c.execute("""
        CREATE TABLE IF NOT EXISTS helius_usage(
            month_key TEXT PRIMARY KEY,
            credits DOUBLE PRECISION NOT NULL DEFAULT 0,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS helius_daily_usage(
            day_key TEXT PRIMARY KEY,
            credits DOUBLE PRECISION NOT NULL DEFAULT 0,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        """)
        await c.execute("""
        CREATE TABLE IF NOT EXISTS members(
            user_id BIGINT PRIMARY KEY,
            username TEXT,
            expires_at TIMESTAMPTZ NOT NULL,
            invite_link TEXT,
            payment_signature TEXT UNIQUE,
            created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS trial_users(
            user_id BIGINT PRIMARY KEY,
            started_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
            expires_at TIMESTAMPTZ NOT NULL
        );
        CREATE TABLE IF NOT EXISTS pending_payments(
            user_id BIGINT PRIMARY KEY,
            username TEXT,
            lamports BIGINT NOT NULL,
            plan TEXT NOT NULL DEFAULT 'monthly',
            duration_days INTEGER NOT NULL DEFAULT 30,
            price_usd DOUBLE PRECISION NOT NULL DEFAULT 4.99,
            created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS signal_history(
            id BIGSERIAL PRIMARY KEY, mint TEXT NOT NULL, symbol TEXT, entry DOUBLE PRECISION, exit_price DOUBLE PRECISION, pnl DOUBLE PRECISION, status TEXT, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(), closed_at TIMESTAMPTZ
        );
        CREATE TABLE IF NOT EXISTS watchlists(
            user_id BIGINT NOT NULL, mint TEXT NOT NULL, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(), PRIMARY KEY(user_id,mint)
        );
        CREATE TABLE IF NOT EXISTS user_settings(
            user_id BIGINT PRIMARY KEY, early_alerts BOOLEAN NOT NULL DEFAULT TRUE, whale_alerts BOOLEAN NOT NULL DEFAULT TRUE, rug_alerts BOOLEAN NOT NULL DEFAULT TRUE, tp_alerts BOOLEAN NOT NULL DEFAULT TRUE
        );
        CREATE TABLE IF NOT EXISTS referrals(
            user_id BIGINT PRIMARY KEY, referrer_id BIGINT, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS token_snapshots(
            mint TEXT NOT NULL,
            ts TIMESTAMPTZ NOT NULL DEFAULT NOW(),
            price DOUBLE PRECISION,
            liquidity_usd DOUBLE PRECISION,
            volume_5m DOUBLE PRECISION,
            buys_5m INTEGER,
            sells_5m INTEGER,
            price_change_5m DOUBLE PRECISION,
            pair_address TEXT,
            PRIMARY KEY(mint, ts)
        );
        CREATE TABLE IF NOT EXISTS token_alerts(
            id BIGSERIAL PRIMARY KEY,
            mint TEXT NOT NULL,
            alert_type TEXT NOT NULL,
            score INTEGER,
            payload JSONB,
            created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS alert_settings(
            user_id BIGINT PRIMARY KEY,
            new_launch BOOLEAN NOT NULL DEFAULT TRUE,
            smart_money BOOLEAN NOT NULL DEFAULT TRUE,
            whale BOOLEAN NOT NULL DEFAULT TRUE,
            rug BOOLEAN NOT NULL DEFAULT TRUE,
            volume_acceleration BOOLEAN NOT NULL DEFAULT TRUE,
            price_move BOOLEAN NOT NULL DEFAULT TRUE
        );
        CREATE INDEX IF NOT EXISTS idx_token_alerts_mint_time ON token_alerts(mint, created_at DESC);
        CREATE TABLE IF NOT EXISTS intelligence_events(
            id BIGSERIAL PRIMARY KEY, mint TEXT NOT NULL, event_type TEXT NOT NULL,
            score INTEGER, message TEXT, payload JSONB, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE INDEX IF NOT EXISTS idx_intelligence_events_mint_time ON intelligence_events(mint, created_at DESC);
        CREATE TABLE IF NOT EXISTS user_portfolio(
            user_id BIGINT NOT NULL, mint TEXT NOT NULL, symbol TEXT, qty DOUBLE PRECISION NOT NULL DEFAULT 0,
            avg_entry DOUBLE PRECISION NOT NULL DEFAULT 0, updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
            PRIMARY KEY(user_id,mint)
        );

        CREATE TABLE IF NOT EXISTS paper_trades(
            id BIGSERIAL PRIMARY KEY,
            user_id BIGINT NOT NULL,
            mint TEXT NOT NULL,
            side TEXT NOT NULL DEFAULT 'LONG',
            entry_price DOUBLE PRECISION NOT NULL,
            size_usd DOUBLE PRECISION NOT NULL DEFAULT 100,
            status TEXT NOT NULL DEFAULT 'OPEN',
            exit_price DOUBLE PRECISION,
            pnl_usd DOUBLE PRECISION,
            opened_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
            closed_at TIMESTAMPTZ
        );
        CREATE TABLE IF NOT EXISTS admin_audit_log(
            id BIGSERIAL PRIMARY KEY,
            admin_id BIGINT NOT NULL,
            action TEXT NOT NULL,
            target TEXT,
            details JSONB,
            created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS system_settings(
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );

        """)


async def member_expiry(user_id):
    if not DB: return None
    async with DB.acquire() as c:
        row=await c.fetchrow("SELECT expires_at FROM members WHERE user_id=$1", user_id)
        return row["expires_at"] if row else None

async def is_premium(user_id):
    exp=await member_expiry(user_id)
    return bool(exp and exp > datetime.now(timezone.utc))

async def save_member(user_id, username, expires_at, invite_link, signature):
    if not DB: return
    async with DB.acquire() as c:
        await c.execute("""INSERT INTO members(user_id,username,expires_at,invite_link,payment_signature)
        VALUES($1,$2,$3,$4,$5) ON CONFLICT(user_id) DO UPDATE SET username=$2,expires_at=$3,invite_link=$4,payment_signature=$5""",
        user_id, username, expires_at, invite_link, signature)

async def trial_available(user_id):
    if not TRIAL_ENABLED or not DB or not PREMIUM_CHANNEL_ID:
        return False
    async with DB.acquire() as c:
        row = await c.fetchrow("SELECT user_id FROM trial_users WHERE user_id=$1", user_id)
    return row is None

async def activate_trial(user_id, username):
    if not await trial_available(user_id):
        return False, "🎁 Your 5-day free trial has already been used."
    expires = now_utc() + timedelta(days=TRIAL_DAYS)
    invite = await create_premium_invite(user_id, invite_days=TRIAL_DAYS)
    async with DB.acquire() as c:
        await c.execute("INSERT INTO trial_users(user_id,started_at,expires_at) VALUES($1,NOW(),$2)", user_id, expires)
        await c.execute("""INSERT INTO members(user_id,username,expires_at,invite_link,payment_signature)
            VALUES($1,$2,$3,$4,$5)
            ON CONFLICT(user_id) DO UPDATE SET username=$2,expires_at=$3,invite_link=$4,payment_signature=$5""",
            user_id, username, expires, invite, f"TRIAL:{user_id}")
    return True, (f"🎁 <b>{TRIAL_DAYS}-DAY FREE TRIAL ACTIVATED</b>\n\n"
                   f"Expires: <b>{expires:%d %b %Y, %H:%M UTC}</b>\n\n"
                   + (f"🔐 <a href=\"{invite}\">Join Premium Channel</a>" if invite else "Premium invite could not be created; contact admin."))

async def trial_status(user_id):
    if not DB:
        return None
    async with DB.acquire() as c:
        row = await c.fetchrow("SELECT started_at,expires_at FROM trial_users WHERE user_id=$1", user_id)
    return dict(row) if row else None

async def payment_monitor_loop():
    """
    Keep the payment monitor alive while PostgreSQL is temporarily unavailable.

    The previous version returned permanently when the first startup DB
    connection failed. On Render/Supabase a short DNS/connection outage could
    therefore leave automatic payment monitoring disabled even after
    db_reconnect_loop restored PostgreSQL.
    """
    if not PAYMENT_WALLET:
        logging.error("Automatic payment monitor disabled: PAYMENT_WALLET is missing.")
        return

    seen = set()
    warned_db = False

    while True:
        # Wait for the background DB reconnect loop instead of exiting forever.
        if DB is None:
            if not warned_db:
                logging.warning(
                    "Payment monitor waiting for PostgreSQL connection; "
                    "it will start automatically after DATABASE_URL/DB is available."
                )
                warned_db = True
            await asyncio.sleep(max(15, int(os.getenv("DB_RETRY_SECONDS", "30"))))
            continue

        warned_db = False
        try:
            sigs=await get_signatures(PAYMENT_WALLET, 20)
            for row in sigs:
                sig=row.get("signature") if isinstance(row,dict) else None
                if not sig or sig in seen: continue
                seen.add(sig)
                tx=await rpc_call("getTransaction", [sig, {"encoding":"jsonParsed","commitment":"confirmed","maxSupportedTransactionVersion":0}])
                if not tx or (tx.get("meta") or {}).get("err") is not None: continue
                meta=tx.get("meta") or {}; keys=((tx.get("transaction") or {}).get("message") or {}).get("accountKeys") or []
                try: idx=next(i for i,k in enumerate(keys) if (k.get("pubkey") if isinstance(k,dict) else k)==PAYMENT_WALLET)
                except StopIteration: continue
                pre=(meta.get("preBalances") or [0]*len(keys))[idx]; post=(meta.get("postBalances") or [0]*len(keys))[idx]
                received=post-pre
                async with DB.acquire() as c:
                    pending=await c.fetch(
                        "SELECT user_id,username,lamports,plan,duration_days,price_usd "
                        "FROM pending_payments WHERE lamports <= $1 AND created_at > NOW()-INTERVAL '24 hours'",
                        received
                    )
                if not pending: continue
                # Exact amount match first.
                match=next((x for x in pending if x["lamports"]==received), None)
                if not match: continue
                exp=datetime.now(timezone.utc)+timedelta(days=int(match["duration_days"] or 30))
                invite=await create_premium_invite(match["user_id"])
                await save_member(match["user_id"], match["username"], exp, invite, sig)
                async with DB.acquire() as c:
                    await c.execute("DELETE FROM pending_payments WHERE user_id=$1", match["user_id"])
                try:
                    text=f"✅ <b>Payment confirmed automatically</b>\n\nPremium expires: <b>{exp}</b>"
                    if invite: text += f"\n\n🔐 <a href=\"{invite}\">Join Premium Channel</a>"
                    await BOT.send_message(match["user_id"], text, parse_mode="HTML")
                except Exception: logging.exception("Could not notify paid user")
        except Exception:
            logging.exception("Payment monitor failed")
        await asyncio.sleep(max(30, PAYMENT_CHECK_SECONDS))

async def expire_members_loop():
    while True:
        try:
            if DB and PREMIUM_CHANNEL_ID:
                now=datetime.now(timezone.utc)
                async with DB.acquire() as c:
                    rows=await c.fetch("SELECT user_id FROM members WHERE expires_at <= $1", now)
                for row in rows:
                    try:
                        uid = row["user_id"]
                        await BOT.ban_chat_member(PREMIUM_CHANNEL_ID, uid)
                        await BOT.unban_chat_member(PREMIUM_CHANNEL_ID, uid, only_if_banned=True)
                        try:
                            await BOT.send_message(uid, "⏰ <b>Premium access expired</b>\n\nYour access was removed automatically. Use /premium to choose a paid plan.", parse_mode="HTML")
                        except Exception:
                            pass
                    except Exception:
                        logging.exception("Failed to remove expired member %s", row["user_id"])
                if rows:
                    async with DB.acquire() as c:
                        await c.execute("DELETE FROM members WHERE expires_at <= $1", now)
        except Exception:
            logging.exception("Membership expiry loop failed")
        await asyncio.sleep(300)

# ============================================================
# USER / ANALYTICS HELPERS
# ============================================================
async def db_add_signal(mint, symbol, entry, exit_price, pnl, status):
    if not DB: return
    async with DB.acquire() as c:
        await c.execute("INSERT INTO signal_history(mint,symbol,entry,exit_price,pnl,status,closed_at) VALUES($1,$2,$3,$4,$5,$6,NOW())", mint,symbol,entry,exit_price,pnl,status)

async def performance_summary():
    if not DB: return None
    async with DB.acquire() as c:
        r=await c.fetchrow("SELECT COUNT(*) n, COUNT(*) FILTER(WHERE pnl>0) wins, COUNT(*) FILTER(WHERE pnl<=0) losses, COALESCE(AVG(pnl),0) avg FROM signal_history")
        return dict(r)

async def add_watch(user_id,mint):
    if not DB: return False
    async with DB.acquire() as c:
        n=await c.fetchval("SELECT COUNT(*) FROM watchlists WHERE user_id=$1",user_id)
        if n >= WATCHLIST_MAX: return False
        await c.execute("INSERT INTO watchlists(user_id,mint) VALUES($1,$2) ON CONFLICT DO NOTHING",user_id,mint)
    return True

async def remove_watch(user_id,mint):
    if not DB: return False
    async with DB.acquire() as c:
        await c.execute("DELETE FROM watchlists WHERE user_id=$1 AND mint=$2",user_id,mint)
    return True

async def user_watchlist(user_id):
    if not DB: return []
    async with DB.acquire() as c:
        rows=await c.fetch("SELECT mint FROM watchlists WHERE user_id=$1 ORDER BY created_at DESC",user_id)
    return [r["mint"] for r in rows]

async def save_referral(user_id, referrer_id):
    if not DB or not referrer_id or referrer_id==user_id: return
    async with DB.acquire() as c:
        await c.execute("INSERT INTO referrals(user_id,referrer_id) VALUES($1,$2) ON CONFLICT DO NOTHING",user_id,referrer_id)

async def referral_count(user_id):
    if not DB: return 0
    async with DB.acquire() as c:
        return await c.fetchval("SELECT COUNT(*) FROM referrals WHERE referrer_id=$1",user_id)

# ============================================================
# BASIC HELPERS
# ============================================================

def font(size, bold=False):
    candidates = [
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"
        if bold else "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        "/usr/share/fonts/truetype/liberation2/LiberationSans-Bold.ttf"
        if bold else "/usr/share/fonts/truetype/liberation2/LiberationSans-Regular.ttf"
    ]
    for p in candidates:
        if os.path.exists(p):
            return ImageFont.truetype(p, size)
    return ImageFont.load_default()

def money(v):
    try: v=float(v)
    except: return "$0"
    if v >= 1_000_000: return f"${v/1_000_000:.2f}M"
    if v >= 1_000: return f"${v/1_000:.1f}K"
    return f"${v:.2f}"

def price(v):
    try: v=float(v)
    except: return "N/A"
    if v >= 1: return f"${v:,.6f}"
    if v >= .01: return f"${v:.8f}"
    return f"${v:.12f}"

def pct(v):
    try: return f"{float(v):+.2f}%"
    except: return "N/A"

def score_label(s):
    if s >= 90: return "EXPLOSIVE"
    if s >= 85: return "STRONG"
    if s >= 75: return "WATCH"
    return "FILTERED"

def now_utc():
    return datetime.now(timezone.utc)

def valid_solana_address(x):
    return isinstance(x, str) and 32 <= len(x) <= 44 and all(c in "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz" for c in x)


# ============================================================
# API / HTTP RELIABILITY LAYER
# ============================================================

def _is_helius_url(url):
    u = (url or "").lower()
    return "helius-rpc.com" in u or "api.helius.xyz" in u or "helius.dev" in u


def _helius_request_cost(url, json_body=None):
    """Conservative credit reservation for one HTTP/RPC attempt."""
    u = (url or "").lower()
    method = ""
    if isinstance(json_body, dict):
        method = str(json_body.get("method") or "")
    # Enhanced Transactions API is 100 credits/request.
    if "api.helius.xyz/v0/" in u or "enhanced" in method.lower():
        return HELIUS_ENHANCED_COST
    # DAS calls and standard historical RPC calls are 10 credits/request.
    if method.startswith(("getAsset", "getAssets", "getAssetBatch")):
        return HELIUS_HTTP_DEFAULT_COST
    if method.startswith(("getTransaction", "getSignaturesForAddress", "getBlock", "getBlocks", "getBlockTime", "getInflationReward")):
        return HELIUS_HTTP_DEFAULT_COST
    # Unknown Helius calls are deliberately budgeted conservatively.
    return HELIUS_HTTP_DEFAULT_COST


async def _helius_reserve(credits):
    """Atomically reserve Helius credits under BOTH daily and monthly caps.

    Every Helius HTTP/RPC attempt is reserved before it is sent. This is a
    conservative accounting guard: retries also consume budget, and unknown
    Helius methods use the default reservation.
    """
    global _helius_month_used, _helius_month_key, _helius_day_used, _helius_day_key
    credits = float(max(0.0, credits))
    if credits <= 0:
        return True
    if HELIUS_HARD_CAP_REQUIRE_DB and DB is None:
        logging.error("Helius hard-cap guard: DATABASE_URL/DB is unavailable; blocking Helius request to avoid untracked usage.")
        return False

    now = datetime.now(timezone.utc)
    month_key = now.strftime("%Y-%m")
    day_key = now.strftime("%Y-%m-%d")

    async with _helius_usage_lock:
        if _helius_month_key != month_key:
            _helius_month_key = month_key
            _helius_month_used = 0.0
        if _helius_day_key != day_key:
            _helius_day_key = day_key
            _helius_day_used = 0.0

        if DB:
            async with DB.acquire() as c:
                async with c.transaction():
                    mrow = await c.fetchrow(
                        "SELECT credits FROM helius_usage WHERE month_key=$1 FOR UPDATE",
                        month_key
                    )
                    drow = await c.fetchrow(
                        "SELECT credits FROM helius_daily_usage WHERE day_key=$1 FOR UPDATE",
                        day_key
                    )
                    month_used = float(mrow["credits"]) if mrow else 0.0
                    day_used = float(drow["credits"]) if drow else 0.0

                    if day_used + credits > (HELIUS_DAILY_CREDIT_CAP - HELIUS_SAFE_DAILY_RESERVE):
                        logging.warning(
                            "HELIUS DAILY HARD CAP: blocked request (%.0f + %.0f > %.0f)",
                            day_used, credits, HELIUS_DAILY_CREDIT_CAP
                        )
                        return False
                    if month_used + credits > (HELIUS_MONTHLY_CREDIT_CAP - HELIUS_SAFE_MONTHLY_RESERVE):
                        logging.error(
                            "HELIUS MONTHLY HARD CAP: blocked request (%.0f + %.0f > %.0f)",
                            month_used, credits, HELIUS_MONTHLY_CREDIT_CAP
                        )
                        return False

                    new_day = day_used + credits
                    new_month = month_used + credits
                    if drow:
                        await c.execute(
                            "UPDATE helius_daily_usage SET credits=$2, updated_at=NOW() WHERE day_key=$1",
                            day_key, new_day
                        )
                    else:
                        await c.execute(
                            "INSERT INTO helius_daily_usage(day_key,credits) VALUES($1,$2)",
                            day_key, new_day
                        )
                    if mrow:
                        await c.execute(
                            "UPDATE helius_usage SET credits=$2, updated_at=NOW() WHERE month_key=$1",
                            month_key, new_month
                        )
                    else:
                        await c.execute(
                            "INSERT INTO helius_usage(month_key,credits) VALUES($1,$2)",
                            month_key, new_month
                        )
                    _helius_day_used = new_day
                    _helius_month_used = new_month
                    return True

        # Fallback in-memory path (only reachable when hard-cap DB requirement
        # is explicitly disabled by the operator).
        if _helius_day_used + credits > (HELIUS_DAILY_CREDIT_CAP - HELIUS_SAFE_DAILY_RESERVE):
            return False
        if _helius_month_used + credits > (HELIUS_MONTHLY_CREDIT_CAP - HELIUS_SAFE_MONTHLY_RESERVE):
            return False
        _helius_day_used += credits
        _helius_month_used += credits
        return True


async def _helius_wait_rps():
    """Keep Helius HTTP/RPC below the configured 10-RPS provider limit."""
    while True:
        now = time.monotonic()
        while _helius_rps_times and now - _helius_rps_times[0] >= 1.0:
            _helius_rps_times.popleft()
        if len(_helius_rps_times) < int(HELIUS_RPS_CAP):
            _helius_rps_times.append(now)
            return
        await asyncio.sleep(max(0.01, 1.0 - (now - _helius_rps_times[0])))


async def _http_json_request(method, url, *, params=None, json_body=None, headers=None):
    """HTTP JSON helper with timeout, retry, concurrency and circuit protection."""
    retryable_statuses = {408, 425, 429, 500, 502, 503, 504}
    timeout = aiohttp.ClientTimeout(total=API_TIMEOUT_SECONDS)
    attempts = API_MAX_RETRIES + 1

    if not await _provider_allowed(url):
        return None, None

    for attempt in range(attempts):
        if _is_helius_url(url):
            await _helius_wait_rps()
            if not await _helius_reserve(_helius_request_cost(url, json_body)):
                return None, None
        try:
            started = time.monotonic()
            _provider_mark_request(url)
            async with PROVIDER_SEMAPHORE:
                async with aiohttp.ClientSession(timeout=timeout) as session:
                    request_kwargs = {"headers": headers or {"Accept": "application/json"}}
                    if params is not None:
                        request_kwargs["params"] = params
                    if json_body is not None:
                        request_kwargs["json"] = json_body
                    async with session.request(method, url, **request_kwargs) as response:
                        status = response.status
                        try:
                            data = await response.json(content_type=None)
                        except Exception:
                            data = None
                        if status == 200 or status not in retryable_statuses:
                            if status == 200:
                                _provider_ok(url, time.monotonic() - started)
                            else:
                                _provider_failed(url)
                            return status, data
                        _provider_failed(url)
        except (asyncio.TimeoutError, aiohttp.ClientError) as exc:
            _provider_failed(url)
            logging.warning("HTTP provider request failed (%s/%s): %s", attempt + 1, attempts, exc)
        except Exception as exc:
            _provider_failed(url)
            logging.warning("HTTP provider error: %s", exc)
            break
        if attempt < attempts - 1:
            await asyncio.sleep(API_RETRY_BACKOFF_SECONDS * (2 ** attempt))
    return None, None


# ============================================================
# PRIVATE RPC LAYER
# ============================================================

async def _provider_allowed(url):
    now = time.monotonic()
    if now < _provider_open_until.get(url, 0.0):
        return False
    # Small per-provider pacing protects shared public RPCs from bursty traffic.
    last = _provider_last_request.get(url, 0.0)
    wait = PROVIDER_MIN_INTERVAL_SECONDS - (now - last)
    if wait > 0:
        await asyncio.sleep(wait)
    _provider_last_request[url] = time.monotonic()
    return True


def _provider_failed(url):
    _provider_failures[url] += 1
    _provider_errors[url] += 1
    if _provider_failures[url] >= PROVIDER_FAILURE_LIMIT:
        _provider_open_until[url] = time.monotonic() + PROVIDER_COOLDOWN_SECONDS
        _provider_failures[url] = 0


def _provider_ok(url, latency=None):
    _provider_failures[url] = 0
    _provider_open_until[url] = 0.0
    _provider_requests[url] += 1
    if latency is not None:
        _provider_latency[url].append(float(latency))


def _provider_mark_request(url):
    _provider_requests[url] += 1


def provider_health_snapshot():
    out = []
    for url in _unique_urls(RPC_URLS + WSS_PROVIDERS):
        samples = list(_provider_latency.get(url, ()))
        out.append({
            "url": url,
            "open": time.monotonic() < _provider_open_until.get(url, 0.0),
            "failures": _provider_failures.get(url, 0),
            "errors": _provider_errors.get(url, 0),
            "requests": _provider_requests.get(url, 0),
            "avg_latency": (sum(samples) / len(samples)) if samples else None,
        })
    return out


def scan_rate_limited(user_id):
    now = time.monotonic()
    last = _user_scan_last.get(user_id, 0.0)
    if now - last < USER_SCAN_RATE_SECONDS:
        return True
    _user_scan_last[user_id] = now
    if len(_user_scan_last) > 5000:
        cutoff = now - max(USER_SCAN_RATE_SECONDS * 20, 60)
        for uid, ts in list(_user_scan_last.items()):
            if ts < cutoff:
                _user_scan_last.pop(uid, None)
    return False


async def rpc_call(method, params=None):
    if not RPC_URLS:
        return None

    payload = {
        "jsonrpc": "2.0",
        "id": int(time.time() * 1000) % 2_000_000_000,
        "method": method,
        "params": params or []
    }

    for url in RPC_URLS:
        status, data = await _http_json_request(
            "POST",
            url,
            json_body=payload,
            headers={"Content-Type": "application/json", "Accept": "application/json"},
        )
        if status == 200 and isinstance(data, dict) and "error" not in data:
            return data.get("result")
        logging.warning("RPC provider failed or returned an error: %s", url)

    return None


async def get_balance(address):
    result = await rpc_call("getBalance", [address])
    try:
        return result["value"] / 1_000_000_000
    except:
        return None


async def get_account_info(address):
    return await rpc_call(
        "getAccountInfo",
        [address, {"encoding": "jsonParsed"}]
    )


async def get_signatures(address, limit=20):
    return await rpc_call(
        "getSignaturesForAddress",
        [address, {"limit": limit}]
    ) or []


async def get_transaction(signature):
    return await rpc_call(
        "getTransaction",
        [
            signature,
            {
                "encoding": "jsonParsed",
                "maxSupportedTransactionVersion": 0
            }
        ]
    )


async def get_token_supply(mint):
    return await rpc_call("getTokenSupply", [mint])


async def get_token_accounts_by_owner(owner, mint):
    return await rpc_call(
        "getTokenAccountsByOwner",
        [
            owner,
            {"mint": mint},
            {"encoding": "jsonParsed"}
        ]
    )


async def get_largest_accounts(mint):
    return await rpc_call(
        "getTokenLargestAccounts",
        [mint]
    )


async def get_multiple_accounts(addresses):
    if not addresses:
        return []
    return await rpc_call(
        "getMultipleAccounts",
        [addresses, {"encoding": "jsonParsed"}]
    ) or []


# ============================================================
# TOKEN / SAFETY ENGINE
# ============================================================

async def token_metadata_basic(mint):
    info = await get_account_info(mint)

    result = {
        "exists": bool(info and info.get("value")),
        "mint_authority": None,
        "freeze_authority": None,
        "decimals": None,
        "supply": None
    }

    try:
        parsed = info["value"]["data"]["parsed"]
        mint_data = parsed["info"]
        result["mint_authority"] = mint_data.get("mintAuthority")
        result["freeze_authority"] = mint_data.get("freezeAuthority")
        result["decimals"] = mint_data.get("decimals")
        result["supply"] = mint_data.get("supply")
    except:
        pass

    supply = await get_token_supply(mint)
    if supply:
        try:
            result["supply_ui"] = supply["value"]["uiAmount"]
        except:
            result["supply_ui"] = None
    else:
        result["supply_ui"] = None

    return result


async def top_holder_report(mint):
    largest = await get_largest_accounts(mint)

    if not largest or not largest.get("value"):
        return {
            "available": False,
            "holders": [],
            "top10_raw": None
        }

    rows = largest["value"][:10]

    supply = await get_token_supply(mint)

    try:
        total = float(supply["value"]["amount"])
    except:
        total = 0

    holders = []

    for row in rows:
        amount = float(row.get("amount") or 0)
        share = amount / total * 100 if total else None
        holders.append({
            "address": row.get("address"),
            "amount": amount,
            "share": share
        })

    top10 = sum(x["share"] for x in holders if x["share"] is not None)

    return {
        "available": True,
        "holders": holders,
        "top10_raw": top10
    }


async def safety_scan(mint):
    meta = await token_metadata_basic(mint)
    holders = await top_holder_report(mint)

    score = 100
    flags = []

    if not meta["exists"]:
        score = 0
        flags.append("Token account not found")
        return {"score": score, "flags": flags, "meta": meta, "holders": holders}

    # Mint authority active is a risk flag; it is not proof of a scam.
    if meta["mint_authority"]:
        score -= 20
        flags.append("Mint authority active")

    if meta["freeze_authority"]:
        score -= 20
        flags.append("Freeze authority active")

    if holders.get("top10_raw") is not None:
        if holders["top10_raw"] > 50:
            score -= 25
            flags.append("Top 10 concentration > 50%")
        elif holders["top10_raw"] > 30:
            score -= 10
            flags.append("Top 10 concentration > 30%")

    return {
        "score": max(0, min(100, score)),
        "flags": flags,
        "meta": meta,
        "holders": holders
    }


# ============================================================
# HELIUS INDEXED / ENHANCED DATA LAYER
# ============================================================

async def helius_get_asset(mint):
    """Get parsed fungible-token metadata and price from Helius DAS."""
    if not HELIUS_RPC_URL:
        return None
    try:
        result = await rpc_call("getAsset", {
            "id": mint,
            "displayOptions": {"showFungible": True}
        })
        return result
    except Exception:
        logging.exception("getAsset failed")
        return None

async def helius_address_transactions(address, limit=50):
    """Parsed wallet/address transaction history from Helius Enhanced API."""
    if not HELIUS_API_KEY or not valid_solana_address(address):
        return []
    url = f"https://api.helius.xyz/v0/addresses/{address}/transactions"
    params = {"api-key": HELIUS_API_KEY, "limit": min(100, max(1, limit))}
    try:
        status, data = await _http_json_request("GET", url, params=params)
        if status != 200:
            logging.warning("Helius enhanced HTTP %s", status)
            return []
        return data if isinstance(data, list) else []
    except Exception:
        logging.exception("Helius enhanced request failed")
        return []


def extract_token_transfers(tx):
    return tx.get("tokenTransfers") or []


def extract_native_transfers(tx):
    return tx.get("nativeTransfers") or []


def transaction_mints(tx):
    out=set()
    for t in extract_token_transfers(tx):
        mint=t.get("mint")
        if mint and valid_solana_address(mint): out.add(mint)
    return out


def transaction_age_seconds(tx):
    ts=tx.get("timestamp") or tx.get("blockTime")
    try: return max(0, time.time()-float(ts))
    except: return 10**9


# ============================================================
# SOL PAYMENT VERIFICATION
# ============================================================
async def verify_incoming_sol(signature, expected_lamports=None):
    if not PAYMENT_WALLET or not valid_solana_address(PAYMENT_WALLET):
        return False, "PAYMENT_WALLET is not configured."
    tx=await rpc_call("getTransaction", [signature, {"encoding":"jsonParsed","commitment":"confirmed","maxSupportedTransactionVersion":0}])
    if not tx: return False, "Transaction not found yet."
    meta=tx.get("meta") or {}
    if meta.get("err") is not None: return False, "Transaction failed."
    msg=((tx.get("transaction") or {}).get("message") or {})
    keys=msg.get("accountKeys") or []
    idx=None
    for i,k in enumerate(keys):
        pub=(k.get("pubkey") if isinstance(k,dict) else k)
        if pub==PAYMENT_WALLET: idx=i; break
    if idx is None: return False, "Payment wallet not found in transaction."
    pre=(meta.get("preBalances") or [0]*len(keys))[idx]
    post=(meta.get("postBalances") or [0]*len(keys))[idx]
    received=post-pre
    need=expected_lamports or int(PAYMENT_SOL*1_000_000_000)
    if received < need: return False, f"Received {received/1e9:.9f} SOL; required {need/1e9:.9f} SOL."
    return True, {"received_lamports":received}

async def create_premium_invite(user_id, invite_days=1):
    if not PREMIUM_CHANNEL_ID: return None
    try:
        invite=await BOT.create_chat_invite_link(PREMIUM_CHANNEL_ID, member_limit=1, expire_date=int(time.time()) + max(3600, int(invite_days)*86400))
        return invite.invite_link
    except Exception:
        logging.exception("Invite creation failed")
        return None

# ============================================================
# TOKEN PRICE / MARKET DATA
# ============================================================

async def token_market_from_rpc(mint):
    """Use Helius DAS price when available; never fabricate market data."""
    asset = await helius_get_asset(mint)
    if not asset:
        return None
    ti = asset.get("token_info") or {}
    pi = ti.get("price_info") or {}
    raw_price = pi.get("price_per_token")
    try:
        p = float(raw_price)
    except Exception:
        p = None
    metadata = asset.get("content", {}).get("metadata", {}) if isinstance(asset.get("content"), dict) else {}
    return {
        "price": p,
        "name": metadata.get("name") or "Solana Token",
        "symbol": metadata.get("symbol") or "TOKEN",
        "decimals": ti.get("decimals"),
        "supply": ti.get("supply"),
        "logo": ((asset.get("content") or {}).get("links") or {}).get("image") if isinstance(asset.get("content"), dict) else None,
        "raw": asset,
    }


# ============================================================
# SMART MONEY / WHALE ENGINE
# ============================================================

async def wallet_activity(address, limit=20):
    sigs = await get_signatures(address, limit)
    return sigs

def is_smart_money(address):
    return address in SMART_MONEY_WALLETS

async def smart_money_check(address):
    return {
        "is_tracked_smart_money": is_smart_money(address),
        "wallet": address
    }


async def wallet_report(address):
    balance = await get_balance(address)
    sigs = await get_signatures(address, 20)
    enhanced = await helius_address_transactions(address, 20)
    swaps = sum(1 for x in enhanced if x.get("type") == "SWAP")
    transfers = sum(1 for x in enhanced if x.get("type") == "TRANSFER")
    return {
        "address": address,
        "sol_balance": balance,
        "recent_transactions": len(sigs),
        "parsed_transactions": len(enhanced),
        "swaps": swaps,
        "transfers": transfers,
        "smart_money": is_smart_money(address),
        "signatures": sigs,
        "enhanced": enhanced,
    }


# ============================================================
# EXACT TRANSFER ANOMALY TRACKER (PARSED DATA)
# ============================================================

async def transfer_blunder_report(wallet):
    txs = await helius_address_transactions(wallet, 100)
    cutoff = time.time() - 600
    recipients = set()
    transfer_rows = []
    for tx in txs:
        if transaction_age_seconds(tx) > 600:
            continue
        for tr in extract_native_transfers(tx):
            if tr.get("fromUserAccount") == wallet and tr.get("toUserAccount"):
                recipients.add(tr["toUserAccount"])
                transfer_rows.append(tr)
        for tr in extract_token_transfers(tx):
            if tr.get("fromUserAccount") == wallet and tr.get("toUserAccount"):
                recipients.add(tr["toUserAccount"])
                transfer_rows.append(tr)
    return {
        "wallet": wallet,
        "events_last_10m": len(transfer_rows),
        "distinct_recipients_last_10m": len(recipients),
        "recipients": sorted(recipients),
        "alert": len(recipients) > 15,
        "transfers": transfer_rows[:100],
        "parsed": bool(txs),
    }


# ============================================================
# AUTOMATIC DISCOVERY ENGINE
# ============================================================

async def discover_new_tokens():
    """Discover token mints from parsed transactions touching configured programs.
    This uses Helius' indexed transaction feed; it does not guess token addresses.
    """
    programs = list(dict.fromkeys(DISCOVERY_PROGRAM_IDS))
    if not programs or not HELIUS_API_KEY:
        return []
    found=[]
    for program in programs:
        txs = await helius_address_transactions(program, 100)
        for tx in txs:
            age = transaction_age_seconds(tx)
            if age > 900:
                continue
            tx_type = str(tx.get("type") or "")
            # TOKEN_MINT is explicit. For swap transactions, token transfers are
            # still useful discovery candidates but safety/score decides whether
            # they become alerts.
            if tx_type == "TOKEN_MINT" or tx_type == "SWAP":
                for mint in transaction_mints(tx):
                    if mint not in found:
                        found.append(mint)
    return found[:50]


async def build_live_alert(mint):
    report = await build_v5_market_report(mint)
    if report.get("score", 0) < MIN_SCORE:
        return None
    return report


async def auto_discovery_loop():
    while True:
        try:
            if AUTO_DISCOVERY_ENABLED and PREMIUM_CHANNEL_ID:
                for mint in await discover_new_tokens():
                    if mint in WATCH_TOKENS:
                        continue
                    alert = await build_live_alert(mint)
                    if not alert:
                        continue
                    key=f"auto:{mint}"
                    if time.time()-last_signal_time.get(key,0) < 1800:
                        continue
                    last_signal_time[key]=time.time()
                    active_signals[mint] = {
                        "entry": alert["price"],
                        "created": time.time(),
                        "data": alert,
                        "history": [(time.time(), alert["price"])],
                    }
                    alert["price_history"] = active_signals[mint]["history"]
                    await BOT.send_photo(
                        PREMIUM_CHANNEL_ID,
                        BufferedInputFile(make_signal_image(alert, premium=True), filename="premium_live_signal.png"),
                        caption=(
                            "🔥 <b>AUTO DISCOVERY SIGNAL</b>\n\n"
                            f"🪙 <code>{mint}</code>\n"
                            f"📌 {alert['symbol']}\n"
                            f"💵 Price: <b>{price(alert['price'])}</b>\n"
                            f"🛡️ Safety: <b>{alert['safety_score']}/100</b>\n"
                            f"🎯 Score: <b>{alert['score']}/100</b>\n\n"
                            "Only provider-backed data is shown."
                        ),
                        parse_mode="HTML",
                        reply_markup=free_signal_keyboard(mint)
                    )
        except Exception:
            logging.exception("Auto discovery loop failed")
        await asyncio.sleep(max(10, DISCOVERY_SCAN_SECONDS))


async def result_tracker_loop():
    while True:
        try:
            for mint, sig in list(active_signals.items()):
                entry=sig.get("entry")
                if not entry:
                    continue
                market=await token_market_from_rpc(mint)
                current=market.get("price") if market else None
                if current is None:
                    continue
                pnl=(current-entry)/entry*100 if entry else 0
                sig["last_price"]=current
                hist=sig.setdefault("history", [])
                hist.append((time.time(), current))
                sig["data"]["price_history"] = hist[-60:]
                # Close on configured TP3/SL, based on actual observed price.
                if pnl >= TP3_PCT or pnl <= -SL_PCT:
                    label="TP3 HIT" if pnl >= TP3_PCT else "SL HIT"
                    # Free channel reveal only after target/SL result: address + logo are shown here.
                    if FREE_CHANNEL_ID and pnl > 0:
                        reveal = f"<code>{mint}</code>\n"
                        try:
                            await BOT.send_photo(
                                FREE_CHANNEL_ID,
                                BufferedInputFile(make_result_image(sig["data"].get("symbol","TOKEN"), entry, current, label), filename="free_result.png"),
                                caption=(f"📊 <b>{label}</b>\n\n{reveal}"
                                         f"Entry: <b>{price(entry)}</b>\nCurrent: <b>{price(current)}</b>\n"
                                         f"P/L: <b>{pnl:+.2f}%</b>\n\n🤖 <a href=\"{BOT_URL or ('https://t.me/'+BOT_USERNAME)}\">Open Signal Bot</a>"),
                                parse_mode="HTML"
                            )
                        except Exception:
                            logging.exception("Free result post failed")
                    await db_add_signal(mint, sig["data"].get("symbol","TOKEN"), entry, current, pnl, label)
                    if PREMIUM_CHANNEL_ID:
                        await BOT.send_photo(
                            PREMIUM_CHANNEL_ID,
                            BufferedInputFile(make_result_image(sig["data"].get("symbol","TOKEN"), entry, current, label), filename="trade_result.png"),
                            caption=(f"📊 <b>{label}</b>\n\n<code>{mint}</code>\n"
                                     f"Entry: <b>{price(entry)}</b>\nCurrent: <b>{price(current)}</b>\n"
                                     f"P/L: <b>{pnl:+.2f}%</b>"),
                            parse_mode="HTML"
                        )
                    del active_signals[mint]
        except Exception:
            logging.exception("Result tracker failed")
        await asyncio.sleep(max(15, RESULT_SCAN_SECONDS))



# ============================================================
# V5 MARKET INTELLIGENCE ENGINE
# ============================================================

async def dexscreener_token_data(mint):
    """Read current pair/market data when DexScreener has the token indexed."""
    if not MARKET_DATA_ENABLED or not mint:
        return None
    now = time.time()
    if now - last_market_refresh.get(mint, 0) < max(5, MARKET_REFRESH_SECONDS):
        return market_cache.get(mint)

    url = DEXSCREENER_API_URL.rstrip("/") + "/" + quote(mint, safe="")
    try:
        status, data = await _http_json_request(
            "GET", url, headers={"Accept": "application/json"}
        )
        if status != 200:
            return market_cache.get(mint)
    except Exception:
        return market_cache.get(mint)

    pairs = data.get("pairs") if isinstance(data, dict) else None
    if not pairs:
        return None

    sol_pairs = [
        p for p in pairs
        if str((p.get("chainId") or "")).lower() == "solana"
    ] or pairs

    def liq(p):
        try: return float((p.get("liquidity") or {}).get("usd") or 0)
        except Exception: return 0.0

    pair = max(sol_pairs, key=liq)
    txns5 = pair.get("txns", {}).get("m5", {}) or {}
    vol = pair.get("volume", {}) or {}
    price_change = pair.get("priceChange", {}) or {}

    try:
        price_usd = float(pair.get("priceUsd")) if pair.get("priceUsd") is not None else None
    except Exception:
        price_usd = None

    buys = int(txns5.get("buys") or 0)
    sells = int(txns5.get("sells") or 0)
    total_tx = buys + sells
    buy_share = (buys / total_tx * 100) if total_tx else None
    ratio = (buys / sells) if sells else (float(buys) if buys else 0)

    created_at_ms = pair.get("pairCreatedAt")
    age_seconds = None
    if created_at_ms:
        try:
            age_seconds = max(0, time.time() - float(created_at_ms) / 1000)
        except Exception:
            pass

    result = {
        "source": "DexScreener",
        "pair_address": pair.get("pairAddress"),
        "dex_id": pair.get("dexId"),
        "url": pair.get("url"),
        "base_symbol": ((pair.get("baseToken") or {}).get("symbol") or "TOKEN"),
        "base_name": ((pair.get("baseToken") or {}).get("name") or "Solana Token"),
        "price": price_usd,
        "liquidity_usd": liq(pair),
        "volume_5m": float(vol.get("m5") or 0),
        "volume_1h": float(vol.get("h1") or 0),
        "buys_5m": buys,
        "sells_5m": sells,
        "buy_share_5m": buy_share,
        "buy_sell_ratio_5m": ratio,
        "price_change_5m": float(price_change.get("m5") or 0),
        "price_change_1h": float(price_change.get("h1") or 0),
        "fdv": float(pair.get("fdv") or 0),
        "market_cap": float(pair.get("marketCap") or 0),
        "age_seconds": age_seconds,
        "pair": pair,
        "observed_at": now,
    }
    market_cache[mint] = result
    last_market_refresh[mint] = now
    return result


def _safe_float(v, default=0.0):
    try: return float(v)
    except Exception: return default


async def save_market_snapshot(mint, market):
    if not market:
        return
    row = (
        time.time(),
        _safe_float(market.get("price"), 0) if market.get("price") is not None else None,
        _safe_float(market.get("liquidity_usd"), 0),
        _safe_float(market.get("volume_5m"), 0),
        int(market.get("buys_5m") or 0),
        int(market.get("sells_5m") or 0),
        _safe_float(market.get("price_change_5m"), 0),
    )
    token_snapshots[mint].append(row)
    if DB:
        try:
            async with DB.acquire() as c:
                await c.execute(
                    """INSERT INTO token_snapshots(
                        mint,price,liquidity_usd,volume_5m,buys_5m,sells_5m,price_change_5m,pair_address
                    ) VALUES($1,TO_TIMESTAMP($2),$3,$4,$5,$6,$7,$8)
                    ON CONFLICT DO NOTHING""",
                    mint, row[0], row[1], row[2], row[3], row[4], row[5],
                    market.get("pair_address")
                )
        except Exception:
            logging.exception("Snapshot save failed")


def market_acceleration(mint, market):
    """Compare the latest snapshot with the prior one; no synthetic values."""
    hist = token_snapshots.get(mint) or []
    if len(hist) < 2:
        return {
            "volume_acceleration": None,
            "buy_acceleration": None,
            "price_acceleration": None,
            "samples": len(hist)
        }

    prev = hist[-2]
    cur = hist[-1]

    def growth(a, b):
        if a is None or b is None:
            return None
        if a == 0:
            return None
        return b / a

    return {
        "volume_acceleration": growth(prev[3], cur[3]),
        "buy_acceleration": growth(prev[4], cur[4]),
        "price_acceleration": growth(prev[1], cur[1]) if prev[1] not in (None, 0) and cur[1] is not None else None,
        "samples": len(hist)
    }


async def smart_money_token_activity(mint):
    """Count configured tracked wallets that visibly touched the token recently."""
    if not SMART_MONEY_WALLETS or not HELIUS_API_KEY:
        return {"wallets": [], "count": 0, "labels": []}

    touched = []
    labels = []
    for wallet in list(SMART_MONEY_WALLETS)[:50]:
        try:
            txs = await helius_address_transactions(wallet, 30)
            found = False
            for tx in txs:
                if transaction_age_seconds(tx) > 3600:
                    continue
                if mint in transaction_mints(tx):
                    found = True
                    break
            if found:
                touched.append(wallet)
                labels.append(SMART_MONEY_LABELS.get(wallet, "Tracked Wallet"))
        except Exception:
            continue

    return {"wallets": touched, "count": len(touched), "labels": labels}


async def wallet_whale_activity(wallet):
    """Parsed large SOL/native transfer activity for a wallet."""
    txs = await helius_address_transactions(wallet, 100)
    large = []
    for tx in txs:
        if transaction_age_seconds(tx) > 900:
            continue
        for tr in extract_native_transfers(tx):
            if tr.get("fromUserAccount") != wallet:
                continue
            sol = _safe_float(tr.get("amount"), 0) / 1_000_000_000
            if sol >= WHALE_ALERT_SOL:
                large.append({
                    "to": tr.get("toUserAccount"),
                    "sol": sol,
                    "signature": tx.get("signature")
                })
    return large[:25]


def classify_meme(market, safety_score, acceleration, smart_count):
    """Evidence-based lifecycle classification."""
    if not market:
        return "UNAVAILABLE"

    age = market.get("age_seconds")
    liq = _safe_float(market.get("liquidity_usd"))
    ratio = _safe_float(market.get("buy_sell_ratio_5m"))
    buy_share = market.get("buy_share_5m")
    buys = int(market.get("buys_5m") or 0)
    vol_acc = acceleration.get("volume_acceleration")
    buy_acc = acceleration.get("buy_acceleration")

    if age is not None and age <= NEW_LAUNCH_MAX_SECONDS:
        return "NEW LAUNCH"
    if age is not None and age <= EARLY_ALERT_MAX_SECONDS:
        return "EARLY ALERT"
    if age is not None and age <= LATE_MEME_MAX_SECONDS:
        if liq >= MIN_LIQUIDITY_EARLY_USD and ratio >= MIN_BUY_SELL_RATIO:
            return "LATE MEME"
        return "MONITOR"

    if (
        liq >= MIN_LIQUIDITY_PREFERRED_USD
        and ratio >= MIN_BUY_SELL_RATIO
        and (buy_share is None or buy_share >= MIN_BUY_SHARE_PCT)
        and buys >= 15
        and safety_score >= MIN_SCORE
        and (vol_acc is None or vol_acc >= 1.5)
    ):
        return "MOMENTUM WATCH"

    return "MONITOR"


async def build_v5_market_report(mint):
    safety = await safety_scan(mint)
    market = await dexscreener_token_data(mint)
    rpc_market = await token_market_from_rpc(mint)
    if not market and rpc_market:
        market = {
            "source": "Helius DAS",
            "price": rpc_market.get("price"),
            "base_symbol": rpc_market.get("symbol", "TOKEN"),
            "base_name": rpc_market.get("name", "Solana Token"),
            "liquidity_usd": None,
            "volume_5m": None,
            "buys_5m": None,
            "sells_5m": None,
            "buy_share_5m": None,
            "buy_sell_ratio_5m": None,
            "price_change_5m": None,
            "age_seconds": None,
            "pair_address": None,
        }

    if market:
        await save_market_snapshot(mint, market)

    acceleration = market_acceleration(mint, market) if market else {
        "volume_acceleration": None, "buy_acceleration": None, "price_acceleration": None, "samples": 0
    }
    smart = await smart_money_token_activity(mint)
    classification = classify_meme(market, safety["score"], acceleration, smart["count"])

    score = int(safety["score"])
    evidence = []

    if market:
        liq = market.get("liquidity_usd")
        if liq is not None:
            if liq >= MIN_LIQUIDITY_PREFERRED_USD:
                score += 5; evidence.append("Preferred liquidity")
            elif liq >= MIN_LIQUIDITY_EARLY_USD:
                score += 2; evidence.append("Minimum liquidity")
        ratio = market.get("buy_sell_ratio_5m")
        if ratio is not None and ratio >= MIN_BUY_SELL_RATIO:
            score += 4; evidence.append("Buy/sell ratio")
        buy_share = market.get("buy_share_5m")
        if buy_share is not None and buy_share >= MIN_BUY_SHARE_PCT:
            score += 3; evidence.append("Buy-side dominance")
        if acceleration.get("volume_acceleration") is not None and acceleration["volume_acceleration"] >= 1.5:
            score += 5; evidence.append("Volume acceleration")
        if acceleration.get("buy_acceleration") is not None and acceleration["buy_acceleration"] >= 1.5:
            score += 4; evidence.append("Buyer acceleration")

    if smart["count"] >= SMART_MONEY_ALERT_MIN_WALLETS:
        score += 8
        evidence.append(f"{smart['count']} tracked wallets touched token")

    score = min(100, score)

    return {
        "address": mint,
        "symbol": (market or {}).get("base_symbol") or (rpc_market or {}).get("symbol") or "TOKEN",
        "name": (market or {}).get("base_name") or (rpc_market or {}).get("name") or mint[:10] + "...",
        "price": (market or {}).get("price") if market else (rpc_market or {}).get("price"),
        "safety": safety,
        "safety_score": safety["score"],
        "score": score,
        "class": classification,
        "market": market,
        "acceleration": acceleration,
        "smart_money": smart,
        "evidence": evidence,
        "created_at": time.time(),
    }


def advanced_score(report):
    """Transparent 0-100 market intelligence score from observed fields only."""
    if not ADVANCED_SCORE_ENABLED:
        return int(report.get("score") or 0), []
    m = report.get("market") or {}
    safety = int(report.get("safety_score") or 0)
    acc = report.get("acceleration") or {}
    smart = report.get("smart_money") or {}
    score = 0
    evidence = []
    # Safety: 30 points
    score += round(safety * 0.30)
    if safety >= 80: evidence.append("strong on-chain safety")
    # Liquidity: 15 points
    liq = _safe_float(m.get("liquidity_usd"))
    if liq is not None:
        if liq >= MIN_LIQUIDITY_PREFERRED_USD: score += 15; evidence.append("preferred liquidity")
        elif liq >= MIN_LIQUIDITY_EARLY_USD: score += 9; evidence.append("minimum liquidity")
        elif liq >= 10000: score += 4
    # Buy pressure: 15 points
    ratio = _safe_float(m.get("buy_sell_ratio_5m"))
    share = _safe_float(m.get("buy_share_5m"))
    if ratio is not None and ratio >= MIN_BUY_SELL_RATIO: score += 8; evidence.append("buy/sell pressure")
    if share is not None and share >= MIN_BUY_SHARE_PCT: score += 7; evidence.append("buy-side dominance")
    # Momentum: 20 points
    va = _safe_float(acc.get("volume_acceleration")); ba = _safe_float(acc.get("buy_acceleration"))
    if va is not None and va >= 1.5: score += 10; evidence.append("volume acceleration")
    if ba is not None and ba >= 1.5: score += 10; evidence.append("buyer acceleration")
    # Smart money: 10 points
    sc = int(smart.get("count") or 0)
    if sc >= 3: score += 10; evidence.append(f"{sc} tracked smart-money wallets")
    elif sc >= 1: score += 5; evidence.append("tracked smart money")
    # Activity/age: 10 points
    age = _safe_float(m.get("age_seconds"))
    if age is not None and age <= EARLY_ALERT_MAX_SECONDS: score += 5; evidence.append("early lifecycle")
    buys = int(m.get("buys_5m") or 0)
    if buys >= 15: score += 5; evidence.append("active buyers")
    return max(0, min(100, int(score))), evidence


def signal_levels(entry):
    try: entry=float(entry)
    except Exception: return {"tp1":None,"tp2":None,"tp3":None,"sl":None}
    return {"tp1":entry*(1+SIGNAL_TP1_PCT/100),"tp2":entry*(1+SIGNAL_TP2_PCT/100),"tp3":entry*(1+SIGNAL_TP3_PCT/100),"sl":entry*(1-SIGNAL_SL_PCT/100)}


def advanced_signal_text(report):
    entry=report.get("price"); levels=signal_levels(entry)
    m=report.get("market") or {}; a=report.get("acceleration") or {}; sm=report.get("smart_money") or {}
    holder=report.get("holders") or {}; top10=holder.get("top10_raw")
    ratio=m.get("buy_sell_ratio_5m")
    va=a.get("volume_acceleration"); ba=a.get("buy_acceleration")
    lines=[
        f"🚀 <b>{report.get('class','MEME SIGNAL')}</b>","",
        f"🪙 <b>{report.get('symbol','TOKEN')}</b>",
        f"🎯 Intelligence Score: <b>{report.get('advanced_score',report.get('score',0))}/100</b>",
        f"🛡 Safety: <b>{report.get('safety_score',0)}/100</b>",
        f"💵 Entry: <b>{price(entry)}</b>",
        f"🎯 TP1: <b>{price(levels['tp1'])}</b> | TP2: <b>{price(levels['tp2'])}</b> | TP3: <b>{price(levels['tp3'])}</b>",
        f"🛑 SL: <b>{price(levels['sl'])}</b>",
        f"💧 Liquidity: <b>{money(m.get('liquidity_usd')) if m.get('liquidity_usd') is not None else 'N/A'}</b>",
        f"⚖️ B/S: <b>{ratio:.2f}x</b>" if ratio is not None else "⚖️ B/S: <b>N/A</b>",
        f"📈 Vol accel: <b>{va:.2f}x</b> | Buy accel: <b>{ba:.2f}x</b>" if va is not None and ba is not None else "📈 Momentum: <b>Limited provider data</b>",
        f"🧠 Smart money: <b>{sm.get('count',0)}</b> tracked wallets",
        f"👥 Top-10: <b>{top10:.1f}%</b>" if top10 is not None else "👥 Top-10: <b>N/A</b>",
        "",
        f"📌 Evidence: {', '.join(report.get('advanced_evidence') or report.get('evidence') or []) or 'No extra evidence'}",
        "⚠️ Observed market/on-chain data can be delayed or incomplete. Not financial advice."
    ]
    return "\n".join(lines)


async def token_timeline(mint, limit=30):
    events=[]
    if DB:
        async with DB.acquire() as c:
            rows=await c.fetch("SELECT created_at,event_type,score,message FROM intelligence_events WHERE mint=$1 ORDER BY created_at DESC LIMIT $2",mint,limit)
            events.extend([dict(r) for r in rows])
            rows=await c.fetch("SELECT created_at,alert_type,score FROM token_alerts WHERE mint=$1 ORDER BY created_at DESC LIMIT $2",mint,limit)
            events.extend([{ "created_at":r["created_at"],"event_type":r["alert_type"],"score":r["score"],"message":None } for r in rows])
    events.sort(key=lambda x:x.get("created_at") or datetime.min.replace(tzinfo=timezone.utc), reverse=True)
    return events[:limit]

async def save_intelligence_event(mint,event_type,report,message=""):
    if not DB: return
    try:
        async with DB.acquire() as c:
            await c.execute("INSERT INTO intelligence_events(mint,event_type,score,message,payload) VALUES($1,$2,$3,$4,$5::jsonb)",mint,event_type,int(report.get("advanced_score",report.get("score",0))),message,json.dumps({"class":report.get("class"),"symbol":report.get("symbol"),"price":report.get("price")},default=str))
    except Exception: logging.exception("intelligence event save failed")

async def portfolio_rows(user_id):
    if not DB: return []
    async with DB.acquire() as c:
        return await c.fetch("SELECT * FROM user_portfolio WHERE user_id=$1 ORDER BY updated_at DESC",user_id)

async def portfolio_upsert(user_id,mint,symbol,qty,entry):
    if not DB: return False
    async with DB.acquire() as c:
        await c.execute("INSERT INTO user_portfolio(user_id,mint,symbol,qty,avg_entry) VALUES($1,$2,$3,$4,$5) ON CONFLICT(user_id,mint) DO UPDATE SET symbol=$3,qty=$4,avg_entry=$5,updated_at=NOW()",user_id,mint,symbol,float(qty),float(entry))
    return True

async def enriched_report(mint):
    report=await build_v5_market_report(mint)
    report["holders"]=report.get("safety",{}).get("holders",{})
    adv,ev=advanced_score(report)
    report["advanced_score"]=adv
    report["advanced_evidence"]=ev
    return report

def v5_signal_text(report):
    m = report.get("market") or {}
    acc = report.get("acceleration") or {}
    smart = report.get("smart_money") or {}
    price_text = price(report.get("price"))
    liq = money(m.get("liquidity_usd")) if m.get("liquidity_usd") is not None else "N/A"
    ratio = f"{m.get('buy_sell_ratio_5m'):.2f}x" if m.get("buy_sell_ratio_5m") is not None else "N/A"
    buyshare = f"{m.get('buy_share_5m'):.1f}%" if m.get("buy_share_5m") is not None else "N/A"
    volacc = f"{acc.get('volume_acceleration'):.2f}x" if acc.get("volume_acceleration") is not None else "N/A"
    buyacc = f"{acc.get('buy_acceleration'):.2f}x" if acc.get("buy_acceleration") is not None else "N/A"
    smartline = ", ".join(smart.get("labels") or []) or "None tracked"
    evidence = ", ".join(report.get("evidence") or []) or "Safety/on-chain evidence only"

    return (
        f"🔥 <b>{report.get('class','MEME SIGNAL')}</b>\n\n"
        f"🪙 <b>{report.get('symbol','TOKEN')}</b>\n"
        f"💵 Price: <b>{price_text}</b>\n"
        f"🎯 Score: <b>{report.get('score',0)}/100</b>\n"
        f"🛡 Safety: <b>{report.get('safety_score',0)}/100</b>\n"
        f"💧 Liquidity: <b>{liq}</b>\n"
        f"🟢 Buy share (5m): <b>{buyshare}</b>\n"
        f"⚖️ Buy/Sell: <b>{ratio}</b>\n"
        f"📈 Volume acceleration: <b>{volacc}</b>\n"
        f"👥 Buyer acceleration: <b>{buyacc}</b>\n"
        f"🧠 Tracked smart money: <b>{smartline}</b>\n\n"
        f"📌 Evidence: {evidence}\n\n"
        "⚠️ Screening data can be incomplete or delayed. Not financial advice."
    )


async def send_v5_alert(report, reason="scanner"):
    mint = report["address"]
    now = time.time()

    # Hourly global discovery limiter.
    while alert_hour_bucket and now - alert_hour_bucket[0] > 3600:
        alert_hour_bucket.popleft()
    if len(alert_hour_bucket) >= MAX_DISCOVERY_ALERTS_PER_HOUR:
        return False

    key = f"{reason}:{mint}"
    if now - last_signal_time.get(key, 0) < GLOBAL_ALERT_COOLDOWN_SECONDS:
        return False

    if not PREMIUM_CHANNEL_ID or not BOT:
        return False

    last_signal_time[key] = now
    alert_hour_bucket.append(now)

    active_signals.setdefault(mint, {
        "entry": report.get("price"),
        "created": now,
        "data": report,
        "history": []
    })
    if report.get("price") is not None:
        active_signals[mint]["history"].append((now, report["price"]))
        report["price_history"] = active_signals[mint]["history"]

    await BOT.send_photo(
        PREMIUM_CHANNEL_ID,
        BufferedInputFile(make_signal_image(report, premium=True), filename="v5_meme_signal.png"),
        caption=v5_signal_text(report),
        parse_mode="HTML",
        reply_markup=free_signal_keyboard(mint)
    )
    await save_alert_event(mint, reason, report)
    return True


async def save_alert_event(mint, alert_type, report):
    if not DB:
        return
    try:
        async with DB.acquire() as c:
            await c.execute(
                "INSERT INTO token_alerts(mint,alert_type,score,payload) VALUES($1,$2,$3,$4::jsonb)",
                mint, alert_type, int(report.get("score") or 0),
                json.dumps({
                    "class": report.get("class"),
                    "symbol": report.get("symbol"),
                    "evidence": report.get("evidence"),
                    "smart_money": report.get("smart_money"),
                    "market": report.get("market"),
                }, default=str)
            )
    except Exception:
        logging.exception("Alert event save failed")


async def v5_scanner_loop():
    """Continuously enrich configured/watchlist tokens and auto-discovered tokens."""
    while True:
        try:
            candidates = set(WATCH_TOKENS)
            candidates.update(active_signals.keys())

            # User watchlists from PostgreSQL.
            if DB:
                async with DB.acquire() as c:
                    rows = await c.fetch("SELECT DISTINCT mint FROM watchlists")
                candidates.update(r["mint"] for r in rows)

            for mint in list(candidates)[:100]:
                if not valid_solana_address(mint):
                    continue
                report = await build_v5_market_report(mint)
                if report.get("price") is None:
                    continue

                cls = report.get("class")
                score = report.get("score", 0)
                if score >= MIN_SCORE and cls in {"NEW LAUNCH", "EARLY ALERT", "LATE MEME", "MOMENTUM WATCH"}:
                    await send_v5_alert(report, reason=f"class:{cls}")
                for event_type, event_text in detect_condition_changes(mint, report):
                    # Respect per-user alert settings for private alerts.
                    if event_type in V6_ALERT_TYPES:
                        await save_alert_event(mint, event_type, report)

        except Exception:
            logging.exception("V5 scanner loop failed")
        await asyncio.sleep(max(10, MARKET_REFRESH_SECONDS))


async def v5_discovery_loop():
    """Enhance the existing verified-program discovery with full V5 scoring."""
    while True:
        try:
            if AUTO_DISCOVERY_ENABLED and PREMIUM_CHANNEL_ID:
                for mint in await discover_new_tokens():
                    if not valid_solana_address(mint):
                        continue
                    report = await build_v5_market_report(mint)
                    if report.get("price") is None:
                        continue
                    if report.get("score", 0) < MIN_SCORE:
                        continue
                    await send_v5_alert(report, reason="auto-discovery")
        except Exception:
            logging.exception("V5 discovery loop failed")
        await asyncio.sleep(max(10, DISCOVERY_SCAN_SECONDS))


async def v5_snapshot_loop():
    while True:
        try:
            candidates = set(WATCH_TOKENS) | set(active_signals.keys())
            for mint in list(candidates)[:100]:
                market = await dexscreener_token_data(mint)
                if market:
                    await save_market_snapshot(mint, market)
        except Exception:
            logging.exception("Snapshot loop failed")
        await asyncio.sleep(max(20, TOKEN_SNAPSHOT_SECONDS))


async def alert_settings(user_id):
    defaults = {
        "new_launch": True, "smart_money": True, "whale": True,
        "rug": True, "volume_acceleration": True, "price_move": True
    }
    if not DB:
        return defaults
    async with DB.acquire() as c:
        row = await c.fetchrow("SELECT * FROM alert_settings WHERE user_id=$1", user_id)
    if not row:
        return defaults
    return {k: bool(row[k]) for k in defaults}


async def set_alert_setting(user_id, field, value):
    allowed = {"new_launch","smart_money","whale","rug","volume_acceleration","price_move"}
    if field not in allowed or not DB:
        return False
    async with DB.acquire() as c:
        await c.execute(
            f"""INSERT INTO alert_settings(user_id,{field}) VALUES($1,$2)
            ON CONFLICT(user_id) DO UPDATE SET {field}=$2""",
            user_id, bool(value)
        )
    return True


async def token_history(mint, limit=20):
    if not DB:
        return []
    async with DB.acquire() as c:
        return await c.fetch(
            """SELECT ts,price,liquidity_usd,volume_5m,buys_5m,sells_5m,price_change_5m
               FROM token_snapshots WHERE mint=$1 ORDER BY ts DESC LIMIT $2""",
            mint, limit
        )


async def smart_money_command_report(mint):
    report = await smart_money_token_activity(mint)
    if not report["wallets"]:
        return "🧠 <b>SMART MONEY</b>\n\nNo configured tracked wallet was observed touching this token recently."
    lines = "\n".join(
        f"• {SMART_MONEY_LABELS.get(w, 'Tracked Wallet')}: <code>{w}</code>"
        for w in report["wallets"]
    )
    return f"🧠 <b>SMART MONEY ACTIVITY</b>\n\n{lines}\n\nThis reflects configured wallet tracking, not a guarantee of future performance."


async def deep_token_report(mint):
    report = await build_v5_market_report(mint)
    m = report.get("market") or {}
    a = report.get("acceleration") or {}
    safety = report.get("safety") or {}
    flags = safety.get("flags") or []
    flag_text = "\n".join("• " + x for x in flags) if flags else "• No basic RPC risk flag detected."

    return (
        f"🔬 <b>DEEP TOKEN REPORT</b>\n\n"
        f"🪙 {report['symbol']} — <code>{mint}</code>\n"
        f"🎯 Composite screen: <b>{report['score']}/100</b>\n"
        f"🛡 Safety screen: <b>{report['safety_score']}/100</b>\n"
        f"🏷 Class: <b>{report['class']}</b>\n"
        f"💵 Price: <b>{price(report.get('price'))}</b>\n"
        f"💧 Liquidity: <b>{money(m.get('liquidity_usd')) if m.get('liquidity_usd') is not None else 'N/A'}</b>\n"
        f"📊 5m volume: <b>{money(m.get('volume_5m')) if m.get('volume_5m') is not None else 'N/A'}</b>\n"
        f"🟢 Buys/Sells: <b>{m.get('buys_5m','N/A')} / {m.get('sells_5m','N/A')}</b>\n"
        f"⚖️ Buy/Sell ratio: <b>{m.get('buy_sell_ratio_5m','N/A')}</b>\n"
        f"📈 Volume acceleration: <b>{a.get('volume_acceleration','N/A')}</b>\n"
        f"👥 Buyer acceleration: <b>{a.get('buy_acceleration','N/A')}</b>\n\n"
        f"🚩 <b>Risk flags</b>\n{flag_text}\n\n"
        "Data is provider-backed where available. Missing fields remain N/A."
    )



# ============================================================
# V6 USER INTELLIGENCE / ADMIN HELPERS
# ============================================================

def lifecycle_for(report):
    m = report.get("market") or {}
    age = m.get("age_seconds")
    if age is not None and age <= NEW_LAUNCH_MAX_SECONDS:
        return "NEW"
    if age is not None and age <= EARLY_ALERT_MAX_SECONDS:
        return "EARLY"
    if age is not None and age <= LATE_MEME_MAX_SECONDS:
        if report.get("score", 0) >= MIN_SCORE:
            return "MOMENTUM"
        return "LATE"
    return "MONITOR"


def detect_condition_changes(mint, report):
    """Detect meaningful changes only; never manufacture missing values."""
    old = token_lifecycle.get(mint)
    new = lifecycle_for(report)
    events = []
    m = report.get("market") or {}
    if old and old != new and new == "MOMENTUM":
        events.append(("momentum", "📈 Momentum conditions strengthened."))
    token_lifecycle[mint] = new

    hist = token_snapshots.get(mint) or []
    if len(hist) >= 2:
        prev, cur = hist[-2], hist[-1]
        # indices: timestamp, price, liquidity, volume, buys, sells, price_change
        if prev[2] and cur[2]:
            liq_change = (cur[2] - prev[2]) / prev[2] * 100
            if liq_change <= -RUG_LIQUIDITY_DROP_PCT:
                events.append(("rug", f"🚨 Liquidity changed {liq_change:.1f}% between observations."))
        if prev[1] and cur[1]:
            price_change = (cur[1] - prev[1]) / prev[1] * 100
            if price_change <= -RUG_PRICE_DROP_PCT:
                events.append(("price_move", f"⚠️ Price changed {price_change:.1f}% between observations."))

    acc = report.get("acceleration") or {}
    if acc.get("volume_acceleration") is not None and acc["volume_acceleration"] >= 1.5:
        events.append(("volume_acceleration", "📊 Volume acceleration detected."))

    smart = report.get("smart_money") or {}
    if smart.get("count", 0) >= SMART_MONEY_ALERT_MIN_WALLETS:
        events.append(("smart_money", f"🧠 {smart['count']} tracked wallets observed."))

    return events


def format_user_risk_summary(report):
    safety = report.get("safety") or {}
    flags = safety.get("flags") or []
    m = report.get("market") or {}
    risk = []
    if m.get("liquidity_usd") is not None and m["liquidity_usd"] < MIN_LIQUIDITY_EARLY_USD:
        risk.append("Low liquidity")
    if m.get("buy_sell_ratio_5m") is not None and m["buy_sell_ratio_5m"] < 1:
        risk.append("Sell pressure")
    risk.extend(flags[:5])
    return risk or ["No configured risk flag triggered"]


async def log_admin(admin_id, action, target=None, details=None):
    if not DB:
        return
    try:
        async with DB.acquire() as c:
            await c.execute(
                "INSERT INTO admin_audit_log(admin_id,action,target,details) VALUES($1,$2,$3,$4::jsonb)",
                admin_id, action, target, json.dumps(details or {}, default=str)
            )
    except Exception:
        logging.exception("Admin audit log failed")


async def is_admin_user(user_id):
    return user_id in ADMIN_IDS


def admin_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📊 Dashboard", callback_data="adm:dashboard"),
         InlineKeyboardButton(text="👥 Users", callback_data="adm:users")],
        [InlineKeyboardButton(text="📡 Scanner", callback_data="adm:scanner"),
         InlineKeyboardButton(text="🧠 Smart Wallets", callback_data="adm:smart")],
        [InlineKeyboardButton(text="🔌 Providers", callback_data="adm:providers"),
         InlineKeyboardButton(text="💳 Payments", callback_data="adm:payments")],
        [InlineKeyboardButton(text="📢 Broadcast", callback_data="adm:broadcast"),
         InlineKeyboardButton(text="📋 Audit Log", callback_data="adm:audit")],
    ])


async def admin_dashboard_text():
    if not DB:
        return "📊 <b>ADMIN DASHBOARD</b>\n\nPostgreSQL is required for full statistics."
    async with DB.acquire() as c:
        users = await c.fetchval("SELECT COUNT(*) FROM members")
        active = await c.fetchval("SELECT COUNT(*) FROM members WHERE expires_at > NOW()")
        signals = await c.fetchval("SELECT COUNT(*) FROM signal_history")
        alerts = await c.fetchval("SELECT COUNT(*) FROM token_alerts")
        pending = await c.fetchval("SELECT COUNT(*) FROM pending_payments")
    return (
        "📊 <b>ADMIN DASHBOARD</b>\n\n"
        f"👥 Users: <b>{users}</b>\n"
        f"💎 Active premium: <b>{active}</b>\n"
        f"📈 Signal history: <b>{signals}</b>\n"
        f"🚨 Alert events: <b>{alerts}</b>\n"
        f"💳 Pending payments: <b>{pending}</b>\n"
        f"👀 Active signals: <b>{len(active_signals)}</b>"
    )


async def admin_provider_text():
    return (
        "🔌 <b>PROVIDER HEALTH</b>\n\n"
        f"Helius: <b>{'CONFIGURED' if HELIUS_API_KEY else 'MISSING'}</b>\n"
        f"Alchemy: <b>{'CONFIGURED' if ALCHEMY_RPC else 'MISSING'}</b>\n"
        f"QuickNode: <b>{'CONFIGURED' if QUICKNODE_RPC else 'MISSING'}</b>\n"
        f"Market data: <b>{'ON' if MARKET_DATA_ENABLED else 'OFF'}</b>\n"
        f"DB: <b>{'CONNECTED' if DB else 'NOT CONNECTED'}</b>"
    )


async def admin_users_text():
    if not DB:
        return "👥 PostgreSQL unavailable."
    async with DB.acquire() as c:
        rows = await c.fetch(
            "SELECT user_id,username,expires_at FROM members ORDER BY expires_at DESC LIMIT 15"
        )
    if not rows:
        return "👥 No members."
    lines = [
        f"• <code>{r['user_id']}</code> @{r['username'] or '-'} → {r['expires_at']}"
        for r in rows
    ]
    return "👥 <b>RECENT MEMBERS</b>\n\n" + "\n".join(lines)


async def admin_payment_text():
    if not DB:
        return "💳 PostgreSQL unavailable."
    async with DB.acquire() as c:
        rows = await c.fetch(
            "SELECT user_id,plan,price_usd,lamports,created_at FROM pending_payments "
            "ORDER BY created_at DESC LIMIT 15"
        )
    if not rows:
        return "💳 No pending payments."
    lines = [
        f"• <code>{r['user_id']}</code> {r['plan']} ${float(r['price_usd']):.2f} | {r['created_at']}"
        for r in rows
    ]
    return "💳 <b>PENDING PAYMENTS</b>\n\n" + "\n".join(lines)


async def admin_audit_text():
    if not DB:
        return "📋 PostgreSQL unavailable."
    async with DB.acquire() as c:
        rows = await c.fetch(
            "SELECT admin_id,action,target,created_at FROM admin_audit_log "
            "ORDER BY created_at DESC LIMIT 15"
        )
    if not rows:
        return "📋 No admin actions logged."
    lines = [
        f"• {r['created_at']} | <code>{r['admin_id']}</code> | {r['action']} | {r['target'] or '-'}"
        for r in rows
    ]
    return "📋 <b>ADMIN AUDIT LOG</b>\n\n" + "\n".join(lines)


async def paper_open(user_id, mint):
    if not PAPER_TRADING_ENABLED:
        return False, "Paper trading is disabled."
    report = await build_v5_market_report(mint)
    if report.get("price") is None:
        return False, "Current price is unavailable."
    if DB:
        async with DB.acquire() as c:
            await c.execute(
                "INSERT INTO paper_trades(user_id,mint,entry_price,size_usd) VALUES($1,$2,$3,$4)",
                user_id, mint, float(report["price"]), PAPER_TRADE_SIZE_USD
            )
    return True, f"🧪 Paper trade opened at {price(report['price'])} with ${PAPER_TRADE_SIZE_USD:.2f} virtual size."


async def paper_close(user_id, mint):
    if not DB:
        return False, "PostgreSQL is required."
    report = await build_v5_market_report(mint)
    if report.get("price") is None:
        return False, "Current price unavailable."
    async with DB.acquire() as c:
        row = await c.fetchrow(
            "SELECT id,entry_price,size_usd FROM paper_trades "
            "WHERE user_id=$1 AND mint=$2 AND status='OPEN' ORDER BY opened_at DESC LIMIT 1",
            user_id, mint
        )
        if not row:
            return False, "No open paper trade for this token."
        entry = float(row["entry_price"])
        exitp = float(report["price"])
        pnl = (exitp - entry) / entry * float(row["size_usd"]) if entry else 0
        await c.execute(
            "UPDATE paper_trades SET status='CLOSED',exit_price=$1,pnl_usd=$2,closed_at=NOW() WHERE id=$3",
            exitp, pnl, row["id"]
        )
    return True, f"🧪 Paper trade closed at {price(exitp)} | P/L: <b>${pnl:+.2f}</b>"


async def paper_stats(user_id):
    if not DB:
        return "PostgreSQL is required."
    async with DB.acquire() as c:
        total = await c.fetchval("SELECT COUNT(*) FROM paper_trades WHERE user_id=$1", user_id)
        closed = await c.fetchval("SELECT COUNT(*) FROM paper_trades WHERE user_id=$1 AND status='CLOSED'", user_id)
        pnl = await c.fetchval("SELECT COALESCE(SUM(pnl_usd),0) FROM paper_trades WHERE user_id=$1", user_id)
    return f"🧪 <b>PAPER TRADING</b>\n\nTrades: <b>{total}</b>\nClosed: <b>{closed}</b>\nTotal P/L: <b>${float(pnl):+.2f}</b>"


# ============================================================
# IMAGE / BRAND ENGINE
# ============================================================

def load_logo(size=(150, 150)):
    """Load optional custom logo; otherwise create a clean branded mark."""
    try:
        if LOGO_PATH and os.path.exists(LOGO_PATH):
            im = Image.open(LOGO_PATH).convert("RGBA")
            im.thumbnail(size, Image.Resampling.LANCZOS)
            return im
    except Exception:
        logging.exception("Logo load failed")

    im = Image.new("RGBA", size, (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    d.ellipse((4, 4, size[0]-4, size[1]-4), fill="#55e38a", outline="white", width=4)
    f = font(42, True)
    d.text((size[0]//2, size[1]//2), "SM", font=f, fill="#08111f", anchor="mm")
    return im


def draw_logo(img, x=1020, y=24, size=(130, 130)):
    logo = load_logo(size)
    img.paste(logo, (x, y), logo)


def draw_chart_panel(d, data, x1=650, y1=210, x2=1115, y2=575):
    """Draw a branded chart-style panel without inventing market prices."""
    d.rounded_rectangle((x1, y1, x2, y2), radius=22, fill="#0b1627", outline="#263956", width=2)
    d.text((x1+22, y1+18), "MARKET STRUCTURE", font=font(22, True), fill="white")

    # Prefer actual OHLC if a provider supplies it; otherwise use actual observed
    # price snapshots collected by this bot. No synthetic candles are generated.
    candles = data.get("candles") or []
    if candles:
        vals=[]
        for c in candles[-24:]:
            try: vals += [float(c["open"]), float(c["high"]), float(c["low"]), float(c["close"])]
            except Exception: pass
        if vals:
            lo, hi = min(vals), max(vals)
            span = hi-lo or 1.0
            left, right = x1+25, x2-25
            top, bottom = y1+75, y2-35
            step = (right-left)/max(1, len(candles[-24:]))
            for i,c in enumerate(candles[-24:]):
                try:
                    o,h,l,cl = map(float, (c["open"],c["high"],c["low"],c["close"]))
                except Exception: continue
                cx = left + i*step + step/2
                sy=lambda v: bottom-(v-lo)/span*(bottom-top)
                d.line((cx,sy(h),cx,sy(l)), fill="#9fb0c8", width=2)
                body_top, body_bottom = sy(max(o,cl)), sy(min(o,cl))
                fill="#55e38a" if cl >= o else "#ff6b6b"
                d.rectangle((cx-step*.28,body_top,cx+step*.28,max(body_bottom,body_top+3)), fill=fill)
            d.text((x1+22,y2-30), "Private market-data candles", font=font(16), fill="#71829b")
            return

    history = data.get("price_history") or []
    if len(history) >= 2:
        vals=[float(x[1]) for x in history if isinstance(x, (list, tuple)) and len(x)==2]
        if len(vals) >= 2:
            lo, hi=min(vals), max(vals); span=hi-lo or max(abs(hi), 1e-12)
            left,right=x1+25,x2-25; top,bottom=y1+75,y2-35
            pts=[]
            for i,v in enumerate(vals[-40:]):
                xx=left+i*(right-left)/max(1,len(vals[-40:])-1)
                yy=bottom-(v-lo)/span*(bottom-top)
                pts.append((xx,yy))
            d.line(pts, fill="#55e38a", width=4)
            d.text((x1+22,y2-30), "Observed private-provider price snapshots", font=font(16), fill="#71829b")
            return

    # No real market history: show a transparent/neutral analysis grid instead of fake prices.
    for i in range(1, 5):
        yy = y1+65 + i*((y2-y1-105)/5)
        d.line((x1+25,yy,x2-25,yy), fill="#1c2a40", width=1)
    for i in range(1, 7):
        xx = x1+25 + i*((x2-x1-50)/7)
        d.line((xx,y1+65,xx,y2-35), fill="#1c2a40", width=1)
    d.text((x1+48, y1+160), "LIVE CHART", font=font(30, True), fill="#55e38a")
    d.text((x1+48, y1+205), "Waiting for private", font=font(21), fill="#d9e2ef")
    d.text((x1+48, y1+238), "OHLC market data", font=font(21), fill="#d9e2ef")
    d.text((x1+48, y1+278), "No price is fabricated", font=font(18), fill="#f0c75e")


def make_signal_image(data, premium=False):
    img = Image.new("RGB", (1400, 820), "#08111f")
    d = ImageDraw.Draw(img)

    title = font(44, True)
    big = font(34, True)
    normal = font(24)
    small = font(18)

    heading = "PREMIUM LIVE MEME SIGNAL" if premium else "FREE DAILY MEME SIGNAL"
    d.text((45, 34), heading, font=title, fill="white")
    d.text((48, 88), BRAND_NAME, font=normal, fill="#9fb0c8")
    if premium or not FREE_HIDE_LOGO:
        draw_logo(img, 1245, 20, (120,120))

    d.rounded_rectangle((35, 145, 1365, 755), radius=25, fill="#111c2f")
    d.text((70, 180), f"{data.get('symbol','TOKEN')} | {data.get('name','Solana Token')[:26]}", font=big, fill="#55e38a")
    d.text((70, 245), f"Score: {data.get('score',0)}/100", font=big, fill="#55e38a")
    d.text((70, 305), f"Safety: {data.get('safety_score','N/A')}/100", font=normal, fill="#d9e2ef")

    if data.get("price") is not None:
        entry=float(data["price"])
        d.text((70, 360), f"Entry: {price(entry)}", font=normal, fill="white")
        d.text((70, 410), f"TP1: {price(entry*(1+TP1_PCT/100))}  TP2: {price(entry*(1+TP2_PCT/100))}", font=normal, fill="#55e38a")
        d.text((70, 460), f"TP3: {price(entry*(1+TP3_PCT/100))}  SL: {price(entry*(1-SL_PCT/100))}", font=normal, fill="#ff6b6b")
    else:
        d.text((70, 360), "Entry: Private market data required", font=normal, fill="#f0c75e")

    d.text((70, 520), f"Liquidity: {money(data.get('liquidity',0)) if data.get('liquidity') else 'N/A'}", font=normal, fill="#d9e2ef")
    d.text((70, 570), f"Buy/Sell: {data.get('buys','N/A')} / {data.get('sells','N/A')}", font=normal, fill="#d9e2ef")
    d.text((70, 620), f"Class: {score_label(data.get('score',0))}", font=normal, fill="#55e38a")
    d.text((70, 675), "Only provider-backed values are displayed.", font=small, fill="#9fb0c8")
    d.text((70, 705), "Data-backed alert • Not financial advice", font=small, fill="#71829b")

    draw_chart_panel(d, data)

    out = BytesIO()
    img.save(out, "PNG", optimize=True)
    return out.getvalue()


def make_result_image(symbol, entry, current, label):
    pnl = ((current-entry)/entry*100) if entry else 0
    img = Image.new("RGB", (1400, 700), "#08111f")
    d = ImageDraw.Draw(img)
    title = font(44, True); big = font(54, True); normal = font(27); small = font(18)
    draw_logo(img, 1245, 20, (120,120))
    d.text((50, 45), f"{symbol} • {label}", font=title, fill="white")
    d.text((52, 105), BRAND_NAME, font=normal, fill="#9fb0c8")
    d.rounded_rectangle((40, 160, 1360, 590), radius=25, fill="#111c2f")
    d.text((80, 215), f"Entry: {price(entry)}", font=normal, fill="#d9e2ef")
    d.text((80, 275), f"Current: {price(current)}", font=normal, fill="#d9e2ef")
    color = "#55e38a" if pnl > 0 else "#ff6b6b" if pnl < 0 else "#f0c75e"
    d.text((80, 350), f"P/L: {pnl:+.2f}%", font=big, fill=color)
    d.text((80, 450), "Calculated from actual price data.", font=normal, fill="#9fb0c8")
    d.text((80, 510), "Result tracking • Not financial advice", font=small, fill="#71829b")
    out = BytesIO(); img.save(out, "PNG", optimize=True); return out.getvalue()


def bot_link():
    if BOT_URL:
        return BOT_URL
    if BOT_USERNAME:
        return f"https://t.me/{BOT_USERNAME}"
    return ""


def free_signal_keyboard(address=""):
    url = bot_link()
    rows = []
    if url:
        rows.append([InlineKeyboardButton(text="🤖 Open Signal Bot", url=url)])
        rows.append([InlineKeyboardButton(text="🔎 Check This Token", url=f"{url}?start=token_{address}" if address else url)])
    if PREMIUM_URL and PREMIUM_URL != "https://t.me/":
        rows.append([InlineKeyboardButton(text="⭐ Premium Access", url=PREMIUM_URL)])
    return InlineKeyboardMarkup(inline_keyboard=rows) if rows else None

# ============================================================
# REPORT TEXT
# ============================================================

def safety_text(report):
    flags = report["flags"]

    if not flags:
        flags_text = "No basic RPC risk flag detected."
    else:
        flags_text = "\n".join(f"• {x}" for x in flags)

    top10 = report["holders"].get("top10_raw")

    return (
        f"🛡️ <b>SAFETY REPORT</b>\n\n"
        f"Score: <b>{report['score']}/100</b>\n"
        f"Mint authority: <b>"
        f"{'ACTIVE' if report['meta']['mint_authority'] else 'OFF/UNKNOWN'}"
        f"</b>\n"
        f"Freeze authority: <b>"
        f"{'ACTIVE' if report['meta']['freeze_authority'] else 'OFF/UNKNOWN'}"
        f"</b>\n"
        f"Top-10 raw concentration: <b>"
        f"{f'{top10:.2f}%' if top10 is not None else 'N/A'}"
        f"</b>\n\n"
        f"{flags_text}\n\n"
        "This is an on-chain screening report, not proof that a token is safe."
    )


# ============================================================
# FREE CHANNEL
# ============================================================

async def send_free_daily():
    global free_sent_today

    if not FREE_CHANNEL_ID:
        return

    today = now_utc().date()

    if free_sent_today == today:
        return

    # Without a private market-data provider, do not fabricate a token/price.
    # If WATCH_TOKENS is configured, choose the first token with a valid safety scan.
    candidate = None

    for mint in WATCH_TOKENS:
        report = await safety_scan(mint)

        if report["score"] < MIN_SCORE:
            continue

        candidate = {
            "address": mint,
            "symbol": "SOLANA TOKEN",
            "name": mint[:8] + "...",
            "score": report["score"],
            "safety_score": report["score"],
            "liquidity": 0,
            "buys": 0,
            "sells": 0,
            "price": None,
            "safety": report
        }
        break

    if not candidate:
        await BOT.send_message(
            FREE_CHANNEL_ID,
            "⚠️ <b>FREE DAILY SIGNAL</b>\n\n"
            "No qualifying on-chain setup was found from the configured "
            "private data sources today. No fabricated signal was posted.",
            parse_mode="HTML"
        )
        free_sent_today = today
        return

    address_line = f"🪙 <code>{candidate['address']}</code>\n" if not FREE_HIDE_ADDRESS else "🪙 <b>Contract hidden until result</b>\n"
    text = (
        "🟢 <b>FREE DAILY SIGNAL</b>\n\n"
        + address_line
        + f"🛡️ Safety score: <b>{candidate['safety_score']}/100</b>\n\n"
        "⚠️ A live USD entry requires a private market-data provider. "
        "This version will not invent one.\n\n"
        "⭐ <b>Premium</b> adds live scanner/data-provider integration "
        "when configured."
    )

    photo = BufferedInputFile(
        make_signal_image(candidate, premium=False),
        filename="free_daily_signal.png"
    )

    await BOT.send_photo(
        FREE_CHANNEL_ID,
        photo=photo,
        caption=text,
        parse_mode="HTML",
        reply_markup=free_signal_keyboard(candidate["address"])
    )

    free_sent_today = today


# ============================================================
# PREMIUM CHANNEL
# ============================================================

async def premium_alert_for_token(mint):
    report = await safety_scan(mint)

    if report["score"] < MIN_SCORE:
        return None

    smart = await smart_money_check(mint)

    return {
        "address": mint,
        "symbol": "TOKEN",
        "name": mint[:10] + "...",
        "score": report["score"],
        "safety_score": report["score"],
        "safety": report,
        "smart_money": smart,
        "price": None,
        "liquidity": 0,
        "buys": 0,
        "sells": 0
    }


async def premium_watchlist_loop():
    while True:
        if PREMIUM_CHANNEL_ID:
            for mint in list(WATCH_TOKENS):
                try:
                    alert = await build_live_alert(mint)
                    if not alert:
                        continue
                    key = f"watch:{mint}"
                    if time.time() - last_signal_time.get(key, 0) < 3600:
                        continue
                    last_signal_time[key] = time.time()
                    active_signals[mint] = {"entry": alert["price"], "created": time.time(), "data": alert, "history": [(time.time(), alert["price"])]}
                    alert["price_history"] = active_signals[mint]["history"]
                    await BOT.send_photo(
                        PREMIUM_CHANNEL_ID,
                        BufferedInputFile(make_signal_image(alert, premium=True), filename="premium_alert.png"),
                        caption=(
                            "🔥 <b>PREMIUM LIVE SIGNAL</b>\n\n"
                            f"🪙 <code>{mint}</code>\n"
                            f"📌 {alert['symbol']}\n"
                            f"💵 Price: <b>{price(alert['price'])}</b>\n"
                            f"🛡️ Safety: <b>{alert['safety_score']}/100</b>\n"
                            f"🎯 Score: <b>{alert['score']}/100</b>\n\n"
                            "TP/SL and result tracking use observed provider-backed price data."
                        ),
                        parse_mode="HTML",
                        reply_markup=free_signal_keyboard(mint)
                    )
                except Exception:
                    logging.exception("Premium watchlist error")
        await asyncio.sleep(max(10, PREMIUM_SCAN_SECONDS))


# ============================================================
# WEBSOCKET PROGRAM MONITOR
# ============================================================

async def _helius_reserve_wss_bytes(byte_count):
    """Reserve Helius WSS traffic at the documented 20 credits/MB rate."""
    credits = (max(0, int(byte_count)) / (1024.0 * 1024.0)) * HELIUS_WSS_CREDITS_PER_MB
    if credits <= 0:
        return True
    return await _helius_reserve(credits)


async def websocket_monitor():
    """
    Private Helius/QuickNode websocket log monitor.
    It records signatures involving configured programs.
    Full token decoding requires provider-specific parsers/indexers.
    """
    if not WSS_PROVIDERS:
        logging.warning("No WSS providers configured; websocket monitor disabled.")
        return

    programs = [PUMPFUN_PROGRAM_ID] + WATCH_PROGRAM_IDS
    programs = list(dict.fromkeys(x for x in programs if x))

    try:
        import websockets
    except ImportError:
        logging.warning("websockets package missing; monitor disabled.")
        return

    provider_index = 0
    backoff = 2
    while True:
        # Prefer the first healthy provider, but rotate through the full pool.
        current_wss = None
        for _ in range(len(WSS_PROVIDERS)):
            candidate = WSS_PROVIDERS[provider_index % len(WSS_PROVIDERS)]
            provider_index += 1
            if await _provider_allowed(candidate):
                current_wss = candidate
                break
        if not current_wss:
            await asyncio.sleep(min(60, backoff))
            backoff = min(60, backoff * 2)
            continue
        try:
            started = time.monotonic()
            async with websockets.connect(
                current_wss,
                ping_interval=20,
                ping_timeout=20
            ) as ws:
                logging.info("Solana WSS connected: %s", current_wss)
                _provider_ok(current_wss, time.monotonic() - started)
                backoff = 2

                sub_id = 1

                for program in programs:
                    request = {
                        "jsonrpc": "2.0",
                        "id": sub_id,
                        "method": "logsSubscribe",
                        "params": [
                            {"mentions": [program]},
                            {"commitment": "confirmed"}
                        ]
                    }

                    await ws.send(json.dumps(request))
                    sub_id += 1

                logging.info("Private Solana websocket monitor connected.")

                while True:
                    raw = await ws.recv()

                    # Only Helius WSS traffic consumes the Helius 31k/day
                    # and 950k/month budget. Public/private non-Helius WSS
                    # traffic is not charged to the Helius ledger.
                    if _is_helius_url(current_wss):
                        if not await _helius_reserve_wss_bytes(len(raw.encode("utf-8") if isinstance(raw, str) else raw)):
                            logging.warning("HELIUS DAILY/MONTHLY CREDIT CAP reached; rotating away from Helius WSS.")
                            break

                    try:
                        msg = json.loads(raw)
                    except:
                        continue

                    value = (
                        msg.get("params", {})
                        .get("result", {})
                        .get("value", {})
                    )

                    signature = value.get("signature")

                    if signature:
                        # WSS can replay a signature after reconnects; process once.
                        if signature in _seen_signatures:
                            continue
                        _seen_signatures.add(signature)
                        _seen_signatures_order.append(signature)
                        if len(_seen_signatures_order) == _seen_signatures_order.maxlen:
                            # Rebuild bounded set when deque rolls over.
                            _seen_signatures.clear()
                            _seen_signatures.update(_seen_signatures_order)
                        recent_signatures.append(signature)

                        # Fetch transaction in background for later decoding.
                        asyncio.create_task(
                            inspect_transaction(signature)
                        )

        except Exception as e:
            _provider_failed(current_wss or "wss:unknown")
            logging.warning("WSS disconnected from %s: %s", current_wss, e)
            await asyncio.sleep(min(60, backoff))
            backoff = min(60, backoff * 2)


async def inspect_transaction(signature):
    tx = await get_transaction(signature)

    if not tx:
        return

    # Keep raw transaction metadata for future decoders.
    # Do not call every transaction a buy/sell without decoding it.
    meta = tx.get("meta") or {}
    if meta.get("err"):
        return


# ============================================================
# WALLET / TOKEN COMMANDS
# ============================================================


def build_start_keyboard(user_id, premium=False):
    rows = []
    if premium or user_id in ADMIN_IDS:
        rows = [
            [InlineKeyboardButton(text="🔎 Deep Scan", callback_data="safety"),
             InlineKeyboardButton(text="🧠 Smart Money", callback_data="smart_menu")],
            [InlineKeyboardButton(text="🐋 Whale Tracker", callback_data="whale"),
             InlineKeyboardButton(text="🛡 Rug/Safety", callback_data="safety")],
            [InlineKeyboardButton(text="⭐ Watchlist", callback_data="watch"),
             InlineKeyboardButton(text="📊 Performance", callback_data="performance")],
            [InlineKeyboardButton(text="🔔 Alerts", callback_data="settings"),
             InlineKeyboardButton(text="🧪 Paper Trade", callback_data="paper_menu")],
            [InlineKeyboardButton(text="🧰 More Tools", callback_data="tools_menu"),
             InlineKeyboardButton(text="💎 Premium", callback_data="premium")],
        ]
    else:
        rows = [[InlineKeyboardButton(text="💎 Unlock Premium", callback_data="premium")]]
    if user_id in ADMIN_IDS:
        rows.append([InlineKeyboardButton(text="👑 Admin Panel", callback_data="adm:dashboard")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


@dp.message(Command("start"))
async def start(message: Message):
    parts = (message.text or "").split(maxsplit=1)
    arg = parts[1].strip() if len(parts) == 2 else ""
    if arg.startswith("ref_"):
        try: await save_referral(message.from_user.id,int(arg[4:]))
        except Exception: pass
    if arg.startswith("token_"):
        if not await is_premium(message.from_user.id):
            await message.answer("🔒 <b>Premium access required.</b>\n\nUse /premium to choose a plan.", parse_mode="HTML")
            return
        mint = arg[6:].strip()
        if not valid_solana_address(mint):
            await message.answer("Invalid Solana token address.")
            return
        report = await safety_scan(mint)
        await message.answer(safety_text(report), parse_mode="HTML")
        return
    kb = build_start_keyboard(message.from_user.id, premium=await is_premium(message.from_user.id))
    await message.answer(
        "🚀 <b>Solana Meme Intelligence</b>\n\n"
        "Send any Solana token mint to scan it instantly.\n"
        "Track safety, liquidity, momentum, holders, smart money, whale activity, alerts and paper trades.\n\n"
        "⚠️ Data is provider-backed screening information, not a profit guarantee.",
        reply_markup=kb, parse_mode="HTML"
    )



async def get_sol_usd_price():
    now = time.time()
    cache = getattr(get_sol_usd_price, "_cache", {"price": None, "ts": 0})
    if cache["price"] and now - cache["ts"] < 300:
        return cache["price"]
    try:
        status, data = await _http_json_request("GET", SOL_USD_PRICE_URL)
        if status == 200 and isinstance(data, dict):
            p = float(data.get("price"))
            if p > 0:
                cache = {"price": p, "ts": now}
                get_sol_usd_price._cache = cache
                return p
    except Exception:
        pass
    return SOL_USD_RATE if SOL_USD_RATE > 0 else None


def plan_keyboard():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🗓 Weekly — $1.99", callback_data="plan:weekly")],
        [InlineKeyboardButton(text="📅 Monthly — $4.99", callback_data="plan:monthly")],
        [InlineKeyboardButton(text="📆 Yearly — $19.99", callback_data="plan:yearly")],
    ])


async def create_plan_payment(message, plan):
    if plan not in PLAN_PRICES_USD:
        await message.answer("Invalid plan.")
        return
    if await is_premium(message.from_user.id):
        exp = await member_expiry(message.from_user.id)
        await message.answer(f"💎 <b>Premium active</b>\nExpires: <b>{exp}</b>", parse_mode="HTML")
        return
    rate = await get_sol_usd_price()
    if not rate:
        await message.answer("⚠️ SOL/USD rate unavailable. Try again shortly.")
        return

    usd = PLAN_PRICES_USD[plan]
    days = PLAN_DAYS[plan]
    lamports = int((usd / rate) * 1_000_000_000) + (message.from_user.id % 100000)
    sol = lamports / 1_000_000_000

    if DB:
        async with DB.acquire() as c:
            await c.execute(
                """INSERT INTO pending_payments(user_id,username,lamports,plan,duration_days,price_usd)
                   VALUES($1,$2,$3,$4,$5,$6)
                   ON CONFLICT(user_id) DO UPDATE SET
                   username=$2,lamports=$3,plan=$4,duration_days=$5,price_usd=$6,created_at=NOW()""",
                message.from_user.id, message.from_user.username, lamports, plan, days, usd
            )

    await message.answer(
        f"💎 <b>Premium {plan.title()}</b>\n\n"
        f"Price: <b>${usd:.2f}</b>\nDuration: <b>{days} days</b>\n"
        f"Current SOL rate: <b>${rate:,.2f}</b>\n\n"
        f"Send exactly <b>{sol:.9f} SOL</b> to:\n<code>{PAYMENT_WALLET}</code>\n\n"
        "Your unique payment amount is used for automatic matching.\n"
        "After payment, access is activated automatically when detected.",
        parse_mode="HTML"
    )


@dp.message(Command("trial"))
async def trial_command(message: Message):
    await message.answer("🎁 <b>Free trial is disabled.</b>\n\nAll user intelligence features require an active Premium plan. Use /premium to subscribe.", parse_mode="HTML")

@dp.message(Command("premium"))
async def premium_command(message: Message):
    if await is_premium(message.from_user.id):
        exp = await member_expiry(message.from_user.id)
        await message.answer(f"💎 <b>Premium active</b>\nExpires: <b>{exp}</b>", parse_mode="HTML")
        return
    await message.answer(
        "💎 <b>Premium Access</b>\n\n"
        "Choose a plan:\n"
        "🗓 Weekly — <b>$1.99</b> / 7 days\n"
        "📅 Monthly — <b>$4.99</b> / 30 days\n"
        "📆 Yearly — <b>$19.99</b> / 365 days",
        reply_markup=plan_keyboard(), parse_mode="HTML"
    )


@dp.callback_query(F.data.startswith("plan:"))
async def plan_callback(callback: CallbackQuery):
    await create_plan_payment(callback.message, callback.data.split(":", 1)[1])
    await callback.answer()


@dp.message(Command("verify"))
async def verify_payment(message: Message):
    parts = message.text.split()
    if len(parts) != 2 or not DB:
        await message.answer("Use <code>/verify TRANSACTION_SIGNATURE</code>", parse_mode="HTML")
        return
    async with DB.acquire() as c:
        pending = await c.fetchrow(
            "SELECT lamports,plan,duration_days,price_usd FROM pending_payments "
            "WHERE user_id=$1 AND created_at > NOW()-INTERVAL '24 hours'",
            message.from_user.id
        )
    if not pending:
        await message.answer("❌ No pending payment. Use /premium first.")
        return
    ok, info = await verify_incoming_sol(parts[1], expected_lamports=int(pending["lamports"]))
    if not ok:
        await message.answer(f"❌ Payment not verified.\n{info}", parse_mode="HTML")
        return
    days = int(pending["duration_days"] or 30)
    exp = datetime.now(timezone.utc) + timedelta(days=days)
    invite = await create_premium_invite(message.from_user.id)
    await save_member(message.from_user.id, message.from_user.username, exp, invite, parts[1])
    async with DB.acquire() as c:
        await c.execute("DELETE FROM pending_payments WHERE user_id=$1", message.from_user.id)
    txt = (
        f"✅ <b>Payment verified</b>\n\n"
        f"Plan: <b>{str(pending['plan']).title()}</b>\n"
        f"Price: <b>${float(pending['price_usd']):.2f}</b>\n"
        f"Expires: <b>{exp}</b>"
    )
    if invite:
        txt += f'\n\n🔐 <a href="{invite}">Join Premium Channel</a>'
    await message.answer(txt, parse_mode="HTML")


@dp.message(Command("dashboard"))
async def dashboard_command(message: Message):
    perf=await performance_summary()
    exp=await member_expiry(message.from_user.id)
    ref=await referral_count(message.from_user.id)
    text="📊 <b>DASHBOARD</b>\n\n"
    text += f"Premium: <b>{'ACTIVE' if exp and exp>now_utc() else 'INACTIVE'}</b>\n"
    if exp: text += f"Expires: <b>{exp}</b>\n"
    text += f"Referrals: <b>{ref}</b>\n\n"
    if perf: text += f"Signals: <b>{perf['n']}</b>\nWins: <b>{perf['wins']}</b>\nLosses: <b>{perf['losses']}</b>\nAverage P/L: <b>{float(perf['avg']):+.2f}%</b>"
    else: text += "Signal history: <b>N/A</b>"
    await message.answer(text,parse_mode="HTML")

@dp.message(Command("watch"))
async def watch_command(message: Message):
    parts=message.text.split()
    if len(parts)==2 and valid_solana_address(parts[1]):
        ok=await add_watch(message.from_user.id,parts[1])
        if not ok:
            await message.answer("Watchlist unavailable or full.")
        return
    items=await user_watchlist(message.from_user.id)
    await message.answer("⭐ <b>WATCHLIST</b>\n\n"+ ("\n".join(f"• <code>{x}</code>" for x in items) if items else "No tokens added."),parse_mode="HTML")

@dp.message(Command("ref"))
async def ref_command(message: Message):
    me=await BOT.get_me()
    link=f"https://t.me/{me.username}?start=ref_{message.from_user.id}"
    count=await referral_count(message.from_user.id)
    await message.answer(f"🎁 <b>REFERRAL</b>\n\nYour link:\n<code>{link}</code>\n\nReferrals: <b>{count}</b>",parse_mode="HTML")

@dp.message(Command("wallet"))
async def wallet_command(message: Message):
    parts = message.text.split()

    if len(parts) != 2 or not valid_solana_address(parts[1]):
        await message.answer(
            "Usage:\n<code>/wallet SOLANA_WALLET_ADDRESS</code>",
            parse_mode="HTML"
        )
        return

    report = await wallet_report(parts[1])

    balance = report["sol_balance"]
    balance_text = f"{balance:.4f} SOL" if balance is not None else "N/A"

    await message.answer(
        "👛 <b>WALLET REPORT</b>\n\n"
        f"Address:\n<code>{parts[1]}</code>\n\n"
        f"SOL balance: <b>{balance_text}</b>\n"
        f"Recent transactions: <b>{report['recent_transactions']}</b>\n"
        f"Tracked smart money: <b>"
        f"{'YES' if report['smart_money'] else 'NO'}"
        f"</b>\n\n"
        "This is an on-chain report, not a profitability guarantee.",
        parse_mode="HTML"
    )


@dp.message(Command("safety"))
async def safety_command(message: Message):
    parts = message.text.split()

    if len(parts) != 2 or not valid_solana_address(parts[1]):
        await message.answer(
            "Usage:\n<code>/safety TOKEN_MINT</code>",
            parse_mode="HTML"
        )
        return

    report = await safety_scan(parts[1])

    await message.answer(
        safety_text(report),
        parse_mode="HTML"
    )


@dp.message(Command("whale"))
async def whale_command(message: Message):
    parts = message.text.split()

    if len(parts) != 2 or not valid_solana_address(parts[1]):
        await message.answer(
            "Usage:\n<code>/whale WALLET_ADDRESS</code>",
            parse_mode="HTML"
        )
        return

    report = await transfer_blunder_report(parts[1])

    if report["alert"]:
        text = (
            "🚨 <b>WALLET ACTIVITY ALERT</b>\n\n"
            f"Wallet: <code>{parts[1]}</code>\n"
            f"Recent signature events: <b>{report['events_last_10m']}</b>\n\n"
            "This is an activity anomaly, not proof of wrongdoing."
        )
    else:
        text = (
            "🐋 <b>WALLET ACTIVITY</b>\n\n"
            f"Wallet: <code>{parts[1]}</code>\n"
            f"Recent signature events: <b>{report['events_last_10m']}</b>\n"
            "No configured anomaly threshold was triggered."
        )

    await message.answer(text, parse_mode="HTML")




@dp.message(Command("paper"))
async def paper_command(message: Message):
    parts = message.text.split()
    if len(parts) == 2 and valid_solana_address(parts[1]):
        ok, text = await paper_open(message.from_user.id, parts[1])
        await message.answer(text, parse_mode="HTML")
    elif len(parts) == 3 and parts[1].lower() == "close" and valid_solana_address(parts[2]):
        ok, text = await paper_close(message.from_user.id, parts[2])
        await message.answer(text, parse_mode="HTML")
    elif len(parts) == 1:
        await message.answer("Use <code>/paper TOKEN</code> or <code>/paper close TOKEN</code>", parse_mode="HTML")
    else:
        await message.answer("Invalid token address.")


@dp.message(Command("paperstats"))
async def paperstats_command(message: Message):
    await message.answer(await paper_stats(message.from_user.id), parse_mode="HTML")


@dp.message(Command("risk"))
async def risk_command(message: Message):
    parts = message.text.split()
    if len(parts) != 2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/risk TOKEN_MINT</code>", parse_mode="HTML")
        return
    report = await build_v5_market_report(parts[1])
    risks = format_user_risk_summary(report)
    await message.answer(
        "🛡 <b>RISK RADAR</b>\n\n" +
        "\n".join("• " + x for x in risks) +
        "\n\n⚠️ Risk flags are screening signals, not a guarantee.",
        parse_mode="HTML"
    )


@dp.message(Command("scan"))
async def scan_command(message: Message):
    parts = message.text.split()
    if len(parts) != 2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/scan TOKEN_MINT</code>", parse_mode="HTML")
        return
    report = await deep_token_report(parts[1])
    await message.answer(report, parse_mode="HTML")


@dp.message(Command("smart"))
async def smart_command(message: Message):
    parts = message.text.split()
    if len(parts) != 2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/smart TOKEN_MINT</code>", parse_mode="HTML")
        return
    await message.answer(await smart_money_command_report(parts[1]), parse_mode="HTML")


@dp.message(Command("history"))
async def history_command(message: Message):
    parts = message.text.split()
    if len(parts) != 2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/history TOKEN_MINT</code>", parse_mode="HTML")
        return
    rows = await token_history(parts[1], 10)
    if not rows:
        await message.answer("No stored market snapshots yet.")
        return
    lines = []
    for r in rows:
        lines.append(
            f"• {r['ts']} | ${r['price'] if r['price'] is not None else 'N/A'} | "
            f"Liq {money(r['liquidity_usd']) if r['liquidity_usd'] is not None else 'N/A'} | "
            f"B/S {r['buys_5m']}/{r['sells_5m']}"
        )
    await message.answer("📚 <b>TOKEN HISTORY</b>\n\n" + "\n".join(lines), parse_mode="HTML")


@dp.message(Command("alerts"))
async def alerts_command(message: Message):
    s = await alert_settings(message.from_user.id)
    text = (
        "🔔 <b>ALERT SETTINGS</b>\n\n"
        f"New launch: <b>{'ON' if s['new_launch'] else 'OFF'}</b>\n"
        f"Smart money: <b>{'ON' if s['smart_money'] else 'OFF'}</b>\n"
        f"Whale: <b>{'ON' if s['whale'] else 'OFF'}</b>\n"
        f"Rug: <b>{'ON' if s['rug'] else 'OFF'}</b>\n"
        f"Volume acceleration: <b>{'ON' if s['volume_acceleration'] else 'OFF'}</b>\n\n"
        "Use /alert TYPE on or /alert TYPE off"
    )
    await message.answer(text, parse_mode="HTML")


@dp.message(Command("alert"))
async def alert_command(message: Message):
    parts = message.text.split()
    allowed = {"new_launch","smart_money","whale","rug","volume_acceleration","price_move"}
    if len(parts) != 3 or parts[1] not in allowed or parts[2].lower() not in {"on","off"}:
        await message.answer("Use <code>/alert smart_money on</code>", parse_mode="HTML")
        return
    ok = await set_alert_setting(message.from_user.id, parts[1], parts[2].lower() == "on")
    if not ok:
        await message.answer("PostgreSQL is required for alert settings.")


@dp.message(Command("intel"))
async def intel_command(message: Message):
    parts=message.text.split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/intel TOKEN_MINT</code>",parse_mode="HTML"); return
    r=await enriched_report(parts[1])
    await message.answer(advanced_signal_text(r),parse_mode="HTML")

@dp.message(Command("score"))
async def score_command(message: Message):
    parts=message.text.split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/score TOKEN_MINT</code>",parse_mode="HTML"); return
    r=await enriched_report(parts[1])
    await message.answer(f"🎯 <b>{r.get('symbol')}</b>\n\nIntelligence: <b>{r.get('advanced_score')}/100</b>\nSafety: <b>{r.get('safety_score')}/100</b>\nClass: <b>{r.get('class')}</b>\n\nEvidence: {', '.join(r.get('advanced_evidence') or []) or 'Limited data'}",parse_mode="HTML")

@dp.message(Command("holders"))
async def holders_command(message: Message):
    parts=message.text.split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/holders TOKEN_MINT</code>",parse_mode="HTML"); return
    r=await safety_scan(parts[1]); h=r.get("holders") or {}
    if not h.get("available"):
        await message.answer("Holder concentration data unavailable from configured RPC."); return
    lines=[f"👥 <b>TOP HOLDERS</b>",f"Top-10 concentration: <b>{h.get('top10_raw',0):.2f}%</b>",""]
    for i,x in enumerate(h.get("holders",[])[:10],1): lines.append(f"{i}. <code>{x.get('address')}</code> — {x.get('share'):.2f}%")
    await message.answer("\n".join(lines),parse_mode="HTML")

@dp.message(Command("timeline"))
async def timeline_command(message: Message):
    parts=message.text.split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/timeline TOKEN_MINT</code>",parse_mode="HTML"); return
    events=await token_timeline(parts[1])
    if not events: await message.answer("📚 No stored timeline events for this token yet."); return
    lines=["📚 <b>TOKEN TIMELINE</b>",""]
    for e in events[:20]:
        ts=e.get("created_at"); ts=ts.strftime("%m-%d %H:%M UTC") if hasattr(ts,"strftime") else str(ts)
        lines.append(f"• {ts} — <b>{e.get('event_type')}</b> — score {e.get('score','N/A')}")
    await message.answer("\n".join(lines),parse_mode="HTML")

@dp.message(Command("portfolio"))
async def portfolio_command(message: Message):
    parts=message.text.split()
    if len(parts)==1:
        rows=await portfolio_rows(message.from_user.id)
        if not rows: await message.answer("📊 Portfolio is empty. Use <code>/portfolio add TOKEN QTY ENTRY</code>",parse_mode="HTML"); return
        lines=["📊 <b>PORTFOLIO</b>",""]
        for r in rows: lines.append(f"• <b>{r['symbol'] or 'TOKEN'}</b> {float(r['qty']):g} @ {price(r['avg_entry'])}")
        await message.answer("\n".join(lines),parse_mode="HTML"); return
    if len(parts)==5 and parts[1].lower()=="add" and valid_solana_address(parts[2]):
        try: qty=float(parts[3]); entry=float(parts[4])
        except: qty=entry=-1
        if qty<=0 or entry<=0: await message.answer("Invalid quantity/entry."); return
        r=await enriched_report(parts[2]); ok=await portfolio_upsert(message.from_user.id,parts[2],r.get("symbol"),qty,entry)
        if not ok:
            await message.answer("PostgreSQL is required for portfolio storage.")
        return
    await message.answer("Use <code>/portfolio</code> or <code>/portfolio add TOKEN QTY ENTRY</code>",parse_mode="HTML")

@dp.message(F.text)
async def address_handler(message: Message):
    text = message.text.strip()

    if valid_solana_address(text):
        if not user_scan_allowed(message.from_user.id):
            return
        report = await cached_enriched_report(text)
        if not report:
            await message.answer("Live provider data is unavailable for this token.")
            return
        await message.answer(
            advanced_signal_text(report),
            parse_mode="HTML"
        )
    else:
        # Ignore ordinary text to keep the chat clean. Commands remain available
        # through Telegram's command menu and the inline UI.
        return


@dp.callback_query(F.data == "premium")
async def premium_callback(callback: CallbackQuery):
    await premium_command(callback.message); await callback.answer()

@dp.callback_query(F.data == "watch")
async def watch_callback(callback: CallbackQuery):
    items=await user_watchlist(callback.from_user.id)
    await callback.message.answer("⭐ <b>WATCHLIST</b>\n\n"+("\n".join(f"• <code>{x}</code>" for x in items) if items else "No tokens added."),parse_mode="HTML"); await callback.answer()

@dp.callback_query(F.data == "performance")
async def performance_callback(callback: CallbackQuery):
    perf=await performance_summary()
    if not perf: text="📊 Signal history is not available until PostgreSQL is configured."
    else: text=f"📊 <b>PERFORMANCE</b>\n\nSignals: {perf['n']}\nWins: {perf['wins']}\nLosses: {perf['losses']}\nAverage P/L: {float(perf['avg']):+.2f}%"
    await callback.message.answer(text,parse_mode="HTML"); await callback.answer()



@dp.message(Command("admin"))
async def admin_command(message: Message):
    if not await is_admin_user(message.from_user.id):
        return
    await log_admin(message.from_user.id, "open_admin")
    await message.answer(await admin_dashboard_text(), reply_markup=admin_keyboard(), parse_mode="HTML")


@dp.callback_query(F.data == "trial")
async def trial_callback(callback: CallbackQuery):
    await callback.message.answer("🎁 <b>Free trial is disabled.</b>\n\nAll user intelligence features require an active Premium plan. Use /premium to subscribe.", parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "paper_menu")
async def paper_menu_callback(callback: CallbackQuery):
    await callback.message.answer("🧪 <b>PAPER TRADING</b>\n\n/paper TOKEN — open paper trade\n/paper close TOKEN — close trade\n/paperstats — view paper P/L\n\nNo real funds are used.", parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "tools_menu")
async def tools_menu_callback(callback: CallbackQuery):
    await callback.message.answer(
        "🧰 <b>MORE TOOLS</b>\n\n"
        "/scan TOKEN — deep scan\n/intel TOKEN — full intelligence\n/radar TOKEN — radar\n/score TOKEN — score\n/momentum TOKEN — momentum\n/launch TOKEN — launch lifecycle\n/holders TOKEN — top holders\n/lp TOKEN — liquidity\n/timeline TOKEN — timeline\n/history TOKEN — market history\n/risk TOKEN — risk radar\n/wallet WALLET — wallet report\n/walletdna WALLET — wallet DNA\n/portfolio — portfolio\n/portfolio_live — live P/L\n\nUse /commands for the complete command list.", parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data.startswith("adm:"))
async def admin_callback(callback: CallbackQuery):
    if not await is_admin_user(callback.from_user.id):
        await callback.answer("Not authorized.", show_alert=True)
        return

    action = callback.data.split(":", 1)[1]
    await log_admin(callback.from_user.id, f"admin:{action}")

    if action == "dashboard":
        text = await admin_dashboard_text()
    elif action == "users":
        text = await admin_users_text()
    elif action == "providers":
        text = await admin_provider_text()
    elif action == "payments":
        text = await admin_payment_text()
    elif action == "audit":
        text = await admin_audit_text()
    elif action == "scanner":
        text = (
            "📡 <b>SCANNER CONTROL</b>\n\n"
            f"Market scanner: <b>{'ON' if MARKET_DATA_ENABLED else 'OFF'}</b>\n"
            f"Discovery: <b>{'ON' if AUTO_DISCOVERY_ENABLED else 'OFF'}</b>\n"
            f"Min score: <b>{MIN_SCORE}</b>\n"
            f"Refresh: <b>{MARKET_REFRESH_SECONDS}s</b>"
        )
    elif action == "smart":
        wallets = list(SMART_MONEY_WALLETS)[:20]
        text = "🧠 <b>TRACKED SMART-MONEY WALLETS</b>\n\n" + (
            "\n".join(f"• {SMART_MONEY_LABELS.get(w,'Tracked Wallet')}: <code>{w}</code>" for w in wallets)
            if wallets else "No tracked wallets configured."
        )
    elif action == "broadcast":
        text = "📢 Use <code>/broadcast YOUR MESSAGE</code> (admin only)."
    else:
        text = "Unknown admin action."

    await callback.message.edit_text(text, reply_markup=admin_keyboard(), parse_mode="HTML")
    await callback.answer()


@dp.message(Command("broadcast"))
async def admin_broadcast(message: Message):
    if not await is_admin_user(message.from_user.id):
        return
    text = message.text.partition(" ")[2].strip()
    if not text:
        await message.answer("Use <code>/broadcast YOUR MESSAGE</code>", parse_mode="HTML")
        return
    if not DB:
        await message.answer("PostgreSQL required.")
        return

    async with DB.acquire() as c:
        rows = await c.fetch("SELECT user_id FROM members WHERE expires_at > NOW()")
    sent = 0
    for r in rows:
        try:
            await BOT.send_message(r["user_id"], "📢 " + text)
            sent += 1
            await asyncio.sleep(0.05)
        except Exception:
            pass
    await log_admin(message.from_user.id, "broadcast", details={"sent": sent})
    await message.answer(f"✅ Broadcast sent to {sent} active members.")


@dp.callback_query(F.data == "smart_menu")
async def smart_menu_callback(callback: CallbackQuery):
    await callback.message.answer("🧠 <b>SMART MONEY</b>\n\nUse <code>/smart TOKEN_MINT</code> for tracked wallet activity.\nUse <code>/wallet WALLET_ADDRESS</code> for a wallet report.\nUse <code>/walletdna WALLET_ADDRESS</code> for wallet behavior analysis.", parse_mode="HTML")
    await callback.answer()


@dp.callback_query(F.data == "whale")
async def whale_callback(callback: CallbackQuery):
    await callback.message.answer("🐋 <b>WHALE TRACKER</b>\n\nUse <code>/whale WALLET_ADDRESS</code> for the parsed 10-minute transfer anomaly check.\nThe anomaly threshold is >15 distinct recipients in 10 minutes.\n\n⚠️ An anomaly is not proof of wrongdoing.",parse_mode="HTML"); await callback.answer()

@dp.callback_query(F.data == "settings")
async def settings_callback(callback: CallbackQuery):
    s = await alert_settings(callback.from_user.id)
    text = ("🔔 <b>ALERT CENTER</b>\n\n"
            f"🚀 New launch: <b>{'ON' if s['new_launch'] else 'OFF'}</b>\n"
            f"🧠 Smart money: <b>{'ON' if s['smart_money'] else 'OFF'}</b>\n"
            f"🐋 Whale: <b>{'ON' if s['whale'] else 'OFF'}</b>\n"
            f"🛡 Rug: <b>{'ON' if s['rug'] else 'OFF'}</b>\n"
            f"📈 Volume acceleration: <b>{'ON' if s['volume_acceleration'] else 'OFF'}</b>\n"
            f"⚡ Price move: <b>{'ON' if s['price_move'] else 'OFF'}</b>\n\n"
            "Use /alert TYPE on|off to change a setting.\n"
            "Use /watch TOKEN to monitor a token.")
    await callback.message.answer(text,parse_mode="HTML"); await callback.answer()

@dp.callback_query(F.data == "safety")
async def safety_callback(callback: CallbackQuery):
    await callback.message.answer(
        "Send a Solana token mint address."
    )
    await callback.answer()


@dp.callback_query(F.data == "wallet")
async def wallet_callback(callback: CallbackQuery):
    await callback.message.answer(
        "Use:\n<code>/wallet WALLET_ADDRESS</code>",
        parse_mode="HTML"
    )
    await callback.answer()


# ============================================================
# V7 ADVANCED MEME INTELLIGENCE PACK
# ============================================================
# These features are deliberately provider-backed. Missing data is reported as
# unavailable instead of being guessed or fabricated.

V7_SCAN_LIMIT = int(os.getenv("V7_SCAN_LIMIT", "60"))
V7_ALERT_SCORE = int(os.getenv("V7_ALERT_SCORE", "85"))
V7_LIQUIDITY_DROP_PCT = float(os.getenv("V7_LIQUIDITY_DROP_PCT", "25"))
V7_VOLUME_SPIKE = float(os.getenv("V7_VOLUME_SPIKE", "2.0"))
V7_BUY_ACCEL = float(os.getenv("V7_BUY_ACCEL", "1.5"))
V7_SMART_CONFIRM = int(os.getenv("V7_SMART_CONFIRM", "2"))
V7_WHALE_SOL = float(os.getenv("V7_WHALE_SOL", "50"))
V7_LOOP_SECONDS = int(os.getenv("V7_LOOP_SECONDS", "45"))


def _num(v, default=None):
    try:
        return float(v)
    except Exception:
        return default


def _ratio(a, b):
    a, b = _num(a), _num(b)
    if a is None or b is None or b <= 0:
        return None
    return a / b


def intelligence_label(score):
    try: score = int(score)
    except Exception: score = 0
    if score >= 90: return "EXPLOSIVE"
    if score >= 85: return "STRONG"
    if score >= 75: return "WATCH"
    if score >= 60: return "EARLY"
    return "FILTERED"


def lifecycle_phase(report):
    m = report.get("market") or {}
    age = _num(m.get("age_seconds"))
    a = report.get("acceleration") or {}
    score = int(report.get("advanced_score", report.get("score", 0)) or 0)
    va = _num(a.get("volume_acceleration")) or 0
    ba = _num(a.get("buy_acceleration")) or 0
    if age is not None and age <= 30: return "DISCOVERY"
    if age is not None and age <= 60: return "EARLY ALERT"
    if age is not None and age <= 180 and score >= 80: return "GEM CANDIDATE"
    if age is not None and age <= 300 and score >= 85: return "EARLY GEM"
    if va >= 1.5 and ba >= 1.5: return "MOMENTUM"
    if age is not None and age <= LATE_MEME_MAX_SECONDS: return "LATE / MONITOR"
    return "MONITOR"


def risk_breakdown(report):
    s = report.get("safety") or {}
    meta = s.get("meta") or {}
    holders = s.get("holders") or {}
    m = report.get("market") or {}
    risks = []
    if meta.get("mint_authority"): risks.append(("HIGH", "Mint authority active"))
    if meta.get("freeze_authority"): risks.append(("HIGH", "Freeze authority active"))
    top10 = _num(holders.get("top10_raw"))
    if top10 is not None:
        if top10 > 50: risks.append(("HIGH", f"Top-10 concentration {top10:.1f}%"))
        elif top10 > TOP10_WARNING_PCT: risks.append(("MED", f"Top-10 concentration {top10:.1f}%"))
    liq = _num(m.get("liquidity_usd"))
    if liq is not None and liq < MIN_LIQUIDITY_EARLY_USD: risks.append(("HIGH", "Low liquidity"))
    elif liq is None: risks.append(("INFO", "Liquidity data unavailable"))
    return risks


def liquidity_quality(report):
    m = report.get("market") or {}
    liq = _num(m.get("liquidity_usd")); vol = _num(m.get("volume_5m"))
    if liq is None: return {"score": None, "label": "UNAVAILABLE", "ratio": None}
    ratio = _ratio(vol, liq)
    score = 50
    if liq >= MIN_LIQUIDITY_PREFERRED_USD: score += 30
    elif liq >= MIN_LIQUIDITY_EARLY_USD: score += 15
    if ratio is not None:
        if ratio <= 0.10: score += 10
        elif ratio >= 0.50: score -= 10
    return {"score": max(0, min(100, score)), "label": "HEALTHY" if score >= 75 else "WATCH", "ratio": ratio}


def momentum_regime(report):
    m = report.get("market") or {}; a = report.get("acceleration") or {}
    va = _num(a.get("volume_acceleration")); ba = _num(a.get("buy_acceleration"))
    ch = _num(m.get("price_change_5m")); ratio = _num(m.get("buy_sell_ratio_5m"))
    points = 0; reasons=[]
    if va is not None and va >= V7_VOLUME_SPIKE: points += 35; reasons.append("volume spike")
    elif va is not None and va >= 1.5: points += 20; reasons.append("volume acceleration")
    if ba is not None and ba >= V7_BUY_ACCEL: points += 25; reasons.append("buyer acceleration")
    if ratio is not None and ratio >= MIN_BUY_SELL_RATIO: points += 20; reasons.append("buy pressure")
    if ch is not None and ch > 0: points += 20; reasons.append("positive price change")
    elif ch is not None and ch < 0: points -= 15; reasons.append("negative price change")
    points=max(0,min(100,points))
    label="STRONG" if points>=70 else "BUILDING" if points>=45 else "WEAK"
    return {"score":points,"label":label,"reasons":reasons}


def build_intelligence_card(report):
    liq=liquidity_quality(report); mom=momentum_regime(report); risks=risk_breakdown(report)
    return {
        "score": int(report.get("advanced_score", report.get("score", 0)) or 0),
        "label": intelligence_label(report.get("advanced_score", report.get("score", 0))),
        "phase": lifecycle_phase(report),
        "liquidity": liq,
        "momentum": mom,
        "risks": risks,
        "smart_wallets": int((report.get("smart_money") or {}).get("count",0) or 0),
    }


async def wallet_dna(address):
    txs = await helius_address_transactions(address, 100)
    native = extract_native_transfers if txs else None
    total_in = total_out = 0.0
    counterparties=set(); mints=set(); swap_count=0; transfer_count=0
    first_ts=None; last_ts=None
    for tx in txs:
        ts=tx.get("timestamp") or tx.get("blockTime")
        if ts:
            first_ts = min(first_ts, ts) if first_ts else ts
            last_ts = max(last_ts, ts) if last_ts else ts
        if str(tx.get("type") or "") == "SWAP": swap_count += 1
        if str(tx.get("type") or "") == "TRANSFER": transfer_count += 1
        for tr in extract_native_transfers(tx):
            lamports=_num(tr.get("amount"),0) or 0
            sol=lamports/1e9
            if tr.get("toUserAccount") == address: total_in += sol
            if tr.get("fromUserAccount") == address: total_out += sol
            other=tr.get("fromUserAccount") if tr.get("toUserAccount")==address else tr.get("toUserAccount")
            if other: counterparties.add(other)
        mints.update(transaction_mints(tx))
    return {
        "wallet":address,"parsed":bool(txs),"transactions":len(txs),
        "swaps":swap_count,"transfers":transfer_count,"unique_tokens":len(mints),
        "counterparties":len(counterparties),"sol_in":total_in,"sol_out":total_out,
        "net_sol":total_in-total_out,"first_ts":first_ts,"last_ts":last_ts,
        "smart_money":is_smart_money(address),
    }


async def live_portfolio(user_id):
    rows=await portfolio_rows(user_id); out=[]
    for r in rows:
        mint=r["mint"]; current=None
        try:
            rep=await enriched_report(mint); current=_num(rep.get("price"))
        except Exception: pass
        qty=_num(r["qty"],0) or 0; entry=_num(r["avg_entry"],0) or 0
        value=qty*current if current is not None else None
        cost=qty*entry
        pnl=value-cost if value is not None else None
        pnl_pct=(pnl/cost*100) if pnl is not None and cost else None
        out.append({"symbol":r["symbol"] or "TOKEN","mint":mint,"qty":qty,"entry":entry,"current":current,"value":value,"pnl":pnl,"pnl_pct":pnl_pct})
    return out


async def v7_watchdog_loop():
    """Background intelligence layer for watchlists and active signals."""
    while True:
        try:
            candidates=set(WATCH_TOKENS)|set(active_signals.keys())
            if DB:
                async with DB.acquire() as c:
                    rows=await c.fetch("SELECT DISTINCT mint FROM watchlists")
                candidates.update(r["mint"] for r in rows)
            for mint in list(candidates)[:V7_SCAN_LIMIT]:
                if not valid_solana_address(mint): continue
                try:
                    r=await enriched_report(mint)
                    card=build_intelligence_card(r)
                    r["v7_card"]=card
                    # Persist meaningful state changes for timeline/history.
                    old=token_alert_state.get(mint) or {}
                    state=(card["phase"], card["label"], card["momentum"]["label"])
                    if old.get("v7_state") != state:
                        await save_intelligence_event(mint,"state_change",r,f"Phase {card['phase']} | {card['label']} | Momentum {card['momentum']['label']}")
                        token_alert_state[mint]={**old,"v7_state":state}
                    # Material risk change.
                    risks=card["risks"]
                    if any(x[0]=="HIGH" for x in risks):
                        await save_intelligence_event(mint,"risk_warning",r,"; ".join(x[1] for x in risks if x[0]=="HIGH"))
                except Exception:
                    logging.exception("V7 token analysis failed for %s", mint)
        except Exception:
            logging.exception("V7 watchdog failed")
        await asyncio.sleep(max(20,V7_LOOP_SECONDS))


@dp.message(Command("radar"))
async def radar_command(message: Message):
    parts=message.text.split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/radar TOKEN_MINT</code>",parse_mode="HTML"); return
    r=await enriched_report(parts[1]); c=build_intelligence_card(r); m=r.get("market") or {}
    await message.answer(
        f"📡 <b>MEME RADAR</b>\n\n🪙 {r.get('symbol')}\n🎯 Score: <b>{c['score']}/100 — {c['label']}</b>\n🧬 Phase: <b>{c['phase']}</b>\n📈 Momentum: <b>{c['momentum']['label']} ({c['momentum']['score']}/100)</b>\n💧 Liquidity: <b>{c['liquidity']['label']}</b>\n🧠 Smart wallets: <b>{c['smart_wallets']}</b>\n💵 Price: <b>{price(r.get('price'))}</b>\n📊 Volume 5m: <b>{money(m.get('volume_5m')) if m.get('volume_5m') is not None else 'N/A'}</b>\n\n" + ("⚠️ Risks:\n"+"\n".join(f"• {a}: {b}" for a,b in c['risks']) if c['risks'] else "✅ No configured high-risk flag detected") + "\n\nData can be incomplete/delayed. Not financial advice.",parse_mode="HTML")


@dp.message(Command("momentum"))
async def momentum_command(message: Message):
    parts=message.text.split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/momentum TOKEN_MINT</code>",parse_mode="HTML"); return
    r=await enriched_report(parts[1]); x=momentum_regime(r)
    await message.answer(f"📈 <b>MOMENTUM ENGINE</b>\n\nRegime: <b>{x['label']}</b>\nScore: <b>{x['score']}/100</b>\n\n"+"\n".join('• '+z for z in x['reasons']) if x['reasons'] else "No momentum evidence available.",parse_mode="HTML")


@dp.message(Command("launch"))
async def launch_command(message: Message):
    parts=message.text.split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/launch TOKEN_MINT</code>",parse_mode="HTML"); return
    r=await enriched_report(parts[1]); m=r.get("market") or {}
    age=_num(m.get("age_seconds")); phase=lifecycle_phase(r)
    age_text=f"{age:.0f}s" if age is not None else "Unavailable"
    await message.answer(f"🆕 <b>LAUNCH INTELLIGENCE</b>\n\nToken: <b>{r.get('symbol')}</b>\nAge: <b>{age_text}</b>\nPhase: <b>{phase}</b>\nScore: <b>{r.get('advanced_score')}/100</b>\nLiquidity: <b>{money(m.get('liquidity_usd')) if m.get('liquidity_usd') is not None else 'N/A'}</b>\nBuyers 5m: <b>{m.get('buys_5m') if m.get('buys_5m') is not None else 'N/A'}</b>\nBuy/Sell: <b>{m.get('buy_sell_ratio_5m'):.2f}x</b>" if m.get('buy_sell_ratio_5m') is not None else f"🆕 <b>LAUNCH INTELLIGENCE</b>\n\nToken: <b>{r.get('symbol')}</b>\nAge: <b>{age_text}</b>\nPhase: <b>{phase}</b>\nScore: <b>{r.get('advanced_score')}/100</b>",parse_mode="HTML")


@dp.message(Command("walletdna"))
async def walletdna_command(message: Message):
    parts=message.text.split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/walletdna WALLET</code>",parse_mode="HTML"); return
    x=await wallet_dna(parts[1])
    if not x["parsed"]:
        await message.answer("⚠️ Parsed wallet history unavailable from configured provider."); return
    await message.answer(f"🧬 <b>WALLET DNA</b>\n\nWallet: <code>{parts[1]}</code>\nTransactions: <b>{x['transactions']}</b>\nSwaps: <b>{x['swaps']}</b>\nTransfers: <b>{x['transfers']}</b>\nUnique tokens seen: <b>{x['unique_tokens']}</b>\nCounterparties: <b>{x['counterparties']}</b>\nSOL in: <b>{x['sol_in']:.4f}</b>\nSOL out: <b>{x['sol_out']:.4f}</b>\nNet: <b>{x['net_sol']:+.4f} SOL</b>\nSmart-money list: <b>{'YES' if x['smart_money'] else 'NO'}</b>",parse_mode="HTML")


@dp.message(Command("lp"))
async def lp_command(message: Message):
    parts=message.text.split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/lp TOKEN_MINT</code>",parse_mode="HTML"); return
    r=await enriched_report(parts[1]); m=r.get("market") or {}; q=liquidity_quality(r)
    await message.answer(f"💧 <b>LIQUIDITY INTELLIGENCE</b>\n\nLiquidity: <b>{money(m.get('liquidity_usd')) if m.get('liquidity_usd') is not None else 'N/A'}</b>\nQuality: <b>{q['label']}</b>\nQuality score: <b>{q['score'] if q['score'] is not None else 'N/A'}</b>\nVolume/Liquidity: <b>{q['ratio']:.2%}</b>" if q['ratio'] is not None else f"💧 <b>LIQUIDITY INTELLIGENCE</b>\n\nLiquidity: <b>{money(m.get('liquidity_usd')) if m.get('liquidity_usd') is not None else 'N/A'}</b>\nQuality: <b>{q['label']}</b>\nQuality score: <b>{q['score'] if q['score'] is not None else 'N/A'}</b>\nVolume/Liquidity: <b>N/A</b>",parse_mode="HTML")


@dp.message(Command("portfolio_live"))
async def portfolio_live_command(message: Message):
    rows=await live_portfolio(message.from_user.id)
    if not rows:
        await message.answer("📊 No portfolio positions."); return
    lines=["📊 <b>LIVE PORTFOLIO</b>",""]
    for x in rows:
        pnl="N/A" if x["pnl"] is None else f"${x['pnl']:+.2f} ({x['pnl_pct']:+.2f}%)"
        lines.append(f"• <b>{x['symbol']}</b> | Current {price(x['current'])} | P/L <b>{pnl}</b>")
    await message.answer("\n".join(lines),parse_mode="HTML")


@dp.message(Command("commands"))
async def commands_command(message: Message):
    await message.answer("""🧠 <b>SOLANA INTELLIGENCE COMMANDS</b>\n\n/scan TOKEN — deep scan\n/intel TOKEN — full intelligence\n/radar TOKEN — radar summary\n/score TOKEN — score\n/momentum TOKEN — momentum engine\n/launch TOKEN — launch lifecycle\n/safety TOKEN — safety\n/holders TOKEN — top holders\n/lp TOKEN — liquidity intelligence\n/smart TOKEN — smart money\n/whale WALLET — whale/activity\n/walletdna WALLET — wallet DNA\n/timeline TOKEN — token timeline\n/history TOKEN — market history\n/risk TOKEN — risk radar\n/watch TOKEN — watchlist\n/portfolio — saved portfolio\n/portfolio_live — live portfolio P/L\n/paper TOKEN — paper trade\n/paperstats — paper stats\n/alerts — alert settings\n/quality TOKEN — entry quality\n/compare TOKEN1 TOKEN2 [TOKEN3] — compare\n/lifecycle TOKEN — lifecycle stage\n/profile — risk profile\n/report TOKEN — advanced report\n/riskmap TOKEN — risk map\n/anomaly TOKEN — anomaly check\n/premium — premium plans\n\n⚠️ Market data depends on configured providers and their limits. No profitability guarantee.""",parse_mode="HTML")

# ============================================================
# DAILY SCHEDULER
# ============================================================

def seconds_to_daily_signal():
    now = now_utc()

    target = now.replace(
        hour=DAILY_SIGNAL_HOUR_UTC,
        minute=DAILY_SIGNAL_MINUTE_UTC,
        second=0,
        microsecond=0
    )

    if target <= now:
        target += timedelta(days=1)

    return max(1, int((target-now).total_seconds()))


async def daily_scheduler():
    while True:
        await asyncio.sleep(seconds_to_daily_signal())

        try:
            await send_free_daily()
        except Exception:
            logging.exception("Free daily signal failed")

        await asyncio.sleep(65)


# ============================================================
# V8 ADVANCED INTELLIGENCE PACK
# ============================================================
ADV8_ENABLED = os.getenv("ADV8_ENABLED", "true").lower() in {"1","true","yes","on"}
ADV8_MAX_EVENTS = int(os.getenv("ADV8_MAX_EVENTS", "100"))
ADV8_ANOMALY_WINDOW = int(os.getenv("ADV8_ANOMALY_WINDOW", "10"))
ADV8_WHALE_SOL = float(os.getenv("ADV8_WHALE_SOL", str(WHALE_ALERT_SOL)))

async def adv8_db_init():
    if not DB:
        return
    async with DB.acquire() as c:
        await c.execute("""
        CREATE TABLE IF NOT EXISTS score_history(
            id BIGSERIAL PRIMARY KEY, mint TEXT NOT NULL, score INTEGER, safety_score INTEGER,
            momentum_score INTEGER, liquidity_score INTEGER, smart_score INTEGER,
            holder_score INTEGER, risk_score INTEGER, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE INDEX IF NOT EXISTS idx_score_history_mint_time ON score_history(mint, created_at DESC);
        CREATE TABLE IF NOT EXISTS wallet_intelligence(
            wallet TEXT PRIMARY KEY, label TEXT, tx_count INTEGER DEFAULT 0,
            swap_count INTEGER DEFAULT 0, transfer_count INTEGER DEFAULT 0,
            sol_balance DOUBLE PRECISION, updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS user_risk_limits(
            user_id BIGINT PRIMARY KEY, max_position_usd DOUBLE PRECISION DEFAULT 100,
            max_open_trades INTEGER DEFAULT 5, max_daily_loss_usd DOUBLE PRECISION DEFAULT 50,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS provider_health(
            provider TEXT PRIMARY KEY, ok BOOLEAN NOT NULL DEFAULT FALSE,
            latency_ms DOUBLE PRECISION, error TEXT, checked_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        """)

async def adv8_save_score(mint, r, parts):
    if not DB:
        return
    try:
        async with DB.acquire() as c:
            await c.execute(
                "INSERT INTO score_history(mint,score,safety_score,momentum_score,liquidity_score,smart_score,holder_score,risk_score) VALUES($1,$2,$3,$4,$5,$6,$7,$8)",
                mint, int(r.get("score") or 0), int(r.get("safety_score") or 0),
                int(parts.get("momentum") or 0), int(parts.get("liquidity") or 0),
                int(parts.get("smart") or 0), int(parts.get("holder") or 0), int(parts.get("risk") or 0)
            )
    except Exception:
        logging.exception("score history save failed")

def adv8_num(x, default=0.0):
    try: return float(x)
    except Exception: return default

def adv8_market_features(r):
    m = r.get("market") or {}
    a = r.get("acceleration") or {}
    safety = r.get("safety") or {}
    holders = safety.get("holders") or {}
    top10 = adv8_num(holders.get("top10_raw"), 100)
    liq = adv8_num(m.get("liquidity_usd"))
    buy = adv8_num(m.get("buy_share_5m"))
    ratio = adv8_num(m.get("buy_sell_ratio_5m"))
    va = adv8_num(a.get("volume_acceleration"), 1)
    ba = adv8_num(a.get("buy_acceleration"), 1)
    pc = adv8_num(m.get("price_change_5m"))
    return liq,buy,ratio,va,ba,pc,top10

def adv8_score_components(r):
    liq,buy,ratio,va,ba,pc,top10 = adv8_market_features(r)
    safety = max(0,min(100,int(r.get("safety_score") or 0)))
    liquidity = min(100, int((liq / max(MIN_LIQUIDITY_PREFERRED_USD,1))*70)) if liq else 0
    liquidity = max(0, min(100, liquidity + (20 if liq >= MIN_LIQUIDITY_PREFERRED_USD else 0)))
    momentum = max(0,min(100, int(buy*0.55 + min(ratio,4)*10 + min(va,3)*10 + min(ba,3)*8 + max(min(pc,20),-20)*0.5)))
    holder = max(0,min(100,int(100-top10))) if top10 <= 100 else 0
    smart = 100 if (r.get("smart_money") or {}).get("labels") else 50 if (r.get("smart_money") or {}).get("count") else 20
    risk = 100-safety
    final = int(safety*0.30 + liquidity*0.15 + momentum*0.25 + holder*0.10 + smart*0.10 + (100-risk)*0.10)
    evidence=[]
    if liq >= MIN_LIQUIDITY_PREFERRED_USD: evidence.append("preferred liquidity")
    if buy >= MIN_BUY_SHARE_PCT: evidence.append("buy pressure")
    if ratio >= MIN_BUY_SELL_RATIO: evidence.append("buy/sell confirmation")
    if va >= 1.5: evidence.append("volume acceleration")
    if ba >= 1.5: evidence.append("buyer acceleration")
    if top10 <= TOP10_WARNING_PCT: evidence.append("holder concentration within threshold")
    return max(0,min(100,final)), {"safety":safety,"liquidity":liquidity,"momentum":momentum,"holder":holder,"smart":smart,"risk":risk}, evidence

def adv8_lifecycle(r):
    age = adv8_num(r.get("age_seconds"), 10**9)
    score = int(r.get("score") or 0)
    if age <= 30: return "DISCOVERY"
    if age <= 60 and score >= 75: return "EARLY ALERT"
    if age <= 180 and score >= 80: return "GEM CANDIDATE"
    if age <= 300 and score >= 85: return "EARLY GEM"
    if age <= 7200 and score >= 75: return "MOMENTUM"
    return "MONITOR"

def adv8_anomalies(r):
    m=r.get("market") or {}; a=r.get("acceleration") or {}
    out=[]
    liq=adv8_num(m.get("liquidity_usd")); va=adv8_num(a.get("volume_acceleration"),1); ba=adv8_num(a.get("buy_acceleration"),1)
    ratio=adv8_num(m.get("buy_sell_ratio_5m")); pc=adv8_num(m.get("price_change_5m"))
    if liq and liq < MIN_LIQUIDITY_EARLY_USD: out.append("low liquidity")
    if va >= 3: out.append("extreme volume acceleration")
    if ba >= 3: out.append("extreme buyer acceleration")
    if ratio < 0.8: out.append("sell pressure")
    if pc <= -20: out.append("sharp price decline")
    if pc >= 30 and va < 1.2: out.append("price-volume divergence")
    if r.get("safety_score",100) < 60: out.append("elevated safety risk")
    return out

async def adv8_full_report(mint):
    r = await build_v5_market_report(mint)
    if not r or r.get("price") is None:
        return None
    final, parts, evidence = adv8_score_components(r)
    r["score"] = final
    r["advanced_components"] = parts
    r["advanced_evidence"] = evidence
    r["lifecycle_v8"] = adv8_lifecycle(r)
    r["anomalies"] = adv8_anomalies(r)
    await adv8_save_score(mint,r,parts)
    return r

async def adv8_score_history(mint, limit=10):
    if not DB: return []
    async with DB.acquire() as c:
        rows=await c.fetch("SELECT score,safety_score,momentum_score,liquidity_score,smart_score,holder_score,risk_score,created_at FROM score_history WHERE mint=$1 ORDER BY created_at DESC LIMIT $2",mint,limit)
    return rows

async def adv8_risk_map(r):
    p=r.get("advanced_components") or {}
    risk=[]
    if p.get("safety",100)<70: risk.append("Safety")
    if p.get("liquidity",0)<50: risk.append("Liquidity")
    if p.get("holder",0)<70: risk.append("Holder concentration")
    if p.get("momentum",0)<50: risk.append("Momentum")
    if r.get("anomalies"): risk.extend(r["anomalies"])
    return list(dict.fromkeys(risk)) or ["No major rule-based risk flag"]

async def adv8_wallet_flow(wallet):
    txs=await helius_address_transactions(wallet,100)
    buys=sells=0; native_out=0.0; native_in=0.0; counterparties=set()
    for tx in txs:
        for tr in extract_native_transfers(tx):
            if tr.get("fromUserAccount")==wallet:
                native_out += adv8_num(tr.get("amount"))/1e9
                if tr.get("toUserAccount"): counterparties.add(tr["toUserAccount"])
            elif tr.get("toUserAccount")==wallet:
                native_in += adv8_num(tr.get("amount"))/1e9
                if tr.get("fromUserAccount"): counterparties.add(tr["fromUserAccount"])
        typ=str(tx.get("type") or "").upper()
        if typ=="SWAP":
            acts=json.dumps(tx).lower()
            if "buy" in acts: buys += 1
            if "sell" in acts: sells += 1
    return {"txs":len(txs),"buys":buys,"sells":sells,"native_in":native_in,"native_out":native_out,"counterparties":len(counterparties)}

async def adv8_provider_health():
    providers=[]
    checks=[]
    for name,url in [("HELIUS_RPC",HELIUS_RPC_URL),("ALCHEMY_RPC",ALCHEMY_SOLANA_RPC_URL),("QUICKNODE_RPC",QUICKNODE_RPC_URL)]:
        if not url: continue
        started=time.perf_counter(); ok=False; err=None
        try:
            result=await rpc_call("getHealth",[])
            ok=result is not None
        except Exception as e: err=str(e)
        latency=round((time.perf_counter()-started)*1000,1)
        checks.append((name,ok,latency,err))
    if DB:
        async with DB.acquire() as c:
            for name,ok,latency,err in checks:
                await c.execute("INSERT INTO provider_health(provider,ok,latency_ms,error) VALUES($1,$2,$3,$4) ON CONFLICT(provider) DO UPDATE SET ok=$2,latency_ms=$3,error=$4,checked_at=NOW()",name,ok,latency,err)
    return checks

async def adv8_watchdog_loop():
    while True:
        try:
            candidates=set(WATCH_TOKENS)|set(active_signals.keys())
            if DB:
                async with DB.acquire() as c:
                    rows=await c.fetch("SELECT DISTINCT mint FROM watchlists")
                candidates.update(x["mint"] for x in rows)
            for mint in list(candidates)[:50]:
                if not valid_solana_address(mint): continue
                r=await adv8_full_report(mint)
                if not r: continue
                if r.get("anomalies") and r.get("safety_score",100)<60:
                    await save_intelligence_event(mint,"advanced_risk",r,"; ".join(r["anomalies"]))
        except Exception:
            logging.exception("V8 watchdog failed")
        await asyncio.sleep(max(30,TOKEN_SNAPSHOT_SECONDS))


def adv8_format(r):
    p=r.get("advanced_components") or {}
    risks=r.get("anomalies") or []
    return (f"🧠 <b>ADVANCED INTELLIGENCE</b>\n\n"
            f"🪙 <b>{r.get('symbol','TOKEN')}</b>\n"
            f"🎯 Score: <b>{r.get('score',0)}/100</b>\n"
            f"🛡 Safety: {p.get('safety',0)}/100\n"
            f"💧 Liquidity: {p.get('liquidity',0)}/100\n"
            f"📈 Momentum: {p.get('momentum',0)}/100\n"
            f"👥 Holder: {p.get('holder',0)}/100\n"
            f"🧠 Smart Money: {p.get('smart',0)}/100\n"
            f"🔄 Lifecycle: <b>{r.get('lifecycle_v8','MONITOR')}</b>\n\n"
            f"✅ Evidence: {', '.join(r.get('advanced_evidence') or []) or 'Limited'}\n"
            f"⚠️ Risks: {', '.join(risks) if risks else 'No major rule-based flag'}\n\n"
            "Data is provider-backed and may be incomplete/delayed. Not financial advice.")

@dp.message(Command("report"))
async def adv8_report_cmd(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]):
        await message.answer("Usage: /report TOKEN_ADDRESS"); return
    r=await adv8_full_report(parts[1])
    await message.answer(adv8_format(r),parse_mode="HTML") if r else await message.answer("No provider-backed market data available for this token.")

@dp.message(Command("riskmap"))
async def adv8_riskmap_cmd(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]): await message.answer("Usage: /riskmap TOKEN_ADDRESS"); return
    r=await adv8_full_report(parts[1])
    if not r: await message.answer("Risk map unavailable: provider data missing."); return
    risks=await adv8_risk_map(r)
    await message.answer("🛡 <b>RISK MAP</b>\n\n"+"\n".join(f"• {x}" for x in risks),parse_mode="HTML")

@dp.message(Command("anomaly"))
async def adv8_anomaly_cmd(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]): await message.answer("Usage: /anomaly TOKEN_ADDRESS"); return
    r=await adv8_full_report(parts[1])
    if not r: await message.answer("Anomaly engine needs live provider data."); return
    await message.answer("🔎 <b>ANOMALY CHECK</b>\n\n"+"\n".join(f"• {x}" for x in (r.get("anomalies") or ["No rule-based anomaly detected"])),parse_mode="HTML")

@dp.message(Command("scorehistory"))
async def adv8_history_cmd(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]): await message.answer("Usage: /scorehistory TOKEN_ADDRESS"); return
    rows=await adv8_score_history(parts[1])
    if not rows: await message.answer("No score history stored yet."); return
    text="📈 <b>SCORE HISTORY</b>\n\n"+"\n".join(f"{x['created_at']:%H:%M:%S} | {x['score']}/100 | M{x['momentum_score']} L{x['liquidity_score']} S{x['safety_score']}" for x in rows)
    await message.answer(text,parse_mode="HTML")

@dp.message(Command("smartflow"))
async def adv8_smartflow_cmd(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]): await message.answer("Usage: /smartflow WALLET_ADDRESS"); return
    d=await adv8_wallet_flow(parts[1])
    await message.answer(f"🧠 <b>WALLET FLOW</b>\n\nTransactions: {d['txs']}\nSwap buy mentions: {d['buys']}\nSwap sell mentions: {d['sells']}\nSOL in: {d['native_in']:.3f}\nSOL out: {d['native_out']:.3f}\nCounterparties: {d['counterparties']}",parse_mode="HTML")

@dp.message(Command("health"))
async def adv8_health_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    rows=await adv8_provider_health()
    if not rows: await message.answer("No RPC providers configured."); return
    await message.answer("🩺 <b>PROVIDER HEALTH</b>\n\n"+"\n".join(f"{n}: {'🟢' if ok else '🔴'} {lat}ms" for n,ok,lat,e in rows),parse_mode="HTML")

@dp.message(Command("backtest"))
async def adv8_backtest_cmd(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]): await message.answer("Usage: /backtest TOKEN_ADDRESS"); return
    rows=await adv8_score_history(parts[1],100)
    if len(rows)<2: await message.answer("Not enough stored snapshots for a historical simulation."); return
    first=adv8_num(rows[-1]["score"]); last=adv8_num(rows[0]["score"])
    delta=last-first
    await message.answer(f"🧪 <b>HISTORICAL SCORE REVIEW</b>\n\nSnapshots: {len(rows)}\nFirst score: {first:.0f}\nLatest score: {last:.0f}\nScore change: {delta:+.0f}\n\nThis is a score-history review, not a profit backtest.",parse_mode="HTML")

# ============================================================
# V9 PROFESSIONAL INTELLIGENCE PACK
# ============================================================
V9_ENABLED = os.getenv("V9_ENABLED", "true").lower() in {"1", "true", "yes", "on"}
V9_MAX_COMPARE = max(2, int(os.getenv("V9_MAX_COMPARE", "5")))
V9_TREND_SNAPSHOTS = max(3, int(os.getenv("V9_TREND_SNAPSHOTS", "12")))
V9_MAX_DAILY_RISK_USD = float(os.getenv("V9_MAX_DAILY_RISK_USD", "100"))
V9_ALERT_DEDUP_SECONDS = max(30, int(os.getenv("V9_ALERT_DEDUP_SECONDS", "900")))


def v9_snapshot_values(rows):
    out=[]
    for r in rows:
        def gv(k):
            try: return float(r[k]) if r[k] is not None else None
            except Exception: return None
        out.append({
            "ts": r["ts"], "price": gv("price"), "liquidity": gv("liquidity_usd"),
            "volume": gv("volume_5m"), "buys": int(r["buys_5m"] or 0),
            "sells": int(r["sells_5m"] or 0), "change": gv("price_change_5m")
        })
    return out


async def v9_get_snapshots(mint, limit=24):
    if not DB:
        return []
    async with DB.acquire() as c:
        rows=await c.fetch("""SELECT ts,price,liquidity_usd,volume_5m,buys_5m,sells_5m,price_change_5m
                             FROM token_snapshots WHERE mint=$1 ORDER BY ts DESC LIMIT $2""", mint, limit)
    return v9_snapshot_values(rows)


def v9_trend(rows, key):
    vals=[x[key] for x in reversed(rows) if x.get(key) is not None]
    if len(vals)<2:
        return {"direction":"UNKNOWN","change":None,"samples":len(vals)}
    first,last=vals[0],vals[-1]
    change=((last-first)/abs(first)*100) if first not in (0,None) else None
    direction="RISING" if change is not None and change>2 else "FALLING" if change is not None and change<-2 else "FLAT"
    return {"direction":direction,"change":change,"samples":len(vals)}


def v9_signal_quality(report):
    card=build_intelligence_card(report)
    checks=[]
    checks.append(("Safety", _num((report.get("safety") or {}).get("score")) or 0, 25))
    checks.append(("Momentum", card["momentum"]["score"], 20))
    checks.append(("Liquidity", card["liquidity"].get("score") or 0, 20))
    checks.append(("Smart Money", min(100, int(card["smart_wallets"])*25), 15))
    top10=_num(((report.get("safety") or {}).get("holders") or {}).get("top10_raw"))
    holder=100 if top10 is None else max(0, 100-int(max(0, top10-20)*1.5))
    checks.append(("Holder", holder, 20))
    weighted=sum(score*weight for _,score,weight in checks)/sum(weight for _,_,weight in checks)
    positives=[name for name,score,_ in checks if score>=70]
    weaknesses=[name for name,score,_ in checks if score<50]
    return {"score":round(weighted),"checks":checks,"positives":positives,"weaknesses":weaknesses}


async def v9_portfolio_risk(user_id):
    rows=await live_portfolio(user_id)
    total=sum((x.get("value") or 0) for x in rows)
    pnl=sum((x.get("pnl") or 0) for x in rows)
    largest=max(rows,key=lambda x:x.get("value") or 0,default=None)
    concentration=((largest.get("value") or 0)/total*100) if largest and total else 0
    return {"positions":rows,"total_value":total,"pnl":pnl,"concentration":concentration,
            "risk":"HIGH" if concentration>60 else "MEDIUM" if concentration>35 else "LOW"}


async def v9_token_compare(mints):
    reports=[]
    for mint in mints[:V9_MAX_COMPARE]:
        try:
            r=await enriched_report(mint)
            if r: reports.append((mint,r))
        except Exception:
            logging.exception("compare failed for %s",mint)
    result=[]
    for mint,r in reports:
        q=v9_signal_quality(r)
        result.append({"mint":mint,"symbol":r.get("symbol") or "TOKEN","score":int(r.get("advanced_score",r.get("score",0)) or 0),
                       "quality":q["score"],"liquidity":liquidity_quality(r).get("score"),
                       "momentum":momentum_regime(r).get("score"),"smart":int((r.get("smart_money") or {}).get("count",0) or 0)})
    return result


async def v9_alert_dedup(mint, alert_type, payload=None):
    key=f"{mint}:{alert_type}"
    now=time.time()
    old=token_alert_state.get(key,{}).get("v9_last",0)
    if now-old < V9_ALERT_DEDUP_SECONDS:
        return False
    token_alert_state[key]={"v9_last":now}
    if DB:
        try:
            async with DB.acquire() as c:
                await c.execute("INSERT INTO token_alerts(mint,alert_type,score,payload) VALUES($1,$2,$3,$4)",
                                mint,alert_type,int((payload or {}).get("score") or 0),json.dumps(payload or {}))
        except Exception:
            logging.exception("alert dedup persistence failed")
    return True


@dp.message(Command("trend"))
async def v9_trend_command(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]):
        await message.answer("Usage: /trend TOKEN_ADDRESS"); return
    rows=await v9_get_snapshots(parts[1],V9_TREND_SNAPSHOTS)
    if len(rows)<2:
        await message.answer("Not enough stored snapshots for a trend report yet."); return
    pt=v9_trend(rows,"price"); lt=v9_trend(rows,"liquidity"); vt=v9_trend(rows,"volume")
    await message.answer(
        "📊 <b>TOKEN TREND</b>\n\n"
        f"Price: <b>{pt['direction']}</b> ({pct(pt['change']) if pt['change'] is not None else 'N/A'})\n"
        f"Liquidity: <b>{lt['direction']}</b> ({pct(lt['change']) if lt['change'] is not None else 'N/A'})\n"
        f"Volume: <b>{vt['direction']}</b> ({pct(vt['change']) if vt['change'] is not None else 'N/A'})\n"
        f"Snapshots: {len(rows)}\n\nData is historical provider-backed data; not a forecast.",parse_mode="HTML")


@dp.message(Command("signalquality"))
async def v9_signalquality_command(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]):
        await message.answer("Usage: /signalquality TOKEN_ADDRESS"); return
    r=await enriched_report(parts[1])
    if not r:
        await message.answer("Signal quality unavailable: provider data missing."); return
    q=v9_signal_quality(r)
    await message.answer("🧪 <b>SIGNAL QUALITY</b>\n\n"
        f"Quality: <b>{q['score']}/100</b>\n"
        f"✅ Strong checks: {', '.join(q['positives']) or 'None'}\n"
        f"⚠️ Weak checks: {', '.join(q['weaknesses']) or 'None'}\n\n"
        "This is a rule-based data quality score, not a profit guarantee.",parse_mode="HTML")


@dp.message(Command("compare"))
async def v9_compare_command(message: Message):
    parts=(message.text or "").split()[1:]
    if len(parts)<2 or len(parts)>V9_MAX_COMPARE or any(not valid_solana_address(x) for x in parts):
        await message.answer(f"Usage: /compare TOKEN1 TOKEN2 [TOKEN3...], max {V9_MAX_COMPARE} tokens."); return
    data=await v9_token_compare(parts)
    if not data:
        await message.answer("No provider-backed reports available."); return
    lines=["📋 <b>TOKEN METRICS COMPARISON</b>",""]
    for i,x in enumerate(data,1):
        lines.append(f"{i}. <b>{x['symbol']}</b> | Score {x['score']}/100 | Quality {x['quality']}/100 | Momentum {x['momentum']}/100 | Liquidity {x['liquidity'] if x['liquidity'] is not None else 'N/A'} | Smart {x['smart']}")
    lines.append("\nMetrics are shown side-by-side without declaring a trading winner.")
    await message.answer("\n".join(lines),parse_mode="HTML")


@dp.message(Command("portfolio_risk"))
async def v9_portfolio_risk_command(message: Message):
    x=await v9_portfolio_risk(message.from_user.id)
    if not x["positions"]:
        await message.answer("Portfolio is empty."); return
    lines=["🛡 <b>PORTFOLIO RISK</b>","",f"Value: <b>${x['total_value']:.2f}</b>",f"Unrealized P/L: <b>${x['pnl']:+.2f}</b>",f"Largest position: <b>{x['concentration']:.1f}%</b>",f"Concentration level: <b>{x['risk']}</b>",""]
    for p in x["positions"][:10]: lines.append(f"• {p['symbol']}: {p['pnl_pct']:+.2f}%" if p.get("pnl_pct") is not None else f"• {p['symbol']}: price unavailable")
    await message.answer("\n".join(lines),parse_mode="HTML")


@dp.message(Command("walletgraph"))
async def v9_walletgraph_command(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]):
        await message.answer("Usage: /walletgraph WALLET_ADDRESS"); return
    d=await wallet_dna(parts[1])
    if not d.get("parsed"):
        await message.answer("Wallet graph unavailable: parsed provider data missing."); return
    await message.answer("🕸 <b>WALLET GRAPH SUMMARY</b>\n\n"
        f"Wallet: <code>{d['wallet']}</code>\nTransactions: <b>{d['transactions']}</b>\n"
        f"Unique tokens: <b>{d['unique_tokens']}</b>\nCounterparties: <b>{d['counterparties']}</b>\n"
        f"SOL in: <b>{d['sol_in']:.3f}</b>\nSOL out: <b>{d['sol_out']:.3f}</b>\nNet flow: <b>{d['net_sol']:+.3f} SOL</b>\n\n"
        "This is a transaction-graph summary, not identity attribution.",parse_mode="HTML")


@dp.message(Command("liquiditytrend"))
async def v9_liquiditytrend_command(message: Message):
    parts=(message.text or "").split()
    if len(parts)<2 or not valid_solana_address(parts[1]):
        await message.answer("Usage: /liquiditytrend TOKEN_ADDRESS"); return
    rows=await v9_get_snapshots(parts[1],V9_TREND_SNAPSHOTS)
    t=v9_trend(rows,"liquidity") if rows else {"direction":"UNKNOWN","change":None,"samples":0}
    await message.answer("💧 <b>LIQUIDITY TREND</b>\n\n"
        f"Direction: <b>{t['direction']}</b>\nChange across stored snapshots: <b>{pct(t['change']) if t['change'] is not None else 'N/A'}</b>\n"
        f"Samples: <b>{t['samples']}</b>\n\nA trend is descriptive and does not predict future liquidity.",parse_mode="HTML")


@dp.message(Command("riskbudget"))
async def v9_riskbudget_command(message: Message):
    if not DB:
        await message.answer("Risk budget requires PostgreSQL (DATABASE_URL)."); return
    async with DB.acquire() as c:
        row=await c.fetchrow("SELECT max_position_usd,max_open_trades,max_daily_loss_usd FROM user_risk_limits WHERE user_id=$1",message.from_user.id)
    if not row:
        await message.answer("No custom risk budget configured. Default limits are used by the paper-trading layer."); return
    await message.answer("⚙️ <b>RISK BUDGET</b>\n\n"
        f"Max position: <b>${row['max_position_usd']:.2f}</b>\nMax open trades: <b>{row['max_open_trades']}</b>\n"
        f"Max daily loss: <b>${row['max_daily_loss_usd']:.2f}</b>",parse_mode="HTML")


@dp.message(Command("healthcheck"))
async def v9_healthcheck_command(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    rows=await adv8_provider_health()
    db_ok=DB is not None
    await message.answer("🩺 <b>SYSTEM HEALTH</b>\n\n"
        f"Database: {'🟢' if db_ok else '🔴'}\n"
        f"RPC configured: {'🟢' if RPC_URLS else '🔴'}\n"
        f"Market data: {'🟢' if MARKET_DATA_ENABLED else '🔴'}\n"
        + ("\n".join(f"{n}: {'🟢' if ok else '🔴'} {lat}ms" for n,ok,lat,e in rows) if rows else "No provider checks available."),parse_mode="HTML")


# ============================================================
# V10 CLEAN UI + USER TOOLS
# ============================================================


# ============================================================
# V10 USER-UTILITY / DATA QUALITY FEATURES
# ============================================================

def v10_fmt_price(value):
    try:
        x=float(value)
    except (TypeError, ValueError):
        return "N/A"
    if x == 0:
        return "0"
    if abs(x) >= 1:
        return f"${x:,.4f}" if x < 100 else f"${x:,.2f}"
    return f"${x:.8f}".rstrip("0").rstrip(".")


def v10_report_freshness(report):
    created = report.get("created_at") if isinstance(report, dict) else None
    if not created:
        return "Unknown"
    age = max(0, int(time.time() - float(created)))
    return f"{age}s ago"


@dp.message(Command("levels"))
async def v10_levels_command(message: Message):
    parts = message.text.split()
    if len(parts) != 2 or not valid_solana_address(parts[1]):
        return
    if not user_scan_allowed(message.from_user.id):
        await message.answer("Please wait a few seconds before scanning again.")
        return
    r = await cached_enriched_report(parts[1])
    if not r:
        await message.answer("No current market data is available for this token.")
        return
    price = r.get("price")
    if price is None or float(price) <= 0:
        await message.answer("Current price is unavailable, so levels cannot be calculated.")
        return
    price = float(price)
    t1 = price * (1 + TP1_PCT / 100)
    t2 = price * (1 + TP2_PCT / 100)
    t3 = price * (1 + TP3_PCT / 100)
    sl = price * (1 - SL_PCT / 100)
    await message.answer(
        f"📐 <b>REFERENCE LEVELS</b>\n\n"
        f"Token: <b>{r.get('symbol','TOKEN')}</b>\n"
        f"Current: <b>{v10_fmt_price(price)}</b>\n\n"
        f"TP1 (+{TP1_PCT:g}%): <b>{v10_fmt_price(t1)}</b>\n"
        f"TP2 (+{TP2_PCT:g}%): <b>{v10_fmt_price(t2)}</b>\n"
        f"TP3 (+{TP3_PCT:g}%): <b>{v10_fmt_price(t3)}</b>\n"
        f"Reference SL (-{SL_PCT:g}%): <b>{v10_fmt_price(sl)}</b>\n\n"
        f"These are configured reference levels, not a prediction or guaranteed outcome.",
        parse_mode="HTML"
    )


@dp.message(Command("watchscan"))
async def v10_watchscan_command(message: Message):
    items = await user_watchlist(message.from_user.id)
    if not items:
        await message.answer("Your watchlist is empty. Use /watch TOKEN to add one.")
        return
    # Keep this deliberately small to protect provider limits.
    limit = 10 if await is_premium(message.from_user.id) else 5
    rows = []
    for mint in items[:limit]:
        try:
            r = await cached_enriched_report(mint)
            if not r:
                rows.append("• <code>" + mint[:8] + "...</code> — data unavailable")
                continue
            rows.append(
                f"• <b>{r.get('symbol','TOKEN')}</b> "
                f"Score <b>{int(r.get('score') or 0)}/100</b> · "
                f"Safety <b>{int(r.get('safety_score') or 0)}/100</b>"
            )
        except Exception:
            rows.append("• <code>" + mint[:8] + "...</code> — scan failed")
    extra = "" if len(items) <= limit else f"\n\nShowing {limit} of {len(items)} tokens to control API usage."
    await message.answer("📋 <b>WATCHLIST SNAPSHOT</b>\n\n" + "\n".join(rows) + extra, parse_mode="HTML")


@dp.message(Command("unwatch"))
async def v10_unwatch_command(message: Message):
    parts = message.text.split()
    if len(parts) != 2 or not valid_solana_address(parts[1]):
        return
    await remove_watch(message.from_user.id, parts[1])
    await message.answer("Removed from your watchlist.")


@dp.message(Command("datahealth"))
async def v10_datahealth_command(message: Message):
    parts = message.text.split()
    if len(parts) != 2 or not valid_solana_address(parts[1]):
        return
    if not user_scan_allowed(message.from_user.id):
        await message.answer("Please wait a few seconds before scanning again.")
        return
    r = await cached_enriched_report(parts[1])
    if not r:
        await message.answer("No report is currently available.")
        return
    m = r.get("market") or {}
    fields = {
        "Price": m.get("price") if m else r.get("price"),
        "Liquidity": m.get("liquidity_usd"),
        "5m Volume": m.get("volume_5m"),
        "5m Buy Share": m.get("buy_share_5m"),
        "5m Buy/Sell": m.get("buy_sell_ratio_5m"),
        "Token Age": m.get("age_seconds"),
    }
    available = sum(v is not None for v in fields.values())
    missing = [k for k, v in fields.items() if v is None]
    source = m.get("source") if m else "On-chain fallback"
    status = "GOOD" if available >= 5 else "PARTIAL" if available >= 3 else "LIMITED"
    text = (
        f"🩺 <b>DATA HEALTH</b>\n\n"
        f"Token: <b>{r.get('symbol','TOKEN')}</b>\n"
        f"Status: <b>{status}</b>\n"
        f"Source: <b>{source or 'Unknown'}</b>\n"
        f"Report age: <b>{v10_report_freshness(r)}</b>\n"
        f"Available fields: <b>{available}/{len(fields)}</b>"
    )
    if missing:
        text += "\nMissing: " + ", ".join(missing)
    text += "\n\nMissing fields mean the configured provider did not supply that metric."
    await message.answer(text, parse_mode="HTML")


@dp.message(Command("clearcache"))
async def v10_clearcache_command(message: Message):
    if not is_admin_user(message.from_user.id):
        return
    scan_report_cache.clear()
    market_cache.clear()
    last_market_refresh.clear()
    await message.answer("Runtime market/report cache cleared.")


@dp.message(Command("menu"))
async def clean_menu_command(message: Message):
    await message.answer(
        "🚀 <b>Solana Meme Intelligence</b>\n\n"
        "Send a token address for a scan, or choose a tool below.",
        reply_markup=build_start_keyboard(message.from_user.id),
        parse_mode="HTML",
    )


@dp.message(Command("status"))
async def compact_status_command(message: Message):
    parts = (message.text or "").split()
    if len(parts) < 2 or not valid_solana_address(parts[1]):
        await message.answer("Usage: /status TOKEN_ADDRESS")
        return
    r = await cached_enriched_report(parts[1])
    if not r:
        await message.answer("Live provider data is unavailable for this token.")
        return
    m = r.get("market") or {}
    adv = r.get("advanced_score", r.get("score", 0))
    safety = r.get("safety_score", 0)
    liq = money(m.get("liquidity_usd")) if m.get("liquidity_usd") is not None else "N/A"
    ratio = m.get("buy_sell_ratio_5m")
    ratio_text = f"{float(ratio):.2f}x" if ratio is not None else "N/A"
    await message.answer(
        "📊 <b>Token Status</b>\n\n"
        f"<b>{r.get('symbol','TOKEN')}</b>\n"
        f"Intelligence: <b>{adv}/100</b>\n"
        f"Safety: <b>{safety}/100</b>\n"
        f"Liquidity: <b>{liq}</b>\n"
        f"Buy/Sell: <b>{ratio_text}</b>\n"
        f"Class: <b>{r.get('class','N/A')}</b>\n\n"
        "Data is provider-backed and may be delayed or incomplete.",
        parse_mode="HTML",
    )


@dp.message(Command("quick"))
async def quick_command(message: Message):
    """Compact scan for users who want the essential decision-support data only."""
    parts = (message.text or "").split()
    if len(parts) != 2 or not valid_solana_address(parts[1]):
        await message.answer("Usage: /quick TOKEN_ADDRESS")
        return
    if not user_scan_allowed(message.from_user.id):
        return
    r = await cached_enriched_report(parts[1])
    if not r:
        await message.answer("Live provider data is unavailable for this token.")
        return
    m = r.get("market") or {}
    score = r.get("advanced_score", r.get("score", 0))
    safety = r.get("safety_score", 0)
    liq = money(m.get("liquidity_usd")) if m.get("liquidity_usd") is not None else "N/A"
    price_v = m.get("price")
    price_text = price(price_v) if price_v is not None else "N/A"
    ratio = m.get("buy_sell_ratio_5m")
    ratio_text = f"{float(ratio):.2f}x" if ratio is not None else "N/A"
    await message.answer(
        "⚡ <b>QUICK SCAN</b>\n\n"
        f"<b>{r.get('symbol','TOKEN')}</b>\n"
        f"Price: <b>{price_text}</b>\n"
        f"Intelligence: <b>{score}/100</b>\n"
        f"Safety: <b>{safety}/100</b>\n"
        f"Liquidity: <b>{liq}</b>\n"
        f"Buy/Sell: <b>{ratio_text}</b>\n"
        f"Class: <b>{r.get('class','N/A')}</b>",
        parse_mode="HTML"
    )


@dp.message(Command("quiet"))
async def quiet_command(message: Message):
    # The premium signal channel is global, so this preference only controls
    # future private notification features. It is stored now without adding
    # noisy confirmation messages to the chat.
    if not DB:
        await message.answer("PostgreSQL is required for user notification preferences.")
        return
    async with DB.acquire() as c:
        await c.execute("""
            CREATE TABLE IF NOT EXISTS user_preferences(
                user_id BIGINT PRIMARY KEY,
                quiet_mode BOOLEAN NOT NULL DEFAULT FALSE,
                updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
        """)
        row = await c.fetchrow("SELECT quiet_mode FROM user_preferences WHERE user_id=$1", message.from_user.id)
        current = bool(row["quiet_mode"]) if row else False
        await c.execute("""
            INSERT INTO user_preferences(user_id,quiet_mode,updated_at)
            VALUES($1,$2,NOW())
            ON CONFLICT(user_id) DO UPDATE SET quiet_mode=$2,updated_at=NOW()
        """, message.from_user.id, not current)
    await message.answer("Quiet mode: <b>ON</b>" if not current else "Quiet mode: <b>OFF</b>", parse_mode="HTML")


# ============================================================
# EXTRA USER UTILITIES
# ============================================================

@dp.message(Command("alerts"))
async def alerts_command(message: Message):
    """Compact personal alert status; no noisy explanations."""
    if not DB:
        return
    async with DB.acquire() as c:
        row = await c.fetchrow("""SELECT new_launch,smart_money,whale,rug,volume_acceleration,price_move
                                 FROM alert_settings WHERE user_id=$1""", message.from_user.id)
    if not row:
        await message.answer("Alerts are enabled by default.")
        return
    enabled = [k.replace('_',' ').title() for k,v in dict(row).items() if v]
    await message.answer("<b>ALERTS</b>\n" + ("\n".join(f"• {x}" for x in enabled) if enabled else "All alerts are off."), parse_mode="HTML")


@dp.message(Command("limits"))
async def limits_command(message: Message):
    await message.answer(
        "<b>RUNTIME LIMITS</b>\n\n"
        f"API timeout: <b>{API_TIMEOUT_SECONDS}s</b>\n"
        f"API retries: <b>{API_MAX_RETRIES}</b>\n"
        f"Concurrent requests: <b>{MAX_CONCURRENT_SCANS}</b>\n"
        f"Scan cache: <b>{'ON' if CACHE_ENABLED else 'OFF'}</b>\n"
        f"Scan cooldown: <b>{USER_SCAN_RATE_SECONDS}s</b>",
        f"Helius daily cap: <b>{HELIUS_DAILY_CREDIT_CAP:,.0f} credits</b>",
        f"Helius monthly cap: <b>{HELIUS_MONTHLY_CREDIT_CAP:,.0f} credits</b>",
        parse_mode="HTML"
    )



# ============================================================
# V9 USER INTELLIGENCE COMMANDS
# ============================================================

def _fmt_num(value, digits=2):
    if value is None:
        return "N/A"
    try:
        return f"{float(value):,.{digits}f}"
    except Exception:
        return "N/A"


def _fmt_usd(value):
    if value is None:
        return "N/A"
    try:
        v = float(value)
        if abs(v) >= 1_000_000:
            return f"${v/1_000_000:.2f}M"
        if abs(v) >= 1_000:
            return f"${v/1_000:.1f}K"
        return f"${v:,.2f}"
    except Exception:
        return "N/A"


@dp.message(Command("watchrank"))
async def watchrank_command(message: Message):
    """Compact score-sorted view of the user's watchlist."""
    if not DB:
        return
    async with DB.acquire() as c:
        rows = await c.fetch(
            "SELECT mint FROM watchlists WHERE user_id=$1 ORDER BY added_at DESC LIMIT $2",
            message.from_user.id, min(MAX_USER_WATCHLIST, 15)
        )
    if not rows:
        await message.answer("Your watchlist is empty. Add a token first.")
        return
    results = []
    for row in rows:
        try:
            report = await build_v5_market_report(row["mint"])
            results.append((float(report.get("score") or 0), report))
        except Exception:
            continue
    results.sort(key=lambda x: x[0], reverse=True)
    if not results:
        await message.answer("No fresh provider data is available for your watchlist.")
        return
    lines = ["<b>WATCHLIST OVERVIEW</b>", ""]
    for score, report in results[:10]:
        symbol = report.get("symbol") or report.get("base_symbol") or "TOKEN"
        safety = report.get("safety_score")
        lifecycle = report.get("lifecycle") or "N/A"
        lines.append(f"<b>{symbol}</b> • Score <b>{int(score)}</b> • Safety {safety if safety is not None else 'N/A'} • {lifecycle}")
    await message.answer("\n".join(lines), parse_mode="HTML")


@dp.message(Command("pulse"))
async def pulse_command(message: Message):
    """Snapshot of tracked tokens; does not claim to predict market direction."""
    candidates = list(set(WATCH_TOKENS) | set(active_signals.keys()))[:8]
    if DB:
        try:
            async with DB.acquire() as c:
                rows = await c.fetch("SELECT DISTINCT mint FROM watchlists WHERE user_id=$1 LIMIT 5", message.from_user.id)
            candidates.extend(r["mint"] for r in rows)
        except Exception:
            pass
    candidates = list(dict.fromkeys(candidates))[:10]
    if not candidates:
        await message.answer("No tracked tokens are available for a pulse yet.")
        return
    valid, scores, liqs, volumes = 0, [], [], []
    for mint in candidates:
        try:
            r = await build_v5_market_report(mint)
            if r.get("price") is None and r.get("score") is None:
                continue
            valid += 1
            if r.get("score") is not None: scores.append(float(r["score"]))
            if r.get("liquidity_usd") is not None: liqs.append(float(r["liquidity_usd"]))
            if r.get("volume_5m") is not None: volumes.append(float(r["volume_5m"]))
        except Exception:
            continue
    if not valid:
        await message.answer("No fresh provider data is available right now.")
        return
    avg = sum(scores) / len(scores) if scores else None
    liquidity = sum(liqs) if liqs else None
    volume = sum(volumes) if volumes else None
    await message.answer(
        "<b>TRACKED MARKET PULSE</b>\n\n"
        f"Tracked tokens: <b>{valid}</b>\n"
        f"Average scanner score: <b>{_fmt_num(avg, 1)}</b>\n"
        f"Combined liquidity: <b>{_fmt_usd(liquidity)}</b>\n"
        f"Combined 5m volume: <b>{_fmt_usd(volume)}</b>\n\n"
        "Snapshot of tracked tokens only; not a market-direction prediction.",
        parse_mode="HTML"
    )


@dp.message(Command("commands2"))
async def commands2_command(message: Message):
    await message.answer(
        "<b>INTELLIGENCE COMMANDS</b>\n\n"
        "/quick TOKEN — fast scan\n"
        "/status TOKEN — compact status\n"
        "/report TOKEN — full report\n"
        "/explain TOKEN — score breakdown\n"
        "/datahealth TOKEN — data availability\n\n"
        "/watchrank — watchlist overview\n"
        "/pulse — tracked market pulse\n"
        "/watchscan — scan watchlist\n"
        "/unwatch TOKEN — remove token\n"
        "/levels TOKEN — reference levels\n"
        "/riskmap TOKEN — risk map\n"
        "/scorehistory TOKEN — score history\n"
        "/smartflow WALLET — wallet flow\n"
        "/portfolio_risk — portfolio risk\n"
        "/limits — runtime limits",
        parse_mode="HTML"
    )

# ============================================================
# FINAL RUNTIME SAFETY / OPERATIONS
# ============================================================

async def runtime_status():
    open_count = sum(1 for u in RPC_URLS if _provider_open_until.get(u, 0) > time.monotonic())
    return {
        "rpc_providers": len(RPC_URLS),
        "rpc_circuit_open": open_count,
        "scan_cache": len(scan_cache) if "scan_cache" in globals() else 0,
        "active_signals": len(active_signals),
        "watch_tokens": len(WATCH_TOKENS),
        "max_concurrent_scans": MAX_CONCURRENT_SCANS,
    }


@dp.message(Command("runtime"))
async def runtime_command(message: Message):
    if not is_admin_user(message.from_user.id):
        return
    st = await runtime_status()
    await message.answer(
        "<b>RUNTIME STATUS</b>\n\n"
        f"RPC providers: <b>{st['rpc_providers']}</b>\n"
        f"Temporarily paused: <b>{st['rpc_circuit_open']}</b>\n"
        f"Cache entries: <b>{st['scan_cache']}</b>\n"
        f"Active signals: <b>{st['active_signals']}</b>\n"
        f"Watch tokens: <b>{st['watch_tokens']}</b>\n"
        f"Concurrency: <b>{st['max_concurrent_scans']}</b>",
        parse_mode="HTML"
    )


# ============================================================
# V9 PRODUCTION / USER INTELLIGENCE PACK
# ============================================================
V9_CACHE_SECONDS = max(5, int(os.getenv("V9_CACHE_SECONDS", "20")))
V9_CLEANUP_HOURS = max(6, int(os.getenv("V9_CLEANUP_HOURS", "24")))
V9_DEFAULT_RISK = os.getenv("DEFAULT_RISK_PROFILE", "normal").lower()
V9_CACHE = {}

async def v9_db_init():
    if not DB:
        return
    async with DB.acquire() as c:
        await c.execute("""
        CREATE TABLE IF NOT EXISTS user_risk_profiles(
            user_id BIGINT PRIMARY KEY,
            profile TEXT NOT NULL DEFAULT 'normal',
            max_position_usd DOUBLE PRECISION NOT NULL DEFAULT 100,
            max_open_trades INTEGER NOT NULL DEFAULT 5,
            daily_loss_limit_usd DOUBLE PRECISION NOT NULL DEFAULT 50,
            updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS signal_dedupe(
            mint TEXT PRIMARY KEY,
            signal_key TEXT NOT NULL,
            score INTEGER NOT NULL DEFAULT 0,
            created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE TABLE IF NOT EXISTS system_events(
            id BIGSERIAL PRIMARY KEY,
            event_type TEXT NOT NULL,
            message TEXT,
            created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
        );
        CREATE INDEX IF NOT EXISTS idx_system_events_time ON system_events(created_at DESC);
        """)

async def v9_setting(key, default=""):
    if not DB:
        return default
    async with DB.acquire() as c:
        row = await c.fetchrow("SELECT value FROM system_settings WHERE key=$1", key)
    return row["value"] if row else default

async def v9_set_setting(key, value):
    if not DB:
        return False
    async with DB.acquire() as c:
        await c.execute("""INSERT INTO system_settings(key,value) VALUES($1,$2)
        ON CONFLICT(key) DO UPDATE SET value=$2,updated_at=NOW()""", key, str(value))
    return True

async def v9_is_paused():
    return (await v9_setting("emergency_pause", "0")) == "1"

async def v9_is_maintenance():
    return (await v9_setting("maintenance_mode", "0")) == "1"

async def v9_cache_report(mint):
    now=time.time()
    item=V9_CACHE.get(mint)
    if item and now-item[0] < V9_CACHE_SECONDS:
        return item[1]
    r=await build_v5_market_report(mint)
    if r:
        V9_CACHE[mint]=(now,r)
    return r

async def v9_risk_profile(user_id):
    if not DB:
        return {"profile":V9_DEFAULT_RISK,"max_position_usd":100.0,"max_open_trades":5,"daily_loss_limit_usd":50.0}
    async with DB.acquire() as c:
        row=await c.fetchrow("SELECT profile,max_position_usd,max_open_trades,daily_loss_limit_usd FROM user_risk_profiles WHERE user_id=$1",user_id)
        if row:
            return dict(row)
        await c.execute("INSERT INTO user_risk_profiles(user_id,profile) VALUES($1,$2) ON CONFLICT DO NOTHING",user_id,V9_DEFAULT_RISK)
    return {"profile":V9_DEFAULT_RISK,"max_position_usd":100.0,"max_open_trades":5,"daily_loss_limit_usd":50.0}

async def v9_set_risk_profile(user_id, profile):
    presets={
        "conservative":(50,3,25),
        "normal":(100,5,50),
        "aggressive":(250,10,100),
    }
    if profile not in presets or not DB:
        return False
    pos,trades,loss=presets[profile]
    async with DB.acquire() as c:
        await c.execute("""INSERT INTO user_risk_profiles(user_id,profile,max_position_usd,max_open_trades,daily_loss_limit_usd)
        VALUES($1,$2,$3,$4,$5) ON CONFLICT(user_id) DO UPDATE SET profile=$2,max_position_usd=$3,max_open_trades=$4,daily_loss_limit_usd=$5,updated_at=NOW()""",user_id,profile,pos,trades,loss)
    return True

def v9_entry_quality(r):
    m=r.get("market") or {}; a=r.get("acceleration") or {}
    safety=float(r.get("safety_score") or 0)
    liq=float(m.get("liquidity_usd") or 0)
    buy=float(m.get("buy_share_5m") or 0)
    ratio=float(m.get("buy_sell_ratio_5m") or 0)
    va=float(a.get("volume_acceleration") or 1)
    ba=float(a.get("buy_acceleration") or 1)
    score=min(100,max(0, safety*.35 + min(liq/max(MIN_LIQUIDITY_PREFERRED_USD,1),2)*15 + min(buy,100)*.15 + min(ratio,3)*5 + min(va,3)*5 + min(ba,3)*5))
    reasons=[]
    if safety>=75: reasons.append("safety support")
    if liq>=MIN_LIQUIDITY_PREFERRED_USD: reasons.append("preferred liquidity")
    if buy>=MIN_BUY_SHARE_PCT: reasons.append("buy pressure")
    if ratio>=MIN_BUY_SELL_RATIO: reasons.append("buy/sell confirmation")
    if va>=1.5: reasons.append("volume acceleration")
    if ba>=1.5: reasons.append("buyer acceleration")
    return int(score),reasons

def v9_lifecycle(r):
    age=float(r.get("age_seconds") or 999999999); score=float(r.get("score") or r.get("advanced_score") or 0)
    if age<=30: return "DISCOVERY"
    if age<=60 and score>=75: return "EARLY ALERT"
    if age<=180 and score>=80: return "GEM CANDIDATE"
    if age<=300 and score>=85: return "EARLY GEM"
    if age<=7200: return "MOMENTUM / MATURING"
    return "MATURE / MONITOR"

async def v9_compare(mints):
    out=[]
    for mint in mints:
        r=await v9_cache_report(mint)
        if not r: continue
        eq,reasons=v9_entry_quality(r)
        out.append({"mint":mint,"symbol":r.get("symbol","TOKEN"),"safety":int(r.get("safety_score") or 0),"quality":eq,"liquidity":float((r.get("market") or {}).get("liquidity_usd") or 0),"lifecycle":v9_lifecycle(r),"reasons":reasons})
    return out

async def v9_duplicate_signal(mint, signal_key, score):
    if not DB: return False
    async with DB.acquire() as c:
        row=await c.fetchrow("SELECT signal_key,score,created_at FROM signal_dedupe WHERE mint=$1",mint)
        if row and row["signal_key"]==signal_key and (datetime.now(timezone.utc)-row["created_at"]).total_seconds()<900:
            return True
        await c.execute("""INSERT INTO signal_dedupe(mint,signal_key,score) VALUES($1,$2,$3)
        ON CONFLICT(mint) DO UPDATE SET signal_key=$2,score=$3,created_at=NOW()""",mint,signal_key,int(score))
    return False

async def v9_admin_stats():
    if not DB: return "PostgreSQL is not configured."
    async with DB.acquire() as c:
        users=await c.fetchval("SELECT COUNT(*) FROM referrals")
        premium=await c.fetchval("SELECT COUNT(*) FROM members WHERE expires_at>NOW()")
        trials=await c.fetchval("SELECT COUNT(*) FROM trial_users WHERE expires_at>NOW()")
        scans=await c.fetchval("SELECT COUNT(*) FROM intelligence_events WHERE created_at>NOW()-INTERVAL '24 hours'")
        alerts=await c.fetchval("SELECT COUNT(*) FROM token_alerts WHERE created_at>NOW()-INTERVAL '24 hours'")
        open_paper=await c.fetchval("SELECT COUNT(*) FROM paper_trades WHERE status='OPEN'")
    return (f"👑 <b>ADMIN ANALYTICS</b>\n\n"
            f"Premium active: <b>{premium}</b>\nTrial active: <b>{trials}</b>\n"
            f"Tracked users/referrals: <b>{users}</b>\n24h intelligence events: <b>{scans}</b>\n"
            f"24h alerts: <b>{alerts}</b>\nOpen paper trades: <b>{open_paper}</b>\n\n"
            f"Emergency pause: <b>{'ON' if await v9_is_paused() else 'OFF'}</b>\n"
            f"Maintenance: <b>{'ON' if await v9_is_maintenance() else 'OFF'}</b>")

async def v9_cleanup_loop():
    while True:
        try:
            if DB:
                async with DB.acquire() as c:
                    await c.execute("DELETE FROM token_alerts WHERE created_at<NOW()-INTERVAL '30 days'")
                    await c.execute("DELETE FROM intelligence_events WHERE created_at<NOW()-INTERVAL '30 days'")
                    await c.execute("DELETE FROM token_snapshots WHERE ts<NOW()-INTERVAL '14 days'")
                    await c.execute("DELETE FROM score_history WHERE created_at<NOW()-INTERVAL '30 days'")
                    await c.execute("DELETE FROM system_events WHERE created_at<NOW()-INTERVAL '30 days'")
        except Exception:
            logging.exception("V9 cleanup failed")
        await asyncio.sleep(V9_CLEANUP_HOURS*3600)

@dp.message(Command("compare"))
async def v9_compare_cmd(message: Message):
    parts=(message.text or "").split()[1:4]
    if len(parts)<2 or any(not valid_solana_address(x) for x in parts):
        await message.answer("Use <code>/compare TOKEN1 TOKEN2 [TOKEN3]</code>",parse_mode="HTML"); return
    rows=await v9_compare(parts)
    if not rows:
        await message.answer("No provider-backed data available."); return
    lines=["🔬 <b>TOKEN COMPARISON</b>",""]
    for x in rows:
        lines.append(f"🪙 <b>{x['symbol']}</b>\nSafety: {x['safety']}/100 | Entry quality: {x['quality']}/100\nLiquidity: {money(x['liquidity'])} | Stage: <b>{x['lifecycle']}</b>\nEvidence: {', '.join(x['reasons']) or 'Limited'}\n")
    await message.answer("\n".join(lines)+"\n⚠️ Comparison is informational, not a recommendation.",parse_mode="HTML")

@dp.message(Command("quality"))
async def v9_quality_cmd(message: Message):
    parts=(message.text or "").split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/quality TOKEN_MINT</code>",parse_mode="HTML"); return
    r=await v9_cache_report(parts[1])
    if not r: await message.answer("Provider-backed market data unavailable."); return
    q,reasons=v9_entry_quality(r)
    await message.answer(f"🎯 <b>ENTRY QUALITY</b>\n\nToken: <b>{r.get('symbol','TOKEN')}</b>\nQuality: <b>{q}/100</b>\nLifecycle: <b>{v9_lifecycle(r)}</b>\n\nEvidence: {', '.join(reasons) or 'Limited evidence'}\n\n⚠️ This score is a rule-based data summary, not a profit guarantee.",parse_mode="HTML")

@dp.message(Command("profile"))
async def v9_profile_cmd(message: Message):
    parts=(message.text or "").split()
    if len(parts)==2 and parts[1].lower() in {"conservative","normal","aggressive"}:
        if await v9_set_risk_profile(message.from_user.id,parts[1].lower()):
            await message.answer(f"✅ Risk profile set to <b>{parts[1].title()}</b>.",parse_mode="HTML"); return
    p=await v9_risk_profile(message.from_user.id)
    await message.answer(f"🛡 <b>RISK PROFILE</b>\n\nProfile: <b>{p['profile'].title()}</b>\nMax position: <b>${p['max_position_usd']:.0f}</b>\nMax open paper trades: <b>{p['max_open_trades']}</b>\nDaily loss limit: <b>${p['daily_loss_limit_usd']:.0f}</b>\n\nSet: <code>/profile conservative</code>, <code>/profile normal</code>, or <code>/profile aggressive</code>",parse_mode="HTML")

@dp.message(Command("lifecycle"))
async def v9_lifecycle_cmd(message: Message):
    parts=(message.text or "").split()
    if len(parts)!=2 or not valid_solana_address(parts[1]):
        await message.answer("Use <code>/lifecycle TOKEN_MINT</code>",parse_mode="HTML"); return
    r=await v9_cache_report(parts[1])
    await message.answer(f"🔄 <b>TOKEN LIFECYCLE</b>\n\n{r.get('symbol','TOKEN') if r else 'TOKEN'}: <b>{v9_lifecycle(r) if r else 'DATA UNAVAILABLE'}</b>",parse_mode="HTML")

@dp.message(Command("system"))
async def v9_system_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return
    await message.answer(await v9_admin_stats(),parse_mode="HTML")

@dp.message(Command("pause"))
async def v9_pause_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    parts=(message.text or "").split()
    if len(parts)==2 and parts[1].lower() in {"on","off"}:
        await v9_set_setting("emergency_pause","1" if parts[1].lower()=="on" else "0")
    await message.answer(f"🚨 Emergency pause: <b>{'ON' if await v9_is_paused() else 'OFF'}</b>",parse_mode="HTML")

@dp.message(Command("maintenance"))
async def v9_maintenance_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS: return
    parts=(message.text or "").split()
    if len(parts)==2 and parts[1].lower() in {"on","off"}:
        await v9_set_setting("maintenance_mode","1" if parts[1].lower()=="on" else "0")
    await message.answer(f"🛠 Maintenance mode: <b>{'ON' if await v9_is_maintenance() else 'OFF'}</b>",parse_mode="HTML")

# ============================================================
# MAIN
# ============================================================

BOT = None


async def v6_condition_loop():
    while True:
        try:
            candidates = set(WATCH_TOKENS) | set(active_signals.keys())
            if DB:
                async with DB.acquire() as c:
                    rows = await c.fetch("SELECT DISTINCT mint FROM watchlists")
                candidates.update(r["mint"] for r in rows)
            for mint in list(candidates)[:100]:
                if not valid_solana_address(mint):
                    continue
                report = await build_v5_market_report(mint)
                if report.get("price") is None:
                    continue
                for event_type, event_text in detect_condition_changes(mint, report):
                    await save_intelligence_event(mint, event_type, report, event_text)
                    # Global channel gets only material scanner events.
                    if event_type in {"rug", "invalidation"}:
                        await send_v5_alert(report, reason=f"v6:{event_type}")
        except Exception:
            logging.exception("V6 condition loop failed")
        await asyncio.sleep(max(20, TOKEN_SNAPSHOT_SECONDS))


# ============================================================
# RENDER WEB-SERVICE HEALTH PORT
# ============================================================
# Telegram polling can run normally, but Render Web Services also expect
# an HTTP listener on $PORT. This tiny health server is additive only; it
# does not change Telegram polling or any bot feature.
async def render_health(request):
    return web.Response(text="OK", content_type="text/plain")


async def start_render_health_server():
    port = int(os.getenv("PORT", "10000"))
    app = web.Application()
    app.router.add_get("/", render_health)
    app.router.add_get("/health", render_health)
    runner = web.AppRunner(app, access_log=None)
    await runner.setup()
    site = web.TCPSite(runner, "0.0.0.0", port)
    await site.start()
    logging.info("Render health server listening on 0.0.0.0:%s", port)
    return runner


async def main():
    global BOT

    if not BOT_TOKEN:
        raise RuntimeError("BOT_TOKEN is missing.")

    if not RPC_URLS:
        raise RuntimeError("No Solana RPC provider is configured.")

    health_runner = await start_render_health_server()

    BOT = Bot(BOT_TOKEN)
    await db_init()
    await adv8_db_init()
    await v9_db_init()

    global BOT_USERNAME
    if not BOT_USERNAME:
        me = await BOT.get_me()
        BOT_USERNAME = me.username or ""

    logging.info("All-in-one private/free-tier Solana bot started as @%s.", BOT_USERNAME)

    tasks = [
        asyncio.create_task(daily_scheduler()),
        asyncio.create_task(premium_watchlist_loop()),
        asyncio.create_task(websocket_monitor()),
        asyncio.create_task(auto_discovery_loop()),
        asyncio.create_task(v5_scanner_loop()),
        asyncio.create_task(v5_discovery_loop()),
        asyncio.create_task(v5_snapshot_loop()),
        asyncio.create_task(v6_condition_loop()),
        asyncio.create_task(v7_watchdog_loop()),
        asyncio.create_task(adv8_watchdog_loop()),
        asyncio.create_task(result_tracker_loop()),
        asyncio.create_task(expire_members_loop()),
        asyncio.create_task(payment_monitor_loop()),
        asyncio.create_task(v9_cleanup_loop()),
        asyncio.create_task(db_reconnect_loop()),
    ]

    try:
        await dp.start_polling(BOT)
    finally:
        for task in tasks:
            task.cancel()
        await BOT.session.close()
        try:
            await health_runner.cleanup()
        except Exception:
            pass


if __name__ == "__main__":
    asyncio.run(main())
