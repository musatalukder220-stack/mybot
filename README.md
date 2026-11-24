# mybot — Crypto Analyst Telegram Bot

বাংলা/English crypto technical-analysis Telegram bot. Ask in plain text or voice ("BTC 4h", "ETH-এর ১ মাসের chart") and get a
TradingView-style chart plus a written report. This is analysis software, **not financial advice**.

## What it does
- Market data from Binance via CCXT, with Bybit/OKX fallback.
- Deterministic indicators and structure (RSI, MACD, ADX, Supertrend, Ichimoku, liquidity sweeps, FVG, order blocks,
  volume profile). Gemini only explains the numbers; it does not compute them.
- Breakout history, backtest (fees, slippage, in/out-of-sample), signal scorecard, multi-timeframe confluence.
- Price/level alerts, watchlist, scanner, portfolio PnL, futures trade manager, daily market report.
- Portfolio trades via /buy, /sell or the Buy/Sell buttons: by coin amount (`ETH 0.5 2000`) or by dollars (`ETH 500 usd` = $500 worth at the live price, `ETH 500 usd 2000` = $500 at price 2000).
- Free / Pro / Admin plans, free trial, referral bonus, manual bKash/Nagad approval flow.

## Layout
| File | Purpose |
|---|---|
| `bot.py` | Telegram handlers, NLU, exchange pool, database, charts, jobs, `main()` |
| `pro_quant.py` | Indicators, market structure, liquidity, imbalances, volume profile, position size |
| `pro_features.py` | TTL cache, retest state, explainable score, data quality, event fingerprint |
| `perf_stats.py` | Latency recorder (handlers, Gemini) and event-loop lag probe behind the admin `/health` command |
| `test_*.py` | pytest suite |

`bot.py` imports the two `pro_*` modules, so there is a single copy of that logic.

### Performance notes
Admin `/health` shows live DB / exchange / Telegram round-trip times, event-loop lag, p50/p95 per handler and Gemini calls, and a list of recent responses slower than 3 s. Plan and settings lookups are cached for 15-30 s (and cleared on every write), tickers for 3 s, RSS headlines for 5 min, per-coin futures context for 2 min, and BTC/ETH/multi-timeframe indicator snapshots per closed candle.

## Run locally
```bash
python -m venv .venv && source .venv/bin/activate
pip install -r requirements-dev.txt
cp .env.example .env   # fill in the values
python bot.py
```
Tests: `python -m pytest -q`

## Configuration (environment variables)
Required: `TELEGRAM_BOT_TOKEN`, `GEMINI_API_KEY`. Without `DATABASE_URL` alerts, watchlists and plans are disabled.

| Variable | Default | Meaning |
|---|---|---|
| `DATABASE_URL` | — | PostgreSQL connection string |
| `ADMIN_USER_IDS` | — | Comma-separated Telegram IDs of admins |
| `GEMINI_MODEL` | see `bot.py` | Gemini model name |
| `EXCHANGE_FALLBACKS` | `bybit,okx` | Fallback exchanges after Binance |
| `BKASH_NUMBER`, `NAGAD_NUMBER` | — | Payment numbers shown on /subscribe |
| `PRO_30_PRICE`, `PRO_90_PRICE` | `Contact admin` | Plan prices |
| `ADMIN_CONTACT_NAME`, `ADMIN_CONTACT_USERNAME` | see `bot.py` | Support contact shown to users |
| `PRICE_ALERT_CHANNEL_ID`, `REPORT_CHANNEL_ID` | — | Channels for price cards / daily report |
| `PRICE_CARD_BRAND` | see `bot.py` | Text on price cards |
| `CHART_THEME` | `dark` | Default chart theme for everyone: `dark` or `paper` (pale yellow). Each user can override it with the 🌙 / 🟡 buttons in /settings |
| `CHART_ZONE_BOXES` | `` | `1` brings back the filled zone rectangles (S/R bands, FVG, order blocks); default draws lines only |
| `CANDLE_LIMIT` / `BACKTEST_CANDLES` | 150 / 2000 | Candles per analysis / backtest |
| `MAX_CONCURRENT_ANALYSES` | 3 | Parallel analyses |
| `ALERT_INTERVAL_SECONDS` / `LEVEL_ALERT_INTERVAL_SECONDS` | 180 / 30 | Alert polling intervals |
| `ANALYSES_RETENTION_DAYS` | 30 | Stored analysis retention |
| `TRIAL_DAYS` / `REFERRAL_BONUS_DAYS` | 3 / 3 | `0` switches the feature off |
| `DAILY_REPORT_HOUR` | 9 | Asia/Dhaka hour of the daily report |
| `PORTFOLIO_REFRESH_SECONDS` / `PORTFOLIO_LIVE_MINUTES` | 30 / 30 | Live portfolio screen |
| `SENTRY_DSN` | — | Optional; also `pip install sentry-sdk` |
| `LOG_LEVEL` | `INFO` | Logging level |

## Deploy (Railway)
Set the variables above on the service, add a PostgreSQL plugin for `DATABASE_URL`, and start with `python bot.py`.
On a start-up crash the bot messages every admin in `ADMIN_USER_IDS`.
