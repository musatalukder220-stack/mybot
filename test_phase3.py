"""Phase-3 tests: MTF confluence, backtest, scorecard, price levels, portfolio,
daily report and the exchange fallback chain.

Run:  pytest -q test_phase3.py
Telegram/DB/exchange are faked; every decision function under test is real.
"""
from __future__ import annotations

import asyncio
from types import SimpleNamespace

import numpy as np
import pandas as pd
import pytest

import bot as B


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def frame_with_breakout(n: int = 200, breakout_at: int | None = None) -> pd.DataFrame:
    """Flat market; optional single strong candle at `breakout_at` (a past bar)."""
    end = pd.Timestamp.utcnow().floor("4h")
    idx = pd.date_range(end=end, periods=n, freq="4h", tz="UTC")
    close = np.full(n, 100.0)
    volume = np.full(n, 100.0)
    if breakout_at is not None:
        close[breakout_at] = 130.0
        volume[breakout_at] = 900.0
    frame = pd.DataFrame({"Open": np.r_[close[0], close[:-1]], "High": close + .5,
                          "Low": close - .5, "Close": close, "Volume": volume}, index=idx)
    frame.iloc[breakout_at, frame.columns.get_loc("Open")] = 118.0 if breakout_at is not None else 100.0
    return frame


class FakeMessage:
    def __init__(self):
        self.replies = []

    async def reply_text(self, text, **kw):
        self.replies.append(text)
        return self

    async def edit_text(self, text, **kw):
        self.replies.append(text)
        return self

    async def delete(self):
        return None


class FakeBotAPI:
    def __init__(self):
        self.sent = []

    async def send_message(self, chat_id, text, **kw):
        self.sent.append((chat_id, text))


class FakeDB:
    def __init__(self, fetch_rows=None, fetchval=1):
        self.fetch_rows = fetch_rows or []
        self.fetchval_result = fetchval
        self.executed = []
        self.fetchvals = []

    async def fetch(self, sql, *args):
        return self.fetch_rows

    async def fetchval(self, sql, *args):
        self.fetchvals.append((sql, args))
        return self.fetchval_result

    async def execute(self, sql, *args):
        self.executed.append((sql, args))
        return "OK"


class FakeAnalyst:
    """Minimal AnalystBot stand-in for command tests."""

    def __init__(self, price=100.0, db=None, plan="pro"):
        self.price = price
        self.db = db if db is not None else FakeDB()
        self.plan = plan
        self.data_source = {}
        self.cache = B.TTLCache(maxsize=16)
        self.price_calls = []

    async def ensure_user(self, update):
        return None

    async def effective_plan(self, user_id):
        return self.plan

    async def fetch_live_price(self, symbol):
        self.price_calls.append(symbol)
        return {"price": self.price}

    @staticmethod
    def _normalize_symbol(raw):
        return B.AnalystBot._normalize_symbol(raw)

    @staticmethod
    def _normalize_tf(raw):
        return B.AnalystBot._normalize_tf(raw)


ARGS=[None]


def use_args(*values):
    """Set the fake context arg list for the next command call."""
    ARGS[0]=list(values)


def update_with(text_message=None, user_id=42, chat_id=42, args=None, callback=None):
    ARGS[0] = list(args or [])          # the context mirrors the update's args
    return SimpleNamespace(
        effective_message=text_message or FakeMessage(),
        effective_user=SimpleNamespace(id=user_id, username="tester"),
        effective_chat=SimpleNamespace(id=chat_id),
        callback_query=callback,
        update_id=1,
    )


def ctx():
    """Command context carrying whatever args update_with() received."""
    return SimpleNamespace(args=ARGS[0], bot=FakeBotAPI())


# --------------------------------------------------------------------------
# 1) MTF confluence
# --------------------------------------------------------------------------
def test_mtf_confluence_full_bullish_agreement():
    per = {tf: {"structure": "bullish (HH/HL)", "rsi": 62, "above_ema50": True} for tf in B.MTF_TIMEFRAMES}
    out = B.mtf_confluence(per)
    assert out["bias"] == "bullish" and out["score"] == 100
    assert out["aligned_count"] == 4 and out["status"] == "live"
    assert "সব টাইমফ্রেম" in out["reading"]


def test_mtf_confluence_split_and_unavailable():
    per = {"15m": {"structure": "bearish (LH/LL)", "rsi": 40, "above_ema50": False},
           "1h": {"structure": "bearish (LH/LL)", "rsi": 44, "above_ema50": False},
           "4h": {"structure": "bullish (HH/HL)", "rsi": 60, "above_ema50": True},
           "1d": {"status": "unavailable"}}
    out = B.mtf_confluence(per)
    assert out["bias"] == "bearish"
    assert out["timeframes"]["1d"]["status"] == "unavailable"
    assert 0 < out["score"] < 100 and out["bearish_score"] == 100 - out["score"]


def test_mtf_confluence_all_unavailable_is_neutral():
    out = B.mtf_confluence({tf: {"status": "unavailable"} for tf in B.MTF_TIMEFRAMES})
    assert out["status"] == "unavailable" and out["score"] == 50 and out["bias"] == "mixed"


def test_analyze_adds_mtf_only_in_professional_mode(monkeypatch):
    captured = {}

    async def fake_gemini(self, system, prompt, schema):
        captured["prompt"] = prompt
        return {"analysis_bn": "TEXT"}

    async def fake_mtf(self, request):
        return {"status": "live", "score": 80, "bias": "bullish", "aligned_count": 3, "timeframes": {}}

    monkeypatch.setattr(B.AnalystBot, "_gemini_json", fake_gemini)
    monkeypatch.setattr(B.AnalystBot, "multi_timeframe", fake_mtf)
    monkeypatch.setattr(B.AnalystBot, "external_context", lambda self, r, all_market=False: _aret({}))
    monkeypatch.setattr(B.AnalystBot, "higher_timeframe", lambda self, r: _aret({"structure": "bullish (HH/HL)"}))
    monkeypatch.setattr(B.AnalystBot, "market_filter", lambda self, tf: _aret({"risk_on": True}))
    analyst = object.__new__(B.AnalystBot)
    analyst.analysis_model = "SYS"
    frame = frame_with_breakout(160)
    request = B.Request("BTC/USDT", "4h")

    asyncio.run(B.AnalystBot.analyze(analyst, request, frame.copy(), detail_mode="professional"))
    assert "MULTI_TIMEFRAME_CONFLUENCE" in captured["prompt"]
    assert '"score":80' in captured["prompt"]

    captured.clear()
    asyncio.run(B.AnalystBot.analyze(analyst, request, frame.copy(), detail_mode="standard"))
    assert "MULTI_TIMEFRAME_CONFLUENCE: {}" in captured["prompt"]


def _aret(value):
    async def _inner():
        return value
    return _inner()


# --------------------------------------------------------------------------
# 2) backtest: fees, slippage, in/out-of-sample
# --------------------------------------------------------------------------
def test_backtest_charges_fees_and_reports_samples():
    frame = frame_with_breakout(200, breakout_at=60)
    result = B.simple_backtest(frame, fee_pct=0.10, slippage_pct=0.05)
    assert result["trades"] >= 1
    assert result["net_r_multiple"] <= result["gross_r_multiple"]      # costs never improve R
    assert "in_sample" in result and "out_sample" in result
    assert result["fee_pct"] == 0.10 and result["slippage_pct"] == 0.05
    assert result["in_sample"]["trades"] + result["out_sample"]["trades"] == result["trades"]
    assert "fees" in result["assumptions"] and "out-of-sample" in result["assumptions"]


def test_backtest_slippage_lowers_the_result():
    frame = frame_with_breakout(200, breakout_at=60)
    clean = B.simple_backtest(frame, fee_pct=0.0, slippage_pct=0.0)
    costly = B.simple_backtest(frame, fee_pct=0.2, slippage_pct=0.2)
    assert costly["net_r_multiple"] < clean["net_r_multiple"]


def test_backtest_empty_input_is_safe():
    out = B.simple_backtest(frame_with_breakout(120))
    assert out["trades"] == 0 and out["win_rate"] == 0 and out["net_r_multiple"] == 0


class PagingExchange:
    """Returns 1000-row batches, like Binance's per-request cap."""

    def __init__(self, total=2500, tf_ms=4 * 3600 * 1000):
        self.total = total
        self.tf_ms = tf_ms
        self.calls = 0

    async def fetch_ohlcv(self, symbol, timeframe, since=None, limit=1000):
        self.calls += 1
        start = since
        rows = []
        for i in range(min(limit, self.total - self.calls * limit + limit)):
            ts = start + i * self.tf_ms
            rows.append([ts, 100.0, 101.0, 99.0, 100.5, 10.0])
            if len(rows) >= limit:
                break
        return rows


def test_fetch_history_paginates_without_touching_candle_limit(monkeypatch):
    fake = FakeAnalyst()
    exchange = PagingExchange(total=2500)
    monkeypatch.setattr(B, "CANDLE_LIMIT", 150)          # analysis limit stays untouched
    analyst = object.__new__(B.AnalystBot)
    analyst.markets_source = "Binance"
    analyst.markets_exchange = exchange
    analyst.fallback_exchanges = {}
    analyst.data_source = {}
    analyst.exchange = exchange
    analyst.markets_loaded = True
    analyst.markets = {"BTC/USDT": {"spot": True, "active": True}}
    exchange.markets = analyst.markets
    analyst._market_lock = asyncio.Lock()

    class Ex(PagingExchange):
        markets = {"BTC/USDT": {"spot": True, "active": True}}

    analyst.exchange = Ex(total=2500)
    frame = asyncio.run(B.AnalystBot.fetch_history(analyst, "BTC/USDT", "4h", target=2000))
    assert len(frame) > 150                       # far more than CANDLE_LIMIT
    assert frame.index.is_monotonic_increasing
    assert frame.index.is_unique
    assert B.CANDLE_LIMIT == 150


# --------------------------------------------------------------------------
# 3) scorecard
# --------------------------------------------------------------------------
def test_event_follow_through_measures_only_future_candles():
    end = pd.Timestamp.utcnow().floor("4h")
    idx = pd.date_range(end=end, periods=12, freq="4h", tz="UTC")
    close = np.full(12, 100.0)
    high = np.full(12, 100.5)
    high[7] = 106.0                                    # +6% two candles after the signal
    frame = pd.DataFrame({"Open": close, "High": high, "Low": close - .5, "Close": close, "Volume": 1.0}, index=idx)
    signal_close = idx[5]
    value = B.event_follow_through(frame, signal_close, 100.0, "BREAKOUT_CONFIRMED", max_candles=10)
    assert value == pytest.approx(6.0)
    # a signal at the very last candle has no future window yet
    assert B.event_follow_through(frame, idx[-1], 100.0, "BREAKOUT_CONFIRMED") is None
    # breakdowns measure the downside
    lowed = frame.copy(); lowed.iloc[7, lowed.columns.get_loc("Low")] = 94.0
    assert B.event_follow_through(lowed, signal_close, 100.0, "BREAKDOWN_CONFIRMED") == pytest.approx(6.0)


def test_scorecard_stats_aggregation():
    rows = [{"event_type": "BREAKOUT_CONFIRMED", "timeframe": "4h", "max_follow_through_pct": 1.2},
            {"event_type": "BREAKOUT_CONFIRMED", "timeframe": "4h", "max_follow_through_pct": 0.1},
            {"event_type": "BREAKDOWN_CONFIRMED", "timeframe": "1h", "max_follow_through_pct": 2.0},
            {"event_type": "BREAKDOWN_CONFIRMED", "timeframe": "1h", "max_follow_through_pct": None}]
    stats = B.scorecard_stats(rows)
    assert stats["total"] == 4 and stats["evaluated"] == 3 and stats["pending"] == 1
    assert stats["hits"] == 2 and stats["hit_rate"] == pytest.approx(66.7)
    assert stats["best"] == 2.0 and stats["worst"] == 0.1
    assert stats["by_type"]["BREAKOUT_CONFIRMED"] == {"total": 2, "hit": 1, "rate": 50.0}
    assert stats["by_timeframe"]["1h"]["total"] == 1   # pending rows are skipped
    assert stats["by_timeframe"]["4h"]["rate"] == 50.0


def test_scorecard_job_updates_pending_events(monkeypatch):
    frame = frame_with_breakout(60, breakout_at=20)
    rows = [{"id": 7, "symbol": "BTC/USDT", "timeframe": "4h",
             "candle_close": frame.index[21], "event_type": "BREAKOUT_CONFIRMED", "close_price": 130.0}]
    fake = FakeAnalyst(db=FakeDB(fetch_rows=rows))

    async def fake_fetch(request, force=False):
        return frame

    fake.fetch_candles = fake_fetch
    monkeypatch.setattr(B, "BOT", fake)
    asyncio.run(B.scorecard_job(None))
    updates = [x for x in fake.db.executed if "UPDATE breakout_events" in x[0]]
    assert updates and updates[0][1][1] == 7


# --------------------------------------------------------------------------
# 4) price levels
# --------------------------------------------------------------------------
def test_price_level_helpers():
    assert B.price_level_direction(105, 100) == "above"
    assert B.price_level_direction(95, 100) == "below"
    assert B.price_level_triggered(105, "above", 106)
    assert not B.price_level_triggered(105, "above", 104.9)
    assert B.price_level_triggered(95, "below", 94)
    assert not B.price_level_triggered(95, "below", 96)
    assert not B.price_level_triggered(0, "above", 100)


def test_check_price_levels_fires_once_and_keeps_repeat(monkeypatch):
    rows = [{"id": 1, "telegram_id": 42, "chat_id": 42, "symbol": "BTC/USDT", "level": 70000.0,
             "direction": "above", "repeat": False},
            {"id": 2, "telegram_id": 42, "chat_id": 42, "symbol": "BTC/USDT", "level": 69000.0,
             "direction": "above", "repeat": True}]
    fake = FakeAnalyst(price=70050.0, db=FakeDB(fetch_rows=rows))
    monkeypatch.setattr(B, "BOT", fake)
    api = FakeBotAPI()
    asyncio.run(B.check_price_levels(SimpleNamespace(bot=api)))
    assert len(api.sent) == 2                          # both levels crossed
    assert len(fake.price_calls) == 1                  # one ticker for both levels
    sqls = [sql for sql, _ in fake.db.executed]
    assert any("active=FALSE" in sql for sql in sqls)  # one-shot level disarmed
    assert any("last_fired_at=NOW() WHERE id=$1" == sql.strip()[-32:] or "SET last_fired_at" in sql and "active" not in sql
               for sql in sqls)


def test_check_price_levels_ignores_uncrossed(monkeypatch):
    rows = [{"id": 1, "telegram_id": 42, "chat_id": 42, "symbol": "BTC/USDT", "level": 80000.0,
             "direction": "above", "repeat": False}]
    fake = FakeAnalyst(price=70000.0, db=FakeDB(fetch_rows=rows))
    monkeypatch.setattr(B, "BOT", fake)
    api = FakeBotAPI()
    asyncio.run(B.check_price_levels(SimpleNamespace(bot=api)))
    assert api.sent == [] and fake.db.executed == []


def test_level_command_adds_level(monkeypatch):
    fake = FakeAnalyst(price=69000.0, db=FakeDB(fetchval=5))
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    update = update_with(message, args=["BTC", "70000"])
    asyncio.run(B.level_command(update, ctx()))
    assert "#5" in message.replies[-1] and "70,000" not in message.replies[-1]
    assert "70000" in message.replies[-1]
    insert = fake.db.fetchvals[-1]
    assert "INSERT INTO price_levels" in insert[0]
    assert insert[1][3] == pytest.approx(70000.0) and insert[1][4] == "above"


def test_level_command_stores_below_level(monkeypatch):
    """A level under the live price becomes a 'below' alert, not a rejection."""
    fake = FakeAnalyst(price=71000.0, db=FakeDB(fetchval=9))
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    asyncio.run(B.level_command(update_with(message, args=["BTC", "70000"]), ctx()))
    assert "নিচে নামলে" in message.replies[-1]
    assert fake.db.fetchvals[-1][1][4] == "below"


def test_level_command_lists_and_deletes(monkeypatch):
    rows = [{"id": 3, "symbol": "ETH/USDT", "level": 3000.0, "direction": "below",
             "active": True, "repeat": True}]
    fake = FakeAnalyst(db=FakeDB(fetch_rows=rows))
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    asyncio.run(B.level_command(update_with(message, args=["list"]), ctx()))
    assert "#3" in message.replies[-1] and "≤" in message.replies[-1] and "repeat" in message.replies[-1]

    asyncio.run(B.level_command(update_with(message, args=["del", "3"]), ctx()))
    assert "DELETE FROM price_levels" in fake.db.executed[-1][0]


# --------------------------------------------------------------------------
# 5) portfolio
# --------------------------------------------------------------------------
def test_portfolio_pnl_totals_and_missing_prices():
    holdings = [{"symbol": "BTC/USDT", "amount": 0.5, "avg_cost": 60000},
                {"symbol": "ETH/USDT", "amount": 4.0, "avg_cost": 2500},
                {"symbol": "SOL/USDT", "amount": 10.0, "avg_cost": 100}]
    stats = B.portfolio_pnl(holdings, {"BTC/USDT": 70000, "ETH/USDT": 2000})
    assert stats["missing"] == ["SOL/USDT"]
    assert stats["total_cost"] == pytest.approx(0.5 * 60000 + 4 * 2500)
    assert stats["total_value"] == pytest.approx(0.5 * 70000 + 4 * 2000)
    assert stats["total_pnl"] == pytest.approx(5000 - 2000)
    assert stats["rows"][0]["symbol"] == "BTC/USDT"       # sorted by value
    assert stats["rows"][0]["pnl_pct"] == pytest.approx((35000 - 30000) / 30000 * 100)


def test_portfolio_command_add_and_show(monkeypatch):
    fake = FakeAnalyst(price=70000.0)
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    asyncio.run(B.portfolio_command(update_with(message, args=["add", "BTC", "0.5", "60000"]), ctx()))
    assert "সেভ হয়েছে" in message.replies[-1]
    assert "INSERT INTO portfolio" in fake.db.executed[-1][0]

    fake.db.fetch_rows = [{"symbol": "BTC/USDT", "amount": 0.5, "avg_cost": 60000.0}]
    asyncio.run(B.portfolio_command(update_with(message, args=[]), ctx()))
    text = message.replies[-1]
    assert "Unrealised PnL" in text and "+5,000.00" in text


def test_portfolio_command_rejects_bad_input(monkeypatch):
    fake = FakeAnalyst()
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    asyncio.run(B.portfolio_command(update_with(message, args=["add", "BTC", "-1", "0"]), ctx()))
    assert "ব্যবহার" in message.replies[-1]


# --------------------------------------------------------------------------
# 6) daily report
# --------------------------------------------------------------------------
def test_top_movers_filters_worst_offenders():
    payload = [
        {"symbol": "BTCUSDT", "priceChangePercent": "1.2", "quoteVolume": "900000000", "lastPrice": "70000"},
        {"symbol": "SCAMUSDT", "priceChangePercent": "450", "quoteVolume": "5000", "lastPrice": "0.1"},
        {"symbol": "USDCUSDT", "priceChangePercent": "0.01", "quoteVolume": "900000000", "lastPrice": "1"},
        {"symbol": "ETHUSDT", "priceChangePercent": "-3.5", "quoteVolume": "500000000", "lastPrice": "2500"},
        {"symbol": "SOLUSDT", "priceChangePercent": "8.0", "quoteVolume": "80000000", "lastPrice": "150"},
    ]
    out = B.top_movers(payload, n=2)
    assert [row["symbol"] for row in out["gainers"]] == ["SOL/USDT", "BTC/USDT"]
    assert out["losers"][0]["symbol"] == "ETH/USDT"
    assert all("SCAM" not in row["symbol"] for row in out["gainers"] + out["losers"])
    assert B.top_movers("garbage") == {"gainers": [], "losers": []}


def test_build_daily_report_sections(monkeypatch):
    async def fake_market(tf):
        return {"btc": {"structure": "bullish (HH/HL)", "rsi": 58, "above_ema50": True},
                "eth": {"structure": "range", "rsi": 49, "above_ema50": False}, "risk_on": True}

    async def fake_sentiment():
        return {"fear_greed": {"value": 40, "label": "Fear"}, "btc_dominance": 55.5,
                "market_cap_change_24h": -1.2, "status": "live"}

    async def fake_http(url, params=None, timeout=10.0):
        return [{"symbol": "SOLUSDT", "priceChangePercent": "9", "quoteVolume": "80000000", "lastPrice": "150"}]

    fake = FakeAnalyst()
    fake.market_filter = fake_market
    fake.market_sentiment = fake_sentiment
    monkeypatch.setattr(B, "http_json", fake_http)
    monkeypatch.setattr(B, "BOT", fake)
    text = asyncio.run(B.build_daily_report())
    assert "Daily crypto market report" in text
    assert "risk-on" in text and "Fear & Greed: 40" in text
    assert "BTC dominance: 55.5%" in text
    assert "SOL/USDT +9.00%" in text
    assert "আর্থিক পরামর্শ নয়" in text


def test_report_command_is_admin_only(monkeypatch):
    monkeypatch.setattr(B, "ADMIN_IDS", {999})
    message = FakeMessage()
    asyncio.run(B.report_command(update_with(message, user_id=42), ctx()))
    assert "Admin only" in message.replies[-1]


# --------------------------------------------------------------------------
# 7) exchange fallback
# --------------------------------------------------------------------------
class BoomExchange:
    async def fetch_ohlcv(self, *a, **kw):
        raise RuntimeError("451 restricted location")


class GoodExchange:
    def __init__(self, rows):
        self.rows = rows

    async def fetch_ohlcv(self, *a, **kw):
        return self.rows


def test_fallback_switches_to_bybit_and_records_source(monkeypatch):
    analyst = object.__new__(B.AnalystBot)
    analyst.exchange = BoomExchange()
    analyst.fallback_exchanges = {}
    analyst.data_source = {}
    analyst.markets_source = "Binance"
    analyst.markets_exchange = None
    rows = [[1700000000000, 1, 2, 0.5, 1.5, 10]]
    monkeypatch.setattr(B.ccxt, "okx", lambda cfg: BoomExchange())      # OKX also down
    monkeypatch.setattr(B.ccxt, "bybit", lambda cfg: GoodExchange(rows))
    got = asyncio.run(B.AnalystBot._fetch_ohlcv_with_fallback(analyst, "BTC/USDT", "4h", 150,
                                                              ("BTC/USDT", "4h")))
    assert got == rows
    assert analyst.data_source[("BTC/USDT", "4h")] == "Bybit"


def test_fallback_raises_when_every_exchange_fails(monkeypatch):
    analyst = object.__new__(B.AnalystBot)
    analyst.exchange = BoomExchange()
    analyst.fallback_exchanges = {}
    analyst.data_source = {}
    analyst.markets_source = "Binance"
    analyst.markets_exchange = None
    monkeypatch.setattr(B.ccxt, "bybit", lambda cfg: BoomExchange())
    monkeypatch.setattr(B.ccxt, "okx", lambda cfg: BoomExchange())
    with pytest.raises(B.UserInputError):
        asyncio.run(B.AnalystBot._fetch_ohlcv_with_fallback(analyst, "BTC/USDT", "4h", 150,
                                                            ("BTC/USDT", "4h")))
    assert analyst.data_source == {}


# --------------------------------------------------------------------------
# 8) venue failover for market lists / history / movers
# --------------------------------------------------------------------------
class MarketExchange:
    def __init__(self, markets=None, rows=None, fail=False):
        self.markets = markets
        self.rows = rows or [[1700000000000, 1, 2, .5, 1.5, 10]]
        self.fail = fail
        self.loaded = False

    async def load_markets(self):
        if self.fail:
            raise RuntimeError("451 restricted location")
        self.loaded = True
        return self.markets

    async def fetch_ohlcv(self, symbol, timeframe, since=None, limit=1000):
        if self.fail:
            raise RuntimeError("451 restricted location")
        return self.rows

    async def fetch_ticker(self, symbol):
        if self.fail:
            raise RuntimeError("451 restricted location")
        return {"last": 70000.0, "bid": 69999.0, "ask": 70001.0, "timestamp": 1}

    async def fetch_time(self):
        if self.fail:
            raise RuntimeError("451")
        return 1700000000000


def test_market_list_fails_over_and_markets_are_reachable(monkeypatch):
    """A Binance 451 must not leave self.exchange.markets = None."""
    analyst = object.__new__(B.AnalystBot)
    analyst.exchange = MarketExchange(fail=True)
    analyst.fallback_exchanges = {}
    analyst.data_source = {}
    analyst.markets_source = None
    analyst.markets_exchange = None
    analyst.markets_loaded = False
    analyst._market_lock = asyncio.Lock()
    okx = MarketExchange(markets={"BTC/USDT": {"spot": True, "active": True}})
    monkeypatch.setattr(B.ccxt, "okx", lambda cfg: okx)

    markets = asyncio.run(B.AnalystBot._ensure_markets(analyst))
    assert markets == {"BTC/USDT": {"spot": True, "active": True}}
    assert analyst.markets_source == "Okx" and analyst.markets_exchange is okx
    # the second call must return the fallback's list, not Binance's None
    assert asyncio.run(B.AnalystBot._ensure_markets(analyst)) == markets


def test_live_price_falls_back_to_secondary_venue(monkeypatch):
    analyst = object.__new__(B.AnalystBot)
    analyst.exchange = MarketExchange(fail=True)
    analyst.fallback_exchanges = {}
    analyst.data_source = {}
    analyst.markets_source = "Okx"
    analyst.markets_exchange = MarketExchange(markets={"BTC/USDT": {}})
    got = asyncio.run(B.AnalystBot.fetch_live_price(analyst, "BTC/USDT"))
    assert got["price"] == 70000.0


def test_parse_okx_tickers_converts_to_binance_shape():
    payload = {"code": "0", "data": [
        {"instId": "BTC-USDT", "last": "110", "open24h": "100", "volCcy24h": "50000000"},
        {"instId": "DOGE-USDC", "last": "1", "open24h": "1", "volCcy24h": "1"},
        {"instId": "ETH-USDT", "last": "0", "open24h": "0", "volCcy24h": "1"},
    ]}
    rows = B.parse_okx_tickers(payload)
    assert rows == [{"symbol": "BTCUSDT", "priceChangePercent": "10.0",
                     "quoteVolume": "50000000", "lastPrice": "110.0"}]
    assert B.parse_okx_tickers({}) == [] and B.parse_okx_tickers("nope") == []
    movers = B.top_movers(rows, n=1)
    assert movers["gainers"][0]["symbol"] == "BTC/USDT"


def test_daily_report_labels_a_fully_red_day(monkeypatch):
    async def fake_http(url, params=None, timeout=10.0):
        if "binance" in url:
            raise RuntimeError("451 restricted location")
        return {"data": [{"instId": "BTC-USDT", "last": "95", "open24h": "100", "volCcy24h": "90000000"},
                         {"instId": "ETH-USDT", "last": "90", "open24h": "100", "volCcy24h": "80000000"}]}

    async def no_market(tf):
        return {}

    async def no_sentiment():
        return {}

    fake = FakeAnalyst()
    fake.market_filter = no_market
    fake.market_sentiment = no_sentiment
    monkeypatch.setattr(B, "http_json", fake_http)
    text = asyncio.run(B.build_daily_report(fake))
    assert "সবচেয়ে ভালো পারফর্মার" in text and "Top gainers" not in text
    assert "BTC/USDT -5.00%" in text


# --------------------------------------------------------------------------
# 9) new commands end-to-end through the fake layer
# --------------------------------------------------------------------------
def test_backtest_command_renders_sample_split(monkeypatch):
    frame = frame_with_breakout(300, breakout_at=80)
    fake = FakeAnalyst()
    targets = {}

    async def fake_history(symbol, timeframe, target=1200):
        targets["args"] = (symbol, timeframe, target)
        return frame

    fake.fetch_history = fake_history
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    asyncio.run(B.backtest_command(update_with(message, args=["BTC", "4h", "1500"]), ctx()))
    text = message.replies[-1]
    assert targets["args"] == ("BTC/USDT", "4h", 1500)
    assert "In-sample" in text and "Out-of-sample" in text
    assert "fees" in text and "slippage" in text.lower()
    assert "নিশ্চয়তা নয়" in text


def test_mtf_command_shows_every_timeframe(monkeypatch):
    fake = FakeAnalyst()

    async def fake_mtf(request):
        return B.mtf_confluence({tf: {"structure": "bullish (HH/HL)", "rsi": 60, "above_ema50": True}
                                 for tf in B.MTF_TIMEFRAMES})

    fake.multi_timeframe = fake_mtf
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    asyncio.run(B.mtf_command(update_with(message, args=["BTC"]), ctx()))
    text = message.replies[-1]
    assert all(tf in text for tf in B.MTF_TIMEFRAMES)
    assert "score 100/100" in text and "4/4" in text
    assert "সম্ভাবনা নয়" in text


def test_mtf_command_is_pro_gated(monkeypatch):
    fake = FakeAnalyst(plan="free")
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    asyncio.run(B.mtf_command(update_with(message, args=["BTC"]), ctx()))
    assert "Pro feature" in message.replies[-1]


def test_scorecard_command_renders_stats(monkeypatch):
    rows = [{"event_type": "BREAKOUT_CONFIRMED", "timeframe": "4h", "max_follow_through_pct": 1.5},
            {"event_type": "BREAKDOWN_CONFIRMED", "timeframe": "1h", "max_follow_through_pct": 0.2},
            {"event_type": "BREAKOUT_CONFIRMED", "timeframe": "4h", "max_follow_through_pct": None}]
    fake = FakeAnalyst(db=FakeDB(fetch_rows=rows))
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    asyncio.run(B.scorecard_command(update_with(message, args=["30"]), ctx()))
    text = message.replies[-1]
    assert "Signal scorecard" in text
    assert "মোট signal: 3" in text and "মূল্যায়িত: 2" in text and "অপেক্ষমাণ: 1" in text
    assert "1 (50.0%)" in text
    assert "BREAKOUT_CONFIRMED" in text and "1h" in text


def test_scorecard_command_without_rows_and_without_db(monkeypatch):
    fake = FakeAnalyst(db=FakeDB(fetch_rows=[]))
    monkeypatch.setattr(B, "BOT", fake)
    message = FakeMessage()
    asyncio.run(B.scorecard_command(update_with(message, args=[]), ctx()))
    assert "কোনো সংরক্ষিত signal নেই" in message.replies[-1]

    no_db = FakeAnalyst()
    no_db.db = None
    monkeypatch.setattr(B, "BOT", no_db)
    asyncio.run(B.scorecard_command(update_with(message, args=[]), ctx()))
    assert "DATABASE_URL" in message.replies[-1]
