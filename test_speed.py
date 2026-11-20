"""Speed-ups must not change behaviour: caches expire/invalidate, work is shared, and the trade confirmation does not wait for the picture."""
import asyncio
import time
from types import SimpleNamespace

import pytest

import bot
from perf_stats import LatencyStats, loop_lag_probe


class CountingDB:
    def __init__(self, row=None):
        self.row, self.fetchrow_calls, self.exec_calls = row, 0, []

    async def fetchrow(self, sql, *a):
        self.fetchrow_calls += 1
        return self.row

    async def execute(self, sql, *a): self.exec_calls.append(a)
    async def fetchval(self, sql, *a): return 1


def make_bot(db=None):
    b = bot.AnalystBot.__new__(bot.AnalystBot)
    b.cache = bot.TTLCache(maxsize=64)
    b.db = db
    return b


def upd(uid=5, name="mo"):
    return SimpleNamespace(effective_user=SimpleNamespace(id=uid, username=name))


def run(coro): return asyncio.run(coro)


# ---------------------------------------------------------------- per-message DB work
def test_ensure_user_writes_once_until_username_changes():
    db = CountingDB(); b = make_bot(db)

    async def go():
        for _ in range(5): await b.ensure_user(upd())
        assert len(db.exec_calls) == 1
        await b.ensure_user(upd(name="renamed"))
        assert len(db.exec_calls) == 2
        await b.ensure_user(upd(uid=9, name=None)); await b.ensure_user(upd(uid=9, name=None))
        assert len(db.exec_calls) == 3                      # a brand-new user without a username is still stored (once)
    run(go())


def test_plan_is_cached_and_forgotten_on_write():
    from datetime import datetime, timedelta, timezone
    db = CountingDB({"plan": "pro", "plan_until": datetime.now(timezone.utc) + timedelta(days=3), "blocked": False}); b = make_bot(db)

    async def go():
        assert [await b.effective_plan(7) for _ in range(4)] == ["pro"] * 4
        assert db.fetchrow_calls == 1
        db.row = {"plan": "pro", "plan_until": None, "blocked": True}
        assert await b.effective_plan(7) == "pro"           # still cached ...
        b.forget_user(7)
        assert await b.effective_plan(7) == "blocked"       # ... until an admin action invalidates it, then instant
    run(go())


def test_settings_cached_returns_independent_copies():
    db = CountingDB({"detail_mode": "quick", "risk_mode": "balanced", "timezone": "Asia/Dhaka", "language": "bn", "chart_theme": ""}); b = make_bot(db)

    async def go():
        first = await b.user_settings(3); first["detail_mode"] = "mutated"
        second = await b.user_settings(3)
        assert second["detail_mode"] == "quick" and db.fetchrow_calls == 1
        b.forget_user(3); await b.user_settings(3)
        assert db.fetchrow_calls == 2
    run(go())


# ---------------------------------------------------------------- shared network work
def test_live_price_requests_are_coalesced_and_not_shared_across_coins():
    b = make_bot(); calls = []

    async def fake(symbol):
        calls.append(symbol); await asyncio.sleep(.05); return {"price": 1.0 + len(calls)}
    b._fetch_live_price = fake

    async def go():
        got = await asyncio.gather(*(b.fetch_live_price("ETH/USDT") for _ in range(10)), b.fetch_live_price("BTC/USDT"))
        assert calls.count("ETH/USDT") == 1 and calls.count("BTC/USDT") == 1
        assert all(g == got[0] for g in got[:10])
    run(go())


def test_external_context_cached_per_coin_and_failures_not_kept():
    b = make_bot(); n = {"ok": 0}

    async def ok(self, request, all_market=False, extended=False, price_change_pct=0.0):
        n["ok"] += 1; return {"funding_rate": .01, "news": [], "news_status": "live_rss"}
    b._external_context = ok.__get__(b)
    req = bot.Request("ETH/USDT", "4h")

    async def go():
        a = await b.external_context(req); a["news"].append("mutated")
        c = await b.external_context(req)
        assert n["ok"] == 1 and c["news"] == []                # shared work, but callers get their own copy
        await b.external_context(bot.Request("SOL/USDT", "4h")); assert n["ok"] == 2

        async def bad(self, *a, **k): n["ok"] += 1; return {"funding_rate": None, "news": [], "news_status": "unavailable"}
        b._external_context = bad.__get__(b); before = n["ok"]
        await b.external_context(bot.Request("XRP/USDT", "4h")); await b.external_context(bot.Request("XRP/USDT", "4h"))
        assert n["ok"] - before == 2                           # a total failure is retried, not remembered
    run(go())


def test_quant_snapshot_memoised_per_closed_candle(monkeypatch):
    import pandas as pd
    b = make_bot(); n = {"c": 0}
    monkeypatch.setattr(bot, "quant_snapshot", lambda f: n.__setitem__("c", n["c"] + 1) or {"x": n["c"]})
    idx = pd.date_range("2025-01-01", periods=5, freq="h", tz="UTC")
    f1 = pd.DataFrame({"Close": range(5)}, index=idx)

    async def go():
        a = await b.quant_cached("BTC/USDT", "1h", f1); c = await b.quant_cached("BTC/USDT", "1h", f1)
        assert a is c and n["c"] == 1
        f2 = pd.DataFrame({"Close": range(6)}, index=pd.date_range("2025-01-01", periods=6, freq="h", tz="UTC"))
        await b.quant_cached("BTC/USDT", "1h", f2); assert n["c"] == 2     # a new candle recomputes
    run(go())


# ---------------------------------------------------------------- trade confirmation is not blocked by the picture
def test_trade_confirmation_sent_while_picture_still_rendering(monkeypatch):
    order = []

    async def fake_apply(*a, **k): return "✅ Buy ETH"

    async def slow_push(bot_, uid, view, page=None):
        order.append("push-start"); await asyncio.sleep(.3); order.append("push-done")

    class Msg:
        message_id = 1; chat = SimpleNamespace(id=1)
        async def reply_text(self, text, **k):
            order.append("reply"); return SimpleNamespace(message_id=2, chat=SimpleNamespace(id=1))

    fake_bot = SimpleNamespace(db=object(), known_bases=lambda: {"ETH"}, ensure_user=lambda u: asyncio.sleep(0))
    monkeypatch.setattr(bot, "BOT", fake_bot)
    monkeypatch.setattr(bot, "apply_portfolio_trade", fake_apply)
    monkeypatch.setattr(bot, "portfolio_push", slow_push)
    monkeypatch.setattr(bot, "schedule_delete", lambda *a, **k: None)
    monkeypatch.setattr(bot, "msg_ref", lambda *a, **k: None)
    bot.PF_VIEWS[5] = {"chat_id": 1, "message_id": 9, "expires": 0, "page": 0}
    update = SimpleNamespace(effective_message=Msg(), effective_user=SimpleNamespace(id=5, username="x"))
    ctx = SimpleNamespace(bot=object(), user_data={})

    async def go():
        t0 = time.perf_counter()
        await bot.finish_trade(update, ctx, "buy", "ETH 500 usd")
        assert time.perf_counter() - t0 < .6               # concurrent, not .3 + .3
    run(go())
    bot.PF_VIEWS.pop(5, None)
    assert order.index("reply") < order.index("push-done")


# ---------------------------------------------------------------- measuring tools
def test_latency_stats_percentiles_and_slow_log():
    s = LatencyStats()
    for v in (.1, .2, .3, 4.0): s.record("x", v)
    out = s.summary("x")
    assert out["n"] == 4 and out["max"] == 4.0 and out["p50"] == pytest.approx(.25)
    assert len(s.slow) == 1 and s.slow[0][1] == "x"
    assert s.summary("missing") is None


def test_timed_wrapper_records_even_on_error():
    s = LatencyStats()

    async def boom(): raise RuntimeError("x")

    async def go():
        with pytest.raises(RuntimeError): await s.timed("boom", boom)()
    run(go())
    assert s.summary("boom")["n"] == 1


def test_loop_lag_probe_sees_a_blocked_event_loop():
    s = LatencyStats()

    async def go():
        task = asyncio.create_task(loop_lag_probe(s, interval=.05))
        await asyncio.sleep(.01); time.sleep(.25)          # simulate CPU work blocking the loop
        await asyncio.sleep(.15); task.cancel()
    run(go())
    assert s.loop_lag_max > .1
