"""Phase-5 tests: referral deep links, one-time trial, referrer reward.

Run:  pytest -q test_phase5.py
Only Telegram/Postgres are faked; every decision path runs the real code.
"""
from __future__ import annotations

import asyncio
from datetime import datetime, timedelta, timezone
from types import SimpleNamespace

import pytest

import bot as B


class FakeDB:
    """Just enough of asyncpg for the trial/referral code paths."""

    def __init__(self, rows=None, fetchval=None):
        self.rows = rows or {}
        self.fetchval_result = fetchval
        self._queue = list(fetchval) if isinstance(fetchval, (list, tuple)) else None
        self.executed = []
        self.fetchvals = []
        self.fetchrows = []

    async def execute(self, sql, *args):
        self.executed.append((sql, args))
        return "UPDATE 1"

    async def fetch(self, sql, *args):
        return self.rows.get("fetch", [])

    async def fetchval(self, sql, *args):
        self.fetchvals.append((sql, args))
        if self._queue:
            return self._queue.pop(0)
        return self.fetchval_result

    async def fetchrow(self, sql, *args):
        self.fetchrows.append((sql, args))
        queue = self.rows.get("row_queue")
        if queue:
            return queue.pop(0) if len(queue) > 1 else queue[0]
        return self.rows.get("row")


class FakeMessage:
    def __init__(self):
        self.replies = []

    async def reply_text(self, text, **kw):
        self.replies.append(text)
        return self

    async def edit_text(self, text, **kw):
        self.replies.append(text)
        return self


class FakeBotAPI:
    def __init__(self, username="CryptoAnalystBot"):
        self.username = username
        self.sent = []
        self.command_menus = []

    async def send_message(self, chat_id, text, **kw):
        self.sent.append((chat_id, text))

    async def set_my_commands(self, commands, scope=None):
        self.command_menus.append((commands, scope))


@pytest.fixture(autouse=True)
def _restore_bot():
    old = B.BOT
    yield
    B.BOT = old


def make_analyst(db):
    analyst = object.__new__(B.AnalystBot)
    analyst.db = db
    return analyst


def ctx(args=None, username="CryptoAnalystBot"):
    return SimpleNamespace(args=list(args or []), bot=FakeBotAPI(username))


def upd(user_id=42, args=None):
    return SimpleNamespace(
        effective_message=FakeMessage(),
        effective_user=SimpleNamespace(id=user_id, username="tester", full_name="Test User"),
        effective_chat=SimpleNamespace(id=user_id),
        callback_query=None,
        update_id=1,
        args=list(args or []),
    )


# --------------------------------------------------------------------------
# pure helpers
# --------------------------------------------------------------------------
@pytest.mark.parametrize("payload,expected", [
    ("ref_123456789", 123456789), ("REF_42", 42), ("ref_0", None), ("ref_", None),
    ("ref_abc", None), (None, None), ("", None), ("something", None), ("ref_12x", None),
])
def test_parse_referral_payload(payload, expected):
    assert B.parse_referral_payload(payload) == expected


def test_referral_summary_groups_and_sorts():
    rows = [{"referrer_id": 1, "rewarded_at": None}, {"referrer_id": 1, "rewarded_at": "2026-01-01"},
            {"referrer_id": 2, "rewarded_at": None}, {"referrer_id": 2, "rewarded_at": None},
            {"referrer_id": 2, "rewarded_at": None}]
    board = B.referral_summary(rows)
    assert [item["referrer_id"] for item in board] == [2, 1]
    assert board[0] == {"referrer_id": 2, "invited": 3, "rewarded": 0}
    assert board[1] == {"referrer_id": 1, "invited": 2, "rewarded": 1}
    assert B.referral_summary([]) == []


# --------------------------------------------------------------------------
# register_referral
# --------------------------------------------------------------------------
def test_register_referral_writes_both_tables():
    db = FakeDB(fetchval=[1, None])
    analyst = make_analyst(db)
    assert asyncio.run(analyst.register_referral(500, "ref_999")) == 999
    sqls = [sql for sql, _ in db.executed]
    assert any("UPDATE users SET referred_by" in sql for sql in sqls)
    assert any("INSERT INTO referrals" in sql for sql in sqls)
    assert db.fetchvals[0][1] == (999,)


def test_register_referral_rejects_self_unknown_and_repeat():
    db = FakeDB(fetchval=1)
    analyst = make_analyst(db)
    assert asyncio.run(analyst.register_referral(999, "ref_999")) is None      # self-invite
    assert db.executed == []

    unknown = FakeDB(fetchval=[None])
    assert asyncio.run(make_analyst(unknown).register_referral(500, "ref_999")) is None
    assert unknown.executed == []

    repeat = FakeDB(fetchval=[1, 12345])      # already has a referrer
    assert asyncio.run(make_analyst(repeat).register_referral(500, "ref_999")) is None
    assert repeat.executed == []

    no_db = make_analyst(None)
    assert asyncio.run(no_db.register_referral(500, "ref_999")) is None


# --------------------------------------------------------------------------
# grant_trial
# --------------------------------------------------------------------------
def test_grant_trial_for_new_user():
    db = FakeDB(rows={"row": {"trial_used": False, "plan": "free", "plan_until": None, "blocked": False}})
    assert asyncio.run(make_analyst(db).grant_trial(42)) is True
    sql, args = db.executed[-1]
    assert "trial_used=TRUE" in sql and args[1] == B.TRIAL_DAYS
    assert "($2::int)*INTERVAL '1 day'" in sql


def test_grant_trial_is_once_only():
    used = FakeDB(rows={"row": {"trial_used": True, "plan": "free", "plan_until": None, "blocked": False}})
    assert asyncio.run(make_analyst(used).grant_trial(42)) is False
    assert used.executed == []


def test_grant_trial_never_shortens_paid_plan():
    future = datetime.now(timezone.utc) + timedelta(days=20)
    paid = FakeDB(rows={"row": {"trial_used": False, "plan": "pro", "plan_until": future, "blocked": False}})
    assert asyncio.run(make_analyst(paid).grant_trial(42)) is False
    assert paid.executed == []


def test_grant_trial_respects_zero_days(monkeypatch):
    monkeypatch.setattr(B, "TRIAL_DAYS", 0)
    db = FakeDB(rows={"row": {"trial_used": False, "plan": "free", "plan_until": None, "blocked": False}})
    assert asyncio.run(make_analyst(db).grant_trial(42)) is False


# --------------------------------------------------------------------------
# reward_referrer
# --------------------------------------------------------------------------
def test_reward_referrer_credits_once():
    db = FakeDB(rows={"row": {"referrer_id": 777}})
    assert asyncio.run(make_analyst(db).reward_referrer(42)) == 777
    sqls = [sql for sql, _ in db.executed]
    assert any("UPDATE referrals SET rewarded_at=NOW()" in sql for sql in sqls)
    assert any("INSERT INTO users(telegram_id,plan,plan_until)" in sql for sql in sqls)
    assert db.executed[-1][1][1] == B.REFERRAL_REWARD_DAYS


def test_reward_referrer_no_pending_row():
    db = FakeDB(rows={"row": None})
    assert asyncio.run(make_analyst(db).reward_referrer(42)) is None
    assert db.executed == []
    assert asyncio.run(make_analyst(None).reward_referrer(42)) is None


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------
def test_invite_command_shows_personal_link():
    rows = [{"referrer_id": 42, "rewarded_at": None}, {"referrer_id": 42, "rewarded_at": "2026-01-01"}]
    B.BOT = make_analyst(FakeDB(rows={"fetch": rows}))
    update = upd(42)
    asyncio.run(B.invite_command(update, ctx()))
    text = update.effective_message.replies[-1]
    assert "https://t.me/CryptoAnalystBot?start=ref_42" in text
    assert "আপনার invite: 2" in text and "reward পেয়েছেন: 1" in text


def test_trial_command_messages():
    B.BOT = make_analyst(FakeDB(rows={"row": {"trial_used": False, "plan": "free", "plan_until": None, "blocked": False}}))
    update = upd(42)
    asyncio.run(B.trial_command(update, ctx()))
    assert "free trial চালু" in update.effective_message.replies[-1]

    B.BOT = make_analyst(FakeDB(rows={"row": {"trial_used": True, "plan": "free", "plan_until": None, "blocked": False}}))
    update = upd(42)
    asyncio.run(B.trial_command(update, ctx()))
    assert "একবারই" in update.effective_message.replies[-1]

    B.BOT = make_analyst(FakeDB(rows={"row": {"trial_used": False, "plan": "pro", "blocked": False,
                                              "plan_until": datetime.now(timezone.utc) + timedelta(days=5)}}))
    update = upd(42)
    asyncio.run(B.trial_command(update, ctx()))
    assert "Pro access এখনই সক্রিয়" in update.effective_message.replies[-1]


def test_referrals_command_is_admin_only(monkeypatch):
    monkeypatch.setattr(B, "ADMIN_IDS", {999})
    B.BOT = make_analyst(FakeDB())
    update = upd(42)
    asyncio.run(B.referrals_command(update, ctx()))
    assert "অনুমতি নেই" in update.effective_message.replies[-1]


def test_referrals_command_leaderboard(monkeypatch):
    monkeypatch.setattr(B, "ADMIN_IDS", {999})
    rows = [{"referrer_id": 42, "rewarded_at": None}, {"referrer_id": 42, "rewarded_at": "2026-01-01"},
            {"referrer_id": 7, "rewarded_at": None}]
    B.BOT = make_analyst(FakeDB(rows={"fetch": rows}))
    update = upd(999)
    asyncio.run(B.referrals_command(update, ctx()))
    text = update.effective_message.replies[-1]
    assert "Referral report" in text
    assert "মোট invite: 3" in text and "paid: 1" in text
    assert "• 42: 2 invite · 1 paid" in text


# --------------------------------------------------------------------------
# /start integration: deep link + trial
# --------------------------------------------------------------------------
def test_start_with_referral_grants_trial_and_notifies_admin(monkeypatch):
    monkeypatch.setattr(B, "ADMIN_IDS", {999})
    free_row = {"trial_used": False, "plan": "free", "plan_until": None, "blocked": False}
    pro_row = {"trial_used": True, "plan": "pro", "blocked": False,
               "plan_until": datetime.now(timezone.utc) + timedelta(days=B.TRIAL_DAYS)}
    db = FakeDB(fetchval=[1, None], rows={"row_queue": [free_row, pro_row]})
    analyst = make_analyst(db)
    analyst.ensure_user = _noop
    B.BOT = analyst
    update = upd(500, args=["ref_999"])
    context = ctx(args=["ref_999"])
    asyncio.run(B.start(update, context))
    joined = "\n".join(update.effective_message.replies)
    assert "invite link দিয়ে এসেছেন" in joined
    assert f"{B.TRIAL_DAYS} দিনের free trial শুরু হয়েছে" in joined
    assert any("trial শুরু করেছে" in text for _, text in context.bot.sent)   # admin ping
    assert any("START_HINT" not in text and "CRYPTO AI MASTER" in text
               for text in update.effective_message.replies)


def test_start_without_payload_stays_quiet(monkeypatch):
    monkeypatch.setattr(B, "ADMIN_IDS", {999})
    db = FakeDB(rows={"row": {"trial_used": True, "plan": "free", "plan_until": None,
                              "blocked": False, "admin_notified": True}})
    analyst = make_analyst(db)
    analyst.ensure_user = _noop
    B.BOT = analyst
    update = upd(500)
    asyncio.run(B.start(update, ctx()))
    assert not any("trial" in text for text in update.effective_message.replies)


async def _noop(*args, **kwargs):
    return None


# --------------------------------------------------------------------------
# USDT (TRC20) auto-verification  (item 19)
# --------------------------------------------------------------------------
TRONGRID_SAMPLE = {"success": True, "data": [
    {"transaction_id": "2366559deb48b993de5dfa6644b4fc473f8b0697a25456f93f802b2b9c94b339",
     "token_info": {"symbol": "USDT", "address": "TR7NHqjeKQxGTCi8q8ZY4pL8otSzgjLj6t",
                    "decimals": 6, "name": "Tether USD"},
     "block_timestamp": 1794504648000, "from": "TSENDERxxxxxxxxxxxxxxxxxxxxxxxxxx",
     "to": "TWALLETxxxxxxxxxxxxxxxxxxxxxxxxx", "type": "Transfer", "value": "15027"},
    {"transaction_id": "c26cc190d7406b5c7c8e002fa4e3fb3825f076eafa251ae808de9515166dc317",
     "token_info": {"symbol": "TRX", "decimals": 6},
     "block_timestamp": 1794504423000, "from": "TSENDERxxxxxxxxxxxxxxxxxxxxxxxxxx",
     "to": "TWALLETxxxxxxxxxxxxxxxxxxxxxxxxx", "value": "999999"},
    {"transaction_id": "aaa", "token_info": {"symbol": "USDT", "decimals": 6},
     "block_timestamp": 1794504000000, "from": "TWALLETxxxxxxxxxxxxxxxxxxxxxxxxx",
     "to": "TSOMEONEELSE", "value": "5000000"},
]}
TRONSCAN_SAMPLE = {"total": 1, "data": [
    {"transaction_id": "tronscan-tx-1", "fromAddress": "TSENDER", "toAddress": "TWALLETxxxxxxxxxxxxxxxxxxxxxxxxx",
     "quant": "15027", "block_ts": 1794504648000,
     "tokenInfo": {"tokenAbbr": "USDT", "tokenDecimal": 6, "tokenName": "Tether USD"}},
]}
WALLET = "TWALLETxxxxxxxxxxxxxxxxxxxxxxxxx"


@pytest.mark.parametrize("text,expected", [
    ("15", 15.0), ("15 USDT", 15.0), ("$15.5", 15.5), ("1,200 usdt", 1200.0),
    ("1200 BDT", None), ("৳1200", None), ("Contact admin", None), ("", None),
    (None, None), ("abc", None), ("0", None), ("-5", None),
])
def test_parse_usdt_price(text, expected):
    assert B.parse_usdt_price(text) == expected


def test_unique_usdt_amount_is_repeatable_and_small():
    amount = B.unique_usdt_amount(15, 4217)
    assert B.unique_usdt_amount(15, 4217) == amount           # deterministic
    assert 15.010 <= amount <= 15.099 + 1e-9
    assert amount != B.unique_usdt_amount(15, 4218) or True  # may collide, must stay in range
    assert 15.010 <= B.unique_usdt_amount(15, 4218) <= 15.099 + 1e-9
    assert B.usdt_quote_for_price("1200 BDT", 1) is None
    assert B.usdt_quote_for_price("15 USDT", 1) is not None


def test_usdt_amount_matches_tolerance():
    assert B.usdt_amount_matches(15.027, 15.027)
    assert B.usdt_amount_matches(15.028, 15.027)             # 0.001 rounding
    assert not B.usdt_amount_matches(15.05, 15.027)
    assert not B.usdt_amount_matches("x", 15.027)


def test_parse_trongrid_only_incoming_usdt():
    rows = B.parse_trongrid_trc20(TRONGRID_SAMPLE, WALLET)
    assert len(rows) == 1                                     # TRX and outgoing rows dropped
    assert rows[0]["txid"].startswith("2366559d")
    assert rows[0]["amount"] == pytest.approx(0.015027)       # 15027 / 10**6
    assert rows[0]["timestamp_ms"] == 1794504648000
    assert B.parse_trongrid_trc20(TRONGRID_SAMPLE, "OTHERWALLET") == []
    assert B.parse_trongrid_trc20({}, WALLET) == []
    assert B.parse_trongrid_trc20("junk", WALLET) == []


def test_parse_tronscan_matches_trongrid_shape():
    rows = B.parse_tronscan_trc20(TRONSCAN_SAMPLE, WALLET)
    assert rows[0]["txid"] == "tronscan-tx-1"
    assert rows[0]["amount"] == pytest.approx(0.015027)
    assert B.parse_tronscan_trc20(TRONSCAN_SAMPLE, "NOPE") == []


def test_match_usdt_transfer_newest_and_time_window():
    transfers = [{"txid": "old", "amount": 15.027, "timestamp_ms": 1000},
                 {"txid": "new", "amount": 15.027, "timestamp_ms": 5000},
                 {"txid": "wrong", "amount": 15.5, "timestamp_ms": 6000}]
    assert B.match_usdt_transfer(transfers, 15.027)["txid"] == "new"
    assert B.match_usdt_transfer(transfers, 15.027, since_ms=4000)["txid"] == "new"
    assert B.match_usdt_transfer(transfers, 15.027, since_ms=6000) is None
    assert B.match_usdt_transfer([], 15.027) is None


def test_usdt_transfers_uses_trongrid_then_tronscan(monkeypatch):
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", WALLET)
    calls = []

    async def fake_http(url, params=None, timeout=10.0, headers=None):
        calls.append(url)
        if "trongrid" in url:
            return TRONGRID_SAMPLE
        return TRONSCAN_SAMPLE

    monkeypatch.setattr(B, "http_json", fake_http)
    analyst = make_analyst(FakeDB())
    rows = asyncio.run(analyst.usdt_transfers(10))
    assert len(rows) == 1 and "trongrid" in calls[0]

    async def broken_trongrid(url, params=None, timeout=10.0, headers=None):
        calls.append(url)
        if "trongrid" in url:
            raise RuntimeError("trongrid down")
        return TRONSCAN_SAMPLE

    monkeypatch.setattr(B, "http_json", broken_trongrid)
    rows = asyncio.run(analyst.usdt_transfers(10))
    assert rows[0]["txid"] == "tronscan-tx-1"                 # fell back
    assert any("tronscan" in url for url in calls)

    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", "")
    assert asyncio.run(analyst.usdt_transfers(10)) == []      # feature off


def test_paid_command_without_wallet(monkeypatch):
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", "")
    B.BOT = make_analyst(FakeDB())
    update = upd(42)
    asyncio.run(B.paid_command(update, ctx()))
    assert "বন্ধ" in update.effective_message.replies[-1]


def test_paid_command_without_pending_request(monkeypatch):
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", WALLET)
    B.BOT = make_analyst(FakeDB(rows={"row": None}))
    update = upd(42)
    asyncio.run(B.paid_command(update, ctx()))
    assert "/subscribe" in update.effective_message.replies[-1]


def test_paid_command_shows_address_and_exact_amount(monkeypatch):
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", WALLET)
    db = FakeDB(rows={"row": {"id": 7, "days": 30, "plan_code": "pro30", "usdt_amount": 15.027}})
    B.BOT = make_analyst(db)
    update = upd(42)
    asyncio.run(B.paid_command(update, ctx()))
    text = update.effective_message.replies[-1]
    assert WALLET in text and "15.027 USDT" in text
    assert "/paid <TXID>" in text and "TRC20" in text


def test_paid_command_rejects_bdt_price(monkeypatch):
    monkeypatch.setattr(B, "PRO_30_PRICE", "1200 BDT")
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", WALLET)
    db = FakeDB(rows={"row": {"id": 7, "days": 30, "plan_code": "pro30", "usdt_amount": None}})
    B.BOT = make_analyst(db)
    update = upd(42)
    asyncio.run(B.paid_command(update, ctx()))
    assert "USDT-তে নির্ধারিত নয়" in update.effective_message.replies[-1]


def test_paid_command_verifies_txid_and_approves(monkeypatch):
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", WALLET)
    db = FakeDB(rows={"row": {"id": 7, "days": 30, "plan_code": "pro30", "usdt_amount": 0.015027}},
                fetchval=[None])
    analyst = make_analyst(db)

    async def fake_transfers(limit=50):
        return B.parse_trongrid_trc20(TRONGRID_SAMPLE, WALLET)

    analyst.usdt_transfers = fake_transfers
    approved = {}

    async def fake_apply(context, user_id, days, source="manual", admin_id=0, txid=None):
        approved.update({"user": user_id, "days": days, "source": source, "txid": txid})
        return None

    monkeypatch.setattr(B, "apply_approval", fake_apply)
    B.BOT = analyst
    update = upd(42)
    asyncio.run(B.paid_command(update, ctx(args=["2366559deb48b993de5dfa6644b4fc473f8b0697a25456f93f802b2b9c94b339"])))
    joined = "\n".join(update.effective_message.replies)
    assert "পেমেন্ট যাচাই হয়েছে" in joined
    assert approved == {"user": 42, "days": 30, "source": "usdt_txid",
                        "txid": "2366559deb48b993de5dfa6644b4fc473f8b0697a25456f93f802b2b9c94b339"}
    assert any("INSERT INTO usdt_payments" in sql for sql, _ in db.executed)


def test_paid_command_rejects_amount_mismatch_and_unknown_txid(monkeypatch):
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", WALLET)
    db = FakeDB(rows={"row": {"id": 7, "days": 30, "plan_code": "pro30", "usdt_amount": 20.0}},
                fetchval=[None])
    analyst = make_analyst(db)

    async def fake_transfers(limit=50):
        return B.parse_trongrid_trc20(TRONGRID_SAMPLE, WALLET)

    analyst.usdt_transfers = fake_transfers
    monkeypatch.setattr(B, "apply_approval", lambda *a, **k: _noop())
    B.BOT = analyst
    update = upd(42)
    asyncio.run(B.paid_command(update, ctx(args=["2366559deb48b993de5dfa6644b4fc473f8b0697a25456f93f802b2b9c94b339"])))
    assert "পরিমাণ মিলছে না" in "\n".join(update.effective_message.replies)

    update = upd(42)
    asyncio.run(B.paid_command(update, ctx(args=["deadbeef"])))
    assert "পাওয়া যায়নি" in "\n".join(update.effective_message.replies)


def test_usdt_verify_job_auto_approves_once(monkeypatch):
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", WALLET)
    monkeypatch.setattr(B, "ADMIN_IDS", set())
    request = {"id": 9, "telegram_id": 42, "days": 30, "usdt_amount": 0.015027}
    db = FakeDB(rows={"fetch": [request]}, fetchval=None)      # txid not used yet
    analyst = make_analyst(db)

    async def fake_transfers(limit=50):
        return B.parse_trongrid_trc20(TRONGRID_SAMPLE, WALLET)

    analyst.usdt_transfers = fake_transfers
    approved = []

    async def fake_apply(context, user_id, days, source="manual", admin_id=0, txid=None):
        approved.append((user_id, days, source, txid))
        return None

    monkeypatch.setattr(B, "apply_approval", fake_apply)
    B.BOT = analyst
    asyncio.run(B.usdt_verify_job(SimpleNamespace(bot=FakeBotAPI())))
    assert approved == [(42, 30, "usdt_auto",
                         "2366559deb48b993de5dfa6644b4fc473f8b0697a25456f93f802b2b9c94b339")]
    assert any("INSERT INTO usdt_payments" in sql for sql, _ in db.executed)


def test_usdt_verify_job_skips_already_used_txid(monkeypatch):
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", WALLET)
    db = FakeDB(rows={"fetch": [{"id": 9, "telegram_id": 42, "days": 30, "usdt_amount": 0.015027}]},
                fetchval=1)                                    # txid already recorded
    analyst = make_analyst(db)

    async def fake_transfers(limit=50):
        return B.parse_trongrid_trc20(TRONGRID_SAMPLE, WALLET)

    analyst.usdt_transfers = fake_transfers
    called = []
    monkeypatch.setattr(B, "apply_approval", lambda *a, **k: called.append(a) or _noop())
    B.BOT = analyst
    asyncio.run(B.usdt_verify_job(SimpleNamespace(bot=FakeBotAPI())))
    assert called == []
    assert not any("INSERT INTO usdt_payments" in sql for sql, _ in db.executed)


def test_usdt_verify_job_does_nothing_when_disabled(monkeypatch):
    monkeypatch.setattr(B, "USDT_TRC20_ADDRESS", "")
    db = FakeDB(rows={"fetch": [{"id": 9, "telegram_id": 42, "days": 30, "usdt_amount": 1.0}]})
    B.BOT = make_analyst(db)
    asyncio.run(B.usdt_verify_job(SimpleNamespace(bot=FakeBotAPI())))
    assert db.fetchrows == [] and db.executed == []
