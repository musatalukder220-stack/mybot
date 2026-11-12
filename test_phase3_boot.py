"""Boot-path tests: post_init() really runs, so scheduling typos fail here.

This file exists because a real Railway boot died with
`TypeError: unbound method datetime.time() needs an argument` — compile-clean
code can still explode at startup, and only running post_init() catches it.
"""
from __future__ import annotations

import asyncio
from datetime import time as dt_time, timezone
from types import SimpleNamespace

import pytest

import bot as B


class FakeJobQueue:
    def __init__(self):
        self.repeating = []
        self.daily = []

    def run_repeating(self, callback, interval, first=None, name=None):
        self.repeating.append({"callback": callback, "interval": interval,
                               "first": first, "name": name})

    def run_daily(self, callback, time=None, name=None):
        self.daily.append({"callback": callback, "time": time, "name": name})


class FakeBot:
    def __init__(self):
        self.commands = []
        self.menu_button = None

    async def set_my_commands(self, commands, scope=None):
        self.commands.append((tuple(c.__class__.__name__ for c in commands), scope))

    async def set_chat_menu_button(self, menu_button=None):
        self.menu_button = menu_button


class FakeApplication:
    def __init__(self):
        self.bot = FakeBot()
        self.job_queue = FakeJobQueue()


@pytest.fixture(autouse=True)
def _restore():
    old = B.BOT
    yield
    B.BOT = old


def test_post_init_builds_every_scheduled_job(monkeypatch):
    monkeypatch.setattr(B, "ADMIN_IDS", {999})

    class FakeInstance:
        db = None

        async def init_db(self):
            self.inited = True

    B.BOT = FakeInstance()
    application = FakeApplication()

    asyncio.run(B.post_init(application))          # must not raise

    names = {job["name"] for job in application.job_queue.repeating}
    assert {"breakout-alert-monitor", "analyses-retention", "signal-scorecard",
            "usdt-auto-verify", "paper-trade-monitor", "channel-price-cards",
            "subscription-expiry"} <= names
    assert B.BOT.inited is True


def test_daily_report_job_is_scheduled_with_a_valid_time(monkeypatch):
    monkeypatch.setattr(B, "ADMIN_IDS", set())
    B.BOT = None
    application = FakeApplication()
    asyncio.run(B.post_init(application))
    daily = [job for job in application.job_queue.daily if job["name"] == "daily-market-report"]
    assert len(daily) == 1
    when = daily[0]["time"]
    assert isinstance(when, dt_time), f"run_daily needs a datetime.time, got {type(when)}"
    assert when.hour == B.DAILY_REPORT_UTC_HOUR and when.minute == 0
    assert when.tzinfo is timezone.utc
    assert daily[0]["callback"] is B.daily_report_job


def test_utc_hour_env_is_respected(monkeypatch):
    monkeypatch.setattr(B, "ADMIN_IDS", set())
    monkeypatch.setattr(B, "DAILY_REPORT_UTC_HOUR", 23)
    B.BOT = None
    application = FakeApplication()
    asyncio.run(B.post_init(application))
    when = [j["time"] for j in application.job_queue.daily if j["name"] == "daily-market-report"][0]
    assert when.hour == 23


def test_menu_commands_are_valid_telegram_commands():
    """Every BotCommand name must match Telegram's rules (lowercase, <=32 chars, no slash)."""
    from telegram import BotCommand
    import re
    seen = []
    for group in (B.PUBLIC_COMMANDS, B.PRO_COMMANDS, B.ADMIN_COMMANDS):
        for command in group:
            assert isinstance(command, BotCommand)
            seen.append(command.command)
    assert seen, "no commands registered"
    for name in seen:
        assert re.fullmatch(r"[a-z0-9_]{1,32}", name), f"invalid command name: {name}"
    # the new Phase 3-5 commands must be discoverable
    for expected in ("scorecard", "mtf", "level", "portfolio", "invite", "trial", "paid", "backtest"):
        assert expected in seen, f"{expected} missing from the command menus"


def test_handler_registration_references_real_functions():
    """Every handler in main() must point at a function that exists."""
    import inspect
    source = inspect.getsource(B.main)
    for name in ("start", "help_command", "paid_command", "trial_command", "invite_command",
                 "referrals_command", "report_command", "mtf_command", "scorecard_command",
                 "level_command", "portfolio_command", "backtest_command", "usdt_verify_job",
                 "daily_report_job", "scorecard_job", "check_price_levels"):
        assert hasattr(B, name), f"main() wires {name} but it does not exist"
        assert name in source or callable(getattr(B, name))
