import asyncio

import pytest

import bot

KNOWN = {"BTC", "ETH", "SOL", "SUI", "LTC", "PEPE"}


def parse(text):
    return bot.parse_trade_text(text, KNOWN)


# ---------------------------------------------------------------- parsing
@pytest.mark.parametrize("text", ["ETH 500 usd", "ETH 500 USD", "eth 500usd", "ETH 500 usdt", "ETH $500", "$500 eth", "ETH 500$",
                                  "ETH 500 dollar", "ETH 500 ডলার", "৫০০ ডলারের ETH", "ইথেরিয়াম ৫০০ ডলার", "bought $500 of eth"])
def test_dollar_amount_in_many_spellings(text):
    assert parse(text) == {"symbol": "ETH/USDT", "qty": None, "price": None, "usd": 500.0}


def test_dollar_amount_with_own_price_and_thousands_separator():
    assert parse("ETH 500 usd 2000") == {"symbol": "ETH/USDT", "qty": None, "price": 2000.0, "usd": 500.0}
    assert parse("ETH 1,500 usd")["usd"] == 1500.0


def test_quantity_wording_is_unchanged():
    assert parse("ETH 0.5 2000") == {"symbol": "ETH/USDT", "qty": 0.5, "price": 2000.0, "usd": None}
    assert parse("eth 0.5")["qty"] == 0.5
    assert parse("ETH all") == {"symbol": "ETH/USDT", "qty": None, "price": None, "usd": None}


def test_currency_word_after_the_price_only_decorates_it():
    # first number is the quantity, so this is 0.5 ETH at 2000 - not "spend $2000"
    for text in ("ETH 0.5 2000 usd", "ETH 0.5 2000 usdt"):
        assert parse(text) == {"symbol": "ETH/USDT", "qty": 0.5, "price": 2000.0, "usd": None}


def test_cash_usdt_still_works():
    for text in ("USDT 100", "100 usdt"):
        assert parse(text) == {"symbol": "USDT/USDT", "qty": 100.0, "price": 1.0, "usd": None}


@pytest.mark.parametrize("text", ["ETH 0 usd", "ETH 500 usd all", "$100"])
def test_bad_dollar_input_is_explained(text):
    with pytest.raises(ValueError):
        parse(text)


# ---------------------------------------------------------------- recording (fake database, fixed live price)
class FakeCon:
    def __init__(self, store): self.store = store

    def transaction(self):
        class Tx:
            async def __aenter__(self_): return None
            async def __aexit__(self_, *a): return False
        return Tx()

    async def fetchrow(self, sql, uid, symbol): return self.store.get((uid, symbol))

    async def execute(self, sql, uid, symbol, qty, avg, realized): self.store[(uid, symbol)] = {"qty": qty, "avg_price": avg, "realized": realized}


class FakeDB:
    def __init__(self): self.store = {}

    def acquire(self):
        outer = self

        class Ctx:
            async def __aenter__(self_): return FakeCon(outer.store)
            async def __aexit__(self_, *a): return False
        return Ctx()


@pytest.fixture
def pf():
    b = object.__new__(bot.AnalystBot)
    b.db = FakeDB(); b.live = 2000.0

    async def live_price(symbol): return {"price": b.live}
    b.fetch_live_price = live_price
    old, bot.BOT = bot.BOT, b
    yield b
    bot.BOT = old


def trade(side, text):
    parsed = bot.parse_trade_text(text, KNOWN)
    return asyncio.run(bot.apply_portfolio_trade(1, side, parsed["symbol"], parsed["qty"], parsed["price"], parsed.get("usd")))


def test_buy_with_dollars_uses_the_live_price(pf):
    msg = trade("buy", "ETH 500 usd")
    pos = pf.db.store[(1, "ETH/USDT")]
    assert pos["qty"] == pytest.approx(0.25) and pos["avg_price"] == pytest.approx(2000)
    assert "$500.00 ÷ 2000 = 0.25 ETH" in msg and "Buy 0.25 ETH @ 2000" in msg


def test_buy_with_dollars_at_own_price(pf):
    trade("buy", "ETH 500 usd 2500")
    assert pf.db.store[(1, "ETH/USDT")]["qty"] == pytest.approx(0.2)


def test_second_buy_averages_the_price(pf):
    trade("buy", "ETH 500 usd")                      # 0.25 ETH @ 2000
    pf.live = 4000.0
    trade("buy", "ETH 1000 usd")                     # 0.25 ETH @ 4000
    pos = pf.db.store[(1, "ETH/USDT")]
    assert pos["qty"] == pytest.approx(0.5) and pos["avg_price"] == pytest.approx(3000)


def test_sell_with_dollars_books_the_profit(pf):
    trade("buy", "ETH 500 usd")                      # 0.25 ETH @ 2000
    pf.live = 2200.0
    msg = trade("sell", "ETH 220 usd")               # 0.1 ETH @ 2200 -> +20 USDT
    pos = pf.db.store[(1, "ETH/USDT")]
    assert pos["qty"] == pytest.approx(0.15) and pos["realized"] == pytest.approx(20)
    assert "+20.00 USDT" in msg and "$220.00 ÷ 2200 = 0.1 ETH" in msg


def test_selling_more_dollars_than_held_is_rejected(pf):
    trade("buy", "ETH 500 usd")                      # holds $500 worth
    with pytest.raises(bot.UserInputError):
        trade("sell", "ETH 1000 usd")
    assert pf.db.store[(1, "ETH/USDT")]["qty"] == pytest.approx(0.25)     # nothing was recorded


def test_quantity_buy_and_cash_unchanged(pf):
    trade("buy", "ETH 0.5 2000")
    assert pf.db.store[(1, "ETH/USDT")]["qty"] == 0.5
    trade("buy", "USDT 100")
    assert pf.db.store[(1, "USDT/USDT")]["qty"] == 100


# ---------------------------------------------------------------- the prompts show both ways, with examples
def test_prompts_show_both_ways_with_examples():
    buy, sell = bot.trade_prompt("buy"), bot.trade_prompt("sell")
    assert "ETH 0.5 2000" in buy and "ETH 500 usd" in buy and "USDT 100" in buy and "cancel" in buy
    assert "ETH 0.2 2100" in sell and "ETH 200 usd" in sell and "ETH all" in sell and "cancel" in sell
