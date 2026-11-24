import asyncio
import io

import numpy as np
import pandas as pd
from PIL import Image

import bot


def make_frame(n=260):
    rng = np.random.default_rng(3)
    idx = pd.date_range("2026-01-01", periods=n, freq="4h", tz="UTC")
    close = 100 + np.cumsum(rng.normal(0, 1, n))
    df = pd.DataFrame({"Open": close - .3, "High": close + 1, "Low": close - 1, "Close": close, "Volume": rng.uniform(900, 1500, n)}, index=idx)
    df.attrs["source"] = "binance"
    return bot.add_indicators(df)


def make_result(frame):
    q = bot.quant_snapshot(frame)
    return {"supports": [z["price"] for z in q["supports"]], "resistances": [z["price"] for z in q["resistances"]], "trendlines": q["trendlines"], "quant": q}


def corner_brightness(png: io.BytesIO) -> int:
    img = Image.open(png).convert("RGB")
    assert img.size == (bot.TV_W, bot.TV_H)
    return sum(img.getpixel((bot.TV_W - 3, bot.TV_H - 3)))     # empty corner of the time strip: pure canvas colour


def render(theme, overlays=False):
    frame = make_frame()
    return bot.tv_chart(frame, bot.Request("BTC/USDT", "4h", view_candles=150), make_result(frame), overlays, theme)


def test_dark_and_paper_render_with_their_own_canvas():
    dark, paper = corner_brightness(render("dark")), corner_brightness(render("paper"))
    assert dark < 200 < 600 < paper          # dark navy canvas vs pale-yellow canvas, independent of the server default


def test_unknown_or_missing_theme_falls_back_to_server_default():
    assert bot.chart_theme_name(None) == bot.CHART_THEME
    assert bot.chart_theme_name("") == bot.CHART_THEME
    assert bot.chart_theme_name("neon") == bot.CHART_THEME
    assert bot.chart_theme_name("paper") == "paper"
    assert corner_brightness(render("neon")) == corner_brightness(render(None))


def test_smart_zones_overlay_follows_theme():
    for theme in ("dark", "paper"):
        assert render(theme, overlays=True).getbuffer().nbytes > 20000


def test_themes_do_not_leak_between_renders():
    first = corner_brightness(render("paper")); corner_brightness(render("dark")); again = corner_brightness(render("paper"))
    assert first == again


def test_async_render_takes_theme():
    frame = make_frame(); result = make_result(frame)
    request = bot.Request("BTC/USDT", "4h", view_candles=150)

    async def both():
        return await asyncio.gather(*[bot.AnalystBot.chart_async(frame, request, result, theme=t) for t in ("dark", "paper")])

    dark, paper = asyncio.run(both())           # two users with different themes rendering at the same time
    assert corner_brightness(dark) < corner_brightness(paper)


def test_settings_keyboard_offers_both_themes():
    data = {b.callback_data for row in bot.settings_keyboard().inline_keyboard for b in row}
    assert {"set|chart_theme|dark", "set|chart_theme|paper"} <= data


# ---------------------------------------------------------------- zone rectangles are hidden by default, kept in code
def _wide_rectangles(boxes, monkeypatch, overlays):
    import matplotlib.axes
    monkeypatch.setattr(bot, "CHART_ZONE_BOXES", boxes)
    seen, orig = [], matplotlib.axes.Axes.add_patch

    def spy(self, patch):
        if patch.__class__.__name__ == "Rectangle" and patch.get_width() > 5 and patch.get_height() > 0: seen.append(patch)
        return orig(self, patch)
    monkeypatch.setattr(matplotlib.axes.Axes, "add_patch", spy)
    frame = make_frame()
    res = make_result(frame)
    q = res["quant"]
    res["support_zones"], res["resistance_zones"] = q["supports"], q["resistances"]
    bot.tv_chart(frame, bot.Request("BTC/USDT", "4h", view_candles=150), res, overlays)
    return seen


def test_zone_rectangles_hidden_by_default(monkeypatch):
    assert not bot.CHART_ZONE_BOXES
    assert _wide_rectangles(False, monkeypatch, True) == []


def test_zone_rectangles_return_with_the_switch(monkeypatch):
    assert len(_wide_rectangles(True, monkeypatch, False)) >= 1
