"""Tiny latency recorder: how long handlers, DB and exchange calls really take in production.

Kept dependency-free so it can be unit-tested and shown by /health without extra services.
"""
from __future__ import annotations

import asyncio
import statistics
import time
from collections import defaultdict, deque
from typing import Any, Awaitable, Callable

SLOW_SECONDS = 3.0


class LatencyStats:
    def __init__(self, keep: int = 200) -> None:
        self._samples: dict[str, deque[float]] = defaultdict(lambda: deque(maxlen=keep))
        self.slow: deque[tuple[float, str, float]] = deque(maxlen=20)   # (unix time, name, seconds)
        self.loop_lag_max = 0.0
        self.loop_lag_last = 0.0

    def record(self, name: str, seconds: float) -> None:
        self._samples[name].append(seconds)
        if seconds >= SLOW_SECONDS: self.slow.append((time.time(), name, seconds))

    def summary(self, name: str) -> dict[str, float] | None:
        data = sorted(self._samples.get(name, ()))
        if not data: return None
        p95 = data[min(len(data) - 1, int(len(data) * 0.95))]
        return {"n": len(data), "p50": statistics.median(data), "p95": p95, "max": data[-1]}

    def names(self) -> list[str]:
        return sorted(self._samples)

    def timed(self, name: str, fn: Callable[..., Awaitable[Any]]) -> Callable[..., Awaitable[Any]]:
        async def wrapper(*args: Any, **kwargs: Any) -> Any:
            start = time.perf_counter()
            try: return await fn(*args, **kwargs)
            finally: self.record(name, time.perf_counter() - start)
        wrapper.__name__ = getattr(fn, "__name__", name)
        return wrapper

    def note_loop_lag(self, lag: float) -> None:
        self.loop_lag_last = lag
        self.loop_lag_max = max(self.loop_lag_max * 0.98, lag)   # slow decay so one old spike does not stick forever


async def loop_lag_probe(stats: LatencyStats, interval: float = 1.0) -> None:
    """If the event loop is blocked by CPU work, this sleep wakes up late; the lateness is the lag every user feels."""
    while True:
        start = time.perf_counter()
        await asyncio.sleep(interval)
        stats.note_loop_lag(max(0.0, time.perf_counter() - start - interval))


def fmt(summary: dict[str, float] | None) -> str:
    if not summary: return "—"
    return f"p50 {summary['p50']*1000:.0f}ms · p95 {summary['p95']*1000:.0f}ms · max {summary['max']*1000:.0f}ms (n={summary['n']})"
