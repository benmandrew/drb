#!/usr/bin/env python3
"""Parse Go and Rust/criterion benchmark outputs and print a comparison table.

Usage:
    python3 bench/compare.py build/bench-go.txt build/bench-rust.txt
"""

import re
import sys
from typing import Optional


# ── Parsing ───────────────────────────────────────────────────────────────────

def to_ns(value: float, unit: str) -> float:
    u = unit.rstrip("/op").strip()
    match u:
        case "ns":             return value
        case "µs" | "us" | "μs": return value * 1_000
        case "ms":             return value * 1_000_000
        case "s":              return value * 1_000_000_000
        case _:                raise ValueError(f"unknown unit: {unit!r}")


def camel_to_snake(name: str) -> str:
    # "ContainsHit" → "contains_hit"
    s = re.sub(r"(?<=[a-z])(?=[A-Z])", "_", name)
    return s.lower()


def parse_go(text: str) -> dict[str, float]:
    """Parse standard Go benchmark output (ns/op lines only)."""
    results: dict[str, float] = {}
    for line in text.splitlines():
        # BenchmarkInsert-8    3056    1672141 ns/op    ...
        m = re.match(r"^Benchmark(\w+)-\d+\s+\d+\s+([\d.]+)\s+ns/op", line)
        if m:
            name = camel_to_snake(m.group(1))
            results[name] = float(m.group(2))
    return results


def parse_rust(text: str) -> dict[str, float]:
    """Parse criterion benchmark output (mean from the [lo mean hi] triple)."""
    results: dict[str, float] = {}
    for line in text.splitlines():
        # insert    time:   [1.118 ms 1.127 ms 1.142 ms]
        m = re.match(
            r"^(\w+)\s+time:\s+\[\S+\s+\S+\s+([\d.]+)\s+(\S+)\s+\S+\s+\S+\]",
            line,
        )
        if m:
            results[m.group(1)] = to_ns(float(m.group(2)), m.group(3))
    return results


# ── Formatting ────────────────────────────────────────────────────────────────

def fmt_ns(ns: float) -> str:
    if ns >= 1_000_000_000:
        return f"{ns / 1_000_000_000:.3f} s"
    if ns >= 1_000_000:
        return f"{ns / 1_000_000:.3f} ms"
    if ns >= 1_000:
        return f"{ns / 1_000:.1f} µs"
    return f"{ns:.1f} ns"


def fmt_ratio(go_ns: float, rust_ns: float) -> str:
    r = go_ns / rust_ns
    faster = "Go faster" if r < 1 else "Rust faster"
    return f"{r:.2f}× ({faster})"


# ── Table ─────────────────────────────────────────────────────────────────────

def print_table(go: dict[str, float], rust: dict[str, float]) -> None:
    names: list[str] = sorted(go.keys() | rust.keys())
    rows: list[tuple[str, str, str, str]] = []
    for name in names:
        g: Optional[float] = go.get(name)
        r: Optional[float] = rust.get(name)
        rows.append((
            name,
            fmt_ns(g) if g is not None else "—",
            fmt_ns(r) if r is not None else "—",
            fmt_ratio(g, r) if (g and r) else "—",
        ))
    headers: tuple[str, str, str, str] = ("Benchmark", "Go", "Rust", "Ratio")
    widths: list[int] = [
        max(len(headers[i]), max(len(row[i]) for row in rows))
        for i in range(4)
    ]

    def rule(seps: tuple[str, str, str]) -> str:
        l, m, r = seps
        return l + m.join("-" * w for w in widths) + r

    def row_line(cells: tuple[str, ...], aligns: str = "<<<<") -> str:
        parts: list[str] = []
        for cell, w, align in zip(cells, widths, aligns):
            parts.append(f" {cell:{align}{w}} ")
        return "|" + "|".join(parts) + "|"

    print(row_line(headers))
    print(rule(("|-", "-|-", "-|")))
    for row in rows:
        print(row_line(row, "<<>>"))


# ── Entry point ───────────────────────────────────────────────────────────────

def main() -> None:
    if len(sys.argv) != 3:
        print(f"usage: {sys.argv[0]} bench-go.txt bench-rust.txt", file=sys.stderr)
        sys.exit(1)
    with open(sys.argv[1]) as f:
        go: dict[str, float] = parse_go(f.read())
    with open(sys.argv[2]) as f:
        rust: dict[str, float] = parse_rust(f.read())
    if not go:
        print("warning: no Go benchmarks parsed", file=sys.stderr)
    if not rust:
        print("warning: no Rust benchmarks parsed", file=sys.stderr)
    print_table(go, rust)


if __name__ == "__main__":
    main()
