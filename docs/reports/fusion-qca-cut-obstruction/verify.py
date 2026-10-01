#!/usr/bin/env python3
"""Exact arithmetic diagnostics; not a proof of operator-algebra/DHR claims."""
from itertools import product
import json
from math import prod


def fib(n: int) -> int:
    if not isinstance(n, int) or n < 0:
        raise ValueError("Fibonacci index must be a nonnegative integer")
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def dim_end(n: int) -> int:
    if not isinstance(n, int) or n < 1:
        raise ValueError("tensor length must be a positive integer")
    return fib(n - 1) ** 2 + fib(n) ** 2


def run() -> dict:
    counts = {"fusion_dimensions": 0, "offset_identity": 0,
              "balanced_multilayer": 0, "ordinary_ancilla": 0}
    for n in range(1, 151):
        assert dim_end(n) == fib(2 * n - 1), ("dimension", n)
        counts["fusion_dimensions"] += 1
    for k in range(-20, 21):
        for n in range(abs(k) + 1, 151):
            delta = dim_end(n+k) * dim_end(n-k) - dim_end(n)**2
            assert delta == fib(2 * abs(k))**2, ("offset", n, k)
            assert (delta > 0) == (k != 0), ("strictness", n, k)
            counts["offset_identity"] += 1
    vector_counts = {}
    for m in range(2, 6):
        vector_counts[str(m)] = 0
        for ks in product(range(-2, 3), repeat=m):
            if sum(ks) != 0 or not any(ks):
                continue
            vector_counts[str(m)] += 1
            n0 = 1 + max(abs(k) for k in ks)
            for n in (n0, n0 + 7):
                assert prod(dim_end(n+k) for k in ks) > dim_end(n)**m, (m, ks, n)
                counts["balanced_multilayer"] += 1
    for q in range(1, 6):
        for k in range(1, 5):
            for n in range(k+1, 26):
                left = q**(2*n) * dim_end(n+k) * dim_end(n-k)
                right = q**(2*n) * dim_end(n)**2
                assert left - right == q**(2*n) * fib(2*k)**2
                counts["ordinary_ancilla"] += 1
    examples = [{"n": n, "identity": dim_end(n)**2,
                 "countershift": dim_end(n+1)*dim_end(n-1),
                 "difference": 1} for n in range(2, 7)]
    return {"status": "passed", "arithmetic": "exact Python integers",
            "case_counts": counts, "total_cases": sum(counts.values()),
            "balanced_vector_counts": vector_counts, "examples": examples,
            "scope": "Finite arithmetic diagnostics only. No Lean, DHR, von Neumann algebra or FDQC verification."}


if __name__ == "__main__":
    print(json.dumps(run(), ensure_ascii=False, indent=2))
