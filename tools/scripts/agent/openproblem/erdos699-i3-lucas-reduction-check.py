#!/usr/bin/env python3
"""Exact bounded audit for the Erdős 699 i=3 Lucas reduction.

This is not a proof of Erdős 699 and not an exhaustive unbounded search.
It checks the direct range n <= 500 and the reduced Lucas candidates n <=
2_000_000 using exact integer arithmetic and a smallest-prime-factor sieve.
"""
from __future__ import annotations

from math import comb, gcd, isqrt


def lucas_nondivides(n: int, j: int, p: int) -> bool:
    """Return p ∤ binom(n,j) by Lucas' digit test."""
    while n or j:
        if j % p > n % p:
            return False
        n //= p
        j //= p
    return True


def make_spf(limit: int) -> list[int]:
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for x in range(p * p, limit + 1, p):
                if spf[x] == x:
                    spf[x] = p
    return spf


def distinct_factors(x: int, spf: list[int]) -> set[int]:
    factors: set[int] = set()
    while x > 1:
        p = spf[x]
        factors.add(p)
        while x % p == 0:
            x //= p
    return factors


def canonical(n: int) -> tuple[int, int]:
    x = n
    a = 0
    while x % 2 == 0:
        a += 1
        x //= 2
    b = 0
    while x % 3 == 0:
        b += 1
        x //= 3
    m = (1 << a) * (3 if b == 1 else 1)
    return m, n // m


def retained_core(x: int) -> int:
    while x % 2 == 0:
        x //= 2
    if x % 3 == 0:
        y = x // 3
        if y % 3 != 0:
            x = y
    return x


def direct_audit(limit: int = 500) -> int:
    checked = 0
    for n in range(8, limit + 1):
        c3 = comb(n, 3)
        for j in range(4, n // 2 + 1):
            checked += 1
            odd = gcd(c3, comb(n, j))
            while odd % 2 == 0:
                odd //= 2
            assert odd > 1, (n, j)
    return checked


def reduced_audit(limit: int = 2_000_000) -> int:
    spf = make_spf(limit)
    candidates = 0
    for n in range(8, limit + 1):
        m, u = canonical(n)
        for t in range(1, m // 2 + 1):
            j = t * u
            if j <= 3:
                continue
            candidates += 1
            primes = (
                distinct_factors(n, spf)
                | distinct_factors(n - 1, spf)
                | distinct_factors(n - 2, spf)
            )
            absent = True
            for p in primes:
                if p < 3:
                    continue
                exponent = 0
                for y in (n, n - 1, n - 2):
                    while y % p == 0:
                        exponent += 1
                        y //= p
                if exponent - (p == 3) > 0 and not lucas_nondivides(n, j, p):
                    absent = False
                    break
            assert not absent, (n, j, m, u, t)
    return candidates


if __name__ == "__main__":
    direct = direct_audit()
    reduced = reduced_audit()
    assert gcd(comb(10, 3), comb(10, 5)) == 12
    print(f"direct_checked={direct} reduced_candidates={reduced}")
