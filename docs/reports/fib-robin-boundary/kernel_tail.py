#!/usr/bin/env python3
"""Exact checks for the five-direction Robin support kernel in theory §155.

All sign decisions use Fraction arithmetic.  The logarithms are bounded by the
atanh series with an explicit geometric tail; Euler's constant is bounded by
the standard harmonic-number remainder.  This is a finite certificate for the
stated kernel and support budget, not a proof of Robin's inequality in general
and not a proof of RH.
"""

from fractions import Fraction as Q
from math import factorial


KERNEL = 2**21 * 3**13 * 5**9 * 7**7 * 11**6
Z_UPPER = Q(77, 16)
DELTA_LOWER = Q(5327, 2000)
SUPPORT_THRESHOLD = Q(2136, 1375)
TERMS = 32


def log_interval(x, terms=TERMS):
    """Return rational lower and upper bounds for log(x), x >= 1."""
    assert x >= 1
    scale = 0
    while x >= 2:
        x /= 2
        scale += 1

    def reduced(y):
        z = (y - 1) / (y + 1)
        partial = 2 * sum(
            (z ** (2 * k + 1) / Q(2 * k + 1) for k in range(terms)),
            Q(0),
        )
        tail = 2 * z ** (2 * terms + 1) / (
            Q(2 * terms + 1) * (1 - z * z)
        )
        return partial, partial + tail

    lo, hi = reduced(x)
    log2_lo, log2_hi = reduced(Q(2))
    return lo + scale * log2_lo, hi + scale * log2_hi


def exp_gamma_lower():
    """A rational lower bound exceeding 89/50 for exp(gamma)."""
    n = 1000
    harmonic = sum((Q(1, k) for k in range(1, n + 1)), Q(0))
    _, log_upper = log_interval(Q(n))
    gamma_lower = harmonic - log_upper - Q(1, 2 * n)
    assert gamma_lower > Q(577, 1000)
    value = sum(
        (Q(577, 1000) ** k / factorial(k) for k in range(6)),
        Q(0),
    )
    assert value > Q(89, 50)
    return gamma_lower, value


def is_prime(n):
    if n < 2:
        return False
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            return n == divisor
        divisor += 1
    return True


def support_product(primes):
    assert len(set(primes)) == len(primes)
    value = Q(1)
    for p in primes:
        assert p >= 13 and is_prime(p)
        value *= Q(p, p - 1)
    return value


def main():
    assert KERNEL == 9527493263501079465984000000000
    assert Q(77, 16) == Q(2) * Q(3, 2) * Q(5, 4) * Q(7, 6) * Q(11, 10)

    log_kernel_lower, _ = log_interval(Q(KERNEL))
    log71_lower, _ = log_interval(Q(71))
    assert log_kernel_lower > Q(71)
    assert log71_lower > Q(21, 5)
    _, exp_lower = exp_gamma_lower()
    assert exp_lower > Q(89, 50)

    # The rational lower margin in (155.3).
    assert Q(89, 50) * Q(21, 5) - Z_UPPER == DELTA_LOWER
    assert DELTA_LOWER > 0

    worst_twelve = (13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59)
    worst_thirteen = worst_twelve + (61,)
    twelve = support_product(worst_twelve)
    thirteen = support_product(worst_thirteen)
    assert twelve == Q(95993978542907, 61802702438400)
    assert twelve < SUPPORT_THRESHOLD
    assert thirteen == Q(5855632691117327, 3708162146304000)
    assert thirteen > SUPPORT_THRESHOLD

    margin = DELTA_LOWER - Z_UPPER * (twelve - 1)
    assert margin == Q(68552407001, 64210599936000)
    assert margin > 0
    assert SUPPORT_THRESHOLD - twelve == Q(68552407001, 309013512192000)

    # The support implication's rational endpoint is exact.
    assert DELTA_LOWER - Z_UPPER * (SUPPORT_THRESHOLD - 1) == 0

    print({
        "status": "exact rational five-direction kernel certificate passed",
        "kernel": str(KERNEL),
        "log_kernel_lower_exceeds": "71",
        "log71_lower_exceeds": "21/5",
        "exp_gamma_lower_exceeds": "89/50",
        "support_threshold": str(SUPPORT_THRESHOLD),
        "worst_twelve_product": str(twelve),
        "worst_twelve_margin_lower": str(margin),
        "worst_thirteen_product": str(thirteen),
        "scope": "fixed v2=21,v3=13,v5=9,v7=7,v11=6 kernel; distinct primes p>=13",
    })


if __name__ == "__main__":
    main()
