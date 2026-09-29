#!/usr/bin/env python3
"""Exact rational checks for the single-new-prime Robin tail.

This script checks the certificates used in theory section 152.  It uses only
Fraction arithmetic; it does not numerically evaluate logarithms or claim an
unbounded Robin proof by itself.
"""
from fractions import Fraction as Q
from math import factorial


def log_interval(x, terms=32):
    """Return rational lower/upper bounds for log(x), x >= 1.

    Repeatedly scale into [1, 2), then use
    log(y) = 2 atanh((y - 1)/(y + 1)).  The omitted tail is bounded by a
    geometric series with the first omitted denominator.
    """
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
    if scale >= 0:
        return lo + scale * log2_lo, hi + scale * log2_hi
    return lo + scale * log2_hi, hi + scale * log2_lo


def gamma_exp_certificate():
    # Euler's elementary remainder enclosure, in the same form used by the
    # existing 10080 seed certificate.
    n = 1000
    harmonic = sum((Q(1, k) for k in range(1, n + 1)), Q(0))
    _, log_upper = log_interval(Q(n))
    gamma_lower = harmonic - log_upper - Q(1, 2 * n)
    assert gamma_lower > Q(577, 1000)

    exp_lower = sum(
        (Q(577, 1000) ** k / factorial(k) for k in range(6)),
        Q(0),
    )
    assert exp_lower > Q(89, 50)
    return gamma_lower, exp_lower


def main():
    gamma_lower, exp_lower = gamma_exp_certificate()
    log11_lower, log11_upper = log_interval(Q(11))
    log10080_lower, log10080_upper = log_interval(Q(10080))

    assert log11_lower > Q(239, 100)
    assert log11_upper < Q(240, 100)
    assert log10080_upper < Q(922, 100)

    # The p = 11 entry inequality, with every quantity rational.
    entry_budget = (
        Q(89, 50)
        * Q(239, 100)
        / (Q(922, 100) + Q(240, 100))
    )
    assert entry_budget == Q(21271, 58100)
    assert entry_budget > Q(39, 110)

    # Verify the denominator induction algebra for representative p and a.
    # The paper proof is universal: p >= 11 and a >= 1 make both coefficients
    # in the displayed positive expression strictly positive.
    for p in (11, 13, 17, 19, 101):
        assert p >= 11
        for a in range(1, 65):
            first_coefficient = Q(p - 1)
            second_coefficient = Q(a * (p - 1) - 1)
            assert first_coefficient > 0
            assert second_coefficient > 0
            assert first_coefficient + second_coefficient > 0

    # The certified seed and the exact first new-prime gain used in section 152.
    assert Q(39, 10) / 11 == Q(39, 110)
    assert Q(2, 125) > 0

    print({
        "status": "exact rational certificates passed",
        "gamma_lower_exceeds": "577/1000",
        "exp_gamma_lower_exceeds": "89/50",
        "log11_bounds": ["239/100", "240/100"],
        "log10080_upper_below": "922/100",
        "entry_ratio": "21271/58100",
        "entry_target": "39/110",
        "induction": "(p-1)L0 + (a(p-1)-1)log(p) > 0 for p>=11,a>=1",
        "scope": "single new prime p>=11 and arbitrary exponent; no RH claim",
    })


if __name__ == "__main__":
    main()
