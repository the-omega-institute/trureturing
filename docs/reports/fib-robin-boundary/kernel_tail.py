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
GROWTH_TERMS = 20
GROWTH_SCALE = 10**12


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


def first_primes_at_least_13(count):
    result = []
    candidate = 13
    while len(result) < count:
        if is_prime(candidate):
            result.append(candidate)
        candidate += 1
    return result


def growth_log_interval(x, terms=GROWTH_TERMS):
    """A shorter exact interval used for the finite growing-support sweep."""
    return log_interval(x, terms)


def floor_to_scale(value, scale=GROWTH_SCALE):
    return Q((value * scale).numerator // (value * scale).denominator, scale)


def growth_lower_bounds(count):
    """Lower bounds for the growth-aware budget through ``count`` primes.

    The downward rounding keeps every cumulative log bound rational and below
    the true log.  It avoids printing the very large unreduced endpoint
    fractions while retaining exact sign comparisons.
    """
    primes = first_primes_at_least_13(count)
    log_product_lower = growth_log_interval(Q(KERNEL), GROWTH_TERMS)[0]
    support = Q(1)
    bounds = []
    for p in primes:
        log_product_lower = floor_to_scale(
            log_product_lower + growth_log_interval(Q(p), GROWTH_TERMS)[0]
        )
        support *= Q(p, p - 1)
        loglog_lower = growth_log_interval(log_product_lower, GROWTH_TERMS)[0]
        bounds.append(Q(89, 50) * loglog_lower - Z_UPPER * support)
    return primes, bounds


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

    # Incorporating the mandatory factor p into N extends the finite family.
    primes, growth_bounds = growth_lower_bounds(122)
    assert primes[120] == 701 and primes[121] == 709
    assert all(bound > Q(1, 3000) for bound in growth_bounds[:121])
    assert growth_bounds[120] == min(growth_bounds[:121])
    assert growth_bounds[121] < 0

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
        "growth_prime_count_certified": "121",
        "growth_last_prime_certified": "701",
        "growth_121_lower_exceeds": "1/3000",
        "growth_next_prime": "709",
        "growth_next_lower_is_negative": True,
        "scope": "fixed v2=21,v3=13,v5=9,v7=7,v11=6 kernel; distinct primes p>=13",
    })


if __name__ == "__main__":
    main()
