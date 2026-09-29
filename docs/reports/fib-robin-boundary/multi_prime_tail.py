#!/usr/bin/env python3
"""Exact support-budget checks for the high-v2 Robin tail.

The certificate is deliberately weaker than a step-by-step multi-prime
argument: it bounds the final Euler-factor product.  It proves the support
criterion used in theory section 154 and records the nine-prime corollary;
failure at ten primes only means that this certificate has run out of budget.
All sign decisions use Fraction arithmetic.
"""

from fractions import Fraction as Q


SEED = 315 * 2**21
Z_UPPER = Q(416, 105)
DELTA_LOWER = Q(1447, 1050)
SUPPORT_THRESHOLD = 1 + Q(1447, 4160)


def euler_support(primes):
    assert len(set(primes)) == len(primes)
    value = Q(1)
    for p in primes:
        assert p >= 19 and is_prime(p)
        value *= Q(p, p - 1)
    return value


def is_prime(n):
    if n < 2:
        return False
    divisor = 2
    while divisor * divisor <= n:
        if n % divisor == 0:
            return n == divisor
        divisor += 1
    return True


def z_factor(p, exponent):
    """The exact factor Z(p^a) for a positive exponent."""
    assert p >= 2 and exponent >= 1
    return Q(p, p - 1) * (1 - Q(1, p ** (exponent + 1)))


def main():
    worst_nine = (19, 23, 29, 31, 37, 41, 43, 47, 53)
    worst_ten = worst_nine + (59,)
    nine = euler_support(worst_nine)
    ten = euler_support(worst_ten)

    assert nine == Q(2775498881101, 2092278988800)
    assert nine < SUPPORT_THRESHOLD
    assert ten > SUPPORT_THRESHOLD

    # The rational lower margin in the nine-prime corollary.
    margin = DELTA_LOWER - Z_UPPER * (nine - 1)
    assert margin == Q(44551188659, 528099264000)
    assert margin > 0

    # Equation (154.1), checked on a mixed-exponent instance.
    primes = (19, 29, 53)
    exponents = (1, 3, 2)
    product = Q(1)
    for p, a in zip(primes, exponents):
        product *= z_factor(p, a)
    assert product < euler_support(primes)
    assert euler_support(()) == 1

    # The support criterion itself is a rational implication.
    assert DELTA_LOWER - Z_UPPER * (SUPPORT_THRESHOLD - 1) == 0

    print({
        "status": "exact rational multi-prime support certificate passed",
        "seed": str(SEED),
        "support_threshold": str(SUPPORT_THRESHOLD),
        "worst_nine_product": str(nine),
        "worst_nine_margin_lower": str(margin),
        "worst_ten_product": str(ten),
        "scope": "v2=21 seed, at most nine distinct primes p>=19, arbitrary positive exponents",
    })


if __name__ == "__main__":
    main()
