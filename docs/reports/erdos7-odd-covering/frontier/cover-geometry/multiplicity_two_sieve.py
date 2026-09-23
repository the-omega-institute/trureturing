#!/usr/bin/env python3
"""Exact numerical endpoint for the labelled BBMST multiplicity-two bound.

The analytic transfer from distinct moduli to labelled progressions is an
ordinary proof in report 348, not verified by this file.
This file checks its universal rational recurrence and two log lower bounds.
"""

from fractions import Fraction
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def primes_through(limit):
    values = []
    for candidate in range(2, limit + 1):
        if all(candidate % p for p in values if p * p <= candidate):
            values.append(candidate)
    return values


def log_lower_positive_series(x, count):
    """For x>1, 2 sum_{j<count} z^(2j+1)/(2j+1) < log(x)."""
    x = Fraction(x)
    require(x > 1 and count > 0, "invalid positive-series arguments")
    z = (x - 1) / (x + 1)
    return 2 * sum((z ** (2 * j + 1) / (2 * j + 1)
                    for j in range(count)), Fraction())


def main():
    primes = primes_through(167)
    require(len(primes) == 39 and primes[:4] == [2, 3, 5, 7],
            "wrong prime enumeration")
    delta = Fraction(1, 4)
    f = Fraction(4)
    steps = []
    for index, prime in enumerate(primes[4:], 5):
        a = Fraction(3 * prime - 1, (prime - 1) ** 2)
        b = Fraction(1, 4 * (prime - 1) ** 2)
        denominator = 1 - b * f / (delta * (1 - delta))
        require(denominator > 0, f"positivity failure at index {index}")
        f = f * (1 + a / (1 - delta)) / denominator
        steps.append({"index": index, "prime": prime,
                      "denominator": str(denominator), "f_upper": str(f)})
    log39_lower = log_lower_positive_series(Fraction(39), 100)
    log366_lower = log_lower_positive_series(Fraction(183, 50), 20)
    require(log39_lower > Fraction(183, 50), "log(39)>3.66 failed")
    require(log366_lower > Fraction(129, 100), "log(3.66)>1.29 failed")
    # Monotonicity: log(log(39)) > log(3.66) > 1.29.
    threshold_lower = 39 * (Fraction(183, 50) + Fraction(129, 100) - 3) ** 2
    require(f < threshold_lower, "Theorem 6.1 endpoint not reached")
    print(json.dumps({
        "source": "arXiv:1811.03547, Lemma 6.2 and Theorem 6.1",
        "analytic_scope": "labelled multiplicity<=2; gcd(period,210)=1",
        "analytic_proof_status": "ordinary proof; not Lean verified",
        "initial_index": 4, "initial_f": "4", "finite_delta": str(delta),
        "finite_indices": [5, 39], "analytic_tail_delta": "1/2",
        "primes": primes, "steps": steps,
        "log_bounds": [
            {"argument": "39", "terms": 100, "proved_lower": "183/50"},
            {"argument": "183/50", "terms": 20, "proved_lower": "129/100"}
        ],
        "terminal_f": str(f), "terminal_threshold_lower": str(threshold_lower),
        "terminal_surplus": str(threshold_lower - f),
        "all_denominators_positive": True,
        "endpoint_inequality_verified": True
    }, indent=2))


if __name__ == "__main__":
    main()
