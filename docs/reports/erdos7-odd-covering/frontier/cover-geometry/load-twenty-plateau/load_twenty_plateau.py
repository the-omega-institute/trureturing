#!/usr/bin/env python3
"""Verify an arithmetic query plateau by complete finite CRT strata."""

import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import prod
from pathlib import Path


PRIMES = (5, 7, 11, 13, 17, 19)
PERIOD = 9 * prod(PRIMES)
DENSITY_CAP = Fraction(6075000000000, 7235955529)
QUERY_CAP = Fraction(70871, 3375)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def stratum_hit(modulus, residue, selected):
    """Return the indicator only after proving it constant on this stratum."""
    factors = (9 if modulus % 9 == 0 else 3,) if modulus % 3 == 0 else ()
    factors += tuple(p for p in PRIMES if modulus % p == 0)
    require(prod(factors) == modulus, "Unresolved modulus")
    outcomes = []
    for factor in factors:
        allowed = (1,) if factor in (3, 9) or factor in selected else tuple(
            value for value in range(factor) if value != 1
        )
        outcomes.append({value == residue % factor for value in allowed})
    if {False} in outcomes:
        return False
    require(all(outcome == {True} for outcome in outcomes),
            "Query is not constant on a CRT stratum")
    return True


def result():
    prime_products = [prod(subset) for size in range(7)
                      for subset in combinations(PRIMES, size)]
    divisors = sorted(a * d for a in (1, 3, 9) for d in prime_products)
    require(len(divisors) == len(set(divisors)) == 192, "Divisor inventory")
    require(all(PERIOD % d == 0 for d in divisors), "Nondivisor")
    changed = {9} | {9 * p * q for p, q in combinations(PRIMES, 2)}
    require(len(changed) == 16 and changed <= set(divisors), "Changed labels")
    query = {d: 0 if d == 1 or d in changed else 1 for d in divisors}
    require(all(0 <= residue < d for d, residue in query.items()), "Query phase")
    strata = []
    for selected in combinations(PRIMES, 3):
        size = prod(p - 1 for p in PRIMES if p not in selected)
        q_load = sum(stratum_hit(d, query[d], selected) for d in divisors)
        aligned_load = sum(stratum_hit(d, 1 % d, selected) for d in divisors)
        require(q_load == 20, "Displayed query is not twenty")
        require(aligned_load == 24, "Aligned query is not twenty-four")
        strata.append({"prime_coordinates_equal_to_one": selected,
                       "point_count": size, "query_load": q_load,
                       "aligned_query_load": aligned_load})
    size = sum(row["point_count"] for row in strata)
    require(len(strata) == 20 and size == 23320, "Stratum inventory")
    mass = Fraction(size, PERIOD)
    density = 1 / mass
    require(mass == Fraction(424, 264537), "Haar mass")
    require(Fraction(1, 5) <= density < DENSITY_CAP, "Density comparison")
    require(mass > 1 / DENSITY_CAP, "Survivor density floor comparison")
    require(Fraction(23) > QUERY_CAP, "Alternate query does not exceed cap")
    return {
        "result": "PASS",
        "period": PERIOD,
        "divisor_count": len(divisors),
        "query_rule": "residue 1 except unit and changed_labels, which use 0",
        "changed_labels": sorted(changed),
        "set_rule": "x=1 mod9; exactly three listed prime coordinates equal 1",
        "other_prime_coordinates": PRIMES,
        "CRT_strata": strata,
        "point_count": size,
        "Haar_mass": str(mass),
        "uniform_set_density_relative_to_Haar": str(density),
        "source_density_cap": str(DENSITY_CAP),
        "displayed_query_load_on_set": 20,
        "aligned_query_load_on_set": 24,
        "R_lower_bound_for_every_supported_probability": 23,
        "source_R_cap": str(QUERY_CAP),
        "verification": "Complete CRT strata, not full-period enumeration",
        "scope": "No original family with this survivor set is asserted; every supported law violates the common-query cap.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(result(), indent=2) + "\n"
    if args.output is None:
        print(output, end="")
    else:
        args.output.write_text(output)


if __name__ == "__main__":
    main()
