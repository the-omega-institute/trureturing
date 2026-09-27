#!/usr/bin/env python3
"""Exact finite-period check; no third-party package or source producer."""
import argparse
from pathlib import Path
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import gcd, prod
import json

K = 315
ORIGINAL = {
    3: 0, 5: 0, 7: 0, 9: 7, 15: 13, 21: 10,
    35: 6, 45: 4, 63: 37, 105: 61, 315: 46,
}
# All inactive query classes have phase zero. Original phases are unchanged.
QUERY = {
    1: 0, 3: 2, 5: 0, 7: 0, 9: 4, 15: 4,
    21: 0, 35: 0, 45: 37, 63: 0, 105: 0, 315: 1,
}
def require(condition, message):
    if not condition:
        raise ValueError(message)


def hit(x, d, a):
    return (x - a) % d == 0


def load(x, family):
    return sum(hit(x, d, a) for d, a in family.items())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    divisors = [d for d in range(1, K + 1) if K % d == 0]
    require(sorted(QUERY) == divisors, "Query is not complete")
    require(sorted(ORIGINAL) == divisors[1:], "Original label mismatch")
    require(all(d > 1 and d % 2 == 1 for d in ORIGINAL), "Non-odd label")
    require(all(0 <= a < d for d, a in ORIGINAL.items()), "Original phase")
    require(all(0 <= a < d for d, a in QUERY.items()), "Query phase")
    original_hits = {x: [d for d, a in ORIGINAL.items() if hit(x, d, a)]
                     for x in range(K)}
    survivors = [x for x in range(K) if not original_hits[x]]
    require(len(survivors) == 86, "Survivor count")
    private = []
    for d in ORIGINAL:
        points = [x for x in range(K) if original_hits[x] == [d]]
        require(points, f"Original class {d} is redundant")
        private.append({"d": d, "count": len(points), "witness": points[0]})
    comparable_count = 0
    overlapping_pairs = []
    for d, e in combinations(ORIGINAL, 2):
        compatible = (ORIGINAL[d] - ORIGINAL[e]) % gcd(d, e) == 0
        if e % d == 0 or d % e == 0:
            comparable_count += 1
            require(not compatible, f"Comparable classes overlap: {d},{e}")
        if compatible:
            overlapping_pairs.append([d, e])
    require(comparable_count == 31, "Comparable pair count")
    require(all(load(x, QUERY) == 2 for x in survivors), "Load is not two")
    active = []
    for d, a in QUERY.items():
        if d == 1:
            continue
        points = [x for x in survivors if hit(x, d, a)]
        if points:
            active.append({"d": d, "a": a, "count": len(points)})
    require([r["count"] for r in active] == [69, 8, 4, 4, 1],
            "Active partition count")
    require(original_hits[46] == [315], "Original largest class private point")
    require(1 in survivors and hit(1, 315, QUERY[315]), "Query largest inactive")
    cylinder_maxima = []
    for d in divisors:
        maximum = max(Counter(x % d for x in survivors).values())
        cylinder_maxima.append([d, maximum])
    max_complete_mean = sum((Fraction(n, len(survivors))
                             for _, n in cylinder_maxima), Fraction())
    padding = [11, 13, 17, 19]
    padded_K = K * prod(padding)
    padded_size = len(survivors) * prod(p - 1 for p in padding)
    # CRT product: the four new original classes are 0 mod p; all new
    # query divisors use phase 0 and are therefore inactive on survivors.
    padded_R = max_complete_mean * prod(Fraction(p, p - 1) for p in padding) - 1
    padded_density = Fraction(padded_K, padded_size)
    source_density_cap = Fraction(6075000000000, 7235955529)
    require(padded_R <= Fraction(70871, 3375), "Source R scalar bound")
    require(Fraction(1, 5) <= padded_density <= source_density_cap,
            "Source density scalar bounds")
    full_Haar_mean = sum((Fraction(1, d) for d in divisors), Fraction())
    require(full_Haar_mean == Fraction(208, 105), "Full Haar query mean")
    full_Haar_histogram = Counter(load(x, QUERY) for x in range(K))
    require(len(full_Haar_histogram) > 1, "Whole Haar load unexpectedly constant")
    require(sum(t * n for t, n in full_Haar_histogram.items())
            == K * full_Haar_mean, "Whole Haar load first moment")
    out = {
        "result": "PASS", "period": K,
        "original_classes": ORIGINAL, "query_classes": QUERY,
        "survivor_count": len(survivors),
        "query_load_on_all_survivors": 2,
        "variance_under_every_probability_supported_on_U": 0,
        "all_original_classes_have_private_points": True,
        "private_regions": private,
        "comparable_original_pairs_checked": comparable_count,
        "all_comparable_original_classes_are_disjoint": True,
        "original_overlapping_incomparable_pairs": overlapping_pairs,
        "nonunit_query_partition": active,
        "largest_original_private_point": 46,
        "largest_query_active_point": 1,
        "base_maximum_complete_query_mean": str(max_complete_mean),
        "base_R_uniform_nonunit_maxima_sum": str(max_complete_mean - 1),
        "base_uniform_density_relative_to_Haar": str(Fraction(K, len(survivors))),
        "complete_Haar_query_mean": str(full_Haar_mean),
        "complete_Haar_query_load_histogram": dict(sorted(full_Haar_histogram.items())),
        "complete_Haar_primitive_K_Fourier": "exp(-2*pi*i/315)/315",
        "seven_prime_CRT_extension": {
            "new_original_classes": {p: 0 for p in padding},
            "new_query_phase_rule": "0 for every divisor not dividing 315",
            "period": padded_K, "survivor_count": padded_size,
            "uniform_density_relative_to_Haar": str(padded_density),
            "source_density_cap": str(source_density_cap),
            "R_uniform_nonunit_maxima_sum": str(padded_R),
            "constant_load": 2,
            "verification": "CRT product identity; full 315-period enumeration above",
        },
        "scope": "Refutes universal positive variance only; no constant-20 realization or exclusion.",
    }
    text = json.dumps(out, indent=2) + "\n"
    if args.output is None:
        print(text, end="")
    else:
        args.output.write_text(text)


if __name__ == "__main__":
    main()
