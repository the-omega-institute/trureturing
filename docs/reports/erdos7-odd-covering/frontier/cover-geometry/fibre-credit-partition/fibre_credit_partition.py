#!/usr/bin/env python3
"""Exact partition reduction for the ternary-height-one fibre inequality."""
from fractions import Fraction
from itertools import combinations
import argparse
import json
from math import isqrt, prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def prime(n):
    return type(n) is int and n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def rational(value):
    require(isinstance(value, list) and len(value) == 2, "rational pair required")
    require(all(type(x) is int for x in value) and value[1] > 0, "invalid rational")
    return Fraction(*value)


def pair(value):
    return [value.numerator, value.denominator]


def calculate(data):
    qs = data["q_primes"]
    later = data["later_primes"]
    require(isinstance(qs, list) and qs and qs == sorted(set(qs)), "ordered distinct q primes required")
    require(all(prime(q) and q >= 5 for q in qs), "q primes must be at least five")
    require(isinstance(later, list) and len(later) == 2, "two later primes required")
    require(later == sorted(set(later)) and all(prime(p) and p > 3 for p in later), "invalid later primes")
    require(set(qs).isdisjoint(later), "old and later primes overlap")
    mass = rational(data["retained_mass_floor"])
    hinge_upper = rational(data["hinge_upper"])
    query_upper = rational(data["query_upper"])
    density_upper = rational(data["density_upper"])
    haar_floor = rational(data["haar_floor"])
    require(0 < mass <= 1 and min(hinge_upper, query_upper, density_upper, haar_floor) > 0, "nonpositive bound")

    ns = [q - 2 for q in qs]
    indices = range(len(ns))
    denominator = 2 * prod(ns)
    supports = [set(s) for size in range(2, len(ns) + 1) for s in combinations(indices, size)]

    def integer_fibre(mask, removed):
        return prod(ns[i] - 1 if mask >> i & 1 else ns[i] for i in indices if i not in removed)

    full = (1 << len(ns)) - 1
    rows = []
    # Complementary partitions have the same F; fix the first q in A.
    for mask in range(1, full + 1, 2):
        other = full ^ mask
        numerator = integer_fibre(mask, set()) + integer_fibre(other, set())
        for support in supports:
            left = integer_fibre(mask, support)
            right = integer_fibre(other, support)
            numerator -= left + right + max(left, right)
        require(numerator * mass.denominator > denominator * mass.numerator, "partition mass floor failed")
        rows.append([mask, numerator])
    minimum = min(row[1] for row in rows)

    ps = [3] + qs
    caps = [Fraction(3, 2)] + [Fraction(q - 1, q - 2) for q in qs]
    zeros = [1 - c / p for c, p in zip(caps, ps)]
    ones = [c * Fraction(p - 1, p * p) for c, p in zip(caps, ps)]
    mean = prod(1 + c / (p - 1) for c, p in zip(caps, ps))
    atom1 = prod(zeros)
    atom2 = atom1 * sum(v / u for v, u in zip(ones, zeros))
    atom3 = atom1 * sum(v / (p * u) for v, u, p in zip(ones, zeros, ps))
    hinge = mean - 4 + 3 * atom1 + 2 * atom2 + atom3
    require(0 <= hinge < hinge_upper, "hinge upper bound failed")
    require(3 + hinge_upper / mass <= query_upper, "query bound failed")
    density = prod(caps) / mass
    require(density <= density_upper, "density upper bound failed")
    tail = prod(Fraction(p, p - 1) for p in later) - 1
    reserve = 1 - tail * (1 + query_upper)
    require(reserve > 0, "later deletion has no positive reserve")
    haar = reserve / density
    require(haar > haar_floor, "Haar floor failed")
    return {
        "partition_denominator": denominator,
        "partition_count": len(rows),
        "partition_numerators": rows,
        "minimum_numerator": minimum,
        "minimizing_masks": [mask for mask, value in rows if value == minimum],
        "minimum_mass": pair(Fraction(minimum, denominator)),
        "mass_floor": pair(mass),
        "minimum_mass_surplus": pair(Fraction(minimum, denominator) - mass),
        "mean": pair(mean),
        "small_atoms": [pair(a) for a in [atom1, atom2, atom3]],
        "hinge4": pair(hinge),
        "hinge_upper": pair(hinge_upper),
        "query_upper": pair(query_upper),
        "density_bound": pair(density),
        "outside_inventory": pair(tail),
        "remaining_probability": pair(reserve),
        "survivor_haar_bound": pair(haar),
        "declared_haar_floor": pair(haar_floor),
    }


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, default=here)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.loads((args.input_dir / "fibre_credit_partition_input.json").read_text())
    result = calculate(data)
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    else:
        expected = json.loads((args.input_dir / "fibre_credit_partition.json").read_text())
        require(result == expected, "retained result mismatch")
    print(json.dumps({"verified_partitions": result["partition_count"], "minimum_mass": result["minimum_mass"], "survivor_haar_bound": result["survivor_haar_bound"]}))


if __name__ == "__main__":
    main()
