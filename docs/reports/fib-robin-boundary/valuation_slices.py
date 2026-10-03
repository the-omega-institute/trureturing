#!/usr/bin/env python3
"""Partition an unbounded exponent orthant by an exact Euler-defect cutoff.

Coordinate cap c represents every exponent >= c. Its factor is enclosed by
[1-p**(-c-1), 1], so a finite grid can certify an infinite exponent domain.
The threshold is an explicit input; this program does not prove its analytic
connection to Robin's inequality. See Library/notes/hertlein2018robin.md.
"""

import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from math import prod
from pathlib import Path


def prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def rational(value):
    return [value.numerator, value.denominator]


def build(primes, lower, caps, threshold):
    if not primes or not (len(primes) == len(lower) == len(caps)):
        raise ValueError("nonempty primes, lower and caps must have equal lengths")
    if any(type(p) is not int or not prime(p) for p in primes):
        raise ValueError("every direction must be prime")
    if tuple(sorted(set(primes))) != tuple(primes):
        raise ValueError("prime directions must be distinct and increasing")
    if any(type(a) is not int or type(c) is not int or not 1 <= a <= c
           for a, c in zip(lower, caps)):
        raise ValueError("exponents must satisfy 1 <= lower <= cap")
    if not 0 < threshold < 1:
        raise ValueError("threshold must lie strictly between zero and one")

    factors = [
        {a: 1 - Fraction(1, p ** (a + 1)) for a in range(b, c + 1)}
        for p, b, c in zip(primes, lower, caps)
    ]
    safe, outside, ambiguous = {}, {}, []
    for point in product(*(range(b, c + 1) for b, c in zip(lower, caps))):
        floor = prod(factor[a] for factor, a in zip(factors, point))
        ceiling = prod(Fraction(1) if a == c else factor[a]
                       for factor, a, c in zip(factors, point, caps))
        if ceiling <= threshold:
            safe[point] = ceiling
        elif floor > threshold:
            outside[point] = floor
        else:
            ambiguous.append({"cell": list(point),
                              "factor_lower": rational(floor),
                              "factor_upper": rational(ceiling)})

    minimal = []
    for point, value in sorted(outside.items()):
        if all(a == b or tuple(v - (i == j) for j, v in enumerate(point))
               not in outside for i, (a, b) in enumerate(zip(point, lower))):
            minimal.append({"exponents": list(point),
                            "multiplier_from_lower": prod(
                                p ** (a - b)
                                for p, a, b in zip(primes, point, lower)),
                            "factor": rational(value),
                            "excess": rational(value - threshold)})
    maximal = []
    for point, value in sorted(safe.items()):
        if all(a == c or tuple(v + (i == j) for j, v in enumerate(point))
               not in safe for i, (a, c) in enumerate(zip(point, caps))):
            maximal.append({
                "upper_exponents": [None if a == c else a
                                    for a, c in zip(point, caps)],
                "factor_supremum": rational(value),
                "slack": rational(threshold - value),
            })
    return {
        "schema": "prime-valuation-slices-v1",
        "status": "RESOLVED" if not ambiguous else "OPEN",
        "primes": list(primes), "lower": list(lower), "caps": list(caps),
        "threshold": rational(threshold),
        "counts": {"cells": len(safe) + len(outside) + len(ambiguous),
                   "certified": len(safe), "outside": len(outside),
                   "ambiguous": len(ambiguous)},
        "minimal_outside": minimal,
        "maximal_certified": maximal,
        "ambiguous_cells": ambiguous,
        "scope": (
            "Exact product-threshold classification on all exponents >= lower; "
            "a cap cell includes every larger exponent. RESOLVED means no "
            "ambiguous cell. Outside means the supplied sufficient condition "
            "fails, not that Robin fails. No analytic theorem is verified here."
        ),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--primes", type=int, nargs="+", required=True)
    parser.add_argument("--lower", type=int, nargs="+", required=True)
    parser.add_argument("--caps", type=int, nargs="+", required=True)
    parser.add_argument("--threshold", type=Fraction, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    result = build(args.primes, args.lower, args.caps, args.threshold)
    result["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "counts": result["counts"],
                      "minimal_outside": len(result["minimal_outside"]),
                      "maximal_certified": len(result["maximal_certified"])}))


if __name__ == "__main__":
    main()
