#!/usr/bin/env python3
"""Finite regression for rough-to-canonical normalization and frontiers."""
import sys
sys.dont_write_bytecode = True

import argparse
from fractions import Fraction
import json
from pathlib import Path

from robin_frontier import build


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def factor(n):
    factors = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            exponent = 0
            while n % p == 0:
                n //= p
                exponent += 1
            factors.append((p, exponent))
        p += 1
    if n > 1:
        factors.append((n, 1))
    return factors


def rough(n, y):
    return all(p > y for p, _ in factor(n))


def geom(p, exponent):
    return sum((Fraction(1, p ** j) for j in range(exponent + 1)), Fraction(0))


def canonical(n, y):
    exponents = sorted((a for p, a in factor(n) if p > y), reverse=True)
    primes = []
    candidate = y + 1
    while len(primes) < len(exponents):
        if is_prime(candidate):
            primes.append(candidate)
        candidate += 1
    number = 1
    weight = Fraction(1)
    for p, exponent in zip(primes, exponents):
        number *= p ** exponent
        weight *= geom(p, exponent)
    return number, weight


def run(y, bound):
    certificate = build(y, bound)
    frontier = [
        (entry["number"], Fraction(*entry["weight"]))
        for entry in certificate["frontier"]
    ]
    tested = 0
    for n in range(1, bound + 1):
        if not rough(n, y):
            continue
        tested += 1
        normalized, weight = canonical(n, y)
        original_weight = Fraction(1)
        for p, exponent in factor(n):
            if p > y:
                original_weight *= geom(p, exponent)
        if not (normalized <= n and weight >= original_weight):
            raise AssertionError((y, bound, n, normalized, weight, original_weight))
        if not any(frontier_number <= normalized and frontier_weight >= weight
                   for frontier_number, frontier_weight in frontier):
            raise AssertionError(("frontier does not dominate", y, bound, n,
                                  normalized, weight))
    return {"y": y, "bound": bound, "rough_inputs": tested,
            "states": len(certificate["states"]),
            "frontier": len(frontier), "status": "PASS"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    results = [run(y, bound) for y, bound in
               ((1, 256), (2, 512), (7, 1000), (11, 2000))]
    report = {"status": "PASS", "cases": results,
              "scope": "Finite rough enumeration only; no logarithm sign."}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
