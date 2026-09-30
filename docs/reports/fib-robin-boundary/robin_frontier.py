#!/usr/bin/env python3
"""Produce an exact Pareto frontier for canonical rough suffixes.

The producer stores only integers and exact rational divisor weights.  It does
not evaluate logarithms or claim a Robin sign.  The external normalization
argument is the prime-exponent exchange theorem in the theory volume.
"""
import sys
sys.dont_write_bytecode = True

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from pathlib import Path


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def pareto(points):
    """Keep points not dominated by a smaller integer with larger weight."""
    unique = {(n, w) for n, w in points}
    ordered = sorted(unique, key=lambda item: (item[0], -item[1]))
    result = []
    best_weight = Fraction(0)
    for number, weight in ordered:
        if weight > best_weight:
            result.append((number, weight))
            best_weight = weight
    return tuple(result)


def build(y, bound):
    if type(y) is not int or y < 1:
        raise ValueError("y must be a positive integer")
    if type(bound) is not int or bound < 1:
        raise ValueError("bound must be a positive integer")

    primes = []

    def prime(i):
        while len(primes) <= i:
            candidate = primes[-1] + 1 if primes else y + 1
            while not is_prime(candidate):
                candidate += 1
            primes.append(candidate)
        return primes[i]

    first = prime(0)
    height = 0
    power = 1
    while power * first <= bound:
        power *= first
        height += 1

    states = {}

    @lru_cache(maxsize=None)
    def solve(i, budget, cap):
        q = prime(i)
        candidates = [(1, Fraction(1))]
        power = 1
        for exponent in range(1, cap + 1):
            power *= q
            if power > budget:
                break
            factor = sum((Fraction(1, q ** j) for j in range(exponent + 1)),
                         Fraction(0))
            child_budget = budget // power
            for suffix, weight in solve(i + 1, child_budget, exponent):
                candidates.append((power * suffix, factor * weight))
        frontier = pareto(candidates)
        states[(i, budget, cap)] = {
            "key": [i, budget, cap],
            "candidate_count": len(candidates),
            "frontier_count": len(frontier),
            "frontier": [
                {"number": number,
                 "weight": [weight.numerator, weight.denominator]}
                for number, weight in frontier
            ],
        }
        return frontier

    root = (0, bound, height)
    frontier = solve(*root)
    return {
        "schema": "robin-rough-frontier-v1",
        "y": y,
        "bound": bound,
        "root": list(root),
        "primes": primes,
        "states": [states[key] for key in sorted(states)],
        "frontier": [
            {"number": number,
             "weight": [weight.numerator, weight.denominator]}
            for number, weight in frontier
        ],
        "scope": (
            "Exact Pareto frontier of canonical consecutive-prime rough suffixes; "
            "no logarithm or Robin sign is evaluated."
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--y", type=int, required=True)
    parser.add_argument("--bound", type=int, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    certificate = build(args.y, args.bound)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(certificate, separators=(",", ":")) + "\n")
    print(json.dumps({
        "certificate": str(args.out),
        "y": args.y,
        "bound": args.bound,
        "states": len(certificate["states"]),
        "primes": certificate["primes"],
        "frontier": len(certificate["frontier"]),
    }))


if __name__ == "__main__":
    main()
