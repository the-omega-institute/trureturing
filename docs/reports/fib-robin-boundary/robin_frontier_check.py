#!/usr/bin/env python3
"""Independently check a robin-frontier-v1 certificate."""
import sys
sys.dont_write_bytecode = True

import argparse
from fractions import Fraction
import hashlib
import json
from math import gcd
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def rational(raw):
    require(type(raw) is list and len(raw) == 2, "malformed rational")
    numerator, denominator = raw
    require(type(numerator) is int and numerator >= 1,
            "invalid rational numerator")
    require(type(denominator) is int and denominator >= 1,
            "invalid rational denominator")
    require(gcd(numerator, denominator) == 1, "noncanonical rational")
    return Fraction(numerator, denominator)


def pareto(points):
    ordered = sorted(set(points), key=lambda item: (item[0], -item[1]))
    result = []
    best = Fraction(0)
    for number, weight in ordered:
        if weight > best:
            result.append((number, weight))
            best = weight
    return tuple(result)


def check(certificate):
    require(certificate.get("schema") == "robin-rough-frontier-v1",
            "wrong schema")
    y = certificate["y"]
    bound = certificate["bound"]
    require(type(y) is int and y >= 1, "invalid y")
    require(type(bound) is int and bound >= 1, "invalid bound")

    supplied_primes = certificate["primes"]
    require(type(supplied_primes) is list and supplied_primes,
            "empty prime prefix")
    previous = y
    for candidate in supplied_primes:
        require(type(candidate) is int and candidate > previous,
                "invalid prime prefix")
        require(prime(candidate), "composite prime prefix entry")
        require(not any(prime(n) for n in range(previous + 1, candidate)),
                "missing intermediate prime")
        previous = candidate

    first = supplied_primes[0]
    height = 0
    power = 1
    while power * first <= bound:
        power *= first
        height += 1
    root = tuple(certificate["root"])
    require(root == (0, bound, height), "incorrect root")

    states = {}
    for raw in certificate["states"]:
        key = tuple(raw["key"])
        require(len(key) == 3, "malformed state key")
        i, budget, cap = key
        require(type(i) is int and 0 <= i < len(supplied_primes),
                "state index out of range")
        require(type(budget) is int and budget >= 1 and
                type(cap) is int and cap >= 0, "invalid state")
        require(key not in states, "duplicate state")
        states[key] = raw
    require(root in states, "missing root state")
    require(len(supplied_primes) == max(key[0] for key in states) + 1,
            "unused trailing primes")

    checked = {}
    for key in sorted(states, reverse=True):
        i, budget, cap = key
        q = supplied_primes[i]
        raw = states[key]
        candidates = [(1, Fraction(1))]
        power = 1
        exponent = 1
        while exponent <= cap:
            power *= q
            if power > budget:
                break
            child = (i + 1, budget // power, exponent)
            require(child in checked, "missing child state")
            factor = sum((Fraction(1, q ** j)
                          for j in range(exponent + 1)), Fraction(0))
            for suffix, weight in checked[child]:
                candidates.append((power * suffix, factor * weight))
            exponent += 1
        expected = pareto(candidates)
        actual = tuple((item["number"], rational(item["weight"]))
                       for item in raw["frontier"])
        require(actual == expected, "frontier mismatch")
        require(raw["candidate_count"] == len(candidates),
                "candidate count mismatch")
        require(raw["frontier_count"] == len(expected),
                "frontier count mismatch")
        checked[key] = expected

    require(tuple(certificate["frontier"][i]["number"] for i in
                  range(len(certificate["frontier"]))) ==
            tuple(item[0] for item in checked[root]),
            "root frontier number mismatch")
    root_frontier = tuple((item["number"], rational(item["weight"]))
                          for item in certificate["frontier"])
    require(root_frontier == checked[root], "root frontier mismatch")
    return {
        "status": "PASS",
        "y": y,
        "bound": bound,
        "states": len(states),
        "frontier": len(root_frontier),
        "scope": "Independent exact check of the canonical joint frontier.",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    data = args.certificate.read_bytes()
    result = check(json.loads(data))
    result["certificate_sha256"] = hashlib.sha256(data).hexdigest()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
