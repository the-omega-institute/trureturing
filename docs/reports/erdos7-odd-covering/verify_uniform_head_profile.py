#!/usr/bin/env python3
"""Exact support-profile recurrence for uniform congruence survivors.

No residue search or optimization solver is used. All bounds are rational;
the infinite projection-envelope sums are evaluated by exact geometric tails.
The proof is in Problems/erdos-7-odd-covering-systems.md. This program
verifies profile arithmetic, not the universal congruence argument or Lean
formalization. Python 3.9+ standard library only.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def subsets(s):
    for n in range(len(s) + 1):
        yield from combinations(s, n)


def envelope_sums(s, coefficients):
    """Return R=sum(nonunit envelopes), K=sum(pair weights * envelopes)."""
    cutoffs = {}
    for p in s:
        others = tuple(q for q in s if q != p)
        ratio = max(
            coefficients[tuple(sorted(t + (p,)))] / coefficients[t]
            for t in subsets(others)
        )
        cutoff = 0
        while p ** (cutoff + 1) < ratio:
            cutoff += 1
        cutoffs[p] = cutoff

    mass = moment = F(0)
    # State cutoff+1 denotes the entire infinite tail, not one exponent.
    for states in product(*(range(cutoffs[p] + 2) for p in s)):
        high = tuple(p for p, a in zip(s, states) if a == cutoffs[p] + 1)
        low = tuple(p for p, a in zip(s, states) if 0 < a <= cutoffs[p])
        exponents = dict(zip(s, states))
        value = min(
            coefficients[tuple(sorted(high + t))]
            / prod(p ** exponents[p] for p in t)
            for t in subsets(low)
        )
        r = k = value
        for p in high:
            cutoff = cutoffs[p]
            r *= F(1, p**cutoff * (p - 1))
            k *= F((2 * cutoff + 3) * (p - 1) + 2,
                   p**cutoff * (p - 1) ** 2)
        for p in low:
            k *= 2 * exponents[p] + 1
        mass += r
        moment += k
    return mass - 1, moment


def recurrence(primes):
    profiles = {(): {(): F(1)}}
    metrics = {(): (F(0), F(1))}
    deletion_bounds = {}
    for size in range(1, len(primes) + 1):
        for s in combinations(primes, size):
            candidates = []
            bounds = {}
            for p in s:
                old = tuple(q for q in s if q != p)
                if old not in profiles:
                    continue
                deletion = metrics[old][0] / F(p - 2)
                bounds[p] = deletion
                if deletion >= 1:
                    continue
                candidate = {(): F(1)}
                for t in subsets(s):
                    if t:
                        previous = tuple(q for q in t if q != p)
                        pure_factor = F(p - 1, p - 2) if p in t else F(1)
                        candidate[t] = profiles[old][previous] * pure_factor / (1 - deletion)
                candidates.append(candidate)
            deletion_bounds[s] = bounds
            if candidates:
                profiles[s] = {
                    t: min(candidate[t] for candidate in candidates)
                    for t in subsets(s)
                }
                metrics[s] = envelope_sums(s, profiles[s])
    return profiles, metrics, deletion_bounds


def main():
    primes = (3, 5, 7, 11)
    profiles, metrics, deletions = recurrence(primes)
    require(len(profiles) == 16, "all four-prime subsets must have a profile")
    expected = {
        (3, 5): (F(5, 2), F(63, 4)),
        (3, 5, 7): (F(77, 15), F(237, 5)),
        primes: (F(1514, 145), F(3885, 29)),
    }
    for s, bound in expected.items():
        require(metrics[s] == bound, "displayed profile bound mismatch")
    for s, coefficients in profiles.items():
        require(coefficients[()] == 1, "unit cylinder cap must equal one")
        require(all(v > 0 for v in coefficients.values()),
                "all cylinder coefficients must be positive")
        if s:
            require(any(v < 1 for v in deletions[s].values()),
                    "survivor normalization is not certified")
    require(metrics[primes][1] < F(138877, 1000),
            "head bound exceeds the continuation seed")
    print(json.dumps({
        "prime_support": primes,
        "cylinder_sum_bound": str(metrics[primes][0]),
        "Gamma_bound": str(metrics[primes][1]),
        "continuation_seed": "138877/1000",
        "all_subsets_admissible": True,
        "profile": {"*".join(map(str, t)) or "1": str(v)
                    for t, v in profiles[primes].items()},
        "last_prime_deletion_bounds": {str(p): str(b)
                                       for p, b in deletions[primes].items()},
        "scope": "Exact profile recurrence and infinite geometric sums. "
                 "Uniformity in residues and finite heights is established "
                 "by the accompanying mathematical proof, not by enumeration. "
                 "No Lean formalization is claimed."
    }, indent=2))


if __name__ == "__main__":
    main()
