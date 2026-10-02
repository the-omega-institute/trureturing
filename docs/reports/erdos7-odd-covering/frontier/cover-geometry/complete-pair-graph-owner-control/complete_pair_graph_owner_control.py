#!/usr/bin/env python3
"""Exact owner audit for a divisor-closed complete pair graph.

The family consists of every prime and every pair product from six odd
primes.  Prime classes use residue 1 and pair classes use residue 0.  It is
an irredundant finite noncover; every nonempty noncoprime intersection has
at least three owners.  This is a local obstruction to extracting an exact
two-owner pair from a crowded prime star, not an Erdos #7 counterexample.
"""

from itertools import combinations
from math import gcd, lcm
import json
from pathlib import Path


PRIMES = (3, 5, 7, 11, 13, 17)
MODULI = tuple(sorted(PRIMES + tuple(p * q for p, q in combinations(PRIMES, 2))))
RESIDUES = {d: (1 if d in PRIMES else 0) for d in MODULI}


def owners(x):
    return tuple(d for d in MODULI if x % d == RESIDUES[d])


def main():
    period = lcm(*MODULI)
    all_owners = tuple(owners(x) for x in range(period))
    private = {d: tuple(x for x in range(period) if owners(x) == (d,)) for d in MODULI}

    noncoprime_pairs = []
    minimum_owner_count = None
    pair_owner_sets = {}
    for d, e in combinations(MODULI, 2):
        if gcd(d, e) == 1:
            continue
        points = tuple(
            x for x in range(period)
            if x % d == RESIDUES[d] and x % e == RESIDUES[e]
        )
        if not points:
            continue
        owner_sets = tuple(sorted({owners(x) for x in points}))
        pair_owner_sets[f"{d},{e}"] = [list(s) for s in owner_sets]
        minimum_owner_count = min(
            len(owners(x)) for x in points
        ) if minimum_owner_count is None else min(
            minimum_owner_count, *(len(owners(x)) for x in points)
        )
        noncoprime_pairs.append((d, e, points))

    divisor_closed = all(
        q in MODULI
        for d in MODULI
        for q in range(3, d + 1, 2)
        if d % q == 0
    )
    crowded_stars = {
        str(p): sum(1 for q in PRIMES if q != p) + 0 >= p
        for p in PRIMES
    }
    result = {
        "schema": "complete-pair-graph-owner-control-v1",
        "scope": "finite local structural control; not a whole-cover result",
        "primes": list(PRIMES),
        "moduli": list(MODULI),
        "residues": {str(d): RESIDUES[d] for d in MODULI},
        "period": period,
        "holes": sum(not o for o in all_owners),
        "private_counts": {str(d): len(private[d]) for d in MODULI},
        "divisor_closed": divisor_closed,
        "irredundant": all(private.values()),
        "noncoprime_intersection_pair_count": len(noncoprime_pairs),
        "minimum_owner_count_on_noncoprime_intersections": minimum_owner_count,
        "all_noncoprime_intersections_have_at_least_three_owners": (
            minimum_owner_count is not None and minimum_owner_count >= 3
        ),
        "crowded_stars": crowded_stars,
        "sample_noncoprime_pair": next(iter(sorted(pair_owner_sets.items()))),
    }
    assert len(MODULI) == 21
    assert period == 255255
    assert divisor_closed
    assert result["irredundant"]
    assert result["holes"] > 0
    assert len(noncoprime_pairs) == 60
    assert minimum_owner_count == 3
    assert result["all_noncoprime_intersections_have_at_least_three_owners"]
    assert crowded_stars["3"]
    assert crowded_stars["5"]

    parser = __import__("argparse").ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args()
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
