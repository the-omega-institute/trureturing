#!/usr/bin/env python3
"""Exact local control for a crowded star with no exact two-owner atom.

The finite period is enumerated in full.  This is a local structural control,
not a covering-system counterexample and not an unrestricted Erdos #7 proof.
"""

from argparse import ArgumentParser
from functools import reduce
from math import gcd, lcm
import json
from pathlib import Path


MODULI = (3, 5, 7, 9, 15, 21, 35, 105)
RESIDUES = {3: 2, 5: 1, 7: 5, 9: 6, 15: 7, 21: 7, 35: 7, 105: 72}
PAIR = (15, 21)


def owners(x):
    return tuple(d for d in MODULI if x % d == RESIDUES[d])


def private_points(period):
    return {
        d: tuple(x for x in range(period) if owners(x) == (d,))
        for d in MODULI
    }


def complete_hull(points, period):
    if not points:
        return None
    witness = points[0]
    return reduce(
        gcd, (period,) + tuple(x - witness for x in points)
    )


def main():
    period = lcm(*MODULI)
    all_owners = tuple(owners(x) for x in range(period))
    private = private_points(period)
    pair_points = tuple(
        x for x in range(period)
        if x % PAIR[0] == RESIDUES[PAIR[0]]
        and x % PAIR[1] == RESIDUES[PAIR[1]]
    )
    pair_owner_sets = tuple(sorted({tuple(owners(x)) for x in pair_points}))
    pair_exact_two = tuple(
        x for x in pair_points if set(owners(x)) == set(PAIR)
    )
    hulls = {str(d): complete_hull(private[d], period) for d in MODULI}
    prime_neighbors = {
        q for d in MODULI if d % 3 == 0
        for q in range(2, d + 1)
        if all(q % r for r in range(2, int(q ** 0.5) + 1))
        and q != 3 and d % (3 * q) == 0
    }
    comparable_disjoint = all(
        not (d != e and (d % e == 0 or e % d == 0)
             and set(owners(x)) >= {d, e})
        for d in MODULI for e in MODULI for x in range(period)
    )
    result = {
        "schema": "crowded-star-owner-control-v1",
        "scope": "finite local structural control; not a whole-cover result",
        "moduli": list(MODULI),
        "residues": {str(d): RESIDUES[d] for d in MODULI},
        "period": period,
        "holes": sum(not o for o in all_owners),
        "private_counts": {str(d): len(private[d]) for d in MODULI},
        "private_witnesses": {str(d): private[d][0] for d in MODULI},
        "comparable_classes_disjoint": comparable_disjoint,
        "prime_three_neighbors": sorted(prime_neighbors),
        "prime_three_neighbor_count": len(prime_neighbors),
        "prime_three_height": 2,
        "crowded_star": len(prime_neighbors) + 1 >= 3,
        "pair": list(PAIR),
        "pair_intersection_modulus": lcm(*PAIR),
        "pair_intersection_points": list(pair_points),
        "pair_owner_sets": [list(s) for s in pair_owner_sets],
        "pair_exact_two_owner_points": list(pair_exact_two),
        "K_pair_empty": not pair_exact_two,
        "complete_private_hulls": hulls,
        "cross_hull_15_to_21": hulls["15"] is not None and hulls["15"] % 21 == 0,
        "cross_hull_21_to_15": hulls["21"] is not None and hulls["21"] % 15 == 0,
        "RH1_holds_for_pair": (
            hulls["15"] is not None and hulls["21"] is not None
            and hulls["15"] % 21 == 0 and hulls["21"] % 15 == 0
        ),
    }
    assert result["period"] == 315
    assert result["holes"] == 89
    assert all(result["private_counts"].values())
    assert result["comparable_classes_disjoint"]
    assert result["prime_three_neighbors"] == [5, 7]
    assert result["crowded_star"]
    assert result["pair_intersection_points"] == [7, 112, 217]
    assert result["pair_owner_sets"] == [[15, 21, 35]]
    assert result["K_pair_empty"]
    assert result["complete_private_hulls"]["15"] == 15
    assert result["complete_private_hulls"]["21"] == 21
    assert not result["RH1_holds_for_pair"]
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    parser = ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args()
    if args.output:
        Path(args.output).write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
