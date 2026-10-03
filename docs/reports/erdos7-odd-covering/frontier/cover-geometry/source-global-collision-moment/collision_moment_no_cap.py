#!/usr/bin/env python3
"""Exact finite pressure test for the source-global collision moment.

This is an incidence model, not an odd whole cover.  It keeps one source,
the original phases, divisor-closed numerical labels, and pairwise distinct
moduli.  A collision counts two nonempty pullback classes with the same
numerical modulus; it does not require one source point to satisfy both
original congruences.  Its purpose is to show that the collision moment
itself has no upper bound from those local/EB1 structural conditions alone.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path


R = 3
S = 5
SAFE = (1, 2)  # the pure 3-class is 0 mod 3
VERTICES = tuple(range(1, S))

# K4 on the nonzero 5-ary children.  Every 3-subset of F_5 contains an edge.
EDGES = tuple(combinations(VERTICES, 2))
COFACTORS = (7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)


def crt_pair(a: int, m: int, b: int, n: int) -> int:
    """CRT for coprime moduli, with a canonical nonnegative result."""
    for x in range(m * n):
        if x % m == a % m and x % n == b % n:
            return x
    raise AssertionError((a, m, b, n))


def crt3(a: int, m: int, b: int, n: int, c: int, q: int) -> int:
    return crt_pair(crt_pair(a, m, b, n), m * n, c, q)


def oriented_edge(edge: tuple[int, int], colour: int) -> tuple[int, int]:
    """Orient so x,y are nonzero and colour 1 never has y=1.

    This makes the divisor-closed 15-class (1 mod 3, 1 mod 5)
    disjoint from all 15*m classes of colour 1.
    """
    x, y = edge
    if colour == 1 and y == 1:
        x, y = y, x
    assert x != y and x in VERTICES and y in VERTICES
    if colour == 1:
        assert y != 1
    return x, y


def labels():
    """Return divisor-closed labels and designated collision pairs.

    Each cofactor receives one pair 5*m,15*m for each safe 3-colour.
    The four labels m,3*m,5*m,15*m are all present, as are 3,5,15.
    Residues are represented by CRT coordinates (mod 3, mod 5, mod m).
    """
    all_labels = []
    pairs = []
    for colour in SAFE:
        for idx, edge in enumerate(EDGES):
            m = COFACTORS[(colour - 1) * len(EDGES) + idx]
            x, y = oriented_edge(edge, colour)
            # m itself has phase 0.  Every m-multiple has phase 1 mod m;
            # this enforces disjointness from the divisor m while preserving
            # the same m-coordinate for the designated 5*m,15*m pair.
            all_labels.extend(
                [
                    {"modulus": m, "coords": {"m": 0}, "kind": "m"},
                    {"modulus": 3 * m, "coords": {"r": colour, "s": 0, "m": 1}, "kind": "3m"},
                    {"modulus": 5 * m, "coords": {"s": x, "m": 1}, "kind": "5m"},
                    {"modulus": 15 * m, "coords": {"r": colour, "s": y, "m": 1}, "kind": "15m"},
                ]
            )
            pairs.append(
                {
                    "colour": colour,
                    "m": m,
                    "x": x,
                    "y": y,
                    "lower": {"modulus": 5 * m, "a": 0, "phase_s": x, "phase_m": 1},
                    "upper": {"modulus": 15 * m, "a": 1, "phase_r": colour, "phase_s": y, "phase_m": 1},
                }
            )
    all_labels.extend(
        [
            {"modulus": 3, "coords": {"r": 0}, "kind": "3"},
            {"modulus": 5, "coords": {"s": 0}, "kind": "5"},
            {"modulus": 15, "coords": {"r": 1, "s": 1}, "kind": "15"},
        ]
    )
    return all_labels, pairs


def embedding_subsets():
    return tuple(frozenset(t) for t in combinations(range(S), R))


def divisors(n: int):
    return tuple(d for d in range(2, n + 1) if n % d == 0 and d % 2 == 1)


def check_divisor_closure(all_labels):
    moduli = {x["modulus"] for x in all_labels}
    return all(d in moduli for n in moduli for d in divisors(n))


def check_comparable_disjointness(all_labels):
    """Check the EB1 necessary no-containment condition symbolically."""
    for left in all_labels:
        for right in all_labels:
            e, d = left["modulus"], right["modulus"]
            if e >= d or d % e:
                continue
            # If every coordinate constrained by e agrees in d, the class
            # with modulus d is contained in the class with modulus e.
            for coord, value in left["coords"].items():
                if right["coords"].get(coord) == value:
                    continue
                break
            else:
                return False, (e, d, left["coords"], right["coords"])
    return True, None


def edge_hits_every_embedding():
    for selected in embedding_subsets():
        if not any(set(edge) <= selected for edge in EDGES):
            return False, selected
    return True, None


def pair_survives(pair, safe_u, selected):
    return (
        safe_u == pair["colour"]
        and pair["x"] in selected
        and pair["y"] in selected
    )


def output_residue(pair, endpoint, selected):
    # The inverse of the common embedding is the unique z mod 3 whose
    # selected child is endpoint; both labels have m-coordinate 1.
    z = next(z for z in range(R) if tuple(sorted(selected))[z] == endpoint)
    return crt_pair(z, R, 1, pair["m"])


def exact_source_checks(pairs):
    source_checks = 0
    min_collisions = None
    per_map = []
    for safe_u, selected in product(SAFE, embedding_subsets()):
        source_checks += 1
        live = [p for p in pairs if pair_survives(p, safe_u, selected)]
        # Every live designated pair has the same output numerical modulus
        # but distinct output phases, so it is a genuine numerical collision.
        for p in live:
            low = output_residue(p, p["x"], selected)
            high = output_residue(p, p["y"], selected)
            assert low != high
            assert p["m"] * R == p["lower"]["modulus"] * R // S
        collision_count = len(live)
        assert collision_count >= 1
        min_collisions = collision_count if min_collisions is None else min(min_collisions, collision_count)
        per_map.append({"u": safe_u, "selected": sorted(selected), "live_pairs": collision_count})
    return source_checks, min_collisions, per_map


def main():
    all_labels, pairs = labels()
    moduli = [x["modulus"] for x in all_labels]
    assert len(moduli) == len(set(moduli))
    assert all(d > 1 and d % 2 == 1 for d in moduli)
    assert check_divisor_closure(all_labels)
    comparable, witness = check_comparable_disjointness(all_labels)
    assert comparable, witness
    assert len(pairs) == len(SAFE) * len(EDGES)
    hit, witness = edge_hits_every_embedding()
    assert hit, witness

    checks, min_collisions, per_map = exact_source_checks(pairs)
    rho = Fraction(1, len(SAFE))
    kappa = Fraction(R * (R - 1), S * (S - 1))
    psi = len(pairs) * rho * kappa
    assert psi == Fraction(9, 5)

    # The source model intentionally is not a whole cover.  This is recorded
    # as a scope check rather than hidden: a whole-cover completion would be
    # an instance of the open Erdős #7 problem.
    result = {
        "status": "PASS",
        "scope": "finite source-global collision incidence model; not a whole cover",
        "parameters": {"r": R, "s": S, "depth": 1, "safe_coordinates": list(SAFE)},
        "edge_count": len(EDGES),
        "pair_count": len(pairs),
        "label_count": len(all_labels),
        "distinct_odd_nonunit_moduli": True,
        "divisor_closed_label_set": check_divisor_closure(all_labels),
        "comparable_classes_disjoint": comparable,
        "common_source_collision_for_every_map": True,
        "source_map_count": checks,
        "minimum_live_designated_collisions": min_collisions,
        "rho": str(rho),
        "kappa": str(kappa),
        "psi": str(psi),
        "psi_gt_one": psi > 1,
        "whole_cover": False,
        "map_summary": per_map,
    }
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
