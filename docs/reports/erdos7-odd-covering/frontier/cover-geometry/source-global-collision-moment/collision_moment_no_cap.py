#!/usr/bin/env python3
"""Exact finite pressure test for the source-global collision moment.

This is an incidence model, not an odd whole cover.  It keeps one source,
the original phases, divisor-closed numerical labels, and pairwise distinct
moduli.  A collision counts two nonempty pullback classes with the same
numerical modulus; it does not require one source point to satisfy both
original congruences.  Its purpose is to show that a unit collision bound
does not follow from these local structural conditions alone.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations, product
import json
from math import gcd
from pathlib import Path


R = 3
S = 5
SAFE = (1, 2)  # the pure 3-class is 0 mod 3
VERTICES = tuple(range(1, S))

# K4 on the nonzero 5-ary children.  Every 3-subset of F_5 contains an edge.
EDGES = tuple(combinations(VERTICES, 2))
COFACTORS = (7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)


def require(condition, detail):
    """Substantive checks stay active under Python -O."""
    if not condition:
        raise AssertionError(detail)


def crt_pair(a: int, m: int, b: int, n: int) -> int:
    """CRT for coprime moduli, with a canonical nonnegative result."""
    require(m >= 1 and n >= 1 and gcd(m, n) == 1, ("noncoprime CRT", m, n))
    return (a + m * (((b - a) * pow(m, -1, n)) % n)) % (m * n) if n > 1 else a % m


def crt3(a: int, m: int, b: int, n: int, c: int, q: int) -> int:
    return crt_pair(crt_pair(a, m, b, n), m * n, c, q)


def coordinate_moduli(label):
    """Coordinates must be exactly the prime-power/cofactor factors of n."""
    n = label["modulus"]
    require(isinstance(n, int) and n > 1 and n % 2 == 1, ("invalid original modulus", n))
    factors = {}
    for name, prime in (("r", R), ("s", S)):
        power = 1
        while n % prime == 0:
            n //= prime
            power *= prime
        if power > 1:
            factors[name] = power
    if n > 1:
        factors["m"] = n
    require(set(label["coords"]) == set(factors),
            ("coordinate does not match numerical modulus", label, factors))
    return factors


def literal_residue(label):
    factors = coordinate_moduli(label)
    residue, modulus = 0, 1
    for name, factor in factors.items():
        value = label["coords"][name]
        require(isinstance(value, int), ("noninteger phase", label))
        residue = crt_pair(residue, modulus, value, factor)
        modulus *= factor
    require(modulus == label["modulus"], "incomplete numerical CRT modulus")
    return residue


def oriented_edge(edge: tuple[int, int], colour: int) -> tuple[int, int]:
    """Orient so x,y are nonzero and colour 1 never has y=1.

    This makes the divisor-closed 15-class (1 mod 3, 1 mod 5)
    disjoint from all 15*m classes of colour 1.
    """
    x, y = edge
    if colour == 1 and y == 1:
        x, y = y, x
    require(x != y and x in VERTICES and y in VERTICES, ("invalid edge", edge))
    if colour == 1:
        require(y != 1, "pure 15 phase conflict")
    return x, y


def labels():
    """Return divisor-closed labels and designated collision pairs.

    Each safe 3-colour/edge uses a fresh cofactor and one pair 5*m,15*m.
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
                    {"modulus": 3 * m, "coords": {"r": 3 - colour, "m": 1}, "kind": "3m"},
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
    """Use the actual CRT residues and gcd of the numerical moduli."""
    residues = [(label["modulus"], literal_residue(label)) for label in all_labels]
    for (m, a), (n, b) in combinations(residues, 2):
        if m % n == 0 or n % m == 0:
            common = gcd(m, n)
            if (a - b) % common == 0:
                return False, {"moduli": [m, n], "residues": [a, b], "gcd": common}
    return True, None


def negative_controls(all_labels):
    lower = next(label for label in all_labels if label["kind"] == "3m")
    upper = next(label for label in all_labels if label["kind"] == "15m")
    invalid = {**lower, "coords": {**lower["coords"], "s": 0}}
    try:
        literal_residue(invalid)
    except AssertionError:
        pass
    else:
        raise AssertionError("accepted a coordinate absent from the numerical modulus")
    compatible = {**lower, "coords": {**lower["coords"], "r": upper["coords"]["r"]}}
    disjoint, witness = check_comparable_disjointness([compatible, upper])
    require(not disjoint, "accepted a contained comparable class")
    return {"nondivisor_coordinate_rejected": True, "compatible_comparable_pair_rejected": True,
            "compatible_pair": witness}


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


def literal_pullback(label, safe_u, children):
    factors = coordinate_moduli(label)
    require(factors.get("r", 1) <= R and factors.get("s", 1) <= S,
            "finite source check requires depth at most one")
    phase = literal_residue(label)
    if "r" in factors and phase % R != safe_u:
        return None
    if "s" in factors and phase % S not in children:
        return None
    m = factors.get("m", 1)
    if "s" in factors:
        return R * m, crt_pair(phase, m, children.index(phase % S), R)
    return m, phase % m


def exact_source_checks(all_labels, pairs):
    source_checks = 0
    pullback_checks = 0
    min_collisions = None
    per_map = []
    for safe_u, selected in product(SAFE, embedding_subsets()):
        source_checks += 1
        children = tuple(sorted(selected))
        outputs, columns = {}, {}
        for label in all_labels:
            original_phase = literal_residue(label)
            m = coordinate_moduli(label).get("m", 1)
            output = literal_pullback(label, safe_u, children)
            for t in range(R * m):
                source = crt3(safe_u, R, children[t % R], S, t % m, m)
                actual = source % label["modulus"] == original_phase
                projected = output is not None and t % output[0] == output[1]
                require(actual == projected, ("literal pullback mismatch", label, safe_u, children, t))
                pullback_checks += 1
            if output is not None:
                require(output[0] > 1, "unit output survived safe source")
                outputs[label["modulus"]] = output
                columns.setdefault(output[0], []).append(output[1])
        require(all(len(phases) == len(set(phases)) for phases in columns.values()),
                "same-column numerical collision has duplicate phase")
        live = [p for p in pairs if pair_survives(p, safe_u, selected)]
        # Every live designated pair has the same output numerical modulus
        # but distinct output phases, so it is a genuine numerical collision.
        for p in live:
            low = output_residue(p, p["x"], selected)
            high = output_residue(p, p["y"], selected)
            require(low != high, "designated phases coincide")
            require(outputs[p["lower"]["modulus"]] == (R * p["m"], low)
                    and outputs[p["upper"]["modulus"]] == (R * p["m"], high),
                    "designated pair differs from literal pullback")
        collision_count = len(live)
        require(collision_count >= 1, "source map has no designated collision")
        min_collisions = collision_count if min_collisions is None else min(min_collisions, collision_count)
        full_count = sum(len(phases) * (len(phases) - 1) // 2 for phases in columns.values())
        per_map.append({"u": safe_u, "selected": sorted(selected), "live_pairs": collision_count,
                        "full_collision_pairs": full_count})
    return source_checks, min_collisions, per_map, pullback_checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().with_suffix(".json"))
    parser.add_argument("--check", action="store_true", help="compare saved results without writing")
    args = parser.parse_args()
    all_labels, pairs = labels()
    moduli = [x["modulus"] for x in all_labels]
    require(len(moduli) == len(set(moduli)), "repeated numerical modulus")
    require(all(d > 1 and d % 2 == 1 for d in moduli), "nonodd or unit original modulus")
    require(check_divisor_closure(all_labels), "divisor closure fails")
    comparable, witness = check_comparable_disjointness(all_labels)
    require(comparable, witness)
    require(len(pairs) == len(SAFE) * len(EDGES), "designated pair count")
    hit, witness = edge_hits_every_embedding()
    require(hit, witness)
    negative = negative_controls(all_labels)

    checks, min_collisions, per_map, pullback_checks = exact_source_checks(all_labels, pairs)
    rho = Fraction(1, len(SAFE))
    kappa = Fraction(R * (R - 1), S * (S - 1))
    psi = len(pairs) * rho * kappa
    empirical = Fraction(sum(row["live_pairs"] for row in per_map), checks)
    full_psi = Fraction(sum(row["full_collision_pairs"] for row in per_map), checks)
    require(psi == empirical == Fraction(9, 5), "designated collision moment")
    require(full_psi == Fraction(159, 20), "full collision moment")

    # Avoid prime singletons, the pure 15-class, and every m-multiple.
    uncovered, period = crt_pair(2, R, 2, S), R * S
    for m in COFACTORS:
        uncovered = crt_pair(uncovered, period, 2, m)
        period *= m
    require(all(uncovered % label["modulus"] != literal_residue(label) for label in all_labels),
            "uncovered CRT witness meets an original class")
    result = {
        "status": "PASS",
        "scope": "finite source-global collision incidence model; not a whole cover",
        "parameters": {"r": R, "s": S, "depth": 1, "safe_coordinates": list(SAFE)},
        "edge_count": len(EDGES),
        "pair_count": len(pairs),
        "label_count": len(all_labels),
        "originals": [{"modulus": label["modulus"], "residue": literal_residue(label),
                       "kind": label["kind"]} for label in all_labels],
        "comparable_pair_count": sum(m % n == 0 or n % m == 0 for m, n in combinations(moduli, 2)),
        "distinct_odd_nonunit_moduli": True,
        "divisor_closed_label_set": check_divisor_closure(all_labels),
        "comparable_classes_disjoint": comparable,
        "common_source_collision_for_every_map": True,
        "source_map_count": checks,
        "literal_pullback_checks": pullback_checks,
        "minimum_live_designated_collisions": min_collisions,
        "minimum_full_collisions": min(row["full_collision_pairs"] for row in per_map),
        "rho": str(rho),
        "kappa": str(kappa),
        "psi": str(psi),
        "psi_scope": "the twelve designated (5m,15m) pairs",
        "full_collision_moment": str(full_psi),
        "psi_gt_one": psi > 1,
        "whole_cover": False,
        "uncovered_witness": {"residue": uncovered, "modulus": period,
                              "coordinates": {"mod_3": 2, "mod_5": 2,
                                              "cofactors": [{"modulus": m, "residue": 2} for m in COFACTORS]}},
        "negative_controls": negative,
        "map_summary": per_map,
    }
    out = args.output if args.output.is_absolute() else Path(__file__).resolve().parent / args.output
    if args.check:
        require(json.loads(out.read_text(encoding="utf-8")) == result, "saved result mismatch")
    else:
        out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "label_count": len(all_labels),
                      "comparable_pair_count": result["comparable_pair_count"],
                      "source_maps": checks, "literal_pullback_checks": pullback_checks,
                      "designated_moment": str(psi), "full_collision_moment": str(full_psi),
                      "mode": "check" if args.check else "write"}, sort_keys=True))


if __name__ == "__main__":
    main()
