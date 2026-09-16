#!/usr/bin/env python3
"""Verify a complete uniform deletion-profile family with Gamma at most35.

Rebuilds its actual mask orbits, one shared270-depth pure7 numerator, every
actual deletion-group maximum, and support-inclusion coverage. Uses NumPy
and the adjacent canonical geometry algorithms; no optimizer or scratch data.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import importlib.util
import json
import numpy as np

SCHEMA = "erdos7-uniform-profile-geometry-v1"
SHAPE = "root1_same_other_column"


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def read_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "canonical module path")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def caps(weights, points, divisors):
    return [max(sum(int(w) for x, w in zip(points, weights) if int(x % d) == a)
                for a in range(d)) for d in divisors]


def profile_group_bound_numerator(points, b, f):
    """Return the exact b-only bound and one old-coordinate maximizer."""
    n = len(points)
    if (not n or len(b) != n or len(f) != n or len(set(points)) != n
            or any(type(x) is not int or not 0 <= x < 45 for x in points)
            or any(type(x) is not int or not 0 <= x <= 6 for x in b)
            or any(type(x) is not int or x < 0 for x in f)):
        raise ValueError("distinct old45 points, deletion counts, nonnegative integer weights required")
    mods = (1, 3, 5, 9, 15, 45)
    cylinders = {}
    for d in mods:
        rows, empty_added = [], False
        for a in range(d):
            indices = tuple(i for i, x in enumerate(points) if x % d == a)
            if indices or not empty_added:
                rows.append((a, indices))
                empty_added = empty_added or not indices
        cylinders[d] = rows

    def layouts(labels):
        rows = []
        for selection in product(*(cylinders[d] for d in labels)):
            counts = [0] * n
            for _, indices in selection:
                for i in indices:
                    counts[i] += 1
            rows.append((tuple(a for a, _ in selection), counts))
        return rows

    def cylinder_max(weights, d):
        return max((sum(weights[i] for i in indices), a)
                   for a, indices in cylinders[d])

    arows, brows = layouts((9, 45)), layouts((5, 15, 45))
    row_weights = [(6 - bi) * fi for bi, fi in zip(b, f)]
    best = None
    for ares, a in arows:
        t = [2 - ai for ai in a]
        ft = [fi * ti for fi, ti in zip(f, t)]
        extra, eres = cylinder_max(ft, 5)
        for bres, bb in brows:
            base = sum(w * (24 * ai + 6 * ti * bi)
                       for w, ai, ti, bi in zip(row_weights, a, t, bb))
            fm = [v * (4 - bi) for v, bi in zip(ft, bb)]
            seven = [cylinder_max(fm, d) for d in mods]
            value = base + 6 * extra + sum(v for v, _ in seven)
            if best is None or value > best["numerator48"]:
                best = {"numerator48": value, "A_residues": list(ares),
                        "B_residues": list(bres), "extra_old5_residue": eres,
                        "E7_old_residues": [a for _, a in seven],
                        "base": base, "extra": 6 * extra,
                        "E7_terms": [v for v, _ in seven]}
    return best


def evaluate(data, directory):
    geometry = read_module("uniform_profile_classification", directory / "verify_seven_digit_classification.py")
    dominance = read_module("uniform_profile_dominance", directory / "verify_carrier_dominance.py")
    pg = read_module("uniform_profile_point", directory / "verify_point_geometry.py")
    require(type(data) is dict and data.get("schema") == SCHEMA, "uniform-profile schema")
    require(data.get("shape") == SHAPE and data.get("target") == "35"
            and data.get("depth_box") == [8, 5, 4], "specified geometry and full-tail target")
    geometries = geometry.read_geometries(directory / "actual_deletion_profile_certificate.json")
    old_case = next(row for row in geometries if row["shape"] == SHAPE)
    old = old_case["old_points"]
    profile = data.get("profile")
    geometry.integer_list(profile, "uniform deletion profile")
    require(len(profile) == len(old) and all(0 <= b <= 5 for b in profile), "profile range")
    maps = geometry.old_maps(old)
    require(all(old[p[i]] % 3 == old[i] % 3 for p in maps for i in range(len(old))),
            "both named mod3 roots preserved by old maps")
    profile_orbit = set()
    for p in maps:
        image = [0] * len(old)
        for i, b in enumerate(profile):
            image[p[i]] = b
        profile_orbit.add(tuple(image))
    states, cylinders, widths = geometry.digit_union_states(old)
    require(len(states) == old_case["digit_union_states"], "complete actual carrier enumeration")
    profile_states = {state for state in states
                      if geometry.deletion_vector(state, len(old)) in profile_orbit}
    representatives = dominance.carrier_orbits(profile_states, maps, geometry)
    families = data.get("families")
    require(type(families) is list and len(families) == 3, "three actual profile representatives")
    cases = []
    represented = set()
    for family in families:
        require(type(family) is list and len(family) == 11, "eleven low original labels")
        for pair in family:
            geometry.integer_list(pair, "low modulus and residue")
            require(len(pair) == 2 and pair[0] > 1 and 0 <= pair[1] < pair[0], "low residue range")
        require({d for d, a in family} == {d for d in range(2, 316) if 315 % d == 0}
                and [7, 0] in family, "complete distinct normalized low labels")
        require([pair for pair in family if pair[0] % 7] == old_case["old_classes"],
                "same canonical old geometry")
        points = [x for x in range(315) if all(x % d != a for d, a in family)]
        masks = [sum(1 << i for i, x in enumerate(old)
                     if not any(p % 45 == x and p % 7 == digit for p in points))
                 for digit in range(1, 7)]
        state = tuple(sorted(mask for mask in masks if mask))
        require(0 in masks and list(geometry.deletion_vector(state, len(old))) == profile,
                "same exact profile and an untouched nonzero digit")
        require(len(points) == 86 and {p % 45 for p in points} == set(old), "actual86point support")
        canonical = min(tuple(sorted(geometry.image_mask(u, p) for u in state)) for p in maps)
        require(canonical not in represented, "distinct supplied profile orbits")
        represented.add(canonical)
        cases.append((points, state, canonical))
    require(represented == set(representatives) and len(profile_states) == 6,
            "every actual profile carrier is represented")
    solve, targets_of, witness, blocks = dominance.resource_problem(
        representatives, dominance.old_cylinders(old, geometry.MODULI))
    require(all(solve(targets_of(state), 31) == sum(u.bit_count() for u in state)
                for state in representatives), "all three profile orbits are inclusion-minimal")

    # Uniform row totals are(6-b)/N; row maxima are1/N. The untouched digit
    # attains W_x=1/N simultaneously. Every coefficient of W_x is nonnegative,
    # so the pure7 bound is N^-1 max sum[(6-b)A^2+2uAB+u^2B^2]. It depends only
    # on this profile, for every finite depth and either original mod3 root.
    points = np.array(cases[0][0], dtype=np.int64)
    xs = np.array(old, dtype=np.int64)
    ri = np.array([old.index(int(p % 45)) for p in points], dtype=np.int64)
    denominator = len(points)
    weights = np.ones(denominator, dtype=np.int64)
    divisors, gamma, eta, remaining, depths, probabilities, beta, eta_out = pg.coeffs((8, 5, 4))
    remaining[divisors.index(35)] -= F(1, 4)
    require(min(remaining) >= 0 and min(eta_out) >= 0 and 0 < beta < 1,
            "complete nonnegative geometric remainder")
    moduli = (3, 5, 9, 15)
    layouts = list(product(*(sorted({x % d for x in old}) for d in moduli)))
    features = np.array([[[int(x % d == a) for x in old] for d, a in zip(moduli, row)]
                         for row in layouts], dtype=np.int64)
    low_roots = np.array([row[0] for row in layouts], dtype=np.int64)
    loads = {(z3, z5): 1 + np.einsum("ajn,j->an", features,
             np.array([1, 1 + z5, 1 + z3, 1 + z5], dtype=np.int64), dtype=np.int64)
             for z3, z5 in product(range(9), range(6))}
    integer_bound = 213444 * denominator
    require(integer_bound < 2**63, "square integer arithmetic range")
    records, _, _, _ = pg.exact_squares(weights, points, ri, loads, depths, low_roots=low_roots)
    common_caps = caps(weights, points, divisors)
    tail = sum((e * F(m, denominator) for e, m in zip(eta_out, common_caps)), F(0))
    root_values = {}
    shared = []
    for root in (1, 2):
        numerators = [record["root_numerators"][str(root)] for record in records]
        upper = (1 - beta) * F(numerators[0], denominator) + tail + sum(
            (p * F(n, denominator) for p, n in zip(probabilities, numerators)), F(0))
        root_values[root] = upper
        shared.append({"root": root, "U": str(upper), "zero_depth_numerator": numerators[0],
                       "depth_maxima_sha256": geometry.digest(numerators)})

    target = F(data["target"])
    profile_weights = [[1] * len(old)] + [
        [34 - 3 * int(x % 3 == root) for x in old] for root in (1, 2)]
    profile_groups = [profile_group_bound_numerator(old, profile, f) for f in profile_weights]
    results = []
    common_weighted_caps = {}
    for rawpoints, masks, canonical in cases:
        points = np.array(rawpoints, dtype=np.int64)
        weights = np.ones(denominator, dtype=np.int64)
        require(caps(weights, points, divisors) == common_caps, "same ordinary caps")
        grouped = pg.group_setup({"survivors": rawpoints, "points": old}, (9, 45), 35)
        best, _, _ = pg.group_oracle(weights, grouped)
        survival = 1 - F(best["value"], 48 * denominator) - sum(
            (e * F(m, denominator) for e, m in zip(remaining, common_caps)), F(0))
        require(survival > 0, "original same-law positive higher survival")
        roots = []
        for root in (1, 2):
            factor = target.numerator - target.denominator * (1 + 3 * (points % 3 == root))
            weighted = weights * factor
            require(int(factor.min()) >= 0 and 48 * int(weighted.sum()) < 2**63,
                    "nonnegative weighted integer measure")
            weighted_caps = caps(weighted, points, divisors)
            if root in common_weighted_caps:
                require(weighted_caps == common_weighted_caps[root], "same weighted caps")
            common_weighted_caps[root] = weighted_caps
            weighted_best, _, _ = pg.group_oracle(weighted, grouped)
            deletion = F(weighted_best["value"], 48 * denominator * target.denominator) + sum(
                (e * F(m, denominator * target.denominator)
                 for e, m in zip(remaining, weighted_caps)), F(0))
            margin = target - root_values[root] - deletion
            require(margin >= 0, "signed criterion for this actual carrier and root")
            roots.append({"root": root, "weighted_group_numerator48": weighted_best["value"],
                          "weighted_deletion_upper": str(deletion), "margin": str(margin)})
        actual_groups = [best["value"]] + [r["weighted_group_numerator48"] for r in roots]
        require(actual_groups == [b["numerator48"] for b in profile_groups],
                "row-count upper bound equals all three actual grouped costs")
        support = {(int(p % 45), int(p % 7)) for p in rawpoints}
        complete_digits = [y for y in range(1, 7) if all((x, y) in support for x in old)]
        attainment = []
        for f, bound in zip(profile_weights, profile_groups):
            a9, a45 = bound["A_residues"]
            t = [2 - int(x % 9 == a9) - int(x == a45) for x in old]
            pairs = [(y, z) for z in complete_digits for y in range(1, 7) if y != z
                     and sum(fi * ti for x, fi, ti in zip(old, f, t)
                             if x % 5 == bound["extra_old5_residue"]
                             and (x, y) not in support) == 0]
            require(bool(pairs), "disjoint extra35 and E7 digits attain row-count bound")
            extra_digit, seven_digit = pairs[0]
            by_old = dict(zip(old, f))
            total = 0
            for x, y in support:
                a = int(x % 9 == a9) + int(x == a45)
                b = sum(int(x % d == r) for d, r in
                        zip((5, 15, 45), bound["B_residues"]))
                extra = int(y == extra_digit and x % 5 == bound["extra_old5_residue"])
                c = sum(int(y == seven_digit and x % d == r) for d, r in
                        zip((1, 3, 5, 9, 15, 45), bound["E7_old_residues"]))
                total += by_old[x] * (24 * a + 6 * (2 - a) * b + 6 * (2 - a) * extra
                                      + (2 - a) * (4 - b - extra) * c)
            require(total == bound["numerator48"], "pointwise actual grouped-union equality witness")
            attainment.append([extra_digit, seven_digit])
        results.append({"masks": list(masks), "group_numerator48": best["value"],
                        "survival_lower": str(survival), "roots": roots,
                        "row_count_attainment_digits": attainment})

    # Coverage is by actual mask inclusion, retaining multiplicities. The three
    # source orbit images are exactly the six profile states already rebuilt.
    used = {u for state in states for u in state}
    edges = [{b: sum(1 << j for j, a in enumerate(source) if b & ~a == 0) for b in used}
             for source in sorted(profile_states)]
    covered = {state for state in states
               if any(dominance.injection(tuple(sorted(edge[b] for b in state))) for edge in edges)}
    covered_orbits = dominance.carrier_orbits(covered, maps, geometry)
    require(len(covered) == 821 and len(covered_orbits) == 355, "exact profile support coverage")
    return {"source_geometry_sha256": geometry.digest(geometries),
            "old_points": old, "profile_orbit_size": len(profile_orbit),
            "profile_carriers": len(profile_states), "profile_carrier_orbits": len(representatives),
            "profile_minimal_orbits": len(representatives),
            "profile_states_sha256": geometry.digest(sorted(profile_states)),
            "profile_representatives": [list(state) for state in representatives],
            "weight_denominator": denominator, "divisors": divisors,
            "common_cap_numerators": common_caps,
            "common_weighted_cap_numerators": {str(root): row for root, row in common_weighted_caps.items()},
            "shared_pure7_bounds": shared, "cases": results,
            "row_count_group_bounds": profile_groups,
            "minimum_margin": str(min(F(row["margin"]) for result in results for row in result["roots"])),
            "covered_carriers": len(covered), "covered_carrier_orbits": len(covered_orbits),
            "covered_minimal_carrier_orbits": len(representatives),
            "covered_orbits_sha256": geometry.digest(covered_orbits),
            "covered_orbits_by_support_size": {
                str(k): v for k, v in sorted(Counter(6 * len(old) - sum(u.bit_count() for u in state)
                                                   for state in covered_orbits).items())},
            "maximum_square_integer_bound": integer_bound}


def exact_json_types(value):
    require(type(value) in (dict, list, str, int), "exact certificate JSON types")
    if type(value) is dict:
        require(all(type(key) is str for key in value), "string certificate keys")
        for item in value.values():
            exact_json_types(item)
    elif type(value) is list:
        for item in value:
            exact_json_types(item)


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--canonical-directory", type=Path, default=here)
    parser.add_argument("--certificate", type=Path, default=here / "uniform_profile_geometry_certificate.json")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())
    exact_json_types(data)
    result = evaluate(data, args.canonical_directory)
    if args.write:
        data["result"] = result
        args.certificate.write_text(json.dumps(data, indent=2) + "\n")
    else:
        require(data.get("result") == result, "exact profile, moments, actual groups, and coverage")
    print(json.dumps({"verified": True, "target": data["target"],
                      "minimum_margin": result["minimum_margin"],
                      "profile_carrier_orbits": result["profile_carrier_orbits"],
                      "covered_carrier_orbits": result["covered_carrier_orbits"]}, indent=2))


if __name__ == "__main__":
    main()
