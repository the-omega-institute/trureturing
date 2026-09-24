#!/usr/bin/env python3
"""Exact low315 support dominance using existing canonical geometry and PG1.

The adjacent canonical classifier supplies the fixed old45 geometry and root
maps. Only standard-library modules are imported. Rebuilds essential carriers,
all six resource-DP minimal-carrier classifications, and PG1's support-inclusion
coverage. This entry does not modify or reinterpret the existing classification
certificate and does not run an LP or evaluate a new moment bound.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from collections import Counter
from functools import lru_cache, reduce
from itertools import permutations, product
from pathlib import Path
import argparse
import importlib.util
import json

SCHEMA = "erdos7-carrier-support-dominance-v1"
SCOPE = ("Complete six-shape support reduction by the five distinct original mixed7 "
         "labels; essential and inclusion-minimal carrier orbits; inherited PG1 "
         "bound for containing carriers, with arbitrary finite higher357 families")
PG1_GAMMA = "105976769844774468812903/2920804491373837228125"
PG1_SHAPE = "root2_other_other_column"
PG1_SOURCE_SHA256 = "57413882013965dbd57d6a31a9019ebe2b0c7ae8d045d696a9f688e0dbd1d068"


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def geometry_module(directory):
    path = directory / "verify_seven_digit_classification.py"
    spec = importlib.util.spec_from_file_location("canonical_carrier_geometry", path)
    require(spec is not None and spec.loader is not None, "canonical geometry module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def old_cylinders(points, moduli):
    return [[sum(1 << i for i, x in enumerate(points) if x % d == residue)
             for residue in sorted({x % d for x in points})] for d in moduli]


def essential_carriers(points, moduli):
    cylinders = old_cylinders(points, moduli)
    blocks = [set() for _ in range(32)]
    for subset in range(1, 32):
        labels = [i for i in range(5) if subset >> i & 1]
        for chosen in product(*(cylinders[i] for i in labels)):
            if any(not (mask & ~reduce(int.__or__, chosen[:j] + chosen[j + 1:], 0))
                   for j, mask in enumerate(chosen)):
                continue
            blocks[subset].add(reduce(int.__or__, chosen, 0))
    states = [set() for _ in range(32)]
    states[0].add(())
    for subset in range(1, 32):
        anchor = subset & -subset
        first = subset
        while first:
            if first & anchor:
                for union in blocks[first]:
                    for rest in states[subset ^ first]:
                        states[subset].add(tuple(sorted((union,) + rest)))
            first = (first - 1) & subset
    return states[31], cylinders


def carrier_orbits(states, maps, geometry):
    masks = {u for state in states for u in state}
    actions = [{u: geometry.image_mask(u, p) for u in masks} for p in maps]
    remaining = states.copy()
    representatives = set()
    covered = 0
    while remaining:
        state = remaining.pop()
        images = {tuple(sorted(action[u] for u in state)) for action in actions}
        require(images <= states, "carrier family closed under old root maps")
        remaining.difference_update(images)
        representative = min(images)
        require(representative not in representatives, "disjoint old-root orbits")
        representatives.add(representative)
        covered += len(images)
    require(covered == len(states), "exact orbit accounting")
    return sorted(representatives)


def contains_support(smaller, larger):
    """Masks are deletions: smaller support has the larger deletion masks."""
    edges = tuple(sorted(sum(1 << j for j, a in enumerate(smaller) if b & ~a == 0)
                         for b in larger))
    return injection(edges)


@lru_cache(None)
def injection(edges):
    if not edges:
        return True
    if edges[0] == 0:
        return False
    first, *rest = edges
    while first:
        bit = first & -first
        first ^= bit
        if injection(tuple(sorted(e & ~bit for e in rest))):
            return True
    return False


def resource_problem(representatives, cylinders):
    blocks = [dict() for _ in range(32)]
    for subset in range(1, 32):
        labels = [i for i in range(5) if subset >> i & 1]
        for chosen in product(*(cylinders[i] for i in labels)):
            union = reduce(int.__or__, chosen, 0)
            blocks[subset].setdefault(union, tuple(zip(labels, chosen)))
    target_masks = {u for state in representatives for u in state}
    covers = {}
    for target in target_masks:
        allowed = {}
        for subset in range(1, 32):
            legal = [u for u in blocks[subset] if target & ~u == 0]
            if legal:
                union = max(legal, key=lambda u: (u.bit_count(), -u))
                allowed[subset] = (union.bit_count(), union)
        covers[target] = allowed
    maxima = [max(u.bit_count() for u in row) for row in cylinders]
    maximizing = [min(u for u in row if u.bit_count() == m)
                  for row, m in zip(cylinders, maxima)]
    leftover = [sum(maxima[i] for i in range(5) if mask >> i & 1) for mask in range(32)]
    decisions = {}

    @lru_cache(None)
    def solve(targets, available):
        if not targets:
            return leftover[available]
        if available.bit_count() < len(targets):
            return -1000
        best = -1000
        chosen = None
        for subset, (score, union) in covers[targets[0]].items():
            rest = available ^ subset
            if subset & available != subset or rest.bit_count() < len(targets) - 1:
                continue
            continuation = solve(targets[1:], rest)
            if continuation < 0:
                continue
            value = score + continuation
            if value > best:
                best, chosen = value, (subset, union)
        if chosen is not None:
            decisions[targets, available] = chosen
        return best

    def targets_of(state):
        return tuple(sorted(state, key=lambda u: (-u.bit_count(), u)))

    def witness(state):
        targets, available = targets_of(state), 31
        unions, assignment = [], []
        while targets:
            subset, union = decisions[targets, available]
            unions.append(union)
            assignment.append([list(pair) for pair in blocks[subset][union]])
            available ^= subset
            targets = targets[1:]
        for i in range(5):
            if available >> i & 1:
                unions.append(maximizing[i])
                assignment.append([[i, maximizing[i]]])
        require(sorted(label for group in assignment for label, mask in group) == list(range(5)),
                "each original label used exactly once")
        require(len(unions) <= 5, "at most five occupied nonzero digits")
        require(all(reduce(int.__or__, (mask for label, mask in group), 0) == union
                    for union, group in zip(unions, assignment)), "assigned union witnesses")
        return tuple(sorted(unions)), assignment

    return solve, targets_of, witness, blocks


def classify_minimal(points, states, representatives, cylinders, maps, geometry):
    solve, targets_of, witness, blocks = resource_problem(representatives, cylinders)
    minimal = []
    gains = Counter()
    example = None
    check_targets = []
    representative_set = set(representatives)
    for state in representatives:
        score = solve(targets_of(state), 31)
        deleted = sum(u.bit_count() for u in state)
        require(score >= deleted, "the given carrier is feasible")
        gains[score - deleted] += 1
        if score == deleted:
            minimal.append(state)
            if not any(kind == "minimal" for kind, item in check_targets):
                check_targets.append(("minimal", state))
        elif example is None:
            smaller, assignment = witness(state)
            require(contains_support(smaller, state), "strict support inclusion witness")
            require(sum(u.bit_count() for u in smaller) == score, "optimal deletion witness")
            canonical = min(tuple(sorted(geometry.image_mask(u, p) for u in smaller)) for p in maps)
            require(canonical in representative_set, "maximal deletion witness is essential")
            require(solve(targets_of(canonical), 31) == score, "maximizer is inclusion-minimal")
            example = {"larger_support_masks": list(state),
                       "smaller_support_masks": list(smaller),
                       "larger_support_size": 6 * len(points) - deleted,
                       "smaller_support_size": 6 * len(points) - score,
                       "original_label_assignment_by_digit": assignment}
            check_targets.append(("dominated", state))
    # Independent finite verification: scan every terminal carrier for one
    # minimal and one dominated target, using only mask inclusion matching.
    crosschecks = []
    for kind, target in check_targets:
        expected = solve(targets_of(target), 31)
        exhaustive = max(sum(u.bit_count() for u in candidate) for candidate in states
                         if contains_support(candidate, target))
        require(exhaustive == expected, "independent exhaustive dominance maximum")
        crosschecks.append({"kind": kind, "target_masks": list(target),
                            "maximum_deletions": exhaustive})
    return {"minimal_carrier_orbits": len(minimal),
            "strictly_dominated_essential_orbits": len(representatives) - len(minimal),
            "minimal_orbits_by_support_size": {
                str(k): v for k, v in sorted(Counter(6 * len(points) - sum(u.bit_count() for u in s)
                                                   for s in minimal).items())},
            "additional_deletions": {str(k): v for k, v in sorted(gains.items())},
            "minimal_orbits_sha256": geometry.digest(minimal),
            "block_union_counts": [len(row) for row in blocks],
            "strict_dominance_example": example,
            "independent_exhaustive_checks": crosschecks}, set(minimal)


def read_pg1(path, geometries, geometry):
    data = json.loads(read_artifact_text(path))
    require(geometry.digest(data) == PG1_SOURCE_SHA256, "published PG1 certificate identity")
    require(type(data) is dict and data.get("schema") == "erdos7-point-geometry-v1", "PG1 schema")
    require(data.get("target") == "3849/106" and data.get("Gamma") == PG1_GAMMA,
            "published PG1 target and bound")
    for key in ("points", "old_points", "weight_numerators"):
        geometry.integer_list(data.get(key), "PG1 " + key)
    family = data.get("family")
    require(type(family) is list, "PG1 family")
    for pair in family:
        geometry.integer_list(pair, "PG1 modulus/residue")
        require(len(pair) == 2 and pair[0] > 1 and 0 <= pair[1] < pair[0], "PG1 pair range")
    require(len(family) == len({d for d, a in family}) == 11, "PG1 distinct low labels")
    require({d for d, a in family} == {d for d in range(2, 316) if 315 % d == 0},
            "PG1 complete low modulus set")
    points = data["points"]
    require(points == [x for x in range(315) if all(x % d != a for d, a in family)],
            "PG1 actual carrier")
    old = next(row for row in geometries if row["shape"] == PG1_SHAPE)["old_points"]
    require(data["old_points"] == old and len(points) == 75, "PG1 old geometry")
    require(type(data.get("weight_denominator")) is int
            and len(data["weight_numerators"]) == len(points)
            and all(w > 0 for w in data["weight_numerators"])
            and sum(data["weight_numerators"]) == data["weight_denominator"], "PG1 full support")
    require(all(x % 7 != 0 for x in points), "PG1 excluded pure7 root")
    masks = []
    for digit in range(1, 7):
        surviving = {x % 45 for x in points if x % 7 == digit}
        mask = sum(1 << i for i, x in enumerate(old) if x not in surviving)
        if mask:
            masks.append(mask)
    return tuple(sorted(masks)), geometry.digest(data)


def pg1_coverage(masks, points, maps, minimal, geometry):
    states, cylinders, widths = geometry.digit_union_states(points)
    images = sorted({tuple(sorted(geometry.image_mask(u, p) for u in masks)) for p in maps})
    used = {u for state in states for u in state}
    edge_maps = [{b: sum(1 << j for j, a in enumerate(image) if b & ~a == 0) for b in used}
                 for image in images]
    covered = {state for state in states
               if any(injection(tuple(sorted(edge[b] for b in state))) for edge in edge_maps)}
    representatives = carrier_orbits(covered, maps, geometry)
    minimal_covered = sorted(minimal.intersection(representatives))
    canonical_pg1 = min(images)
    require(canonical_pg1 in minimal and minimal_covered == [canonical_pg1],
            "PG1 settles exactly one minimal orbit")
    require(len(covered) == 1648 and len(representatives) == 232, "published-law support coverage")
    return {"shape": PG1_SHAPE, "Gamma": PG1_GAMMA,
            "PG1_nonempty_deletion_masks": list(masks), "old_root_images": len(images),
            "covered_carriers": len(covered), "covered_carrier_orbits": len(representatives),
            "covered_minimal_carrier_orbits": len(minimal_covered),
            "covered_orbits_by_support_size": {
                str(k): v for k, v in sorted(Counter(6 * len(points) - sum(u.bit_count() for u in s)
                                                   for s in representatives).items())},
            "covered_orbits_sha256": geometry.digest(representatives)}


MOD3_SOURCE_SHA256 = "35cd4a830d1ccb413c8530c83a9d9af0a0deb6be3f7d87dc5a82d3bd640d0662"
C2_SHAPE = "root2_other_same_column"


def read_mod3_source(path, geometries, geometry):
    data = json.loads(read_artifact_text(path))
    require(geometry.digest(data) == MOD3_SOURCE_SHA256, "mod3 source certificate identity")
    require(type(data) is dict and data.get("schema") == "erdos7-mod3-conditioned-geometry-v1",
            "mod3 source schema")
    cases = data.get("cases")
    require(type(cases) is list and len(cases) == 2
            and [case.get("name") for case in cases] == ["PG1", "C2-minimal75"],
            "two inherited mod3 sources")
    require(cases[0].get("target") == "69/2" and cases[1].get("target") == "35",
            "inherited mod3 targets")
    source = cases[1]
    for key in ("points", "old_points", "weight_numerators"):
        geometry.integer_list(source.get(key), "C2 " + key)
    family = source.get("family")
    require(type(family) is list and len(family) == 11, "C2 original low family")
    for pair in family:
        geometry.integer_list(pair, "C2 modulus/residue")
        require(len(pair) == 2 and pair[0] > 1 and 0 <= pair[1] < pair[0], "C2 pair range")
    require({d for d, a in family} == {d for d in range(2, 316) if 315 % d == 0},
            "C2 eleven distinct original modulus labels")
    old_case = next(row for row in geometries if row["shape"] == C2_SHAPE)
    old = old_case["old_points"]
    require(source["old_points"] == old
            and [pair for pair in family if pair[0] % 7] == old_case["old_classes"],
            "C2 canonical old geometry")
    points = source["points"]
    require(points == [x for x in range(315) if all(x % d != a for d, a in family)]
            and len(points) == 75 and [7, 0] in family, "C2 actual75 carrier")
    weights = source["weight_numerators"]
    require(type(source.get("weight_denominator")) is int and len(weights) == len(points)
            and all(w > 0 for w in weights)
            and sum(weights) == source["weight_denominator"], "C2 full positive law")
    require({x % 45 for x in points} == set(old), "C2 support projects onto old carrier")
    by_digit = [sum(1 << i for i, x in enumerate(old)
                    if not any(p % 45 == x and p % 7 == digit for p in points))
                for digit in range(1, 7)]
    assignments = []
    for modulus, residue in family:
        if modulus % 7 == 0 and modulus > 7:
            cofactor = modulus // 7
            mask = sum(1 << i for i, x in enumerate(old) if x % cofactor == residue % cofactor)
            assignments.append({"modulus": modulus, "residue": residue,
                                "digit": residue % 7, "old_mask": mask})
    for digit in range(1, 7):
        require(reduce(int.__or__, (row["old_mask"] for row in assignments
                                    if row["digit"] == digit), 0) == by_digit[digit - 1],
                "C2 original-label union witness")
    return tuple(sorted(mask for mask in by_digit if mask)), assignments


def old_shape_embedding_counts(geometries):
    # Exhaustive restrictions of modulus-preserving CRT tree maps: each old
    # support occupies roots with respectively two and three mod9 children.
    # Three nonempty children cannot inject into two, so root types must match.
    # All four nonzero mod5 columns occur, so their images are a permutation.
    for row in geometries:
        points = row["old_points"]
        require({x % 9 for x in points} == {1, 7, 2, 5, 8}
                and {x % 5 for x in points} == {1, 2, 3, 4}, "old embedding domain")
    counts = []
    for source in geometries:
        row_counts = []
        for target in geometries:
            allowed = {(x % 9, x % 5) for x in target["old_points"]}
            count = 0
            for short, long, columns in product(permutations((1, 7)),
                                                permutations((2, 5, 8)),
                                                permutations((1, 2, 3, 4))):
                rows = dict(zip((1, 7, 2, 5, 8), short + long))
                cols = dict(zip((1, 2, 3, 4), columns))
                count += all((rows[x % 9], cols[x % 5]) in allowed
                             for x in source["old_points"])
            require(count > 0 if source["shape"] == target["shape"] else count == 0,
                    "old support embeddings stay in their canonical shape")
            row_counts.append(count)
        counts.append(row_counts)
    return counts


def c2_coverage(masks, assignments, points, maps, minimal, geometry):
    states, cylinders, widths = geometry.digit_union_states(points)
    images = sorted({tuple(sorted(geometry.image_mask(u, p) for u in masks)) for p in maps})
    used = {u for state in states for u in state}
    edge_maps = [{b: sum(1 << j for j, a in enumerate(image) if b & ~a == 0) for b in used}
                 for image in images]
    covered = {state for state in states
               if any(injection(tuple(sorted(edge[b] for b in state))) for edge in edge_maps)}
    representatives = carrier_orbits(covered, maps, geometry)
    minimal_covered = sorted(minimal.intersection(representatives))
    require(minimal_covered == [min(images)], "C2 settles exactly one minimal orbit")
    require(len(images) == 18 and len(covered) == 2291 and len(representatives) == 152,
            "C2 exact support coverage")
    return {"name": "C2-minimal75", "shape": C2_SHAPE, "target": "35",
            "source_nonempty_deletion_masks": list(masks),
            "canonical_source_masks": list(min(images)),
            "source_original_label_witness": assignments,
            "old_root_images": len(images), "covered_carriers": len(covered),
            "covered_carrier_orbits": len(representatives),
            "covered_minimal_carrier_orbits": len(minimal_covered),
            "covered_orbits_by_support_size": {
                str(k): v for k, v in sorted(Counter(6 * len(points) - sum(u.bit_count() for u in s)
                                                   for s in representatives).items())},
            "covered_orbits_sha256": geometry.digest(representatives)}


def reconstruct(directory):
    geometry = geometry_module(directory)
    geometries = geometry.read_geometries(directory / 'certificates/actual_deletion_profile_certificate.json')
    pg1_masks, pg1_digest = read_pg1(directory / 'certificates/point_geometry_certificate.json', geometries, geometry)
    c2_masks, c2_assignments = read_mod3_source(
        directory / 'certificates/mod3_conditioned_geometry_certificate.json', geometries, geometry)
    embedding_counts = old_shape_embedding_counts(geometries)
    rows = []
    coverage = None
    c2_result = None
    for old in geometries:
        points = old["old_points"]
        maps = geometry.old_maps(points)
        states, cylinders = essential_carriers(points, geometry.MODULI)
        representatives = carrier_orbits(states, maps, geometry)
        result, minimal = classify_minimal(points, states, representatives, cylinders, maps, geometry)
        row = {"shape": old["shape"], "old_points": len(points),
               "essential_carriers": len(states), "essential_carrier_orbits": len(representatives),
               "essential_carriers_sha256": geometry.digest(sorted(states)),
               "essential_orbits_sha256": geometry.digest(representatives), **result}
        rows.append(row)
        if old["shape"] == PG1_SHAPE:
            coverage = pg1_coverage(pg1_masks, points, maps, minimal, geometry)
        if old["shape"] == C2_SHAPE:
            c2_result = c2_coverage(c2_masks, c2_assignments, points, maps, minimal, geometry)
    keys = ("essential_carriers", "essential_carrier_orbits", "minimal_carrier_orbits",
            "strictly_dominated_essential_orbits")
    totals = {key: sum(row[key] for row in rows) for key in keys}
    require(totals == {"essential_carriers": 640932, "essential_carrier_orbits": 107695,
                       "minimal_carrier_orbits": 56966,
                       "strictly_dominated_essential_orbits": 50729}, "complete dominance totals")
    require(coverage is not None and c2_result is not None, "both support coverages present")
    return {"schema": SCHEMA, "scope": SCOPE,
            "source_geometry_sha256": geometry.digest(geometries),
            "source_PG1_certificate_sha256": pg1_digest,
            "inherited_PG1_verification": "existing canonical verify_point_geometry.py",
            "cases": rows, "totals": totals, "PG1_support_coverage": coverage,
            "mod3_conditioned_support_coverage": {
                "source_certificate_sha256": MOD3_SOURCE_SHA256,
                "inherited_verification": "existing canonical verify_mod3_conditioned_geometry.py",
                "old_shape_order": [row["shape"] for row in geometries],
                "old_shape_embedding_counts": embedding_counts,
                "C2_support_coverage": c2_result,
                "PG1_target": "69/2",
                "combined_target": "35",
                "covered_carriers": coverage["covered_carriers"] + c2_result["covered_carriers"],
                "covered_carrier_orbits": (coverage["covered_carrier_orbits"]
                                           + c2_result["covered_carrier_orbits"]),
                "intersection_carrier_orbits": 0,
                "covered_minimal_carrier_orbits": 2,
                "remaining_minimal_carrier_orbits": totals["minimal_carrier_orbits"] - 2}}


def check_json_types(value):
    require(type(value) in (dict, list, str, int), "exact result JSON types")
    if type(value) is dict:
        require(all(type(key) is str for key in value), "string result keys")
        for item in value.values():
            check_json_types(item)
    elif type(value) is list:
        for item in value:
            check_json_types(item)


def main():
    base = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--canonical-directory", type=Path, default=base)
    parser.add_argument("--check", type=Path, default=base / 'certificates/carrier_dominance_certificate.json')
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()
    expected = None
    if args.write is None:
        expected = json.loads(read_artifact_text(args.check))
        check_json_types(expected)
        require(type(expected) is dict and expected.get("schema") == SCHEMA, "result schema")
    result = reconstruct(args.canonical_directory)
    if args.write is not None:
        write_certificate_text(args.write, json.dumps(result, indent=2) + "\n")
    else:
        require(result == expected, "exact deterministic dominance result")
    print(json.dumps({"verified": True, **result["totals"],
                      "PG1_covered_carrier_orbits": result["PG1_support_coverage"]["covered_carrier_orbits"],
                      "combined_covered_carrier_orbits": result["mod3_conditioned_support_coverage"]["covered_carrier_orbits"]}, indent=2))


if __name__ == "__main__":
    main()
