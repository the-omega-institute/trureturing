#!/usr/bin/env python3
"""Exact data-search experiment for the common actual315 fibre profile.

Requires Python3 and NumPy. The default input is the adjacent existing
marked_head_profile_certificate.json; --source-certificate can select it
explicitly. This program rebuilds all optional mixed7 configurations, checks
an independent enumeration, recomputes six old costs and independently
checks four of them, and transfers the same b through nine existing rectangle
hinge duals. --write records a compact deterministic result; --check compares
with a previously recorded result. No cache or other module is required.

Mathematical scope: full original357 part divides315; arbitrary actual
11/13 axes, point holes and finite heights; the same C=40/31 clipped law.
This is a finite research computation supporting the ordinary universal
head argument, not a Lean admission or an unrestricted tail proof. The
existing rectangle duals and JC upper bounds are explicit source inputs.
"""
from __future__ import annotations

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

import argparse
from collections import Counter
from fractions import Fraction as F
from functools import reduce
from hashlib import sha256
from itertools import product
import json
from math import gcd
from pathlib import Path
import sys

import numpy as np

MODULI = (3, 5, 9, 15, 45)
CATEGORIES = ("same_other_column", "other_same_column", "other_other_column")
COORDINATES = (228733, 264815, 215188, 41873)
SCALE = 10**6
I64 = 2**63 - 1
COST_NAMES = ("mean", "hinge2", "hinge3", "hinge4", "hinge5", "square")
INDEPENDENT_COSTS = (0, 1, 3, 5)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def int64_bound(bound, message):
    require(0 <= int(bound) <= I64, "int64 overflow bound: " + message)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def progress(message):
    print(message, file=sys.stderr, flush=True)


def old_points(root, category):
    other = 3 - root
    row, column = {"same_other_column": (root, 2),
                   "other_same_column": (other, 1),
                   "other_other_column": (other, 2)}[category]
    a15 = next(a for a in range(15) if a % 3 == root and a % 5 == 1)
    a45 = next(a for a in range(45) if a % 9 == row and a % 5 == column)
    classes = ((3, 0), (9, 4), (5, 0), (15, a15), (45, a45))
    points = [x for x in range(45) if all(x % d != a for d, a in classes)]
    return points, classes


def partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for blocks in partitions(rest):
        yield ((first,),) + blocks
        for i in range(len(blocks)):
            yield blocks[:i] + ((first,) + blocks[i],) + blocks[i + 1:]


def original_states(points):
    """Labelled cylinder choices and all52 digit partitions, including empties."""
    n = len(points)
    groups = [[sum(1 << i for i, x in enumerate(points) if x % d == a)
               for a in sorted({x % d for x in points})] for d in MODULI]
    blocks = list(partitions(tuple(range(5))))
    require(len(blocks) == len(set(blocks)) == 52, "five-label set partitions")
    unions_seen = set()
    for cylinders in product(*[[0] + group for group in groups]):
        for partition in blocks:
            unions_seen.add(tuple(sorted(reduce(int.__or__, (cylinders[j] for j in block), 0)
                                         for block in partition
                                         if any(cylinders[j] for j in block))))
    vectors = set()
    for unions in unions_seen:
        b = [0] * n
        for mask in unions:
            while mask:
                bit = mask & -mask
                b[bit.bit_length() - 1] += 1
                mask ^= bit
        vectors.add(tuple(b))
    # Independent construction: append one original label to an existing digit
    # union or give it a fresh digit. State equality forgets digit names only.
    states = {()}
    widths = [1]
    for d in MODULI:
        cylinders = {sum(1 << i for i, x in enumerate(points) if x % d == a)
                     for a in range(d)}
        next_states = set()
        for unions in states:
            for cylinder in cylinders:
                if not cylinder:
                    next_states.add(unions)
                    continue
                next_states.add(tuple(sorted(unions + (cylinder,))))
                for j, old in enumerate(unions):
                    next_states.add(tuple(sorted(unions[:j] + (old | cylinder,) + unions[j + 1:])))
        states = next_states
        widths.append(len(states))
    require(states == unions_seen, "independent exact digit-union enumeration")
    independent = {tuple(sum((mask >> i) & 1 for mask in unions) for i in range(n))
                   for unions in states}
    require(independent == vectors, "independent exact deletion-vector enumeration")
    ordered = sorted(vectors, key=lambda b: (sum(b), b))
    b = np.array(ordered, dtype=np.int64)
    require(np.all((0 <= b) & (b <= 5)), "five original labels and a globally unused digit")
    geometry = {"vectors": len(ordered), "digit_union_states": len(states),
                "independent_state_widths": widths,
                "vectors_by_deleted_count": {str(d): c for d, c in sorted(Counter(map(sum, ordered)).items())},
                "ordered_vectors_sha256": digest(ordered)}
    return b, groups, geometry


def complete_loads(points, groups):
    n = len(points)
    loads = np.array([[1 + sum((mask >> i) & 1 for mask in chosen) for i in range(n)]
                      for chosen in product(*groups)], dtype=np.int64)
    require(np.all((1 <= loads) & (loads <= 6)), "complete old45 test loads")
    return loads


def cost_values(x, index):
    if index == 0:
        return x
    if index == 5:
        return x * x
    return np.maximum(x - (index + 1), 0)


def exact_old_profiles(points, b, loads):
    n, count = len(points), len(loads)
    # All complete pair costs are bounded by n*12^2. All sums retained below
    # are bounded by 6*n*12^2, including intermediate K and deleted costs.
    int64_bound(6 * n * 144, "old pair costs, K and retained sums")
    J = np.empty((count, 6), dtype=np.int64)
    for i, a in enumerate(loads):
        sums = loads + a
        for j in range(6):
            J[i, j] = cost_values(sums, j).sum(axis=1).max()
    profiles = np.empty((len(b), 6), dtype=np.int64)
    for j in range(6):
        values = cost_values(loads, j)
        K = 5 * values.sum(axis=1) + J[:, j]
        for lo in range(0, len(b), 512):
            hi = min(lo + 512, len(b))
            profiles[lo:hi, j] = (K[None, :] - b[lo:hi] @ values.T).max(axis=1)
    # Rebuild test choices directly from residues, in reverse enumeration
    # order. Repeated load functions are allowed; there is one row per layout.
    choices = [[a for a in reversed(range(d)) if any(x % d == a for x in points)]
               for d in MODULI]
    other = np.array([[1 + sum(x % d == a for d, a in zip(MODULI, chosen)) for x in points]
                      for chosen in product(*choices)], dtype=np.int64)
    require(len(other) == count, "independent complete old layout count")
    J2 = np.empty((count, 4), dtype=np.int64)
    for lo in range(0, count, 64):
        hi = min(lo + 64, count)
        sums = other[lo:hi, None, :] + other[None, :, :]
        for j, cost in enumerate(INDEPENDENT_COSTS):
            J2[lo:hi, j] = cost_values(sums, cost).sum(axis=2).max(axis=1)
    lookup = {tuple(a): tuple(map(int, row)) for a, row in zip(loads, J[:, INDEPENDENT_COSTS])}
    for a, row in zip(other, J2):
        require(lookup[tuple(a)] == tuple(row), "independent four pair-cost maxima")
    # Positive retained terms, A-layout blocks and einsum provide an independent
    # evaluation of every state maximum, rather than reusing K-b*cost.
    w = 5 - b
    independent = np.zeros((len(b), 4), dtype=np.int64)
    for j, cost in enumerate(INDEPENDENT_COSTS):
        values = cost_values(other, cost)
        for lo in range(0, count, 128):
            hi = min(lo + 128, count)
            retained = J2[lo:hi, j, None] + np.einsum(
                "ax,rx->ar", values[lo:hi], w, dtype=np.int64, optimize=False)
            independent[:, j] = np.maximum(independent[:, j], retained.max(axis=0))
    require(np.array_equal(independent, profiles[:, INDEPENDENT_COSTS]),
            "independent four old costs on every optional b")
    check = {"pair_costs": [COST_NAMES[j] for j in INDEPENDENT_COSTS],
             "independent_pair_cost_values": count * count * n * 4,
             "independent_state_cost_maxima": len(b) * 4,
             "profiles_sha256": sha256(profiles.astype("<i8").tobytes()).hexdigest()}
    return profiles, check


def determinant(matrix):
    """Small exact determinant; Python integers make products unbounded."""
    if len(matrix) == 1:
        return matrix[0][0]
    return sum((-1)**j * matrix[0][j] * determinant([r[:j] + r[j + 1:] for r in matrix[1:]])
               for j in range(len(matrix)))


def rectangle_constraints(shared):
    C = F(40, 31)
    require(F(shared["clip"]) == C, "same actual clipping constant")
    require(F(shared["high_reference_mass_per_old_mean"]) == F(89, 4800), "high first coefficient")
    high_square = C * (F(shared["square_reference_factor"]) - F(13, 8))
    require(high_square == F(12259, 83700), "high square coefficient")
    require(C * (F(shared["reference_auxiliary_mean"]) - 1) == F(1009, 3720),
            "full auxiliary first coefficient")
    minimum = [None] * 4
    count = 0
    max_first = F(0)
    for m, n in product(range(1, 11), range(1, 13)):
        for k in range(min(12, m * n - 1) + 1):
            D = max(93, m * n - k)
            B = [[0, n, m, 1], [n, n, 1, 1], [m, 1, m, 1], [1, 1, 1, 1]]
            A = [[(D * COORDINATES[i] if i == j else 0) - SCALE * B[i][j]
                  for j in range(4)] for i in range(4)]
            for size in range(1, 5):
                det = determinant([r[:size] for r in A[:size]])
                require(det > 0, "common diagonal matrix: four positive leading minors")
                minimum[size - 1] = det if minimum[size - 1] is None else min(minimum[size - 1], det)
            f = min(C, F(120, m * n - k))
            q = (f * n / 120, f * m / 120, f / 120)
            require(all(a <= c for a, c in zip(q, (C / 10, C / 12, C / 120))),
                    "first moment coordinate coefficients")
            require(sum(q) <= F(55, 240), "first moment common rectangle sum")
            max_first = max(max_first, sum(q))
            count += 1
    saving = C / 10 + C / 12 + C / 120 - max_first
    require(count == 1372 and saving == F(9, 496), "complete rectangle domain and first saving")
    return {"rectangle_triples": count, "common_diagonal_numerators": list(COORDINATES),
            "common_diagonal_denominator": SCALE, "minimum_leading_principal_minors": minimum,
            "common_diagonal_sum": str(F(sum(COORDINATES), SCALE)),
            "high_square_coefficient": str(high_square), "first_numerator_saving": str(saving)}, high_square


def argmax_ratio(numerators, denominators):
    require(np.all(denominators > 0), "positive comparison denominators")
    best = 0
    for i in range(1, len(numerators)):
        if int(numerators[i]) * int(denominators[best]) > int(numerators[best]) * int(denominators[i]):
            best = i
    return best


def maximum_record(numerators, denominators, N, b):
    i = argmax_ratio(numerators, denominators)
    return {"bound": str(F(int(numerators[i]), int(denominators[i]))),
            "N": int(N[i]), "b": list(map(int, b[i]))}


def exact_first_shape_patches(b, N, loads, costs, indices):
    """Exact whole costs on firstshape N77..83; no external patch file."""
    int64_bound(144 * int(costs[indices].max()), "whole convex-cost table")
    table = np.maximum(np.arange(13)[:, None] - np.arange(12)[None, :], 0) @ costs[indices].T
    int64_bound(6 * loads.shape[1] * int(table.max()), "five exact whole convex costs")
    J = np.empty((len(loads), len(indices)), dtype=np.int64)
    for i, a in enumerate(loads):
        both = a + loads
        for j in range(len(indices)):
            J[i, j] = table[:, j][both].sum(axis=1).max()
    rows = []
    for count in range(77, 84):
        chosen = b[N == count]
        require(len(chosen) > 0, "exact whole-cost count is realized")
        values = []
        for j in range(len(indices)):
            v = table[:, j][loads]
            K = 5 * v.sum(axis=1) + J[:, j]
            loss = (v @ chosen.T).min(axis=1)
            values.append(int((K - loss).max()))
        rows.append({"N": count, "cost_indices": indices, "exact_numerators": values})
    return rows


def one_shape(index, name, points, classes, b, groups, geometry, data, square_factor, costs, assignments):
    n = len(points)
    case = data["shared_count_clipped_head"]["cases"][index]
    require(case["shape"] == name and len(points) == case["old_survivors"], "source shape identity")
    loads = complete_loads(points, groups)
    require(len(loads) == case["test_layouts"], "complete effective old layouts")
    profiles, independent = exact_old_profiles(points, b, loads)
    N = 6 * n - b.sum(axis=1)
    require(np.all(N > 0), "old survivor count")
    H = np.empty((len(b), 13), dtype=np.int64)
    H[:, 0] = profiles[:, 0]
    H[:, 1] = H[:, 0] - N
    H[:, 2:6] = profiles[:, 1:5]
    H[:, 6:13] = np.array([10, 7, 4, 3, 2, 1, 0], dtype=np.int64)
    G = profiles[:, 5]
    previous = {r["survivors"]: r for r in case["rows"]}
    common_previous = {r["survivors"]: r for r in
                       data["common_rectangle_moment_bounds"]["cases"][index]["rows"]}
    old = data["deletion_weighted_comparison"]["cases"][index]
    for count in sorted(set(map(int, N))):
        subset = N == count
        for t, key in ((0, "mean_upper"), (2, "hinge2_upper"), (4, "hinge4_upper")):
            require(F(int(H[subset, t].max()), count) <= F(previous[count][key]), "exact old hinge refines old cap")
        require(F(int(G[subset].max()), count) <= F(previous[count]["square_upper"]), "exact old square refines old cap")
        for t in (3, 5):
            require(F(int(H[subset, t].max()), count) <= F(old["hinge_bounds_at_0_through_5"][t]),
                    "exact old middle hinge refines old cap")
    int64_bound((3720 * int(N.max()) + 929 * int(H.max())), "head mass arithmetic")
    D = 3720 * N - 680 * H[:, 2] - 160 * H[:, 4] - 89 * H[:, 0]
    require(np.all(D > 0), "positive full actual head mass")
    sf_n, sf_d = square_factor.numerator, square_factor.denominator
    int64_bound(int(D.max()) * sf_d + 3720 * (sf_n * int(G.max()) + sf_d * int(N.max())),
                "transferred square numerator")
    gn = D * sf_d + 3720 * (sf_n * G - sf_d * N)
    gd = D * sf_d
    int64_bound(2 * int(D.max()) + 9458 * int(H[:, 0].max()) + 7575 * int(N.max()),
                "transferred first numerator")
    mn = 2 * D + 9458 * H[:, 0] - 7575 * N
    md = 2 * D
    require(np.all(gn >= 0) and np.all(mn >= 0), "nonnegative transferred moments")
    jc = data["joint_cost_hinge_refinement"]["cases"][index]
    base = np.array(jc["normalized_cost_numerator_upper"], dtype=np.int64)
    count_index = {count: j for j, count in enumerate(jc["survivor_counts"])}
    patches = []
    if index == 0:
        indices = [ci for ci, _ in assignments[2]]
        require(len(indices) == len(set(indices)) == 5, "five theta6 normalized whole costs")
        patches = exact_first_shape_patches(b, N, loads, costs, indices)
        for patch in patches:
            for ci, numerator in zip(patch["cost_indices"], patch["exact_numerators"]):
                base[ci, count_index[patch["N"]]] = min(base[ci, count_index[patch["N"]]], numerator)
    column_indices = np.array([count_index[int(count)] for count in N], dtype=np.int64)
    int64_bound(int(costs.max()) * int(H.max()) * 12, "normalized hinge-cost dot product")
    caps = np.minimum(H[:, :12] @ costs.T, base[:, column_indices].T)
    witnesses = data["actual_rectangle_hinge_profile"]["witnesses"]
    hinges = []
    for wi, witness in enumerate(witnesses):
        absolute_low_bound = abs(witness["constant_numerator"]) * int(N.max())
        absolute_low_bound += sum(scale * int(caps[:, ci].max()) for ci, scale in assignments[wi])
        int64_bound(absolute_low_bound, "rectangle dual numerator")
        low = witness["constant_numerator"] * N
        for ci, scale in assignments[wi]:
            low = low + scale * caps[:, ci]
        require(np.all(low >= 0), "nonnegative rectangle hinge upper bound")
        denominator = witness["denominator"]
        int64_bound(3720 * absolute_low_bound + 89 * denominator * int(H[:, 0].max()),
                    "transferred hinge numerator")
        int64_bound(denominator * int(D.max()), "transferred hinge denominator")
        numerator = 3720 * low + 89 * denominator * H[:, 0]
        denom = denominator * D
        record = maximum_record(numerator, denom, N, b)
        record["threshold"] = wi + 4
        hinges.append(record)
    ell_index = argmax_ratio(-D, 4800 * N)
    ell = {"bound": str(F(int(D[ell_index]), 4800 * int(N[ell_index]))),
           "N": int(N[ell_index]), "b": list(map(int, b[ell_index]))}
    # Check transferred formulas on every state with scalar Python/Fraction
    # arithmetic. This also checks coefficient simplification independently.
    for i, count in enumerate(N):
        count = int(count)
        m, h2, h4, g = (F(int(H[i, 0]), count), F(int(H[i, 2]), count),
                         F(int(H[i, 4]), count), F(int(G[i]), count))
        mass = 1 - (17 * h2 + 4 * h4) / 93 - F(89, 3720) * m
        require(mass == F(int(D[i]), 3720 * count), "scalar same-b mass identity")
        require(1 + (square_factor * g - 1) / mass == F(int(gn[i]), int(gd[i])),
                "scalar same-b square identity")
        require(1 + ((1 + F(1009, 3720)) * m - 1 - F(9, 496)) / mass == F(int(mn[i]), int(md[i])),
                "scalar same-b first identity")
        require(F(int(gn[i]), int(gd[i])) <= F(common_previous[count]["Gamma_upper"]),
                "same-b square refines the existing common rectangle result")
        require(F(int(mn[i]), int(md[i])) <= F(common_previous[count]["same_law_first_upper"]),
                "same-b mean refines the existing common rectangle result")
    return {"shape": name, "old_classes": [list(v) for v in classes], "old_points": points,
            "geometry": geometry, "old_test_layouts": len(loads),
            "N_range": [int(N.min()), int(N.max())], "independent_old_cost_check": independent,
            "Gamma_upper": maximum_record(gn, gd, N, b),
            "mean_upper": maximum_record(mn, md, N, b), "reference_fraction_lower": ell,
            "full_hinge_upper_at_4_through_12": hinges, "exact_whole_cost_patches": patches}


def verify(source):
    selected = {key: source[key] for key in ("shared_count_clipped_head", "deletion_weighted_comparison",
                "actual_rectangle_hinge_profile", "joint_cost_hinge_refinement", "common_rectangle_moment_bounds")}
    shared = source["shared_count_clipped_head"]
    constraints, high_square = rectangle_constraints(shared)
    common = source["common_rectangle_moment_bounds"]
    require(list(map(F, common["diagonal_witness"])) == [F(x, SCALE) for x in COORDINATES],
            "same existing common diagonal witness")
    require(F(common["square_extra_coefficient_sum"]) == F(sum(COORDINATES), SCALE)
            and F(common["high_square_coefficient"]) == high_square
            and F(common["positive_first_coefficient"]) == F(1009, 3720)
            and F(common["first_numerator_saving"]) == F(9, 496),
            "same existing exact rectangle moment coefficients")
    square_factor = 1 + F(sum(COORDINATES), SCALE) + high_square
    original_costs = source["joint_cost_hinge_refinement"]["normalized_hinge_costs"]
    require(len(original_costs) == 32 and all(len(row) == 12 and min(row) >= 0 for row in original_costs),
            "32 nonnegative normalized hinge costs")
    int64_bound(max(max(row) for row in original_costs), "input normalized costs")
    costs = np.array(original_costs, dtype=np.int64)
    assignments = []
    witnesses = source["actual_rectangle_hinge_profile"]["witnesses"]
    require([w["threshold"] for w in witnesses] == list(range(4, 13)), "nine existing rectangle duals")
    for witness in witnesses:
        require(witness["denominator"] > 0, "rectangle dual denominator")
        terms = []
        for values in witness["load_hinge_numerators"] + [witness["hole_hinge_numerators"]]:
            require(len(values) == 12 and min(values) >= 0, "nonnegative rectangle dual hinge coefficients")
            scale = gcd(*values)
            normal = [v // scale for v in values] if scale else [0] * 12
            terms.append((original_costs.index(normal), scale))
        assignments.append(terms)
    rows = []
    for root, category in product((1, 2), CATEGORIES):
        name = f"root{root}_{category}"
        progress(name + ": rebuilding both exact geometry enumerations")
        points, classes = old_points(root, category)
        b, groups, geometry = original_states(points)
        progress(name + ": independently verifying old costs and same-state transfer")
        row = one_shape(len(rows), name, points, classes, b, groups, geometry,
                        source, square_factor, costs, assignments)
        rows.append(row)
        progress(name + ": " + str(len(b)) + " states verified")
    require(sum(r["geometry"]["vectors"] for r in rows) == 161375, "complete optional-state count")
    def extreme(field, smallest=False):
        chooser = min if smallest else max
        row = chooser(rows, key=lambda r: F(r[field]["bound"]))
        return {"shape": row["shape"], **row[field]}
    full = []
    for index in range(9):
        row = max(rows, key=lambda r: F(r["full_hinge_upper_at_4_through_12"][index]["bound"]))
        full.append({"shape": row["shape"], **row["full_hinge_upper_at_4_through_12"][index]})
    return {"schema": "erdos7-common-fibre-head-experiment-v1",
            "scope": "same actual C=40/31 clipped law; full original357 part divides315; arbitrary actual11/13 axes, point holes and finite heights; no tail or Lean conclusion",
            "source_certificate_sections": list(selected), "source_sections_sha256": digest(selected),
            "source_inputs": "existing verified rectangle hinge duals, JC whole-cost bounds, common rectangle coefficients and high-height coefficients",
            "arithmetic": "exact signed-int64 arrays with checked intermediate bounds; Python integers and Fractions for final comparisons",
            "all_optional_deletion_vectors": 161375, "old_test_layouts": sum(r["old_test_layouts"] for r in rows),
            "rectangle_constraints": constraints, "square_transfer_factor": str(square_factor),
            "Gamma_upper": extreme("Gamma_upper"), "mean_upper": extreme("mean_upper"),
            "reference_fraction_lower": extreme("reference_fraction_lower", True),
            "full_hinge_upper_at_4_through_12": full, "cases": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-certificate", type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/marked_head_profile_certificate.json'))
    parser.add_argument("--write", type=Path, help="write the deterministic experiment result")
    parser.add_argument("--check", type=Path, help="compare with a saved experiment result")
    args = parser.parse_args()
    result = verify(json.loads(read_artifact_text(args.source_certificate)))
    if args.check:
        require(result == json.loads(read_artifact_text(args.check)), "saved experiment result matches recomputation")
    if args.write:
        write_certificate_text(args.write, json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("all_optional_deletion_vectors", "Gamma_upper", "mean_upper",
                      "reference_fraction_lower", "full_hinge_upper_at_4_through_12")}, separators=(",", ":")))


if __name__ == "__main__":
    main()
