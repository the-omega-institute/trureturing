#!/usr/bin/env python3
"""Exact five-cell bound for all-height distinct-modulus 3-star grids.

Each parent/child role carries the entire outside-height budget 1/(q-2),
not just the single numerical label 3q or 9q. The general fractional-budget
reduction and five-cell domination are ordinary mathematical premises.
This program certifies their fixed-six-prime incidence optimum, literal
witnesses, complete a>=3 tail, one-law consequences, and fresh23/29 bound.
It imports no project producer and scans no original periods or heights.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
import hashlib
import json

Q = (5, 7, 11, 13, 17, 19)
P = (3,) + Q
M = 1 << len(Q)
FULL = M - 1
D = prod(q - 2 for q in Q)
checks = {}
work = {"local_partition_candidates": 0, "outer_root_splits": 0}


def require(name, value):
    if name in checks:
        raise ValueError("duplicate check: " + name)
    checks[name] = bool(value)
    if not value:
        raise ValueError("failed check: " + name)


submasks = []
for b in range(M):
    terms, c = [], b
    while True:
        terms.append(c)
        if c == 0:
            break
        c = (c - 1) & b
    submasks.append(terms)


def integer_leaf(a, b):
    return prod(q - 2 - ((a >> i) & 1) - ((b >> i) & 1)
                for i, q in enumerate(Q))


def rational_leaf(a, b):
    return prod(1 - F(((a >> i) & 1) + ((b >> i) & 1), q - 2)
                for i, q in enumerate(Q))


K = [[integer_leaf(a, b) for b in range(M)] for a in range(M)]
require("common_denominator", D == 378675)
require("all4096_integer_leaf_factors", all(F(K[a][b], D) == rational_leaf(a, b)
                                           for a in range(M) for b in range(M)))
require("all_leaf_factors_positive", all(x > 0 for row in K for x in row))
require("empty_leaf_includes_avoidance_cost", K[0][0] == D)

# Build the unscaled symmetric pair first. The resulting pair then gives
# both types of 3-leaf root. This is an independent formulation of SO4.
local = {(s, anchored): [[0] * M for _ in range(M)]
         for s in (2, 3) for anchored in (False, True)}
back = {name: [[0] * M for _ in range(M)]
        for name in ("pair", "anchor2", "ordinary3", "anchor3")}
for a in range(M):
    row = K[a]
    pair = [0] * M
    for b in range(M):
        c = min(submasks[b], key=lambda t: row[t] + row[b ^ t])
        work["local_partition_candidates"] += len(submasks[b])
        pair[b] = row[c] + row[b ^ c]
        back["pair"][a][b] = c
        local[2, False][a][b] = 2 * pair[b]
    for b in range(M):
        choices = (
            ("anchor2", (2, True), lambda c: row[c] + 2 * row[b ^ c]),
            ("ordinary3", (3, False), lambda c: 2 * (row[c] + pair[b ^ c])),
            ("anchor3", (3, True), lambda c: row[c] + 2 * pair[b ^ c]),
        )
        for name, key, objective in choices:
            c = min(submasks[b], key=objective)
            work["local_partition_candidates"] += len(submasks[b])
            back[name][a][b] = c
            local[key][a][b] = objective(c)


def child_partition(a, b, size, anchored):
    if size == 2:
        c = back["anchor2" if anchored else "pair"][a][b]
        return [c, b ^ c]
    c = back["anchor3" if anchored else "ordinary3"][a][b]
    rest = b ^ c
    e = back["pair"][a][rest]
    return [c, e, rest ^ e]


def optimize(anchor_size):
    best = None
    for a in range(M):
        for b in range(M):
            value = (local[anchor_size, True][a][b]
                     + local[5 - anchor_size, False][FULL ^ a][FULL ^ b])
            work["outer_root_splits"] += 1
            if best is None or value < best[0]:
                best = value, a, b
    W, a, b = best
    roots = [
        {"parent_mask": a, "child_masks": child_partition(a, b, anchor_size, True),
         "anchor_cell": 0},
        {"parent_mask": FULL ^ a,
         "child_masks": child_partition(FULL ^ a, FULL ^ b, 5-anchor_size, False),
         "anchor_cell": None},
    ]
    return {"anchor_root_size": anchor_size, "minimum_integer_cost": W,
            "linearized_bound": 1 - F(W, 9 * D), "roots": roots}


def check_literal(name, data):
    parents, children = 0, 0
    values, weighted, anchors = [], 0, []
    role_layout = {}
    for root_index, root in enumerate(data["roots"]):
        a = root["parent_mask"]
        require(name + "_parent_disjoint_root" + str(root_index), not (parents & a))
        parents |= a
        for i, q in enumerate(Q):
            if a & (1 << i):
                role_layout.setdefault(str(q), {})["parent_root"] = root_index
        root_values = []
        for cell, b in enumerate(root["child_masks"]):
            require(name + "_child_disjoint_" + str(root_index) + "_" + str(cell),
                    not (children & b))
            children |= b
            value = integer_leaf(a, b)
            root_values.append(value)
            values.append(value)
            is_anchor = cell == root["anchor_cell"]
            weighted += (1 if is_anchor else 2) * value
            if is_anchor:
                anchors.append(value)
            for i, q in enumerate(Q):
                if b & (1 << i):
                    role_layout.setdefault(str(q), {})["child_cell"] = [root_index, cell]
        root["integer_avoidance_values"] = root_values
    require(name + "_all_parent_roles_once", parents == FULL)
    require(name + "_all_child_roles_once", children == FULL)
    require(name + "_five_cells_one_anchor", len(values) == 5 and len(anchors) == 1)
    require(name + "_literal_integer_cost", weighted == data["minimum_integer_cost"])
    phi = 1 - F(2 * sum(values) - max(values), 9 * D)
    require(name + "_branch_not_above_its_full_phi", data["linearized_bound"] <= phi)
    data["literal_role_layout"] = role_layout
    data["full_phi"] = phi
    data["anchor_avoidance_numerator"] = anchors[0]
    data["maximum_avoidance_numerator"] = max(values)


cases = {str(size): optimize(size) for size in (2, 3)}
for size, data in cases.items():
    check_literal("anchor" + size, data)
require("two_cell_anchor_endpoint", cases["2"]["minimum_integer_cost"] == 1517020)
require("three_cell_anchor_endpoint", cases["3"]["minimum_integer_cost"] == 1569570)
B12 = max(data["linearized_bound"] for data in cases.values())
require("complete_low_depth_block", B12 == F(378211, 681615))
require("all_reconstructed_full_phis_below_optimum", all(data["full_phi"] <= B12 for data in cases.values()))
require("winning_anchor_is_global_maximum", cases["2"]["anchor_avoidance_numerator"] == cases["2"]["maximum_avoidance_numerator"])

# Separately supplied explicit layout: root A has two cells with anchor A1.
# Every budget is global: one root and one cell per outside prime.
explicit = {"anchor_root_size": 2, "minimum_integer_cost": 1517020,
            "linearized_bound": B12,
            "roots": [{"parent_mask": 2, "child_masks": [58, 0], "anchor_cell": 1},
                      {"parent_mask": 61, "child_masks": [1, 4, 0], "anchor_cell": None}]}
check_literal("independent_explicit_layout", explicit)
require("explicit_five_leaf_numerators", [x for r in explicit["roots"] for x in r["integer_avoidance_values"]]
        == [181440, 302940, 89600, 156800, 179200])
require("explicit_layout_attains_relaxed_optimum", explicit["full_phi"] == B12)

# Every outside height was already absorbed at a=1,2. Only a>=3 remains.
full_budget = sum(F(1, q-2) for q in Q)
ternary_tail = full_budget / 9
loss = B12 + ternary_tail
threshold = F(173, 250)
r_lower = 1 - loss
pure_mass_lower = prod(F(p-2, p-1) for p in P)
base_H_lower = pure_mass_lower * r_lower
Dmax = 1 / pure_mass_lower
R_upper = (Dmax - 1) / r_lower
query_target = F(565, 51)
require("full_outside_budget", full_budget == F(7244, 8415))
require("complete_ternary_tail", ternary_tail == F(7244, 75735))
require("actual_mixed_loss_upper", loss == F(443407, 681615))
require("loss_threshold_margin", threshold - loss == F(1413529, 34080750) > 0)
require("pure_mass_floor", pure_mass_lower == F(935, 4096))
require("actual_full_base_survivor_mass", base_H_lower == F(1861, 23328))
require("same_law_query_bound", R_upper == F(2304369, 238208))
require("query_target_margin", query_target - R_upper == F(17064701, 12148608) > 0)

# The existing541 G bridge: one core, one complete pure source, full U.
A = F(212731, 110592)
require("unused_query_budget_monotonicity", (A-loss)/(1-loss) < (A-threshold)/(1-threshold) < 4)
require("survivor_density_threshold", Dmax/(1-loss) < Dmax/(1-threshold) < 15)
require("entropy_rational_guard", F(19, 7)**8 > (Dmax/(1-threshold))**3)
require("lambda_rational_guard", F(68, 25)**20 < F(800)**3)

# Arbitrary distinct NEW labels touching23or29, arbitrary old P cofactors.
# This pays all fresh heights, including the unit old cofactor exactly once.
fresh_factor = F(23, 22) * F(29, 28) - 1
fresh_remaining = 1 - (1+R_upper) * fresh_factor
extension_H_lower = base_H_lower * fresh_remaining
require("complete_fresh_prime_factor", fresh_factor == F(51, 616))
require("fresh_remaining_probability", fresh_remaining == F(17064701, 146736128) > 0)
require("full_fresh_extension_survivor_mass", extension_H_lower == F(17064701, 1839366144) > 0)
require("local_partition_work", work["local_partition_candidates"] == 4*M*3**len(Q))
require("outer_root_work", work["outer_root_splits"] == 2*M*M)

out = {
    "complete": True,
    "scope": "Exact conservative fractional-budget incidence optimum for all-height3^a q^b families; not a sharp actual-family supremum or unrestricted odd-covering result.",
    "prime_order": Q, "base_carrier": P,
    "role_meaning": "Parent q carries all b>=1 at a=1; child q carries all b>=1 at a=2. Each budget is1/(q-2).",
    "common_denominator": D, "leaf_rule": "product(q-2-parent_bit-child_bit)",
    "anchor_orbits": cases, "independent_explicit_layout": explicit,
    "B12": B12, "all_outside_height_budget": full_budget,
    "complete_a_ge3_tail": ternary_tail, "actual_mixed_loss_upper": loss,
    "actual_mixed_loss_threshold_margin": threshold-loss,
    "pure_survivor_mass_lower": pure_mass_lower,
    "conditional_survivor_mass_lower": r_lower,
    "full_base_H_survivor_mass_lower": base_H_lower,
    "complete_base_query_upper": R_upper,
    "base_query_target_margin": query_target-R_upper,
    "fresh_extension": {
        "carrier": P+(23,29), "all_height_cap_factor": fresh_factor,
        "survivor_under_base_law_times_fresh_Haar_lower": fresh_remaining,
        "full_H_survivor_mass_lower": extension_H_lower,
        "hypothesis": "New numerical labels are distinct, supported on the extended carrier, and each touches23or29. Old P-only mixed labels retain the star hypothesis; all new P cofactors, phases and finite heights are arbitrary.",
        "limitation": "The base query bound and base G are not asserted unchanged after conditioning on the new originals."
    },
    "bridge": "Use report541 SC1-SC3 on one fixed core/pure source and its full actual survivor.",
    "work": work, "checks": checks, "passed_count": len(checks),
    "verification": "Exact integers and fractions. No old producer, original-family enumeration, height cutoff, or Lean."
}

def encode(x):
    if isinstance(x, F):
        return str(x)
    raise TypeError(type(x).__name__)

dest = Path(__file__).with_suffix(".json")
dest.write_text(json.dumps(out, indent=2, default=encode)+"\n", encoding="utf-8")
print(json.dumps({"B12": str(B12), "actual_mixed_loss_upper": str(loss),
                  "base_query_upper": str(R_upper), "base_H_lower": str(base_H_lower),
                  "extension_H_lower": str(extension_H_lower),
                  "passed_count": len(checks), "work": work,
                  "output": str(dest), "output_sha256": hashlib.sha256(dest.read_bytes()).hexdigest()}, indent=2))
