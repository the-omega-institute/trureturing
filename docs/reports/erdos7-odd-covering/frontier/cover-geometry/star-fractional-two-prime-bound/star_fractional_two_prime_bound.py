#!/usr/bin/env python3
"""Independent exact checker for the all-height fractional two-prime lemma.

No project producer or old output is imported.  Enumerates literal five-cell
incidences and independently checks analytic elimination of the7 child.
The general fractional reduction remains a separate ordinary proof.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import hashlib
import json

CELLS = tuple(range(5))
ROOTS = (frozenset((0, 1, 2)), frozenset((3, 4)))
ANCHOR_REPS = (0, 3)
checks = {}


def require(name, condition):
    if name in checks:
        raise ValueError("duplicate check name: " + name)
    checks[name] = bool(condition)
    if not condition:
        raise ValueError(name)


def base_values(r5, r7, c5, c7, anchor):
    return tuple((F(1, 2) if j == anchor else F(1))
                 * (1 - F(int(j in ROOTS[r5]) + int(j == c5), 3))
                 * (1 - F(int(j in ROOTS[r7]) + int(j == c7), 5))
                 for j in CELLS)


def statistics(b):
    S = sum(b)
    R = max(sum(b[j] for j in root) for root in ROOTS)
    M = max(b)
    return S, R, M, 3 * S - R - M


rows = []
all_witnesses = []
representative_count = 0
elimination_count = 0
for r5, r7, anchor in product(range(2), range(2), ANCHOR_REPS):
    samples = []
    for c5, c7 in product(CELLS, repeat=2):
        b = base_values(r5, r7, c5, c7, anchor)
        S, R, M, L = statistics(b)
        samples.append({"child5": c5, "child7": c7,
                        "b": b, "S": S, "R": R, "M": M, "L": L})
        representative_count += 1
    s_winner = min(samples, key=lambda x: x["S"])
    l_winner = min(samples, key=lambda x: x["L"])

    # Independent analytic route: after fixing5, eliminate the7 child
    # by the exact sum(w)-[sum_on_7root(w)+max(w)]/5 identity.
    s_candidates, l_candidates = [], []
    for c5 in CELLS:
        w0 = tuple((F(1, 2) if j == anchor else F(1))
                   * (1 - F(int(j in ROOTS[r5]) + int(j == c5), 3))
                   for j in CELLS)
        s_candidates.append(sum(w0) - (sum(w0[j] for j in ROOTS[r7]) + max(w0)) / 5)
        for sigma, m in product(range(2), CELLS):
            w = tuple((3 - int(j in ROOTS[sigma]) - int(j == m)) * w0[j]
                      for j in CELLS)
            l_candidates.append(sum(w) - (sum(w[j] for j in ROOTS[r7]) + max(w)) / 5)
            elimination_count += 1
    key = "roots" + str(len(ROOTS[r5])) + str(len(ROOTS[r7])) + "_anchor" + str(3 if anchor == 0 else 2)
    require(key + "_S_elimination_agrees", min(s_candidates) == s_winner["S"])
    require(key + "_L_elimination_agrees", min(l_candidates) == l_winner["L"])
    require(key + "_S_lower", s_winner["S"] >= F(79, 30))
    require(key + "_L_lower", l_winner["L"] >= F(28, 5))
    row = {"parent5_root_size": len(ROOTS[r5]), "parent7_root_size": len(ROOTS[r7]),
           "anchor_root_size": 3 if anchor == 0 else 2,
           "min_S": s_winner["S"], "min_3S_R_M": l_winner["L"],
           "S_witness": s_winner, "L_witness": l_winner}
    rows.append(row)
    all_witnesses.extend(samples)

# Literal anchors, without orbit reduction, check all500 possibilities.
literal_count = 0
literal_S, literal_L = None, None
linearization_checks = 0
for r5, r7, c5, c7, anchor in product(range(2), range(2), CELLS, CELLS, CELLS):
    b = base_values(r5, r7, c5, c7, anchor)
    S, R, M, L = statistics(b)
    if S < F(79, 30) or L < F(28, 5):
        raise ValueError("literal five-cell inequality")
    if L != min(sum((3 - int(j in ROOTS[sigma]) - int(j == m)) * b[j]
                    for j in CELLS) for sigma, m in product(range(2), CELLS)):
        raise ValueError("R+M linearization")
    literal_S = S if literal_S is None else min(literal_S, S)
    literal_L = L if literal_L is None else min(literal_L, L)
    literal_count += 1
    linearization_checks += 1
require("all_500_literal_layouts_checked", literal_count == 500)
require("all_500_R_M_linearizations_checked", linearization_checks == 500)
require("global_S_constant_sharp_in_relaxation", literal_S == F(79, 30))
require("global_L_constant_sharp_in_relaxation", literal_L == F(28, 5))
require("two_anchor_orbits_cover_global_minima", min(r["min_S"] for r in rows) == literal_S and min(r["min_3S_R_M"] for r in rows) == literal_L)
require("representative_candidate_count", representative_count == 200)
require("analytic_child_elimination_candidates", elimination_count == 400)

expected_table = (
    (3, 3, 3, F(14, 5), F(29, 5)),
    (3, 3, 2, F(79, 30), F(28, 5)),
    (3, 2, 3, F(41, 15), F(6)),
    (3, 2, 2, F(8, 3), F(17, 3)),
    (2, 3, 3, F(14, 5), F(29, 5)),
    (2, 3, 2, F(43, 15), F(28, 5)),
    (2, 2, 3, F(91, 30), F(6)),
    (2, 2, 2, F(49, 15), F(31, 5)),
)
require("recovered_eight_row_table", tuple((r["parent5_root_size"], r["parent7_root_size"], r["anchor_root_size"], r["min_S"], r["min_3S_R_M"]) for r in rows) == expected_table)

big_primes = (11, 13, 17, 19)
ustar = sum(F(1, q - 2) for q in big_primes)
all_u = F(1, 3) + F(1, 5) + ustar
coefficient = 1 - 3 * ustar
W_lower = coefficient * F(79, 30) + F(28, 5) * ustar
small_depth_loss = 1 - F(2, 9) * W_lower
deep_ternary_tail = all_u / 9
total_loss = small_depth_loss + deep_ternary_tail
simple_loss = F(64, 135) + F(28, 45) * ustar
threshold = F(173, 250)
survivor = 1 - total_loss
omega_lower = F(935, 4096)
haar_survivor = omega_lower * survivor
query_upper = (1 / omega_lower - 1) / survivor
query_target = F(565, 51)

require("large_prime_budget", ustar == F(2756, 8415))
require("S_coefficient_positive", coefficient == F(49, 2805) > 0)
require("all_prime_budget", all_u == F(7244, 8415))
require("W_lower", W_lower == F(158207, 84150))
require("small_depth_union_bound", small_depth_loss == F(220468, 378675))
require("complete_ternary_tail", deep_ternary_tail == F(7244, 75735))
require("total_loss_two_equivalent_forms", total_loss == simple_loss == F(256688, 378675))
require("strict_loss_target", threshold - total_loss == F(53551, 3786750) > 0)
require("same_source_conditional_survivor", survivor == F(121987, 378675))
require("full_Haar_survivor_bound", haar_survivor == F(121987, 1658880) > 0)
require("complete_query_upper_bound", query_upper == F(1280205, 121987))
require("strict_query_target", query_target - query_upper == F(3632200, 6221337) > 0)
require("actual_seven_prime_pure_factor", prod(F(p - 2, p - 1) for p in (3, 5, 7, 11, 13, 17, 19)) == omega_lower)

# For any finite R of primes>=11, the ordinary proof uses only
# U=sum_{q in R}1/(q-2), provided 0<=U<=1/3.  Its formula is affine in U.
# These endpoint checks verify exact stated constants; they do not replace
# the general proof of the budget reduction or of monotonicity.
general_endpoints = []
for u, expected_loss, expected_survivor in (
        (F(0), F(64, 135), F(71, 135)),
        (F(1, 3), F(92, 135), F(43, 135))):
    coeff = 1 - 3 * u
    low_w = coeff * F(79, 30) + F(28, 5) * u
    loss = 1 - F(2, 9) * low_w + (F(1, 3) + F(1, 5) + u) / 9
    tag = "general_U_" + str(u)
    require(tag + "_S_coefficient_nonnegative", coeff >= 0)
    require(tag + "_loss_formula", loss == F(64, 135) + F(28, 45) * u == expected_loss)
    require(tag + "_positive_survivor", 1 - loss == expected_survivor > 0)
    general_endpoints.append({"U": u, "S_coefficient": coeff, "W_lower": low_w,
                              "loss_upper": loss, "survivor_lower": 1 - loss})
require("general_base_pure_factor", prod(F(p - 2, p - 1) for p in (3, 5, 7)) == F(5, 16))
require("general_uniform_bound_below_one", F(92, 135) < 1)

out = {"complete": True,
       "scope": "Independent exact finite two-prime lemma and downstream arithmetic; fractional five-cell dominance and vertex reduction are separate ordinary proofs, not empirical conclusions.",
       "cells": CELLS, "roots": [sorted(r) for r in ROOTS],
       "anchor_representatives": ANCHOR_REPS, "u5": F(1, 3), "u7": F(1, 5),
       "eight_rows": rows, "representative_layouts": representative_count,
       "literal_layouts": literal_count, "literal_R_M_linearizations": linearization_checks,
       "analytic_child_elimination_candidates": elimination_count,
       "Ustar": ustar, "positive_S_coefficient": coefficient, "W_lower": W_lower,
       "depth12_union_bound": small_depth_loss, "complete_depth3plus_tail": deep_ternary_tail,
       "full_actual_loss_upper": total_loss, "loss_target": threshold,
       "strict_loss_margin": threshold - total_loss,
       "pure_source_survivor_lower": survivor, "full_Haar_survivor_lower": haar_survivor,
       "all_query_upper": query_upper, "all_query_target": query_target,
       "strict_query_margin": query_target - query_upper,
       "general_finite_R_scope": "R is any finite set of primes>=11 with U=sum1/(q-2)<=1/3; mixed moduli are3^a*q^b for q in{5,7} union R. The same seven-prime G constants are not asserted for arbitrary R.",
       "general_formula": "loss<=64/135+(28/45)*U<=92/135; Haar(U_actual)>=(5/16)*product_R[(q-2)/(q-1)]*[71/135-(28/45)*U]",
       "general_endpoints": general_endpoints,
       "checks": checks, "passed_count": len(checks), "Lean": "not run"}


def encode(v):
    if isinstance(v, F):
        return str(v)
    raise TypeError(type(v).__name__)


dest = Path(__file__).with_suffix(".json")
dest.write_text(json.dumps(out, indent=2, default=encode) + "\n", encoding="utf-8")
for row in rows:
    print(row["parent5_root_size"], row["parent7_root_size"], row["anchor_root_size"], row["min_S"], row["min_3S_R_M"])
print(json.dumps({"passed_count": len(checks), "literal_layouts": literal_count,
                  "loss": str(total_loss), "loss_display": float(total_loss),
                  "loss_margin": str(threshold - total_loss),
                  "output": str(dest), "sha256": hashlib.sha256(dest.read_bytes()).hexdigest()}, indent=2))
