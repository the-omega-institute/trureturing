#!/usr/bin/env python3
"""Exact fixed-family bad-mass rearrangement and final-survivor comparison.

Run with Python 3, optionally under -I -O. The default recomputes every result
and compares the entire adjacent certificate. --write generates that file.
Only standard-library integer and Fraction arithmetic is used.

Full physical test domain: each divisor d of 225 has its own independently
chosen residue, including the unit label. On the old Dirac law at 1 mod 9,
choosing every old component to meet 1 can only increase the nonnegative
load. There are three distinct original old labels (1,3,9) at each current
depth 0,1,2. The load is then 3 + sum_j I_(r_j mod5) + sum_k I_(t_k mod25).
It is the average of the nine loads 3(1 + I_(r_j mod5) + I_(t_k mod25)).
Jensen's inequality bounds its squared expectation by the largest of the
125 (root,leaf) squared expectations. Conversely each pair is realized by
choosing that root or leaf for all three original labels at its depth.
Thus the reduction is exact over every physical residue assignment; the
125 pairs include nonnested root/leaf choices. All reported maximizers are
also replayed as literal CRT classes modulo the nine original divisors.

For the fixed feasible kernel class, good leaves retain mass 1/12, bad
densities relative to the 20-point pure base lie in [0,1], and total bad
mass is 1/3. Every feasible law puts at least 1/3 on root 3, due to its four
good leaves, and exactly 1/12 on good leaf 8. The nested pair (3,8) forces
V >= 9(1 + 3/3 + 5/12) = 87/4. The candidate attains this lower bound.
Here V denotes the preconditioning complete-test value. Both laws give the
same normalized actual survivor law, whose complete-test value is Gamma.
This fixed-family gain does not improve an outer worst-family envelope or
the final survivor law, and is not a Lean kernel verification.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import argparse
import json


PERIOD = 225
OLD_MODULUS = 9
OLD_POINT = 1
OLD_CLASSES = [(3, 0), (9, 0)]
PURE_CLASSES = [(5, 0), (25, 0)]
MIXED_CLASSES = [(15, 1), (45, 37), (75, 28), (225, 154)]
DIVISORS = [d for d in range(1, PERIOD + 1) if PERIOD % d == 0]


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def crt(a, m, b, n):
    values = [x for x in range(m * n) if x % m == a and x % n == b]
    require(len(values) == 1, "unique coprime CRT solution")
    return values[0]


def mass(law, points):
    return sum((law[x] for x in points), F(0))


def caps(law, modulus):
    return [mass(law, (x for x in range(PERIOD) if x % modulus == a))
            for a in range(modulus)]


def test_family(root, leaf):
    classes = []
    for depth in range(3):
        current_modulus = 5 ** depth
        current_residue = (0, root, leaf)[depth]
        for old_divisor in (1, 3, 9):
            residue = crt(OLD_POINT % old_divisor, old_divisor,
                          current_residue, current_modulus)
            classes.append([old_divisor * current_modulus, residue])
    classes.sort()
    require([d for d, a in classes] == DIVISORS, "complete original test labels")
    return classes


def physical_square(law, classes):
    return sum((weight * sum(x % d == a for d, a in classes) ** 2
                for x, weight in enumerate(law)), F(0))


def complete_value(law):
    require(sum(law, F(0)) == 1, "normalized test law")
    require(all(w >= 0 and (w == 0 or x % 9 == OLD_POINT)
                for x, w in enumerate(law)), "old Dirac support")
    roots, leaves = caps(law, 5), caps(law, 25)
    values = {}
    for root, leaf in product(range(5), range(25)):
        value = 9 * (1 + 3 * roots[root]
                     + (3 + 2 * (leaf % 5 == root)) * leaves[leaf])
        require(value == physical_square(law, test_family(root, leaf)),
                "every reduced test has its literal CRT realization")
        values[root, leaf] = value
    maximum = max(values.values())
    maximizers = [list(pair) for pair, value in values.items() if value == maximum]
    return {"value": str(maximum), "maximizing_pairs": maximizers,
            "physical_test_witness": test_family(*maximizers[0])}


def law_record(law, base, bad, good, all_classes, beta, C):
    require(sum(law, F(0)) == 1, "total probability")
    require(caps(law, OLD_MODULUS) == [F(int(a == OLD_POINT)) for a in range(9)],
            "unchanged full old marginal")
    require(all(0 <= law[x] <= C * base[x] for x in range(PERIOD)),
            "pointwise global density cap")
    require(all(law[x] == C * base[x] for x in good), "fixed good density")
    require(all(0 <= law[x] <= base[x] for x in bad),
            "pointwise bad-subset domination")
    require(mass(law, bad) == beta and mass(law, good) == 1 - beta,
            "fixed assigned bad charge and good mass")
    for d in DIVISORS:
        require(all(q <= C * p for q, p in zip(caps(law, d), caps(base, d))),
                "every original-divisor cylinder cap")
    current_caps = {d: caps(law, d) for d in (5, 25)}
    class_masses = [mass(law, (x for x in range(PERIOD) if x % d == a))
                    for d, a in all_classes]
    require(class_masses[:4] == [0] * 4, "old and pure classes have zero mass")
    require(sum(class_masses[4:], F(0)) == beta,
            "disjoint literal mixed classes carry the assigned charge")
    return {"current_leaf_masses": [str(v) for v in current_caps[25]],
            "current_root_masses": [str(v) for v in current_caps[5]],
            "old_marginal": [str(v) for v in caps(law, 9)],
            "total_mass": "1", "bad_mass_and_assigned_charge": str(beta),
            "good_mass": str(1 - beta),
            "density_cap": str(C),
            "sharp_prefix_caps": {"depth1": str(max(current_caps[5])),
                                  "depth2": str(max(current_caps[25]))},
            "required_prefix_upper_caps": {"depth1": str(C / 4),
                                           "depth2": str(C / 20)},
            "original_class_masses": [str(v) for v in class_masses],
            "physical_complete_test_V": complete_value(law)}


def recompute():
    all_classes = OLD_CLASSES + PURE_CLASSES + MIXED_CLASSES
    require(len(all_classes) == len({d for d, a in all_classes}) == 8,
            "eight distinct original labels")
    require(sorted(d for d, a in all_classes) == DIVISORS[1:],
            "literal full nonunit divisor inventory")
    require(all(d % 2 == 1 and 0 <= a < d for d, a in all_classes),
            "odd original moduli and canonical residues")
    old_survivors = [x for x in range(9) if all(x % d != a for d, a in OLD_CLASSES)]
    require(OLD_POINT in old_survivors, "old law avoids old forbidden classes")
    points = [crt(OLD_POINT, 9, y, 25) for y in range(25)]
    require(len(set(points)) == 25, "one physical point per current leaf")
    base_points = [x for x in points if all(x % d != a for d, a in PURE_CLASSES)]
    require(len(base_points) == 20 and {x % 25 for x in base_points}
            == {y for y in range(25) if y % 5 != 0}, "actual pure-survivor base")
    bad = [x for x in base_points if any(x % d == a for d, a in MIXED_CLASSES)]
    good = sorted(set(base_points) - set(bad))
    bad_leaves = sorted(x % 25 for x in bad)
    good_leaves = sorted(x % 25 for x in good)
    require(bad_leaves == [y for y in range(25) if y % 5 in (1, 2) or y in (3, 4)],
            "actual mixed union: roots 1,2 and leaves 3,4")
    projections = []
    for (d, a), old_d, depth, residue in zip(MIXED_CLASSES, (3, 9, 3, 9),
                                            (1, 1, 2, 2), (1, 2, 3, 4)):
        require(d == old_d * 5 ** depth and a % old_d == OLD_POINT % old_d
                and a % (5 ** depth) == residue, "literal mixed CRT projection")
        projections.append({"modulus": d, "residue": a, "old_cofactor": old_d,
                            "old_residue": a % old_d, "current_depth": depth,
                            "current_residue": residue})
    base = [F(int(x in base_points), 20) for x in range(PERIOD)]
    alpha, delta = mass(base, bad), F(2, 5)
    require(0 < delta < alpha < 1, "nondegenerate distortion row")
    C, beta = 1 / (1 - delta), (alpha - delta) / (1 - delta)
    r = beta / alpha
    bb = [C * base[x] if x in good else r * base[x] if x in bad else F(0)
          for x in range(PERIOD)]
    candidate = [C * base[x] if x in good else F(2, 3) * base[x]
                 if x in bad and x % 5 in (1, 2) else F(0) for x in range(PERIOD)]
    laws = {"BB": law_record(bb, base, bad, good, all_classes, beta, C),
            "candidate": law_record(candidate, base, bad, good, all_classes, beta, C)}
    require(F(laws["BB"]["physical_complete_test_V"]["value"]) == F(45, 2), "BB value")
    candidate_value = F(laws["candidate"]["physical_complete_test_V"]["value"])
    require(candidate_value == F(87, 4), "candidate value")
    forced_root_mass = sum((C * base[x] for x in good if x % 5 == 3), F(0))
    forced_leaf_mass = C * base[crt(OLD_POINT, 9, 8, 25)]
    minimax_lower = 9 * (1 + 3 * forced_root_mass + 5 * forced_leaf_mass)
    require(forced_root_mass == F(1, 3) and forced_leaf_mass == F(1, 12)
            and minimax_lower == candidate_value, "fixed-class minimax lower bound attained")
    actual_survivors = [x for x in range(PERIOD)
                        if all(x % d != a for d, a in all_classes)]
    global_bad = {x for x in range(PERIOD) if any(x % d == a for d, a in MIXED_CLASSES)}
    require(not set(actual_survivors).intersection(global_bad), "all actual survivors avoid mixed union")
    require(set(actual_survivors).intersection(base_points) == set(good),
            "actual surviving support is precisely the eight good leaves")
    survivor_masses = [mass(law, actual_survivors) for law in (bb, candidate)]
    require(survivor_masses == [F(2, 3), F(2, 3)], "same positive actual survivor mass")
    conditioned = [[law[x] / rho if x in actual_survivors else F(0)
                    for x in range(PERIOD)] for law, rho in zip((bb, candidate), survivor_masses)]
    require(conditioned[0] == conditioned[1], "identical full normalized survivor laws")
    require(all(conditioned[0][x] == F(1, 8) for x in good), "uniform eight-point survivors")
    final_value = complete_value(conditioned[0])
    require(F(final_value["value"]) == F(225, 8), "exact final survivor Gamma")
    return {
        "schema": "erdos7-bad-mass-rearrangement-v1",
        "scope": "A strict fixed-family reduction of physical complete-test V; the final survivor laws and Gamma are unchanged. No outer worst-family improvement is claimed.",
        "period": PERIOD, "old_modulus": OLD_MODULUS, "old_Dirac_point": OLD_POINT,
        "original_forbidden_classes": [list(c) for c in all_classes],
        "mixed_CRT_projections": projections,
        "mixed_labels_per_depth": {"1": 2, "2": 2},
        "old_survivors": old_survivors,
        "physical_points_by_current_leaf": points,
        "pure_base_current_leaves": sorted(x % 25 for x in base_points),
        "bad_current_leaves": bad_leaves, "good_current_leaves": good_leaves,
        "alpha": str(alpha), "delta": str(delta), "C": str(C),
        "retained_bad_mass_beta": str(beta), "BB_bad_density_r": str(r),
        "candidate_bad_densities": {"roots1and2": "2/3", "leaves3and4": "0"},
        "laws": laws,
        "full_test_domain": {
            "original_moduli": DIVISORS, "original_residue_assignments": prod(DIVISORS),
            "old_labels_at_each_depth": [1, 3, 9], "reduced_root_leaf_pairs": 125,
            "reduction": "On the old Dirac support all old components may be chosen to match 1. The load 3+sum_j I_rj+sum_k I_tk is the average of nine loads 3(1+I_rj+I_tk). Jensen gives the maximum of all 5*25 pairs; repeating any pair across all three original labels attains it. Each pair is replayed as literal CRT tests.",
        },
        "fixed_feasible_class_minimax": {
            "constraints": "Good density is C; bad densities relative to the pure base lie in [0,1]; bad mass is beta; the old marginal stays Dirac1.",
            "forced_root3_mass_lower": str(forced_root_mass),
            "forced_good_leaf8_mass": str(forced_leaf_mass),
            "test_pair": [3, 8], "exact_minimum_V": str(minimax_lower),
            "proof": "Root3 contains four fixed good leaves, hence mass at least 1/3. Good leaf8 has mass 1/12. Its nested physical test gives V>=9(1+3/3+5/12)=87/4, attained by the candidate.",
            "BB_minus_minimum_V": str(F(45, 2) - minimax_lower),
        },
        "actual_survivor_comparison": {
            "all_actual_survivors_mod225": actual_survivors,
            "supported_actual_survivors": sorted(good),
            "BB_survivor_mass": str(survivor_masses[0]),
            "candidate_survivor_mass": str(survivor_masses[1]),
            "common_normalized_current_leaf_masses": [str(v) for v in caps(conditioned[0], 25)],
            "Gamma": final_value["value"],
            "maximizing_pairs": final_value["maximizing_pairs"],
            "physical_test_witness": final_value["physical_test_witness"],
        },
    }


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate certificate key: " + key)
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("bad_mass_rearrangement_certificate.json"))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = recompute()
    if args.write:
        args.certificate.write_text(json.dumps(result, indent=2) + "\n")
    else:
        stored = json.loads(args.certificate.read_text(), object_pairs_hook=unique_object)
        require(json.dumps(stored, sort_keys=True) == json.dumps(result, sort_keys=True),
                "entire exact rearrangement certificate matches recomputation")
    print(json.dumps({"BB_V": result["laws"]["BB"]["physical_complete_test_V"]["value"],
                      "minimum_V": result["fixed_feasible_class_minimax"]["exact_minimum_V"],
                      "survivor_Gamma": result["actual_survivor_comparison"]["Gamma"]}))


if __name__ == "__main__":
    main()
