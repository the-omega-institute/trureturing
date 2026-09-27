#!/usr/bin/env python3
"""Exact all-height stars, triangle and old57 boundary with joint root queries.

Requires Python3 standard library and a C++17 compiler (default c++).
Compiles the adjacent integer optimizer in a temporary directory. Retains
only result data; no build products, old producers or old data are used.
"""
import argparse
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import shlex
import subprocess
import tempfile

checks = {}


def require(name, condition):
    if name in checks:
        raise ValueError("duplicate check: " + name)
    checks[name] = bool(condition)
    if not condition:
        raise ValueError(name)


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--compiler", default="c++")
parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
args = parser.parse_args()
source = Path(__file__).with_suffix(".cpp")
compiler = shlex.split(args.compiler)
if not compiler:
    raise ValueError("--compiler must name a C++17 compiler")
with tempfile.TemporaryDirectory(prefix="star-triangle-") as tmp:
    executable = Path(tmp) / "optimize"
    subprocess.run(compiler + ["-O3", "-std=c++17", str(source), "-o", str(executable)], check=True)
    optimum = json.loads(subprocess.check_output([str(executable)], text=True))

expected = (2939540, 3003618, 3024138, 3122120, 3186026, 3223414)
require("six_signed_orbits_with_off", tuple(x["minimum_with_off"] for x in optimum["orbits"]) == expected)
require("off_never_improves_saturated_minimum", all(x["minimum_with_off"] == x["minimum_saturated"] for x in optimum["orbits"]))
require("global_minimum", min(expected) == 2939540)
require("node_candidate_count", optimum["node_candidates"] == 4 * 128**2 * 3**7)
require("root_candidate_count", optimum["root_convolution_candidates"] == 10 * 128 * 9**7)

# Every pure3/9/27 mask, with pairwise disjoint pure cylinders.
cells = set(range(27))
roots = [{j for j in cells if j % 3 == r} for r in range(3)]
middles = [{j for j in cells if j % 9 == m} for m in range(9)]
masks = set()
for r, m, l in product(range(-1, 3), range(-1, 9), range(-1, 27)):
    a = roots[r] if r >= 0 else set()
    b = middles[m] if m >= 0 else set()
    c = {l} if l >= 0 else set()
    if not (a & b or a & c or b & c):
        masks.add(tuple(sorted(cells - a - b - c)))
shapes = set()
for mask in masks:
    J = set(mask)
    first = [J - R for R in roots] if len({j % 3 for j in J}) == 3 else [J]
    for K in first:
        mid_ids = {j % 9 for j in K}
        if len(mid_ids) not in (5, 6):
            raise ValueError("pruned middle count")
        second = [K - middles[m] for m in mid_ids] if len(mid_ids) == 6 else [K]
        for L in second:
            if len(L) not in (14, 15):
                raise ValueError("pruned leaf count")
            third = [L - {j} for j in L] if len(L) == 15 else [L]
            for A in third:
                shape = tuple(sorted(tuple(sorted(sum(j % 9 == m for j in A)
                                  for m in {j % 9 for j in A} if m % 3 == r))
                                  for r in {j % 3 for j in A}))
                shapes.add(shape)
require("598_disjoint_pure_masks", len(masks) == 598)
require("exact_two_pruned_shapes", shapes == {((2, 3), (3, 3, 3)), ((2, 3, 3), (3, 3))})

# A literal global placement attains the signed minimum with positive leaves.
names = ["a" + str(i) for i in range(5)] + ["b" + str(i) for i in range(9)]
parent = {**{f"a{i}": "A0" if i < 2 else "A1" for i in range(5)},
          **{f"b{i}": "B" + str(i // 3) for i in range(9)}}
placement = {"5": ("B", "B1", "b0"), "7": ("B", "B2", "b1"),
             "11": ("A", "A1", "a1"), "13": ("A", "A1", "a1"),
             "17": ("A", "A1", "a4"), "19": ("A", "A1", "a1"),
             "T": ("B", "B2", "b4")}
nums = []
for j in names:
    n = {e: int(j[0].upper() == a) + int(parent[j] == b) + int(j == c)
         for e, (a, b, c) in placement.items()}
    v = (3 - n["5"]) * (5 - n["7"]) - n["T"] - 1
    for q in (11, 13, 17, 19):
        v *= q - 2 - n[str(q)]
    nums.append(v)
require("literal_leaf_numerators", nums == [250880, 185220, 171990, 171990, 158760,
        50490, 100980, 151470, 50490, 25245, 50490, 75735, 75735, 75735])
require("literal_witness_attains_global_minimum", nums[0] + 2 * sum(nums[1:]) == min(expected))
require("literal_witness_has_positive_leaves", min(nums) > 0)
require("literal_anchor_is_maximal_avoidance", nums[0] == max(nums))

D = 378675
head = 1 - F(min(expected), 27 * D)
star_tail = sum(F(1, q - 2) for q in (5, 7, 11, 13, 17, 19)) / 27
triangle_tail = F(1, 405)
ell = head + star_tail + triangle_tail
omega = F(935, 4096)
mass = omega * (1 - ell)
P = (3, 5, 7, 11, 13, 17, 19)
from math import prod
caps = {p: F(p - 1, p - 2) for p in P}
root_caps = {p: caps[p] / p for p in P}
Fcap = prod(1 + caps[p] / (p - 1) for p in P)
root_avoidance = prod(1 - root_caps[p] for p in P)
target = F(565, 51)
# Evaluate all seven independent root indicators; no final-law
# independence is assumed. The source caps parameterize this comparison.
root_pmf = [F(0) for _ in range(8)]
for indicators in product((0, 1), repeat=len(P)):
    weight = prod(root_caps[p] if on else 1 - root_caps[p]
                  for p, on in zip(P, indicators))
    root_pmf[sum(indicators)] += weight
require("root_probability_total", sum(root_pmf) == 1)
root_hinges = [sum(max(j - tau, 0) * root_pmf[j] for j in range(8))
               for tau in range(8)]
B_by_tau = [Fcap - 1 - sum(root_caps.values()) + h for h in root_hinges]
query_by_tau = [tau + B_by_tau[tau] / (1 - ell) for tau in range(8)]
thresholds = [1 - B_by_tau[tau] / (target - tau) for tau in range(8)]
tau = 2
B = B_by_tau[tau]
hinge = root_hinges[tau]
loss_threshold = thresholds[tau]
query = query_by_tau[tau]
reserve = 1 - (1 + query) * F(51, 616)
require("threshold_two_best_for_this_loss", query == min(query_by_tau))
require("threshold_two_best_target_loss_threshold", loss_threshold == max(thresholds))
# At tau=2, E min(M,2)=2-2 Pr(M=0)-Pr(M=1).
# Ordinary coordinate monotonicity is proved in the report; these corners
# are an exact arithmetic consistency check, not its proof.
corner_values = []
for av in product(*( (F(1), caps[p]) for p in P )):
    ap = dict(zip(P, av))
    cp = {p: ap[p] / p for p in P}
    zero = prod(1 - cp[p] for p in P)
    one = sum(cp[p] * prod(1 - cp[q] for q in P if q != p) for p in P)
    corner_values.append(prod(1 + ap[p] / (p - 1) for p in P) - 3 + 2 * zero + one)
require("all128_pure_cap_corners", len(corner_values) == 128 and max(corner_values) == B)
require("independent_root_hinge_one", root_hinges[1] == sum(root_caps.values()) - 1 + root_avoidance)
require("independent_root_hinge_two", B == Fcap - 3 + 2 * root_pmf[0] + root_pmf[1])
require("complete_query_cap_sum", Fcap - 1 == F(3161, 935))
require("root_avoidance", root_avoidance == F(4929320269, 33391182825))
require("joint_query_numerator", B == F(3864341559277, 1836515055375))
require("head", head == F(1456937, 2044845))
require("star_tail", star_tail == F(7244, 227205))
require("triangle_complete_tail", F(2, 1) * F(1, 54) * F(1, 15) == triangle_tail)
require("all_height_loss", ell == F(1527182, 2044845))
require("joint_query_loss_threshold", loss_threshold == F(12808334335598, 16672675894875))
require("actual_loss_below_threshold", ell < loss_threshold)
require("Haar_survivor", mass == F(517663, 8957952))
require("common_law_query", query == F(43147691740943, 4184308853725))
require("query_target", target - query == F(9623660209796, 12552926561175) > 0)
require("outside23_29_reserve", reserve == F(2405915052449, 37904915498450) > 0)
require("outside23_29_Haar", mass * reserve == F(2405915052449, 655929462988800))


extra_loss_budget = loss_threshold - ell
extra_old713_loss = ell + F(1, 55)
extra_old713_query = tau + B / (1 - extra_old713_loss)
extra_old713_Haar = omega * (1 - extra_old713_loss)
extra_old713_extended = extra_old713_Haar * (1 - (1 + extra_old713_query) * F(51, 616))
require("extra_inventory_budget", extra_loss_budget == F(9623660209796, 450162249161625))
require("complete_old713_inventory_fits", F(1, 55) < extra_loss_budget)
require("extra_old713_query", extra_old713_query == F(42546650450093, 3883788208300) < target)
require("extra_old713_extended_Haar", extra_old713_extended == F(1438892043221, 2623717851955200) > 0)

result = {"scope": "Finite distinct P-smooth originals: arbitrary pure heights, all mixed labels of form3^a*q^b,3^a*5^b*7^c or5^b*7^c; arbitrary fixed phases and no exponent cutoff. One uniform full-survivor law. Ordinary proof plus exact computation, not Lean or unrestricted Erdos7; no claim of G membership.",
          "roles": ["5", "7", "11", "13", "17", "19", "T"],
          "optimizer_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
          "signed_integer_optimizer": optimum, "pure_mask_count": len(masks),
          "pruned_shapes": sorted(shapes), "denominator": D,
          "literal_placement": placement, "literal_leaf_order": names,
          "literal_leaf_numerators": nums, "shallow_loss_upper": head,
          "star_tail": star_tail, "triangle_tail": triangle_tail,
          "all_height_loss_upper": ell, "joint_query_loss_threshold": loss_threshold,
          "loss_threshold_margin": loss_threshold - ell,
          "root_query_caps": root_caps, "joint_root_avoidance": root_avoidance,
          "root_count_distribution": root_pmf, "root_hinges_by_threshold": root_hinges,
          "query_numerators_by_threshold": B_by_tau, "query_bounds_by_threshold": query_by_tau,
          "loss_thresholds_by_threshold": thresholds, "selected_threshold": tau,
          "joint_root_hinge": hinge, "joint_query_numerator": B,
          "extra_inventory_budget": extra_loss_budget,
          "extra_old713_loss": extra_old713_loss, "extra_old713_query": extra_old713_query,
          "extra_old713_Haar": extra_old713_Haar, "extra_old713_extended_Haar": extra_old713_extended,
          "pure_cap_corner_count": len(corner_values),
          "full_Haar_survivor_lower": mass, "one_law_query_upper": query,
          "query_target_margin": target - query,
          "outside23_29_relative_reserve": reserve, "extended_Haar_lower": mass * reserve,
          "checks": checks, "passed_count": len(checks), "Lean": "not run"}


def encode(x):
    if isinstance(x, F):
        return str(x)
    raise TypeError(type(x).__name__)


dest = args.output
dest.write_text(json.dumps(result, indent=2, default=encode) + "\n", encoding="utf-8")
print(json.dumps({"passed_count": len(checks), "optimizer_checks": optimum["checks_passed"],
                  "six_orbit_minima": expected, "loss": ell, "query": query,
                  "extended_Haar_lower": mass * reserve,
                  "json_sha256": hashlib.sha256(dest.read_bytes()).hexdigest()},
                 indent=2, default=encode))
