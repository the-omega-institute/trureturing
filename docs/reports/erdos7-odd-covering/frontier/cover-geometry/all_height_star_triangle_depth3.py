#!/usr/bin/env python3
"""Exact all-height star-plus-triangle boundary certificate.

Requires Python3 standard library and a C++17 compiler (CXX, default c++).
Compiles the adjacent integer optimizer in a temporary directory. Retains
only result data; no build products, old producers or old data are used.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import os
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


source = Path(__file__).with_suffix(".cpp")
compiler = shlex.split(os.environ.get("CXX", "c++"))
if not compiler:
    raise ValueError("CXX must name a C++17 compiler")
with tempfile.TemporaryDirectory(prefix="star-triangle-") as tmp:
    executable = Path(tmp) / "optimize"
    subprocess.run(compiler + ["-O3", "-std=c++17", str(source), "-o", str(executable)], check=True)
    optimum = json.loads(subprocess.check_output([str(executable)], text=True))

expected = (3510150, 3577860, 3586365, 3676920, 3725466, 3748782)
require("six_signed_orbits_with_off", tuple(x["minimum_with_off"] for x in optimum["orbits"]) == expected)
require("off_never_improves_saturated_minimum", all(x["minimum_with_off"] == x["minimum_saturated"] for x in optimum["orbits"]))
require("global_minimum", min(expected) == 3510150)
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
    v = (3 - n["5"]) * (5 - n["7"]) - n["T"]
    for q in (11, 13, 17, 19):
        v *= q - 2 - n[str(q)]
    nums.append(v)
require("literal_leaf_numerators", nums == [268800, 198450, 184275, 184275, 170100,
        75735, 126225, 176715, 75735, 50490, 75735, 100980, 100980, 100980])
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
query = (1 / omega - 1) / (1 - ell)
reserve = 1 - (1 + query) * F(51, 616)
require("head", head == F(89521, 136323))
require("star_tail", star_tail == F(7244, 227205))
require("triangle_complete_tail", F(2, 1) * F(1, 54) * F(1, 15) == triangle_tail)
require("all_height_loss", ell == F(8564, 12393))
require("G_threshold", F(173, 250) - ell == F(2989, 3098250) > 0)
require("Haar_survivor", mass == F(210595, 2985984))
require("common_law_query", query == F(2304369, 210595))
require("query_target", F(565, 51) - query == F(1463356, 10740345) > 0)
require("outside23_29_reserve", reserve == F(365839, 32431630) > 0)
require("outside23_29_Haar", mass * reserve == F(365839, 459841536) > 0)

result = {"scope": "Finite distinct P-smooth originals: arbitrary pure heights, all mixed labels of form3^a*q^b or3^a*5^b*7^c; arbitrary fixed phases and no exponent cutoff. Ordinary proof plus exact computation, not Lean or unrestricted Erdos7.",
          "roles": ["5", "7", "11", "13", "17", "19", "T"],
          "optimizer_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
          "signed_integer_optimizer": optimum, "pure_mask_count": len(masks),
          "pruned_shapes": sorted(shapes), "denominator": D,
          "literal_placement": placement, "literal_leaf_order": names,
          "literal_leaf_numerators": nums, "shallow_loss_upper": head,
          "star_tail": star_tail, "triangle_tail": triangle_tail,
          "all_height_loss_upper": ell, "loss_threshold_margin": F(173, 250) - ell,
          "full_Haar_survivor_lower": mass, "one_law_query_upper": query,
          "query_target_margin": F(565, 51) - query,
          "outside23_29_relative_reserve": reserve, "extended_Haar_lower": mass * reserve,
          "checks": checks, "passed_count": len(checks), "Lean": "not run"}


def encode(x):
    if isinstance(x, F):
        return str(x)
    raise TypeError(type(x).__name__)


dest = Path(__file__).with_suffix(".json")
dest.write_text(json.dumps(result, indent=2, default=encode) + "\n", encoding="utf-8")
print(json.dumps({"passed_count": len(checks), "optimizer_checks": optimum["checks_passed"],
                  "six_orbit_minima": expected, "loss": ell, "query": query,
                  "extended_Haar_lower": mass * reserve,
                  "json_sha256": hashlib.sha256(dest.read_bytes()).hexdigest()},
                 indent=2, default=encode))
