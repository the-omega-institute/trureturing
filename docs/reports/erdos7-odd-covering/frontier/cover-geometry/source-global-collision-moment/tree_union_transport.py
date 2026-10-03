#!/usr/bin/env python3
"""Exact finite checks of common-subtree variance transport.

A single random tree selects r of the s children uniformly and independently
at each retained node.  Every label uses that same tree.  Direct averages
over its leaves are compared with martingale energies computed only from
the original s-ary leaf function.  These finite checks are not an all-depth
proof, Lean verification, or a whole-cover result.

Run with python -B -I -S -O tree_union_transport.py --check.  Relative input
and output paths are resolved beside this file.  Optional --input JSON:
{"cases": [{"name": "custom", "r": 2, "s": 3, "depth": 2,
"functions": [{"name": "f", "values": ["0", "1/2", ...]}]}]}.
There must be exactly s**depth values, indexed by the original leaf integer
whose lowest-significant digits come first.  A case may instead specify
"all_indicators": true.  Supplied cases replace the default finite cases;
the conditional-old-law controls always run.  Full tree enumeration grows
as binomial(s,r)**(1+r+...+r**(depth-1)).
The literal old-survivor control imports the adjacent conditional_replica.py
by its exact path and reuses its CRT, pullback, structure, and moment checks.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
import json
import importlib.util
from math import comb
from pathlib import Path
import sys


def require(condition, detail):
    """Keep every check active under Python -O."""
    if not condition:
        raise AssertionError(detail)


def parameters(r, s, depth):
    require(all(isinstance(n, int) for n in (r, s, depth))
            and 1 <= r <= s and s >= 2 and depth >= 0,
            ("invalid branching parameters", r, s, depth))


@lru_cache(maxsize=None)
def tree_images(r, s, depth):
    """Enumerate literal leaf sets; one common subset at each source node."""
    parameters(r, s, depth)
    if depth == 0:
        return ((0,),)
    smaller = tree_images(r, s, depth - 1)
    images = []
    for children in combinations(range(s), r):
        for branches in product(smaller, repeat=r):
            images.append(tuple(sorted(j + s * leaf
                                       for j, branch in zip(children, branches)
                                       for leaf in branch)))
    return tuple(images)


def martingale_data(values, s, depth):
    """Compute Haar prefix averages and energies, without inspecting trees."""
    require(len(values) == s**depth, "leaf count does not match depth")
    mean = sum(values, F(0)) / len(values)
    previous = (mean,)
    energies = []
    for level in range(1, depth + 1):
        count = s**level
        averages = tuple(sum(values[a::count], F(0)) / (s**(depth - level))
                         for a in range(count))
        energy = sum(((value - previous[a % len(previous)])**2
                      for a, value in enumerate(averages)), F(0)) / count
        energies.append(energy)
        previous = averages
    variance = sum(((value - mean)**2 for value in values), F(0)) / len(values)
    require(sum(energies, F(0)) == variance, "martingale energy decomposition")
    return mean, variance, tuple(energies)


def check_function(r, s, depth, images, values):
    """Compare exhaustive quadrature with the independent energy formula."""
    values = tuple(F(value) for value in values)
    mean, original_variance, energies = martingale_data(values, s, depth)
    direct_mean = direct_second = F(0)
    for image in images:
        alpha = sum((values[leaf] for leaf in image), F(0)) / (r**depth)
        direct_mean += alpha
        direct_second += alpha**2
    direct_mean /= len(images)
    direct_second /= len(images)
    c = F(s - r, r * (s - 1))
    transported = c * sum((energy / r**j for j, energy in enumerate(energies)), F(0))
    require(direct_mean == mean, "common-tree first moment")
    require(direct_second - direct_mean**2 == transported, "variance transport identity")
    require(transported <= c * original_variance, "variance contraction")
    # Every finite cut keeps the complete unresolved tail inside this bound.
    for cut in range(depth + 1):
        resolved = c * sum((energy / r**j for j, energy in enumerate(energies[:cut])), F(0))
        tail_cap = c * sum(energies[cut:], F(0)) / r**cut
        require(resolved <= transported <= resolved + tail_cap,
                ("coarse energy tail bound", cut))
    indicator = all(value in (0, 1) for value in values)
    upper = mean**2 + c * original_variance
    if indicator:
        require(original_variance == mean * (1 - mean), "indicator variance")
        require(direct_second <= (1 - c) * mean**2 + c * mean, "union second-moment bound")
    return {"mean": str(mean), "original_variance": str(original_variance),
            "martingale_energies": list(map(str, energies)),
            "tree_variance": str(transported), "tree_second_moment": str(direct_second),
            "variance_bound_second_moment": str(upper), "bound_slack": str(upper - direct_second),
            "indicator": indicator, "bound_equality": direct_second == upper}


def prefix_values(s, depth, prefixes):
    """Literal union of prefixes, retaining duplicate/nested input semantics."""
    prefixes = tuple(tuple(word) for word in prefixes)
    require(all(len(word) <= depth and all(isinstance(j, int) and 0 <= j < s for j in word)
                for word in prefixes), "invalid prefix")
    residues = [(sum(j * s**k for k, j in enumerate(word)), s**len(word))
                for word in prefixes]
    return tuple(F(any(leaf % modulus == residue for residue, modulus in residues))
                 for leaf in range(s**depth))


def default_cases():
    functions = [
        {"name": "empty", "values": [0] * 27},
        {"name": "full", "values": [1] * 27},
        {"name": "first_digit", "values": prefix_values(3, 3, [(0,)])},
        {"name": "last_digit", "values": [int(leaf // 9 == 0) for leaf in range(27)]},
        {"name": "one_leaf", "values": prefix_values(3, 3, [(1, 0, 2)])},
        {"name": "mixed_depth_antichain", "values": prefix_values(3, 3, [(0,), (1, 0), (1, 1, 2)])},
        {"name": "nested_duplicate_prefix_union",
         "values": prefix_values(3, 3, [(0,), (0,), (0, 1), (0, 1, 2), (1, 0)])},
        {"name": "signed_rational", "values": [F((-1)**leaf * (leaf - 13), 7) for leaf in range(27)]},
    ]
    return [
        {"name": "all_ternary_depth_two_indicators", "r": 2, "s": 3, "depth": 2, "all_indicators": True},
        {"name": "ternary_depth_three_functions", "r": 2, "s": 3, "depth": 3, "functions": functions},
        {"name": "all_seven_child_indicators", "r": 5, "s": 7, "depth": 1, "all_indicators": True},
        {"name": "one_branch", "r": 1, "s": 3, "depth": 2,
         "functions": [{"name": "mixed_prefix", "values": prefix_values(3, 2, [(0,), (1, 2)])}]},
        {"name": "all_branches", "r": 3, "s": 3, "depth": 2,
         "functions": [{"name": "mixed_prefix", "values": prefix_values(3, 2, [(0,), (1, 2)])}]},
        {"name": "depth_zero", "r": 2, "s": 3, "depth": 0,
         "functions": [{"name": "constant_rational", "values": ["7/3"]}]},
    ]


def check_case(case):
    r, s, depth = (case[key] for key in ("r", "s", "depth"))
    parameters(r, s, depth)
    images = tree_images(r, s, depth)
    expected_trees = comb(s, r)**sum(r**j for j in range(depth))
    require(len(images) == len(set(images)) == expected_trees, "common-tree count/uniqueness")
    require(all(len(image) == len(set(image)) == r**depth
                and all(0 <= leaf < s**depth for leaf in image) for image in images),
            "common-tree leaf support")
    require(bool(case.get("all_indicators")) != ("functions" in case),
            "choose all_indicators or explicit functions")
    exhaustive = bool(case.get("all_indicators"))
    functions = ({"name": str(mask), "values": tuple((mask >> j) & 1 for j in range(s**depth))}
                 for mask in range(2**(s**depth))) if exhaustive else case["functions"]
    results, function_count, equality_count, indicator_count = [], 0, 0, 0
    for function in functions:
        result = check_function(r, s, depth, images, function["values"])
        function_count += 1
        equality_count += int(result["bound_equality"])
        indicator_count += int(result["indicator"])
        if not exhaustive:
            results.append({"name": function["name"], **result})
    require(function_count > 0, "empty function inventory")
    if exhaustive and r > 1 and r < s and depth >= 1:
        require(equality_count == 2**s, "sharpness occurs exactly for first-digit indicators")
    return {"name": case["name"], "r": r, "s": s, "depth": depth,
            "c": str(F(s - r, r * (s - 1))), "original_leaf_count": s**depth,
            "selected_leaf_count": r**depth, "tree_count": len(images),
            "all_indicators": exhaustive, "function_count": function_count,
            "indicator_count": indicator_count, "bound_equality_count": equality_count,
            "direct_tree_evaluations": function_count * len(images),
            "coarse_tail_bound_checks": function_count * (depth + 1), "named_functions": results}


def dependent_old_law(r, s):
    """Same marginal Haar old law, but X|S uniform S changes the answer."""
    parameters(r, s, 1)
    require(r < s, "boundary control requires strict subsampling")
    subsets = tuple(combinations(range(s), r))
    masses = [F(0)] * s
    second = F(0)
    for selected in subsets:
        for x in selected:
            joint_weight = F(1, len(subsets) * r)
            masses[x] += joint_weight
            alpha = F(sum(y == x for y in selected), r)
            second += joint_weight * alpha**2
    fixed_old_second = F(0)
    for x, selected in product(range(s), subsets):
        alpha = F(sum(y == x for y in selected), r)
        fixed_old_second += alpha**2 / (s * len(subsets))
    require(all(mass == F(1, s) for mass in masses), "old marginal is Haar")
    require(second == F(1, r*r) and fixed_old_second == F(1, r*s)
            and second > fixed_old_second, "conditional old-law counterexample")
    return {"r": r, "s": s, "joint_states": len(subsets) * r,
            "independent_states": s * len(subsets), "old_marginal": list(map(str, masses)),
            "conditional_tree_second_moment": str(second),
            "independent_old_second_moment": str(fixed_old_second),
            "conditional_law": "S uniform among r-subsets; X conditional on S uniform in S; f_x(j)=1_{j=x}"}


def old_survivor_control():
    """A same-source union improvement on an actual old survivor."""
    path = Path(__file__).resolve().with_name("conditional_replica.py")
    spec = importlib.util.spec_from_file_location("_tree_union_arithmetic_source", path)
    require(spec is not None and spec.loader is not None, "arithmetic source unavailable")
    arithmetic = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = arithmetic
    spec.loader.exec_module(arithmetic)
    originals = [(str(n), n, a) for n, a in
                 [(3, 0), (5, 0), (7, 0), (9, 2), (15, 2), (21, 4), (35, 2), (63, 1), (105, 1)]]
    comparable_pairs = arithmetic.structure(originals)
    weights = tuple(F(x == 1) for x in range(9))
    union_second = labelled_second = F(0)
    checks = replica_states = 0
    for children in combinations(range(7), 5):
        output, current = arithmetic.verify_pullback(originals, 5, 7, 1, children, 9)
        require(all(not c.old_hit(1) for c in output if c.depth == 0),
                "fixed old point meets a depth-zero original")
        stage = [c for c in output if c.depth == 1]
        require(all(c.cofactor in (1, 3, 9) for c in stage), "cofactor outside earlier prime support")
        result = arithmetic.moments(5, stage, weights)
        union_second += F(result["conditional_second_moment"]) / 21
        labelled_second += F(result["labelled_pair_bound"]) / 21
        checks += current
        replica_states += result["replica_states"]
    active = []
    for label, n, phase in originals:
        rest, a = arithmetic.factor_out(n, 5)
        m, b = arithmetic.factor_out(rest, 7)
        if b == 1 and (not a or phase % 5 == 1) and phase % m == 1 % m:
            active.append({"label": label, "prefix": phase % 7, "cofactor": m})
    prefixes = sorted({a["prefix"] for a in active})
    geometric = check_function(5, 7, 1, tree_images(5, 7, 1),
                               prefix_values(7, 1, [(j,) for j in prefixes]))
    require(prefixes == [0, 1, 4] and union_second == F(geometric["tree_second_moment"])
            == F(1, 5) and labelled_second == F(38, 105), "literal old-survivor moments")
    witness = arithmetic.crt(((1, 9), (1, 5), (2, 7)))[0]
    require(all(witness % n != phase for _, n, phase in originals), "noncoverage witness")
    return {"originals": [list(t) for t in originals], "divisor_closed": True,
            "comparable_disjoint_pairs": comparable_pairs, "r": 5, "s": 7,
            "safe_u": 1, "old_period": 9, "old_law": "Dirac at x=1, independent of the tree",
            "depth_zero_originals_avoided": [3, 5, 9, 15], "active_originals": active,
            "old_cofactors": [1, 3, 9], "distinct_active_prefixes": prefixes,
            "union_second_moment": str(union_second), "labelled_second_moment": str(labelled_second),
            "strict_improvement": str(labelled_second - union_second), "uncovered_witness": witness,
            "source_maps": 21, "literal_pullback_checks": checks, "replica_states": replica_states,
            "scope": "actual old survivor with earlier-prime cofactors; local noncover, no whole-cover or Lean conclusion"}


def run(cases):
    results = [check_case(case) for case in cases]
    require(results, "empty case inventory")
    controls = [dependent_old_law(2, 3), dependent_old_law(5, 7)]
    return {"schema_version": 1, "status": "PASS",
            "scope": "finite exact common-subtree enumeration; no all-depth proof, Lean verification, or whole-cover conclusion",
            "transport_identity": {"c": "(s-r)/(r*(s-1))",
                                   "mean": "E_theta alpha = H_s f",
                                   "variance": "Var_theta alpha = c*sum_{j=1}^B r^{-(j-1)}*D_j",
                                   "D_j": "H_s[(E(f|first j digits)-E(f|first j-1 digits))^2]",
                                   "indicator_bound": "E_theta alpha^2 <= (1-c)*mu^2+c*mu",
                                   "conditions": "fixed original leaf function; uniform independent r-child choices at each node; old coordinates independent of the tree"},
            "cases": results, "dependent_old_law_controls": controls,
            "old_survivor_control": old_survivor_control(),
            "counts": {"cases": len(results), "functions": sum(c["function_count"] for c in results),
                       "indicator_functions": sum(c["indicator_count"] for c in results),
                       "direct_tree_evaluations": sum(c["direct_tree_evaluations"] for c in results),
                       "coarse_tail_bound_checks": sum(c["coarse_tail_bound_checks"] for c in results),
                       "dependent_old_joint_states": sum(c["joint_states"] for c in controls),
                       "independent_old_states": sum(c["independent_states"] for c in controls)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="optional explicit case JSON")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().with_suffix(".json"))
    parser.add_argument("--check", action="store_true", help="compare saved results without writing")
    args = parser.parse_args()
    beside = lambda path: path if path.is_absolute() else Path(__file__).resolve().parent / path
    cases = default_cases() if args.input is None else json.loads(beside(args.input).read_text(encoding="utf-8"))["cases"]
    result = run(cases)
    output = beside(args.output)
    if args.check:
        require(json.loads(output.read_text(encoding="utf-8")) == result, "saved result mismatch")
    else:
        output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "counts": result["counts"],
                      "mode": "check" if args.check else "write"}, sort_keys=True))


if __name__ == "__main__":
    main()
