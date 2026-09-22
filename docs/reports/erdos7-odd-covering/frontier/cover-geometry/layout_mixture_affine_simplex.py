#!/usr/bin/env python3
"""Exact affine-simplex construction from complete literal layout mixtures.

Uses the sibling standard-library module prime_layout_mixture_certificate.py.
Its self-check also reuses fixed_source_subclass_decomposition_obstruction.py.
For a rational subprobability p on {1,2,3,4} x Z/7^K, construct a finite
mixture with pointwise cost A_K + C_K*p, including unused mass at row zero.
All original divisor phases remain present and may be incompatible.

This construction realizes arbitrary sets as some strict superlevel sets.
It does not produce a counterexample at the covering target 2*t_K.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import importlib.util
import json

def _load_sibling(filename, module_name):
    path = Path(__file__).with_name(filename)
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise ImportError("cannot load sibling " + filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_certificate = _load_sibling("prime_layout_mixture_certificate.py", "_exact_prime_layout_certificate")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def affine_constants(height):
    """Return the exact baseline A_K and singleton increment C_K."""
    _certificate.original_divisors(height)
    baseline = sum((F(2 * j + 1, 7 ** j) for j in range(height + 1)), F(0))
    increment = 1 + 2 * sum((F(1, 7 ** j) for j in range(height + 1)), F(0))
    return baseline, increment


def affine_scope_budget(height):
    """Exact pointwise and tree-rank bounds for this constructed simplex only.

    Every complete five-ary height-K tree has 5**K distinct leaves. If its
    selected points all have probability at least b, total mass is at least
    5**K*b. Hence B4 <= B <= A_K + C_K/5**K for this affine construction.
    The report's sharp minimum-cardinality theorem improves the denominator
    to 5**K+2; exactly four active rows instead requires 4 at K = 0.
    No bound for arbitrary squared-layout mixtures is asserted.
    """
    baseline, increment = affine_constants(height)
    target = _certificate.default_target(height)
    rank_bound = baseline + increment / (5 ** height)
    pointwise_bound = baseline + increment
    sharp_rank_bound = baseline + increment / (5 ** height + 2)
    sharp_four_active_bound = baseline + increment / (4 if height == 0 else 5 ** height + 2)
    if height >= 1:
        require(rank_bound < target, "constructed simplex rank stays below covering target")
    if height >= 2:
        require(pointwise_bound < F(44, 9) < F(46, 9) <= target,
                "height-at-least-two pointwise scope budget")
    return {"height": height, "baseline": baseline, "increment": increment,
            "pointwise_bound": pointwise_bound, "rank_bound": rank_bound,
            "sharp_rank_bound": sharp_rank_bound, "sharp_four_active_bound": sharp_four_active_bound,
            "covering_target": target, "rank_margin": target - rank_bound}


def validate_subprobability(height, probabilities):
    """Normalize exact rational input while rejecting floats, bools and excess mass."""
    _certificate.original_divisors(height)
    require(isinstance(probabilities, dict), "subprobabilities must be a dictionary")
    for point in probabilities:
        require(isinstance(point, tuple) and len(point) == 2, "point must be a tuple pair")
        row, residue = point
        require(type(row) is int and row in (1, 2, 3, 4)
                and type(residue) is int and 0 <= residue < 7 ** height,
                "point outside the four-row carrier")
    require(all(type(w) in (int, F) and w >= 0 for w in probabilities.values()),
            "subprobabilities must be nonnegative integers or Fractions")
    normalized = {point: F(w) for point, w in probabilities.items()}
    require(sum(normalized.values(), F(0)) <= 1, "subprobability mass exceeds one")
    return normalized


def make_affine_mixture(height, probabilities):
    """Return (weight, full_literal_phase_tuple) components with cost A_K+C_K*p.

    A uniform pure-7 phase T is independent of the final joint point Z.
    Earlier joint labels use residue zero. Unused subprobability mass also
    sends the final joint label to row zero. No source point at row zero is
    added to the carrier.
    """
    probabilities = validate_subprobability(height, probabilities)
    modulus = 7 ** height
    total = sum(probabilities.values(), F(0))
    choices = [(point, w) for point, w in sorted(probabilities.items()) if w]
    if total < 1:
        choices.append(((0, 0), 1 - total))
    mixture = []
    for t in range(modulus):
        for (row, residue), weight in choices:
            final = residue + modulus * (((row - residue) * pow(modulus, -1, 5)) % 5)
            phases = tuple(a for j in range(height + 1)
                           for a in (t % (7 ** j), 0 if j < height else final))
            mixture.append((weight / modulus, phases))
    return tuple(mixture)


def verify_affine_mixture(height, probabilities, components=None):
    """Check every literal squared load against the claimed affine formula.

    Supplied components are audited as an actual probability mixture by the
    companion evaluator. If omitted, construct them with make_affine_mixture.
    The result includes exact carrier costs for further tree-rank checks.
    """
    probabilities = validate_subprobability(height, probabilities)
    mixture = make_affine_mixture(height, probabilities) if components is None else tuple(components)
    costs = _certificate.evaluate_layout_mixture(height, mixture)
    baseline, increment = affine_constants(height)
    require(all(value == baseline + increment * probabilities.get(point, F(0))
                for point, value in costs.items()), "literal cost fails the pointwise affine formula")
    return {"height": height, "baseline": baseline, "increment": increment,
            "subprobability_mass": sum(probabilities.values(), F(0)),
            "layout_components": len(mixture), "carrier_size": len(costs), "costs": costs}


def verify_obstruction_fixture():
    """Realize the retained 399 source as a strict 8/5 superlevel set.

    Reuses its literal 28-point fixture and independent source auditor;
    no new copy of that source is embedded here.
    """
    source_api = _load_sibling("fixed_source_subclass_decomposition_obstruction.py",
                              "_fixed_source_subclass_obstruction")
    source = source_api.fixture(2)
    require(len(source) == 28, "retained obstruction fixture cardinality")
    probabilities = {point: F(1, len(source)) for point in source}
    mixture = make_affine_mixture(2, probabilities)
    checked = verify_affine_mixture(2, probabilities, mixture)
    require(len(mixture) == 1372 and all(w == F(1, 1372) for w, _ in mixture),
            "complete equiprobable layout count")
    inside, outside, threshold = F(2263, 1372), F(75, 49), F(8, 5)
    require(all(v == (inside if x in source else outside) for x, v in checked["costs"].items()),
            "obstruction fixture pointwise cost")
    audited = _certificate.audit_layout_mixture(2, mixture, threshold)
    require(set(audited["strict_highset"]) == source, "strict superlevel is the retained source")
    require(audited["rank"] == audited["four_active_rank"] == inside,
            "exact B and four-active-row B4 ranks")
    require(audited["strict_target_verified"] and audited["strict_four_active_verified"],
            "strict source passes all trees and uses four rows")
    source_audit = source_api.audit_fixed_source(source, 2)
    require(all(source_audit["pair_ternary"].values()) and source_audit["full_fiveary"]
            and source_audit["excludes_fixed_subclasses"], "actual source decomposition obstruction")
    require(max(checked["costs"].values()) < audited["default_target"],
            "this is not a covering-target counterexample")
    return {"height": 2, "source_atoms": len(source), "literal_layouts": len(mixture),
            "mixture_weight": "1/1372", "inside_value": str(inside), "outside_value": str(outside),
            "threshold": str(threshold), "B": str(audited["rank"]),
            "B4": str(audited["four_active_rank"]), "strict_superlevel_matches_399": True,
            "all_source_premises": True, "fixed_subclasses_excluded": True,
            "covering_target": str(audited["default_target"]), "covering_counterexample": False}


def sharp_source(height):
    """Construct an actual source of cardinality 5**K + 2 at every K >= 0.

    At K = 0 use three rows. At K >= 1 use exact root type C with
    three full private five-ary tails and two shared five-ary tails.
    In each shared tail, A uses digits 0,1,2 and B uses digits 2,3,4;
    their only common leaf has every digit equal to 2. Row 2 receives
    T minus (B minus A), the other row receives B. Both rows retain a
    ternary tail, their union is T, and exactly one point is duplicated.
    """
    _certificate.original_divisors(height)
    if height == 0:
        return {(r, 0) for r in (1, 2, 3)}

    def digit_tree(digits):
        leaves = {0}
        for _ in range(height - 1):
            leaves = {digit + 7 * leaf for digit in digits for leaf in leaves}
        return leaves

    full = digit_tree(range(5))
    left = digit_tree(range(3))
    right = digit_tree(range(2, 5))
    main = full - (right - left)
    source = {(r, c + 7 * y) for r, c in ((1, 0), (3, 3), (4, 4)) for y in full}
    source |= {(2, c + 7 * y) for c in (1, 2) for y in main}
    source |= {(r, c + 7 * y) for r, c in ((3, 1), (4, 2)) for y in right}
    return source


def verify_minimum_cardinality_control():
    """Check the generic sharp source and the small necessary count bounds.

    The row-count enumeration is a necessary local cardinality check only.
    It does not enumerate all sources of size at most 26. The general
    cardinality lower bound is proved in the accompanying report.
    Actual source trees are checked through height 5. Full literal-mixture
    costs are checked only through height 2.
    """
    source_api = _load_sibling("fixed_source_subclass_decomposition_obstruction.py",
                              "_fixed_source_subclass_obstruction")
    source_controls = []
    mixture_controls = []
    for height in range(6):
        source = sharp_source(height)
        cardinality = 5 ** height + 2
        active_rows = {r for r, _ in source}
        require(len(source) == cardinality and active_rows == ({1, 2, 3} if height == 0 else {1, 2, 3, 4}),
                "generic sharp source cardinality and active rows")
        groups = [(pair, 3) for pair in combinations((1, 2, 3, 4), 2)] + [((1, 2, 3, 4), 5)]
        require(all(_certificate.contains_bary_tree({y for r, y in source if r in rows}, height, b)
                    for rows, b in groups), "generic source passes every actual tree premise")
        if height > 0:
            source_audit = source_api.audit_fixed_source(source, height)
            require(all(source_audit["pair_ternary"].values()) and source_audit["full_fiveary"],
                    "independent generic source tree audit")
        source_controls.append({"height": height, "source_atoms": len(source),
                                "active_rows": len(active_rows), "all_source_premises": True})
        if height > 2:
            continue
        probabilities = {point: F(1, cardinality) for point in source}
        mixture = make_affine_mixture(height, probabilities)
        checked = verify_affine_mixture(height, probabilities, mixture)
        baseline, increment = affine_constants(height)
        expected = baseline + increment / cardinality
        audited = _certificate.audit_layout_mixture(height, mixture, (baseline + expected) / 2)
        count = 7 ** height * cardinality
        require(len(mixture) == count and all(w == F(1, count) for w, _ in mixture),
                "sharp source complete equiprobable layout count")
        require(audited["rank"] == expected and max(checked["costs"].values()) == expected,
                "sharp source exact B")
        require(audited["four_active_rank"] == (baseline if height == 0 else expected),
                "sharp source exact four-active-row B4")
        require(set(audited["strict_highset"]) == source
                and audited["strict_four_active_verified"] == (height > 0),
                "sharp source actual strict superlevel")
        require(affine_scope_budget(height)["sharp_rank_bound"] == expected,
                "source attains the reported sharp simplex rank")
        mixture_controls.append({"height": height, "literal_layouts": len(mixture),
                                 "mixture_weight": str(F(1, count)), "B": str(audited["rank"]),
                                 "B4": str(audited["four_active_rank"])})
    require(mixture_controls[2]["B"] == "2188/1323", "height-two sharp rank")
    four_zero = {(r, 0): F(1, 4) for r in (1, 2, 3, 4)}
    four_mixture = make_affine_mixture(0, four_zero)
    verify_affine_mixture(0, four_zero, four_mixture)
    four_audit = _certificate.audit_layout_mixture(0, four_mixture)
    require(four_audit["rank"] == four_audit["four_active_rank"] == F(7, 4)
            and affine_scope_budget(0)["sharp_four_active_bound"] == F(7, 4),
            "height-zero exactly-four-active boundary")
    counts = []
    for total, expected_count, expected_maximum in ((5, 56, 3), (6, 84, 5)):
        row_counts = [c for c in product(range(total + 1), repeat=4) if sum(c) == total]
        maximum = max(sum(c[i] + c[j] >= 3 for i, j in combinations(range(4), 2))
                      for c in row_counts)
        require(len(row_counts) == expected_count and maximum == expected_maximum,
                "necessary pair-count bound at fixed column mass")
        counts.append({"column_points": total, "row_count_vectors": len(row_counts),
                       "maximum_pairs_with_count_at_least_three": maximum})
    return {"source_controls": source_controls, "mixture_controls": mixture_controls,
            "height_zero_exactly_four_active_rank": "7/4", "positive_height_root_type": "C",
            "necessary_column_count_controls": counts,
            "scope": "actual attainment and local necessary counts; lower-bound proof is in the report"}


def self_check():
    cases = (
        (0, {}),
        (0, {(1, 0): F(1, 3), (4, 0): F(1, 4)}),
        (1, {}),
        (1, {(1, 0): F(1, 3), (4, 6): F(1, 4)}),
        (2, {(2, 17): F(2, 5), (3, 48): F(3, 5)}),
    )
    controls = []
    for height, probabilities in cases:
        checked = verify_affine_mixture(height, probabilities)
        controls.append({"height": height, "components": checked["layout_components"],
                         "atoms": checked["carrier_size"],
                         "subprobability_mass": str(checked["subprobability_mass"])})
    require(affine_constants(0) == (F(1), F(3)), "height-zero constants")
    require(affine_constants(2) == (F(75, 49), F(163, 49)), "height-two constants")
    for height in range(5):
        a, c = affine_constants(height)
        require(a == F(14, 9) - F(3 * height + 5, 9 * 7 ** height)
                and c == F(10, 3) - F(1, 3 * 7 ** height), "closed constants")
        affine_scope_budget(height)
    require(affine_scope_budget(1)["rank_bound"] == F(73, 35), "height-one rank budget")
    actual = make_affine_mixture(1, {(1, 0): F(1)})
    perturbed = ((actual[0][0], (0, 1, 0, 21)),) + actual[1:]
    invalid = (
        lambda: make_affine_mixture(True, {}),
        lambda: make_affine_mixture(-1, {}),
        lambda: make_affine_mixture(1, {(0, 0): F(1)}),
        lambda: make_affine_mixture(1, {(True, 0): F(1)}),
        lambda: make_affine_mixture(1, {(1, 7): F(1)}),
        lambda: make_affine_mixture(1, {(1, 0): 1.0}),
        lambda: make_affine_mixture(1, {(1, 0): True}),
        lambda: make_affine_mixture(1, {(1, 0): F(-1, 2)}),
        lambda: make_affine_mixture(1, {(1, 0): F(3, 2)}),
        lambda: verify_affine_mixture(1, {(1, 0): F(1)}, perturbed),
    )
    rejected = 0
    for operation in invalid:
        try:
            operation()
        except ValueError:
            rejected += 1
    require(rejected == len(invalid), "invalid subprobability and altered-layout controls")
    return {"controls": controls, "invalid_controls": rejected,
            "height_two_baseline": "75/49", "height_two_increment": "163/49",
            "height_one_rank_budget": "73/35", "height_one_covering_target": "4",
            "obstruction_fixture": verify_obstruction_fixture(),
            "minimum_cardinality_control": verify_minimum_cardinality_control(),
            "scope": "exact affine construction controls, not a high-threshold counterexample"}


if __name__ == "__main__":
    print(json.dumps(self_check(), indent=2))
