#!/usr/bin/env python3
"""Sparse-second-digit laws and fixed-subclass source obstructions.

Exact finite tools for actual four-row sources; no covering realization or
unrestricted Erdős #7 conclusion is asserted.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def _integer(value):
    return isinstance(value, int) and not isinstance(value, bool)


def select_complete_tree(leaves, height, branching, base=7):
    """Return leaves of one complete low-digit-prefix tree, or None.

    Input leaves are integer residues in [0, base**height). The chosen
    children may vary at every prefix. Empty input never contains a tree,
    including at height zero.
    """
    require(_integer(height) and height >= 0, "nonnegative integer height")
    require(_integer(base) and base >= 2, "integer base at least two")
    require(_integer(branching) and 1 <= branching <= base, "valid branching")
    leaves = set(leaves)
    require(all(_integer(x) and 0 <= x < base ** height for x in leaves),
            "leaf outside residue space")

    def choose(values, depth):
        if not values:
            return None
        if depth == 0:
            return {0}
        groups = defaultdict(set)
        for x in values:
            groups[x % base].add(x // base)
        selected = []
        for digit in sorted(groups):
            subtree = choose(groups[digit], depth - 1)
            if subtree is not None:
                selected.append((digit, subtree))
                if len(selected) == branching:
                    return {digit + base * x for digit, tree in selected for x in tree}
        return None

    return choose(leaves, height)


def has_complete_tree(leaves, height, branching, base=7):
    """Decide finite complete prefix-tree containment."""
    return select_complete_tree(leaves, height, branching, base) is not None


def _source(source, height):
    require(_integer(height) and height >= 1, "positive integer source height")
    points = set(source)
    require(all(isinstance(p, tuple) and len(p) == 2 for p in points),
            "source points must be (row, residue) tuples")
    require(all(_integer(r) and r in range(1, 5)
                and _integer(y) and 0 <= y < 7 ** height for r, y in points),
            "source point outside four-row residue space")
    return points


def audit_fixed_source(source, height):
    """Check tree premises and a sufficient fixed-subclass obstruction.

    excludes_fixed_subclasses=True certifies that no same-height subsource
    meets the hypotheses of 396, 397 or 398. False does not assert that a
    component exists. Relabelling must preserve the prime-prefix structure.
    """
    points = _source(source, height)

    def row_leaves(rows):
        return {y for r, y in points if r in rows}

    pair = {p: has_complete_tree(row_leaves(p), height, 3)
            for p in combinations(range(1, 5), 2)}
    full = has_complete_tree(row_leaves(range(1, 5)), height, 5)
    individual = {r: has_complete_tree(row_leaves([r]), height, 5)
                  for r in range(1, 5)}
    omitted = {r: has_complete_tree(row_leaves([s for s in range(1, 5) if s != r]),
                                     height, 5) for r in range(1, 5)}
    root = {(r, y % 7) for r, y in points}
    joint = {(r, c): has_complete_tree(
                {y // 7 for s, y in points if s == r and y % 7 == c}, height - 1, 3)
             for r, c in root}
    return {"height": height, "points": len(points), "root_cells": len(root),
            "pair_ternary": pair, "full_fiveary": full,
            "individual_fiveary": individual, "omitted_row_fiveary": omitted,
            "joint_tail_ternary": joint,
            "excludes_fixed_subclasses": not any(individual.values())
                and not all(omitted.values()) and not any(joint.values())}


def sparse_second_digit_law(source, height):
    """Construct one actual supported law under the sparse-digit theorem.

    Requires height >= 2, a full five-ary projection tree, and at most two
    second digits in each actual (row, first digit) cell. Select a complete
    tree, choose an available row for each leaf, and use uniform leaf mass.
    The returned dictionary is a probability on the input carrier.
    """
    points = _source(source, height)
    require(height >= 2, "sparse theorem needs height at least two")
    digits = defaultdict(set)
    rows = defaultdict(set)
    for r, y in points:
        digits[r, y % 7].add((y // 7) % 7)
        rows[y].add(r)
    require(all(len(ds) <= 2 for ds in digits.values()),
            "more than two second digits in a joint root cell")
    tree = select_complete_tree(rows, height, 5)
    require(tree is not None, "projection lacks a complete five-ary tree")
    require(len(tree) == 5 ** height, "selected tree cardinality")
    law = {(min(rows[y]), y): F(1, 5 ** height) for y in tree}
    require(set(law) <= points and sum(law.values(), F(0)) == 1,
            "common law must be a supported probability")
    return law


def sparse_envelope(height):
    require(_integer(height) and height >= 2, "envelope height at least two")
    bound = F(88, 25) + 4 * sum((F(2 * j + 1, 5 ** j)
                                for j in range(2, height + 1)), F(0))
    target = 2 * (3 - F(height + 2, 3 ** height))
    return {"bound": bound, "target": target, "margin": target - bound,
            "limit": F(231, 50)}


def verify_sparse_law(law, source, height):
    """Verify the simultaneous prefix caps and complete independent root maximum."""
    require(_integer(height) and height >= 2, "sparse verification height at least two")
    require(isinstance(law, dict), "probability must be a dictionary")
    require(all(type(m) in (int, F) for m in law.values()),
            "probability masses must be exact integers or fractions")
    points = _source(source, height)
    law_points = _source(law, height)
    require(law_points <= points and all(m >= 0 for m in law.values())
            and sum(law.values(), F(0)) == 1, "actual supported probability")
    row_mass = defaultdict(F)
    root_mass = defaultdict(F)
    column_mass = defaultdict(F)
    for (r, y), m in law.items():
        row_mass[r] += m
        root_mass[r, y % 7] += m
        column_mass[y % 7] += m
    require(max(row_mass.values()) <= F(2, 5), "row cap")
    require(max(root_mass.values()) <= F(2, 25), "joint root cap")
    require(max(column_mass.values()) <= F(1, 5), "root-column cap")
    maxima = []
    for j in range(1, height + 1):
        prefix = defaultdict(F)
        joint = defaultdict(F)
        for (r, y), m in law.items():
            prefix[y % 7 ** j] += m
            joint[r, y % 7 ** j] += m
        require(max(prefix.values()) <= F(1, 5 ** j), "plain prefix cap")
        require(max(joint.values()) <= F(1, 5 ** j), "joint prefix cap")
        maxima.append((max(prefix.values()), max(joint.values())))
    root_max = F(0)
    count = 0
    for a, b, c, d in product(range(5), range(7), range(5), range(7)):
        value = sum((m * (1 + (r == a) + (y == b) + ((r, y) == (c, d))) ** 2
                     for (r, y), m in root_mass.items()), F(0))
        root_max = max(root_max, value)
        count += 1
    require(count == 1225 and root_max <= F(88, 25), "complete root-layout bound")
    envelope = sparse_envelope(height)
    require(envelope["margin"] > 0, "finite-height target comparison")
    return {"root_maximum": root_max, "root_layouts": count,
            "prefix_maxima": maxima, **envelope}


TABLE = {
    1: ({4}, {0, 4}, {2}, {2, 3}, set()),
    2: ({4}, {3}, {1, 3}, {0}, {0, 4}),
    3: ({1, 3}, {1}, {1, 4}, {1, 4}, {1}),
    4: ({0, 2}, {2}, {0, 4}, set(), {2, 3}),
}


def fixture(height):
    require(_integer(height) and height >= 2, "fixture height at least two")
    return {(r, c + 7 * d + 49 * z)
            for r, cells in TABLE.items() for c, ds in enumerate(cells) for d in ds
            for z in range(7 ** (height - 2))}


def self_check():
    source = fixture(2)
    require(len(source) == 28, "source cardinality")
    root = {(r, y % 7) for r, y in source}
    require(len(root) == 18, "root cardinality")
    type_b = {(1, 3), (2, 0), (2, 1), (3, 0), (3, 2), (4, 0), (4, 4)}
    require(type_b < root, "strict type-B containment")

    def counts(rows):
        return tuple(len({y // 7 for r, y in source if r in rows and y % 7 == c})
                     for c in range(5))

    expected_pairs = ((1, 3, 3, 3, 2), (3, 3, 3, 4, 1), (3, 3, 3, 2, 2),
                      (3, 2, 3, 3, 3), (3, 2, 4, 1, 4), (4, 2, 3, 2, 3))
    for p, expected in zip(combinations(range(1, 5), 2), expected_pairs):
        require(counts(p) == expected, "literal pair counts")
    expected_omits = ((5, 3, 4, 3, 5), (5, 4, 4, 4, 3),
                      (3, 4, 5, 3, 4), (3, 4, 4, 5, 3))
    for r, expected in zip(range(1, 5), expected_omits):
        require(counts([s for s in range(1, 5) if s != r]) == expected,
                "literal omitted-row counts")
    require(counts(range(1, 5)) == (5, 5, 5, 5, 5), "literal full counts")
    restricted = {(r, y) for r, y in source if (r, y % 7) in type_b}
    columns = {2, 3, 4, 5, 6}
    tree = {c + 7 * d for c in columns
            for d in ({0, 1, 4, 5, 6} if c == 3 else set(range(5)))}
    require(has_complete_tree(tree, 2, 5), "lost product witness is a fiveary tree")
    require(not any(r in {0, 1, 2} and y in tree for r, y in restricted),
            "restricted source misses the literal product tree")

    controls = []
    for height in range(2, 6):
        lifted = fixture(height)
        audit = audit_fixed_source(lifted, height)
        require(audit["points"] == 28 * 7 ** (height - 2), "lift cardinality")
        require(all(audit["pair_ternary"].values()) and audit["full_fiveary"],
                "lift full source hypotheses")
        require(audit["excludes_fixed_subclasses"], "lift subclass obstruction")
        law = sparse_second_digit_law(lifted, height)
        checked = verify_sparse_law(law, lifted, height)
        controls.append({"height": height, "source_points": len(lifted),
                         "law_points": len(law), "root_maximum": str(checked["root_maximum"]),
                         "bound": str(checked["bound"]), "margin": str(checked["margin"])})

    # Prefix-dependent children, including first digits absent from the main fixture.
    varying = set()
    for i, c in enumerate((0, 1, 3, 4, 6)):
        for j, d in enumerate(((2 * i + t) % 7 for t in range(5))):
            r = 1 + (((0, 0, 1, 2, 3)[j] + i) % 4)
            for e in ((i + 2 * j + t) % 7 for t in range(5)):
                varying.add((r, c + 7 * d + 49 * e))
    varying_law = sparse_second_digit_law(varying, 3)
    varying_check = verify_sparse_law(varying_law, varying, 3)
    require(len(varying_law) == 125, "varying-child tree size")

    require(sparse_envelope(2)["bound"] == F(108, 25), "height-two bound")
    require(sparse_envelope(2)["margin"] == F(178, 225), "height-two margin")
    # Sum_{j>=2}(2j+1)/5^j = 11/40 from the geometric-series identity.
    require(F(88, 25) + 4 * F(11, 40) == F(231, 50), "infinite envelope")
    # Analytic q=3 remark; the constructive API above still requires q<=2.
    root_three = F(40 + 24 * 3, 25)
    third_three = root_three + 4 * (F(5, 25) + F(7, 125))
    require(third_three == F(688, 125)
            and sparse_envelope(3)["target"] - third_three == F(424, 3375),
            "three-digit height-three extension")
    require(root_three + 4 * F(11, 40) == F(279, 50), "three-digit limit")
    require(root_three + 4 * F(5, 25) == F(132, 25)
            and F(132, 25) > sparse_envelope(2)["target"],
            "three-digit height-two estimate gives no conclusion")
    for j in range(3, 13):
        before, after = sparse_envelope(j - 1), sparse_envelope(j)
        require(after["bound"] == F(231, 50) - F(4 * j + 7, 2 * 5 ** j),
                "closed envelope formula")
        delta = (2 * j + 1) * (F(2, 3 ** j) - F(4, 5 ** j))
        require(after["margin"] - before["margin"] == delta > 0,
                "comparison increment")
    require(select_complete_tree([], 0, 3) is None, "empty height-zero tree")
    require(select_complete_tree([0], 0, 3) == {0}, "nonempty height-zero tree")
    require(not has_complete_tree([0, 1], 1, 3), "insufficient children")
    rejected = 0
    invalid = (
        lambda: select_complete_tree([7], 1, 3),
        lambda: select_complete_tree([0], -1, 3),
        lambda: select_complete_tree([0], 1, 8),
        lambda: audit_fixed_source({(0, 0)}, 2),
        lambda: sparse_second_digit_law(source, 1),
        lambda: sparse_second_digit_law({(1, y) for y in range(49)}, 2),
        lambda: sparse_second_digit_law({(r, 0) for r in range(1, 5)}, 2),
        lambda: verify_sparse_law({(1, 28): 1.0}, source, 2),
        lambda: verify_sparse_law([((1, 28), F(1))], source, 2),
        lambda: verify_sparse_law({(True, 28): F(1)}, source, 2),
    )
    for operation in invalid:
        try:
            operation()
        except ValueError:
            rejected += 1
    require(rejected == len(invalid), "invalid input rejection")
    return {"scope": "exact source obstruction and common-law controls; all-height proofs are analytic",
            "source_points": 28, "root_cells": 18, "lift_controls": controls,
            "varying_child_control": {"points": len(varying),
                                      "root_maximum": str(varying_check["root_maximum"])},
            "root_layouts_per_law": 1225, "invalid_controls": rejected}


if __name__ == "__main__":
    print(json.dumps(self_check(), indent=2))
