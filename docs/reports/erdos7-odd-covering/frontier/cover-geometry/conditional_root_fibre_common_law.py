#!/usr/bin/env python3
"""Glue actual admissible root fibres and private trees into one probability.

The two proved sufficient patterns are four admissible root fibres, or
two admissible root fibres plus three private five-ary tails in distinct
rows. Every chosen continuing child must separately have six pair-3 and
one full-5 tail tree. No such inheritance is asserted for arbitrary sources.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import importlib.util
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def _sibling(filename, name):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    if spec is None or spec.loader is None:
        raise ImportError(filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_common = _sibling("full_and_pair_tree_common_law.py", "_four_fibre_common_law")
LIMIT = F(1381, 245)


def bound(height):
    require(type(height) is int and height >= 1, "positive integer height")
    return F(77, 20) + sum((F(2 * j + 3, 4) *
                           (F(8, 5 ** (j + 1)) + F(9, 5 * 3 ** j) - F(6, 5 * 15 ** j))
                           for j in range(1, height)), F(0))


def glue_four_fibres(height, source, columns):
    """Select four actual admissible tail sources and equally mix their laws."""
    require(type(height) is int and height >= 1, "positive integer height")
    source = _common.validate_source(height, source)
    require(type(columns) in (tuple, list) and len(columns) == 4
            and all(type(c) is int and 0 <= c < 7 for c in columns)
            and len(set(columns)) == 4, "four distinct literal root columns required")
    laws, certificates, audits = {}, {}, {}
    result = {}
    for c in columns:
        child = {(r, y // 7) for r, y in source if y % 7 == c}
        certificate = _common.make_common_law(height - 1, child)
        certificates[c] = certificate
        audits[c] = _common.verify_common_law(height - 1, child, certificate)
        laws[c] = certificate["nu"]
        for (r, z), mass in laws[c].items():
            result[r, c + 7 * z] = mass / 4
    require(set(result) <= source and sum(result.values(), F(0)) == 1, "one actual supported glued law")
    row, root = defaultdict(F), defaultdict(F)
    for (r, y), mass in result.items():
        row[r] += mass
        root[r, y % 7] += mass
    require(max(row.values()) <= F(2, 5) and max(root.values()) <= F(1, 10), "actual root row and cell caps")
    root_max = max(sum((mass * (1 + (r == a) + (c == b) + ((r, c) == (u, v))) ** 2
                       for (r, c), mass in root.items()), F(0))
                   for a, b, u, v in product(range(5), range(7), range(5), range(7)))
    require(root_max <= F(77, 20), "all independent root phases")
    caps = []
    actual_envelope = root_max
    for depth in range(2, height + 1):
        j = depth - 1
        plain, joint = defaultdict(F), defaultdict(F)
        for (r, y), mass in result.items():
            plain[y % 7 ** depth] += mass
            joint[r, y % 7 ** depth] += mass
        m = F(2, 5 ** (j + 1)) + F(3, 5 * 3 ** j)
        c = F(2, 5) * (F(1, 5 ** j) + (1 - F(1, 5 ** j)) / 3 ** j)
        m0, m1 = max(plain.values()), max(joint.values())
        require(m0 <= m / 4 and m1 <= c / 4, "same-law conditional prefix caps")
        actual_envelope += (2 * depth + 1) * (m0 + 3 * m1)
        caps.append({"depth": depth, "pure": str(m0), "joint": str(m1)})
    target = 6 - F(2 * (height + 2), 3 ** height)
    require(actual_envelope <= bound(height) and target - bound(height) >= F(3, 20), "original-label comparison")
    return {"law": result, "child_certificates": certificates, "child_audits": audits,
            "audit": {"height": height, "source_points": len(source), "law_support_points": len(result),
                      "root_maximum": str(root_max), "root_bound": "77/20", "prefix_caps": caps,
                      "actual_original_label_envelope": str(actual_envelope), "bound": str(bound(height)),
                      "target": str(target), "margin": str(target - bound(height))}}


def two_continuing_bound(height):
    require(type(height) is int and height >= 1, "positive integer height")
    return F(157, 40) + F(11, 40) * sum((F(2 * j + 3) *
                           (F(8, 5 ** (j + 1)) + F(9, 5 * 3 ** j) - F(6, 5 * 15 ** j))
                           for j in range(1, height)), F(0))


def glue_two_continuing(height, source, continuing, private_rows):
    """Glue two admissible tail fibres and three distinct-row private five-trees."""
    require(type(height) is int and height >= 1, "positive integer height")
    source = _common.validate_source(height, source)
    require(type(continuing) in (tuple, list) and len(continuing) == 2
            and all(type(c) is int and 0 <= c < 7 for c in continuing)
            and len(set(continuing)) == 2, "two distinct actual continuing columns")
    require(type(private_rows) is dict and len(private_rows) == 3
            and all(type(c) is int and 0 <= c < 7 and type(r) is int and 1 <= r <= 4
                    for c, r in private_rows.items())
            and len(set(private_rows.values())) == 3
            and not set(continuing) & set(private_rows), "three disjoint private columns in three distinct rows")
    result, witnesses = {}, {}
    for c in continuing:
        child = {(r, y // 7) for r, y in source if y % 7 == c}
        certificate = _common.make_common_law(height - 1, child)
        _common.verify_common_law(height - 1, child, certificate)
        witnesses[c] = certificate
        for (r, y), mass in certificate["nu"].items():
            result[r, c + 7 * y] = F(11, 40) * mass
    for c, r in private_rows.items():
        membership = {(s, y): F((s, c + 7 * y) in source) for s, y in product(range(1, 5), range(7 ** (height - 1)))}
        witness = _common._trees.row_tree_witness(membership, height - 1, (r,), 5)
        require(witness["value"] == 1, "private cell lacks its actual full five-ary tail")
        witnesses[c] = witness
        for s, y in witness["points"]:
            result[s, c + 7 * y] = F(3, 20 * 5 ** (height - 1))
    require(set(result) <= source and sum(result.values(), F(0)) == 1, "one actual two-continuing probability")
    row, root = defaultdict(F), defaultdict(F)
    for (r, y), mass in result.items():
        row[r] += mass
        root[r, y % 7] += mass
    require(max(row.values()) <= F(37, 100), "two-continuing row bound")
    root_max = max(sum((mass * (1 + (r == a) + (c == b) + ((r, c) == (u, v))) ** 2
                       for (r, c), mass in root.items()), F(0))
                   for a, b, u, v in product(range(5), range(7), range(5), range(7)))
    require(root_max <= F(157, 40), "two-continuing independent root phases")
    actual_envelope = root_max
    for depth in range(2, height + 1):
        j = depth - 1
        plain, joint = defaultdict(F), defaultdict(F)
        for (r, y), mass in result.items():
            plain[y % 7 ** depth] += mass
            joint[r, y % 7 ** depth] += mass
        m = F(2, 5 ** (j + 1)) + F(3, 5 * 3 ** j)
        c = F(2, 5) * (F(1, 5 ** j) + (1 - F(1, 5 ** j)) / 3 ** j)
        m0, m1 = max(plain.values()), max(joint.values())
        require(m0 <= F(11, 40) * m and m1 <= F(11, 40) * c, "two-continuing actual deeper caps")
        actual_envelope += (2 * depth + 1) * (m0 + 3 * m1)
    target = 6 - F(2 * (height + 2), 3 ** height)
    require(actual_envelope <= two_continuing_bound(height)
            and target - two_continuing_bound(height) >= F(7, 225), "two-continuing target comparison")
    return {"law": result, "witnesses": witnesses,
            "audit": {"height": height, "source_points": len(source), "law_support_points": len(result),
                      "root_maximum": str(root_max), "actual_original_label_envelope": str(actual_envelope),
                      "bound": str(two_continuing_bound(height)), "target": str(target),
                      "margin": str(target - two_continuing_bound(height))}}


def self_check():
    recursive = _sibling("recursive_minimum_source_common_law.py", "_four_fibre_recursive_fixture")
    obstruction = _sibling("fixed_source_subclass_decomposition_obstruction.py", "_four_fibre_obstruction_fixture")
    controls = []
    two_controls = []
    for height in range(1, 5):
        h = height - 1
        children = [set(recursive.law(h)),
                    set(recursive.coloured_law(h, recursive.last_digit_colour)),
                    {(r, y) for r in (1, 2, 3) for y in recursive.five_leaves(h)},
                    set(product((1, 2, 3, 4), range(7 ** h)))]
        if h == 2:
            children[3] = obstruction.fixture(2)
        source = {(r, c + 7 * z) for c, child in zip((0, 2, 4, 6), children) for r, z in child}
        # A fifth projection branch makes the whole carrier globally admissible,
        # although it need not be used by the constructed probability.
        source |= {(1, 1 + 7 * z) for z in recursive.five_leaves(h)}
        global_certificate = _common.make_common_law(height, source)
        _common.verify_common_law(height, source, global_certificate)
        controls.append(glue_four_fibres(height, source, (0, 2, 4, 6))["audit"])
        two_source = {(r, c + 7 * z) for c, child in zip((0, 6), children[:2]) for r, z in child}
        for c, r in ((1, 1), (3, 2), (5, 3)):
            tails = {0}
            for _ in range(h):
                tails = {d + 7 * z for d in range(r - 1, r + 4) for z in tails}
            two_source |= {(r, c + 7 * z) for z in tails}
        global_certificate = _common.make_common_law(height, two_source)
        _common.verify_common_law(height, two_source, global_certificate)
        require(len(two_source) == 5 ** height + 4, "minimum-child two-continuing source size")
        two_controls.append(glue_two_continuing(height, two_source, (0, 6), {1: 1, 3: 2, 5: 3})["audit"])
    require(LIMIT == F(77, 20) + F(1, 4) *
            (F(8, 5) * F(11, 8) + F(9, 5) * 3 - F(6, 5) * F(37, 98)), "limit series")
    require([6 - F(2 * (k + 2), 3 ** k) - bound(k) for k in (1, 2, 3)]
            == [F(3, 20), F(19, 90), F(3739, 13500)], "initial exact margins")
    require(F(158, 27) - LIMIT - F(3, 20) == F(1723, 26460) > 0, "all later margins")
    two_limit = F(157, 40) + F(11, 40) * (F(8, 5) * F(11, 8) + F(9, 5) * 3 - F(6, 5) * F(37, 98))
    require(two_limit == F(28863, 4900), "two-continuing limit")
    require([6 - F(2 * (k + 2), 3 ** k) - two_continuing_bound(k) for k in (1, 2, 3, 4)]
            == [F(3, 40), F(7, 225), F(6979, 135000), F(5273, 67500)], "two-continuing initial margins")
    require(F(1444, 243) - two_limit > F(7, 225), "two-continuing all later margins")
    rejected = 0
    for columns in ((0, 1, 2), (0, 0, 2, 3), (True, 1, 2, 3), (0, 1, 2, 7)):
        try:
            glue_four_fibres(1, {(r, y) for r in (1, 2, 3) for y in range(7)}, columns)
        except ValueError:
            rejected += 1
    try:
        glue_four_fibres(1, {(1, y) for y in range(7)}, (0, 1, 2, 3))
    except ValueError:
        rejected += 1
    require(rejected == 5, "malformed columns or failed child premises")
    valid_source = {(r, y) for r in (1, 2, 3) for y in range(7)}
    bad_two = (
        lambda: glue_two_continuing(1, valid_source, (0, 0), {1: 1, 2: 2, 3: 3}),
        lambda: glue_two_continuing(1, valid_source, (0, True), {2: 1, 3: 2, 4: 3}),
        lambda: glue_two_continuing(1, valid_source, (0, 1), {2: 1, 3: 1, 4: 3}),
        lambda: glue_two_continuing(1, valid_source, (0, 1), {1: 1, 2: 2, 3: 3}),
        lambda: glue_two_continuing(1, valid_source, (0, 1), {2: 1, 3: 2, 4: 4}),
    )
    for operation in bad_two:
        try:
            operation()
        except ValueError:
            rejected += 1
    require(rejected == 10, "two-continuing malformed or unavailable private tree controls")
    return {"controls": controls, "two_continuing_controls": two_controls,
            "rejected_controls": rejected, "uniform_limit": str(LIMIT),
            "two_continuing_limit": str(two_limit), "two_continuing_uniform_margin": "7/225",
            "uniform_target_margin": "3/20",
            "scope": "two actual conditional patterns suffice; no general inheritance or optimality claim"}


if __name__ == "__main__":
    print(json.dumps(self_check(), indent=2))
