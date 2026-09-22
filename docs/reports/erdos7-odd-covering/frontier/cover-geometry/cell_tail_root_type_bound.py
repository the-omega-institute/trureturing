#!/usr/bin/env python3
"""Exact root layouts and cell-tail bounds on Z/5 x Z/7^K.

The reusable envelope accepts a positive rational root law and a branching
base from 3 through 7 for each cell. It computes all independent root
layouts and a uniform bound for every higher depth. An optional constructor
checks actual conditional tail laws and builds one common supported law.

The six fixtures are the exact root types A--F. Combinatorial controls check
the root rectangle premise and each isolating rectangle; full-depth tree
inheritance remains the analytic implication in the companion report.
No actual distinct odd covering or Lean certification is claimed.
All checks remain active under -O; only the standard library is used.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json


def check(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    check(type(value) in (int, Fraction), "exact int or Fraction required")
    return Fraction(value)


def positive_height(height):
    check(type(height) is int and height >= 1, "height must be a positive integer")


def validate_root(root_law):
    check(type(root_law) is dict and root_law, "root law must be a nonempty dictionary")
    law = {}
    for point, mass in root_law.items():
        check(type(point) is tuple and len(point) == 2, "root points must be pairs")
        row, col = point
        check(type(row) is int and 0 <= row < 5 and type(col) is int and 0 <= col < 7,
              "canonical root residues required")
        law[point] = rational(mass)
        check(law[point] > 0, "root masses must be positive")
    check(sum(law.values()) == 1, "root masses must sum to one")
    return law


def root_maximum(root_law):
    """All 1225 independent root layouts, including every absent residue."""
    law = validate_root(root_law)
    row_mass, col_mass = Counter(), Counter()
    for (row, col), mass in law.items():
        row_mass[row] += mass
        col_mass[col] += mass
    best, witness, count = Fraction(-1), None, 0
    for row, col, point_row, point_col in product(range(5), range(7), range(5), range(7)):
        direct = sum((mass * (1 + (r == row) + (c == col)
                             + ((r, c) == (point_row, point_col)))**2
                      for (r, c), mass in law.items()), Fraction(0))
        expansion = (1 + 3 * row_mass[row] + 3 * col_mass[col] + 2 * law.get((row, col), 0)
                     + (3 + 2 * (row == point_row) + 2 * (col == point_col))
                     * law.get((point_row, point_col), 0))
        check(direct == expansion, "root integration must agree with the independent-layout expansion")
        if direct > best:
            best, witness = direct, (row, col, point_row, point_col)
        count += 1
    return dict(maximum=best, witness=witness, layouts=count)


def cell_tail_envelope(root_law, tail_bases):
    """Bound every height from a root law and per-cell uniform-tree bases.

At tail depth j>=1 a cell of base b has mass <= w*b**(-j).
Since b>=3, its normalization by 3**(-j) decreases with j.
Thus the plain and joint normalized caps are computed at j=1.
Input tree existence must come from the actual source, not this function.
"""
    law = validate_root(root_law)
    check(type(tail_bases) is dict and set(tail_bases) == set(law), "one tail base per root cell required")
    check(all(type(base) is int and 3 <= base <= 7 for base in tail_bases.values()),
          "tail bases must be integers from three through seven")
    normalized_columns = Counter()
    normalized_atoms = []
    for point, mass in law.items():
        normalized = mass * Fraction(3, tail_bases[point])
        normalized_columns[point[1]] += normalized
        normalized_atoms.append(normalized)
    plain, joint = max(normalized_columns.values()), max(normalized_atoms)
    root = root_maximum(law)
    slope = 3 * (plain + 3 * joint)
    gap_at_zero = 4 - root["maximum"]
    gap_at_one = 6 - root["maximum"] - slope
    return dict(root_maximum=root["maximum"], root_witness=root["witness"], root_layouts=root["layouts"],
                plain_coefficient=plain, joint_coefficient=joint, shell_coefficient=slope,
                infinite_bound=root["maximum"] + slope,
                initial_gap=gap_at_zero, limit_gap=gap_at_one,
                all_finite_comparison=(gap_at_zero >= 0 and gap_at_one >= 0))


def tail_sum(height):
    positive_height(height)
    return 1 - Fraction(height + 2, 3**height)


def finite_bound(envelope, height):
    return envelope["root_maximum"] + envelope["shell_coefficient"] * tail_sum(height)


def mix_cell_tail_laws(root_law, tail_bases, component_laws, height):
    """Validate actual per-cell tail laws and form their one common mixture.

component_laws[(r,c)] is a probability dictionary on z mod 7**(height-1).
Every prefix at depth j must have conditional mass <= tail_bases[(r,c)]**(-j).
The resulting source point is (r,c+7*z). The caller supplies the actual
source membership; this function uses the union of the supplied supports.
"""
    positive_height(height)
    law = validate_root(root_law)
    envelope = cell_tail_envelope(law, tail_bases)
    check(type(component_laws) is dict and set(component_laws) == set(law),
          "one conditional probability per root cell required")
    mixture = {}
    for (row, col), weight in law.items():
        component = component_laws[row, col]
        check(type(component) is dict and component, "nonempty conditional probability dictionary required")
        normalized = {}
        for z, mass in component.items():
            check(type(z) is int and 0 <= z < 7**(height - 1), "canonical tail residue required")
            normalized[z] = rational(mass)
            check(normalized[z] >= 0, "conditional masses must be nonnegative")
        check(sum(normalized.values()) == 1, "conditional probability must normalize")
        for depth in range(height):
            prefix = Counter()
            for z, mass in normalized.items():
                prefix[z % 7**depth] += mass
            check(max(prefix.values()) <= Fraction(1, tail_bases[row, col]**depth),
                  "conditional prefix violates its cell-tree bound")
        for z, mass in normalized.items():
            if mass:
                mixture[row, col + 7*z] = weight * mass
    check(sum(mixture.values()) == 1, "the common law must normalize")
    roots = Counter()
    for (row, y), mass in mixture.items():
        roots[row, y % 7] += mass
    check(dict(roots) == law, "mixture must have the prescribed root law")
    for depth in range(2, height + 1):
        prefix, joint = Counter(), Counter()
        for (row, y), mass in mixture.items():
            prefix[y % 7**depth] += mass
            joint[row, y % 7**depth] += mass
        check(max(prefix.values()) <= envelope["plain_coefficient"] / 3**(depth - 1),
              "common-law pure prefix bound")
        check(max(joint.values()) <= envelope["joint_coefficient"] / 3**(depth - 1),
              "common-law joint prefix bound")
    return dict(probability=mixture, envelope=envelope)


def root_tree_consequences(source):
    """Finite root implications; global source tree tests remain hypotheses."""
    source = set(source)
    check(source and all(type(point) is tuple and len(point) == 2
                         and type(point[0]) is int and 0 <= point[0] < 5
                         and type(point[1]) is int and 0 <= point[1] < 7
                         for point in source), "canonical nonempty root source required")
    isolators, rectangles = {}, 0
    for rows in combinations(range(5), 3):
        for columns in combinations(range(7), 5):
            hit = {point for point in source if point[0] in rows and point[1] in columns}
            check(hit, "root source misses a three-by-five rectangle")
            if len(hit) == 1:
                isolators.setdefault(next(iter(hit)), (rows, columns))
            rectangles += 1
    columns = {point[1] for point in source}
    private = {point for point in source if sum(q[1] == point[1] for q in source) == 1}
    forced_five = private if len(columns) == 5 else set()
    return dict(isolators=isolators, forced_five=forced_five, columns=len(columns), rectangles=rectangles)


def fixtures():
    """Columns a,...,g are represented by 0,...,6; rows stay 1,...,4."""
    neighborhoods = {
        "A": ((0,), (1, 2), (0, 1, 2), (3, 4)),
        "B": ((0,), (1, 2), (1, 3), (1, 4)),
        "C": ((0,), (1, 2), (1, 3), (2, 4)),
        "D": ((0,), (1, 2), (1, 3), (4, 5)),
        "E": ((0, 1), (0, 2), (1, 2), (3, 4)),
        "F": ((0,), (1, 2), (3, 4), (5, 6)),
    }
    output = {}
    for name, rows in neighborhoods.items():
        points = {(row, col) for row, cols in enumerate(rows, 1) for col in cols}
        law = {point: Fraction(1, len(points)) for point in points}
        bases = {point: 3 for point in points}
        if name == "B":
            law = {point: Fraction(1, 9) if point[1] == 1 else Fraction(1, 6) for point in points}
            bases = {point: 3 if point[1] == 1 else 5 for point in points}
        elif name == "C":
            private = {(3, 3), (4, 4)}
            law = {point: Fraction(1, 6) if point in private else Fraction(2, 15) for point in points}
            bases = {point: 5 if point in private or point == (1, 0) else 3 for point in points}
        elif name == "D":
            law = {point: Fraction(2, 15) if point == (1, 0) or point[1] == 1
                   else Fraction(3, 20) for point in points}
        elif name == "E":
            bases = {point: 5 if point[0] == 4 else 3 for point in points}
        output[name] = (law, bases)
    return output


def cell_tree_fixture(root_law, bases, height):
    """Actual, prefix-dependent conditional laws for the mixture API control."""
    positive_height(height)
    components = {}
    for (row, col) in root_law:
        leaves = [0]
        for depth in range(height - 1):
            leaves = [prefix + ((3 * prefix + row + col + depth + offset) % 7) * 7**depth
                      for prefix in leaves for offset in range(bases[row, col])]
        check(len(set(leaves)) == bases[row, col]**(height - 1), "selected tree leaf count")
        for depth in range(height - 1):
            children = {}
            for z in leaves:
                children.setdefault(z % 7**depth, set()).add((z // 7**depth) % 7)
            check(all(len(digits) == bases[row, col] for digits in children.values()),
                  "every selected node has its specified number of children")
        components[row, col] = {z: Fraction(1, len(leaves)) for z in leaves}
    return components


def rejects(operation):
    try:
        operation()
    except ValueError:
        return
    raise ValueError("invalid input was accepted")


def verify():
    expected = {
        "A": (Fraction(4), Fraction(1, 4), Fraction(1, 8), Fraction(15, 8)),
        "B": (Fraction(35, 9), Fraction(1, 3), Fraction(1, 9), Fraction(2)),
        "C": (Fraction(39, 10), Fraction(4, 15), Fraction(2, 15), Fraction(2)),
        "D": (Fraction(77, 20), Fraction(4, 15), Fraction(3, 20), Fraction(43, 20)),
        "E": (Fraction(29, 8), Fraction(1, 4), Fraction(1, 8), Fraction(15, 8)),
        "F": (Fraction(25, 7), Fraction(1, 7), Fraction(1, 7), Fraction(12, 7)),
    }
    cases = []
    ordered_pairs = 0
    for name, (law, bases) in fixtures().items():
        root_geometry = root_tree_consequences(law)
        for point, base in bases.items():
            check(point in root_geometry["isolators"] or point in root_geometry["forced_five"],
                  "each cell must have a supported tree-inheritance argument")
            check(base == 3 or (base == 5 and point in root_geometry["forced_five"]),
                  "five-ary cell selection must have the private-column premise")
        envelope = cell_tail_envelope(law, bases)
        observed = tuple(envelope[key] for key in
                         ("root_maximum", "plain_coefficient", "joint_coefficient", "shell_coefficient"))
        check(observed == expected[name], "exact root and tail coefficient table")
        check(envelope["all_finite_comparison"], "both affine comparison endpoints must be nonnegative")
        components = cell_tree_fixture(law, bases, 3)
        mixed = mix_cell_tail_laws(law, bases, components, 3)
        comparisons = []
        for height in range(1, 7):
            labels = tuple(product((0, 1), range(height + 1)))
            counts, root_pairs = Counter(), 0
            for (a, b), (c, d) in product(labels, repeat=2):
                ordered_pairs += 1
                if max(b, d) <= 1:
                    root_pairs += 1
                else:
                    counts[max(a, c), max(b, d)] += 1
            check(root_pairs == 16, "complete four-label root square retained")
            expanded = envelope["root_maximum"]
            for depth in range(2, height + 1):
                check(counts[0, depth] == 2 * depth + 1
                      and counts[1, depth] == 3 * (2 * depth + 1), "original-label LCM multiplicities")
                expanded += (counts[0, depth] * envelope["plain_coefficient"]
                             + counts[1, depth] * envelope["joint_coefficient"]) / 3**(depth - 1)
            bound = finite_bound(envelope, height)
            check(bound == expanded, "literal ordered labels give the proposed finite envelope")
            target = 4 + 2 * tail_sum(height)
            gap = target - bound
            check(gap >= 0 and (gap > 0 or (name == "A" and height == 1)),
                  "finite target comparison and strictness")
            affine_gap = ((1 - tail_sum(height)) * envelope["initial_gap"]
                          + tail_sum(height) * envelope["limit_gap"])
            check(gap == affine_gap, "endpoint interpolation yields the exact finite margin")
            comparisons.append(dict(height=height, bound=str(bound), target=str(target), gap=str(gap)))
        cases.append(dict(type=name, root_edges=len(law), active_columns=root_geometry["columns"],
                          isolatable_cells=len(root_geometry["isolators"]),
                          forced_five_cells=len(root_geometry["forced_five"]),
                          root_rectangles=root_geometry["rectangles"],
                          root_layouts=envelope["root_layouts"], root_witness=envelope["root_witness"],
                          coefficients=[str(x) for x in observed],
                          infinite_bound=str(envelope["infinite_bound"]),
                          fixture_height=3, mixture_points=len(mixed["probability"]),
                          finite_comparisons=comparisons))
    law, bases = fixtures()["B"]
    components = cell_tree_fixture(law, bases, 2)
    rejects(lambda: cell_tail_envelope({(1, 0): 1.0}, {(1, 0): 3}))
    rejects(lambda: cell_tail_envelope({(1, 0): Fraction(1, 2)}, {(1, 0): 3}))
    rejects(lambda: cell_tail_envelope({(1, 0): 1}, {(1, 0): 2}))
    rejects(lambda: cell_tail_envelope({(5, 0): 1}, {(5, 0): 3}))
    rejects(lambda: mix_cell_tail_laws(law, bases, components, 0))
    missing = dict(components)
    del missing[next(iter(missing))]
    rejects(lambda: mix_cell_tail_laws(law, bases, missing, 2))
    concentrated = dict(components)
    concentrated[next(iter(concentrated))] = {0: Fraction(1)}
    rejects(lambda: mix_cell_tail_laws(law, bases, concentrated, 2))
    rejects(lambda: root_tree_consequences({(1, 0)}))
    return dict(cases=cases, total_root_layouts=sum(case["root_layouts"] for case in cases),
                total_root_rectangles=sum(case["root_rectangles"] for case in cases),
                ordered_original_label_pairs=ordered_pairs, invalid_inputs_rejected=8,
                scope="Exact A--F root projections, 5-height one, arbitrary 7-height, both full source tree tests",
                fixture_scope="Conditional mixture controls; global source tree tests are not checked",
                status="exact rational controls; analytic all-height proof; not Lean certification or an odd-cover realization")


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
