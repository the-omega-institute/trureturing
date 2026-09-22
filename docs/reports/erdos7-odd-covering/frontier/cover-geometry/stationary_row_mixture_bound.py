#!/usr/bin/env python3
"""Exact stationary mixtures of row-avoiding prefix-bounded probabilities.

Standard library only. The generic stationary_distribution function accepts
an exact rational stochastic matrix with zero diagonal; reducibility and
periodicity are allowed. mix_row_avoiding_laws accepts four actual finite
probabilities on (row, seven-adic residue), checks their row exclusions and
all depth-dependent five-ary prefix caps, and constructs one common law.

The default fixture uses four different complete five-ary depth-two trees.
Its row assignments, prefix bounds, stationary mixture, and all independent
root layouts are checked exactly. The all-height bound is an analytic
consequence of the root inequality and LCM expansion, not finite enumeration.
No assertion about arbitrary sources satisfying only the older full-union
condition, actual covering-system realization, or Lean certification is made.
All checks remain enabled under -O.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
import json


ROWS = (1, 2, 3, 4)


def check(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    check(type(value) in (int, Fraction), "values must be exact integers or Fractions")
    return Fraction(value)


def positive_height(height):
    check(type(height) is int and height >= 1, "height must be a positive integer")


def _solve_square(matrix, rhs):
    """Rational Gauss-Jordan elimination with an explicit nonsingularity check."""
    n = len(matrix)
    augmented = [list(row) + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((row for row in range(col, n) if augmented[row][col]), None)
        check(pivot is not None, "closed irreducible class must have a unique normalized stationary law")
        augmented[col], augmented[pivot] = augmented[pivot], augmented[col]
        scale = augmented[col][col]
        augmented[col] = [entry / scale for entry in augmented[col]]
        for row in range(n):
            if row != col and augmented[row][col]:
                scale = augmented[row][col]
                augmented[row] = [x - scale * y for x, y in zip(augmented[row], augmented[col])]
    return tuple(augmented[i][-1] for i in range(n))


def stationary_distribution(matrix):
    """Return one exact stationary law; no irreducibility hypothesis is imposed."""
    matrix = tuple(tuple(rational(x) for x in row) for row in matrix)
    n = len(matrix)
    check(n >= 2 and all(len(row) == n for row in matrix), "matrix must be square of order at least two")
    check(all(x >= 0 for row in matrix for x in row), "transition entries must be nonnegative")
    check(all(sum(row) == 1 for row in matrix), "every transition row must sum to one")
    check(all(matrix[i][i] == 0 for i in range(n)), "transition diagonal must be zero")

    reach = []
    for start in range(n):
        seen, pending = {start}, [start]
        while pending:
            vertex = pending.pop()
            for target in range(n):
                if matrix[vertex][target] and target not in seen:
                    seen.add(target)
                    pending.append(target)
        reach.append(seen)
    classes = sorted({tuple(i for i in range(n) if i in reach[j] and j in reach[i])
                      for j in range(n)})
    closed = [component for component in classes
              if all(not matrix[i][j] for i in component for j in range(n) if j not in component)]
    check(closed, "a finite transition graph must have a closed communicating class")
    component = closed[0]
    equations = [[matrix[i][j] - int(i == j) for i in component] for j in component[:-1]]
    equations.append([Fraction(1)] * len(component))
    solution = _solve_square(equations, [Fraction(0)] * (len(component) - 1) + [Fraction(1)])
    weights = [Fraction(0)] * n
    for i, value in zip(component, solution):
        weights[i] = value
    check(all(x >= 0 for x in weights) and sum(weights) == 1, "stationary probability normalizes")
    check(all(sum(weights[i] * matrix[i][j] for i in range(n)) == weights[j] for j in range(n)),
          "the returned probability is stationary for the original matrix")
    check(max(weights) <= Fraction(1, 2), "zero diagonal bounds every stationary atom by one half")
    return tuple(weights)


def mix_row_avoiding_laws(component_laws, height):
    """Mix four actual laws, each avoiding its indexed row, preserving all caps.

    Each input is a dictionary {(row, y): exact mass}; rows are 1,...,4 and
    0 <= y < 7**height. Every law must obey prefix mass <= 5**(-j), for all
    depths 0 <= j <= height. These are checked premises, not inferred from
    the existence of a tree or from separate marginal optima.
    """
    positive_height(height)
    component_laws = tuple(component_laws)
    check(len(component_laws) == 4, "one component law is required for each excluded row")
    laws = []
    for excluded, law in zip(ROWS, component_laws):
        check(type(law) is dict and law, "each component must be a nonempty probability dictionary")
        normalized = {}
        for point, mass in law.items():
            check(type(point) is tuple and len(point) == 2, "source points must be coordinate pairs")
            row, y = point
            check(type(row) is int and row in ROWS and type(y) is int and 0 <= y < 7**height,
                  "source coordinates must be actual canonical row and seven-adic residues")
            mass = rational(mass)
            check(mass >= 0, "component masses must be nonnegative")
            normalized[point] = mass
        check(sum(normalized.values()) == 1, "each component must have total mass one")
        check(sum(mass for (row, _), mass in normalized.items() if row == excluded) == 0,
              "component law must avoid its own indexed row")
        for depth in range(height + 1):
            prefix = Counter()
            for (_, y), mass in normalized.items():
                prefix[y % 7**depth] += mass
            check(max(prefix.values()) <= Fraction(1, 5**depth), "component prefix capacity")
        laws.append(normalized)

    transition = tuple(tuple(sum(mass for (row, _), mass in law.items() if row == target)
                             for target in ROWS) for law in laws)
    weights = stationary_distribution(transition)
    mixture = Counter()
    for coefficient, law in zip(weights, laws):
        for point, mass in law.items():
            mixture[point] += coefficient * mass
    mixture = {point: mass for point, mass in mixture.items() if mass > 0}
    check(sum(mixture.values()) == 1, "the actual mixture normalizes")
    check(all(sum(mass for (row, _), mass in mixture.items() if row == r) == weights[r - 1]
              for r in ROWS), "stationary weights equal the actual row masses")
    for depth in range(height + 1):
        prefix, joint = Counter(), Counter()
        for (row, y), mass in mixture.items():
            prefix[y % 7**depth] += mass
            joint[row, y % 7**depth] += mass
        check(max(prefix.values()) <= Fraction(1, 5**depth), "same-law plain prefix bound")
        check(all(mass <= (1 - weights[row - 1]) * Fraction(1, 5**depth)
                  for (row, _), mass in joint.items()), "same-law row-prefix bound")
    return dict(probability=mixture, stationary_weights=weights, transition_matrix=transition)


def finite_bound(height):
    """The analytic full independent-layout upper bound at a positive height."""
    positive_height(height)
    return 4 + 4 * sum((Fraction(2 * j + 1, 5**j) for j in range(2, height + 1)), Fraction(0))


def comparison_target(height):
    positive_height(height)
    return 2 * (3 - Fraction(height + 2, 3**height))


def root_maximum(probability):
    """Literal complete root test, including all zero-mass/absent phases."""
    roots, rows, columns = Counter(), Counter(), Counter()
    for (row, y), mass in probability.items():
        roots[row, y % 7] += mass
        rows[row] += mass
        columns[y % 7] += mass
    best, witness = Fraction(-1), None
    count = 0
    for row, column, point_row, point_column in product(range(5), range(7), range(5), range(7)):
        value = sum((mass * (1 + int(r == row) + int(c == column)
                     + int((r, c) == (point_row, point_column)))**2
                     for (r, c), mass in roots.items()), Fraction(0))
        expansion = (1 + 3 * rows[row] + 3 * columns[column] + 2 * roots[row, column]
                     + (3 + 2 * int(row == point_row) + 2 * int(column == point_column))
                     * roots[point_row, point_column])
        check(value == expansion, "literal root square agrees with the independent-layout expansion")
        if value > best:
            best, witness = value, (row, column, point_row, point_column)
        count += 1
    return best, witness, count


def tree_fixture(height=2):
    """Four nonidentical complete five-ary trees with varying actual row assignments."""
    positive_height(height)
    laws, tree_leaves = [], []
    for excluded_index in range(4):
        prefixes = [(0, ())]
        for depth in range(height):
            prefixes = [(value + digit * 7**depth, digits + (digit,))
                        for value, digits in prefixes
                        for digit in ((2 * value + excluded_index + depth + offset) % 7
                                      for offset in range(5))]
        available = [ROWS[(excluded_index + offset) % 4] for offset in (1, 2, 3)]
        law = {}
        for value, digits in prefixes:
            row = available[sum((j + 1) * digit for j, digit in enumerate(digits)) % 3]
            law[row, value] = Fraction(1, 5**height)
        leaves = {value for value, _ in prefixes}
        check(len(law) == len(leaves) == 5**height, "fixture tree has its full leaf count")
        for depth in range(height):
            children = {}
            for y in leaves:
                children.setdefault(y % 7**depth, set()).add((y // 7**depth) % 7)
            check(all(len(digits) == 5 for digits in children.values()), "every fixture tree node has five children")
        laws.append(law)
        tree_leaves.append(leaves)
    check(len({tuple(sorted(leaves)) for leaves in tree_leaves}) == 4, "component trees must be different")
    return laws


def _rejects(operation):
    try:
        operation()
    except ValueError:
        return
    raise ValueError("invalid input was accepted")


def verify():
    periodic = stationary_distribution(((0, 1), (1, 0)))
    check(periodic == (Fraction(1, 2), Fraction(1, 2)), "periodic two-state control")
    reducible = stationary_distribution(((0, 1, 0, 0), (1, 0, 0, 0),
                                        (0, 0, 0, 1), (0, 0, 1, 0)))
    check(reducible == (Fraction(1, 2), Fraction(1, 2), 0, 0), "reducible two-closed-class control")
    cycle = stationary_distribution(((0, 1, 0, 0), (0, 0, 1, 0),
                                     (0, 0, 0, 1), (1, 0, 0, 0)))
    check(cycle == (Fraction(1, 4),) * 4, "four-cycle control")
    bad_matrices = (((0,),), ((0, 1),), ((0, 0), (1, 0)),
                    ((Fraction(1, 2), Fraction(1, 2)), (1, 0)),
                    ((0, -1), (1, 0)), ((0, 1.0), (1, 0)), ((False, 1), (1, 0)))
    for matrix in bad_matrices:
        _rejects(lambda matrix=matrix: stationary_distribution(matrix))
    laws = tree_fixture()
    result = mix_row_avoiding_laws(laws, 2)
    maximum, witness, root_tests = root_maximum(result["probability"])
    check(maximum <= 4, "actual nonidentical-tree mixture passes every root layout")
    half = Fraction(1, 2)
    case_bounds = (Fraction(17, 5) + Fraction(6, 5) * half,
                   3 + Fraction(8, 5) * half,
                   Fraction(5, 2) + 3 * half,
                   Fraction(5, 2) + Fraction(13, 5) * half)
    check(case_bounds == (4, Fraction(19, 5), 4, Fraction(19, 5)), "four root-overlap case bounds")
    finite, ordered_label_pairs = [], 0
    for height in range(1, 7):
        bound, target = finite_bound(height), comparison_target(height)
        labels = tuple(product((0, 1), range(height + 1)))
        root_pairs, depth_pairs = 0, Counter()
        for (_, depth_a), (_, depth_b) in product(labels, repeat=2):
            ordered_label_pairs += 1
            if depth_a <= 1 and depth_b <= 1:
                root_pairs += 1
            else:
                depth_pairs[max(depth_a, depth_b)] += 1
        check(root_pairs == 16, "all ordered pairs from the four root labels are retained together")
        check(all(depth_pairs[j] == 4 * (2 * j + 1) for j in range(2, height + 1)),
              "literal original labels have the claimed LCM multiplicity")
        expanded_bound = 4 + sum((Fraction(count, 5**depth) for depth, count in depth_pairs.items()),
                                 Fraction(0))
        check(expanded_bound == bound, "original-label expansion gives the analytic finite bound")
        difference = sum(((2 * j + 1) * (Fraction(2, 3**j) - Fraction(4, 5**j))
                          for j in range(2, height + 1)), Fraction(0))
        check(target - bound == difference, "finite target difference identity")
        check(difference == 0 if height == 1 else difference > 0, "finite target comparison")
        finite.append(dict(height=height, bound=str(bound), target=str(target), margin=str(difference)))
    check(finite_bound(2) == Fraction(24, 5) and comparison_target(2) - finite_bound(2) == Fraction(14, 45),
          "first strict finite comparison")
    limit = 4 + 4 * (Fraction(15, 8) - Fraction(8, 5))
    check(limit == Fraction(51, 10) < 6, "exact infinite envelope")
    # A separate two-heavy-row fixture attains the root constant four.
    sharp_laws = [{(2 if excluded == 1 else 1, digit): Fraction(1, 5) for digit in range(5)}
                  for excluded in ROWS]
    sharp = mix_row_avoiding_laws(sharp_laws, 1)
    sharp_max, _, _ = root_maximum(sharp["probability"])
    check(sharp_max == 4, "root constant is attained by an actual stationary mixture")
    _rejects(lambda: mix_row_avoiding_laws(laws, 0))
    _rejects(lambda: mix_row_avoiding_laws(laws[:3], 2))
    invalid = [dict(law) for law in laws]
    invalid[0] = {(1, 0): Fraction(1)}
    _rejects(lambda: mix_row_avoiding_laws(invalid, 2))
    invalid = [dict(law) for law in laws]
    invalid[0] = {(2, 0): Fraction(1)}
    _rejects(lambda: mix_row_avoiding_laws(invalid, 2))
    return dict(
        scope="Four row-avoiding five-ary-prefix laws produce one full-layout law; every triple union containing a five-ary tree is sufficient",
        fixture_height=2, fixture_component_trees=4, fixture_leaves_per_tree=25,
        fixture_source_points=len(set().union(*(set(law) for law in laws))),
        actual_mixture_points=len(result["probability"]),
        transition_matrix=[[str(x) for x in row] for row in result["transition_matrix"]],
        stationary_row_masses=[str(x) for x in result["stationary_weights"]],
        root_independent_layouts=root_tests, actual_root_maximum=str(maximum),
        root_attaining_layout=dict(row=witness[0], column=witness[1], point=list(witness[2:])),
        sharp_root_constant=str(sharp_max), root_case_bounds=[str(x) for x in case_bounds],
        finite_comparisons=finite, infinite_bound=str(limit), infinite_margin=str(6 - limit),
        ordered_label_pairs=ordered_label_pairs,
        matrix_controls=3, matrix_rejections=len(bad_matrices), law_rejections=4,
        assumptions="The row-avoiding component laws must share one actual source and each preserve all required five-ary prefix caps; full-union blocking alone is not sufficient input",
        status="exact rational checks; not Lean certification or an unrestricted covering theorem",
    )


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
