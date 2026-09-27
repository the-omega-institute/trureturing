#!/usr/bin/env python3
"""Standalone tree blocking can fail inside joint prefix fibres.

Exact controls for one 116-point source and a supported law whose full
height-two second moment has an analytic upper bound below 529/81.
Local rectangle checks support the ordinary full-tree proof. They do
not enumerate full trees, exclude conditional-law recursion, or assert
realizability by an actual odd cover. All checks remain enabled under -O.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json


ROOT_B = ((1, 1), (2, 2), (2, 3), (3, 2), (3, 4), (4, 2), (4, 5))
FIVE_TAIL = (1, 2, 3, 4)
SEVEN_FULL = (1, 2, 3, 4, 5)
HUB_TAILS = {2: (1, 2, 3), 3: (2, 3, 4), 4: (3, 4, 5)}


def check(condition, message):
    if not condition:
        raise ValueError(message)


def source_weights():
    """Integer atom masses over 1080, before any coordinate projection."""
    return {
        (r + 5 * a, c + 7 * b): 10 if c == 2 else 9
        for r, c in ROOT_B
        for a in FIVE_TAIL
        for b in (HUB_TAILS[r] if c == 2 else SEVEN_FULL)
    }


def verify():
    weights = source_weights()
    points = set(weights)
    denominator = sum(weights.values())
    check(len(points) == 116 and denominator == 1080, "source size and law normalization")
    check(Counter(weights.values()) == {9: 80, 10: 36}, "actual atom multiplicities")
    roots = {(x % 5, y % 7) for x, y in points}
    check(roots == set(ROOT_B), "actual root projection")
    check(all(x % 5 and y % 7 for x, y in points), "zero first roots are absent")

    row_sets = tuple(combinations(range(5), 3))
    column_sets = tuple(combinations(range(7), 5))
    rectangles = tuple(product(row_sets, column_sets))
    for rows, columns in rectangles:
        check(any(r in rows and c in columns for r, c in roots), "root rectangle blocker")

    isolating = []
    fibre_checks = 0
    failing_fibres = []
    for edge in ROOT_B:
        witnesses = [(rows, columns) for rows, columns in rectangles
                     if {(r, c) for r, c in roots if r in rows and c in columns} == {edge}]
        check(witnesses, "each root edge must have an isolating rectangle")
        rows, columns = witnesses[0]
        isolating.append(dict(root=list(edge), rows=list(rows), columns=list(columns)))
        fibre = {(x // 5, y // 7) for x, y in points if (x % 5, y % 7) == edge}
        tails = HUB_TAILS[edge[0]] if edge[1] == 2 else SEVEN_FULL
        check(fibre == set(product(FIVE_TAIL, tails)), "literal joint root fibre")
        for rows, columns in rectangles:
            check(any(a in rows and b in columns for a, b in fibre), "tail rectangle blocker")
            fibre_checks += 1
        seven_projection = {b for _, b in fibre}
        if edge[1] == 2:
            missing = [digits for digits in combinations(range(7), 3)
                       if not seven_projection.intersection(digits)]
            check(len(seven_projection) == 3 and missing,
                  "hub fibre fails the standalone ternary seven-root test")
            failing_fibres.append(dict(root=list(edge), seven_tail=sorted(seven_projection),
                                       disjoint_ternary_digits=list(missing[0])))

    check({x for x, _ in points} == {r + 5 * a for r, a in product(FIVE_TAIL, repeat=2)},
          "five projection is a full four-ary depth-two tree")
    check({y for _, y in points} == {c + 7 * b for c, b in product(SEVEN_FULL, repeat=2)},
          "seven projection is a full five-ary depth-two tree")
    five_child_tests = tuple(combinations(range(5), 3))
    seven_child_tests = tuple(combinations(range(7), 3))
    for digits in five_child_tests:
        check(set(FIVE_TAIL).intersection(digits), "standalone five-tree next digit")
    for digits in seven_child_tests:
        check(set(SEVEN_FULL).intersection(digits), "standalone seven-tree next digit")

    root_weights = Counter()
    for (x, y), mass in weights.items():
        root_weights[x % 5, y % 7] += mass
    for edge in ROOT_B:
        check(Fraction(root_weights[edge], denominator)
              == (Fraction(1, 9) if edge[1] == 2 else Fraction(1, 6)),
              "the root marginal is the specified type-B law")
    root_best = -1
    root_witness = None
    root_layouts = 0
    for a, b, u, v in product(range(5), range(7), range(5), range(7)):
        cost = sum(mass * (1 + (r == a) + (c == b) + ((r, c) == (u, v)))**2
                   for (r, c), mass in root_weights.items())
        if cost > root_best:
            root_best, root_witness = cost, (a, b, u, v)
        root_layouts += 1
    root_bound = Fraction(root_best, denominator)
    check(root_bound == Fraction(35, 9), "full independent root maximum")

    expected = ((Fraction(1), Fraction(1, 3), Fraction(1, 9)),
                (Fraction(5, 18), Fraction(1, 6), Fraction(1, 27)),
                (Fraction(5, 72), Fraction(1, 24), Fraction(1, 108)))
    maxima = {}
    for a, b in product(range(3), repeat=2):
        masses = Counter()
        for (x, y), mass in weights.items():
            masses[x % (5**a), y % (7**b)] += mass
        maxima[a, b] = Fraction(max(masses.values()), denominator)
        check(maxima[a, b] == expected[a][b], "actual same-law prefix maximum")

    exponents = tuple(product(range(3), repeat=2))
    lcm_counts = Counter((max(a, c), max(b, d))
                         for (a, b), (c, d) in product(exponents, repeat=2))
    check(sum(lcm_counts.values()) == 81, "all ordered pairs of nine original labels")
    check(all(count == (2 * a + 1) * (2 * b + 1)
              for (a, b), count in lcm_counts.items()), "LCM multiplicities")
    outside = {depth: count for depth, count in lcm_counts.items() if max(depth) == 2}
    check(outside == {(2, 0): 5, (0, 2): 5, (2, 1): 15, (1, 2): 15, (2, 2): 25},
          "exact complement of the squared root block")
    bound = root_bound + sum((count * maxima[depth] for depth, count in outside.items()),
                             Fraction(0))
    target = Fraction(529, 81)
    check(bound == Fraction(335, 54) and target - bound == Fraction(53, 162) > 0,
          "analytic full-layout bound passes the finite-height comparison")
    hub_bound = 1 + 3 * Fraction(1, 4) + 3 * Fraction(1, 3) + 9 * Fraction(1, 12)
    check(hub_bound == Fraction(7, 2) < 4, "conditional probability recursion remains possible")

    return dict(
        scope="Standalone tree blocking need not pass to joint root fibres; conditional-law recursion remains possible",
        source_points=len(points), root_rectangle_checks=len(rectangles),
        fibre_rectangle_checks=fibre_checks, isolating_root_rectangles=isolating,
        standalone_five_digit_checks=len(five_child_tests),
        standalone_seven_digit_checks=len(seven_child_tests), failing_joint_fibres=failing_fibres,
        law_denominator=denominator, atom_multiplicities=dict(sorted(Counter(weights.values()).items())),
        root_independent_layouts=root_layouts, exact_root_maximum=str(root_bound),
        root_attaining_layout=dict(row=root_witness[0], column=root_witness[1],
                                   point=list(root_witness[2:])),
        prefix_maxima=[[str(maxima[a, b]) for b in range(3)] for a in range(3)],
        ordered_original_divisor_pairs=sum(lcm_counts.values()),
        analytic_full_layout_upper_bound=str(bound), finite_height_target=str(target),
        target_margin=str(target - bound), conditional_hub_root_upper_bound=str(hub_bound),
        exact_full_layout_maximum="not asserted",
    )


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
