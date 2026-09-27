#!/usr/bin/env python3
"""Exact root-layout laws without a standalone column-count condition.

Uses only the Python standard library. All checks remain active under -O.
The classification enumerates all multisets of at most seven nonempty
column incidence types on four labelled rows. It checks the ten minimal
supports and every independent layout, including absent residue choices.

The five-row reduction and the arbitrary-source theorem are proved in
report 395. These checks do not certify arbitrary tails or actual covers.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations, product
import json
from math import comb


def check(condition, message):
    if not condition:
        raise ValueError(message)


TEMPLATES = {
    "A": (1, 6, 7, 24),
    "B": (1, 6, 10, 18),
    "C": (1, 6, 10, 20),
    "D": (1, 6, 10, 48),
    "F": (1, 6, 24, 96),
    "cycle4": (3, 6, 12, 9),
    "triangle_full": (3, 5, 6, 7),
    "two_triples": (1, 6, 7, 7),
    "singleton_triangle": (1, 6, 10, 12),
    "A_shared": (1, 6, 7, 10),
}

EXPECTED_MAXIMA = {
    "A": Fraction(4), "B": Fraction(35, 9), "C": Fraction(4),
    "D": Fraction(4), "F": Fraction(25, 7), "cycle4": Fraction(29, 8),
    "triangle_full": Fraction(4), "two_triples": Fraction(4),
    "singleton_triangle": Fraction(4), "A_shared": Fraction(4),
}


def valid_four_rows(rows):
    return all(rows) and all((a | b).bit_count() >= 3 for a, b in combinations(rows, 2))


def minimal_four_rows(rows):
    if not valid_four_rows(rows):
        return False
    for i, row in enumerate(rows):
        for j in range(7):
            if row >> j & 1:
                smaller = rows[:i] + (row ^ (1 << j),) + rows[i + 1:]
                if valid_four_rows(smaller):
                    return False
    return True


def edges(rows):
    return tuple((i, j) for i, row in enumerate(rows) for j in range(7) if row >> j & 1)


def column_types(rows):
    return tuple(sum(1 << i for i, row in enumerate(rows) if row >> j & 1)
                 for j in range(7) if any(row >> j & 1 for row in rows))


ROW_PERMUTATIONS = tuple(
    tuple(sum(1 << perm[i] for i in range(4) if mask >> i & 1) for mask in range(16))
    for perm in permutations(range(4)))


def canonical_columns(columns):
    return min(tuple(sorted(table[mask] for mask in columns)) for table in ROW_PERMUTATIONS)


def verify_classification():
    canonical = {canonical_columns(column_types(rows)): name for name, rows in TEMPLATES.items()}
    check(len(canonical) == 10, "ten distinct row/column isomorphism classes")
    check(all(minimal_four_rows(rows) for rows in TEMPLATES.values()),
          "every declared template is edge-minimal under the exact hypotheses")
    examined, valid, minimal = 0, 0, 0
    orbit_counts = Counter()
    for size in range(1, 8):
        for columns in combinations_with_replacement(range(1, 16), size):
            examined += 1
            rows = tuple(sum(1 << j for j, mask in enumerate(columns) if mask >> i & 1)
                         for i in range(4))
            if not valid_four_rows(rows):
                continue
            valid += 1
            if not minimal_four_rows(rows):
                continue
            minimal += 1
            key = canonical_columns(columns)
            check(key in canonical, "every minimal support has a declared template")
            orbit_counts[canonical[key]] += 1
    check(examined == comb(22, 7) - 1 == 170543, "complete nonempty column-multiset enumeration")
    check(set(orbit_counts) == set(TEMPLATES), "every template occurs in the exhaustive classification")
    return dict(column_multisets=examined, valid_supports=valid,
                minimal_supports=minimal, minimal_row_label_counts=dict(sorted(orbit_counts.items())))


def verify_laws():
    results = []
    shared_table = None
    for name, rows in TEMPLATES.items():
        support = edges(rows)
        if name == "B":
            weights = {(i, j): 2 if j == 1 else 3 for i, j in support}
        elif name == "A_shared":
            weights = {(i, j): 3 if (i, j) in ((0, 0), (3, 3)) else 2 for i, j in support}
        else:
            weights = {point: 1 for point in support}
        denominator = sum(weights.values())
        row_mass, col_mass = Counter(), Counter()
        for (i, j), weight in weights.items():
            row_mass[i] += weight
            col_mass[j] += weight
        best, witness, count = -1, None, 0
        table = [[0] * 7 for _ in range(5)]
        for a, b, u, v in product(range(5), range(7), range(5), range(7)):
            direct = sum(weight * (1 + (i == a) + (j == b) + ((i, j) == (u, v)))**2
                         for (i, j), weight in weights.items())
            expanded = (denominator + 3 * row_mass[a] + 3 * col_mass[b]
                        + 2 * weights.get((a, b), 0)
                        + (3 + 2 * (u == a) + 2 * (v == b)) * weights.get((u, v), 0))
            check(direct == expanded, "literal and expanded squared loads agree")
            table[a][b] = max(table[a][b], direct)
            count += 1
            if direct > best:
                best, witness = direct, (a, b, (u, v))
        check(count == 1225, "all independent choices including absent cells")
        value = Fraction(best, denominator)
        check(value == EXPECTED_MAXIMA[name] <= 4, "the specified law's exact full-layout maximum")
        if name == "A_shared":
            shared_table = [row[:4] for row in table[:4]]
            check(denominator == 18 and shared_table ==
                  [[69, 60, 54, 51], [60, 66, 60, 54],
                   [70, 72, 66, 60], [63, 70, 60, 69]],
                  "A_shared exact row/column table")
        results.append(dict(name=name, rows=list(rows), edges=len(support),
                            weights=[[i, j, weights[i, j]] for i, j in support],
                            denominator=denominator, exact_maximum=str(value),
                            independent_layouts=count, attaining_choice=witness))
    return results, shared_table


def verify():
    classification = verify_classification()
    laws, table = verify_laws()
    # The old triangle-plus-isolated-edge support ceases to be minimal
    # when total column count is no longer a protected condition.
    old_e, reduced_e = (3, 5, 6, 24), (3, 5, 6, 8)
    check(valid_four_rows(old_e) and valid_four_rows(reduced_e)
          and sum(map(int.bit_count, reduced_e)) < sum(map(int.bit_count, old_e)),
          "old E has a legal strict reduction")
    check(canonical_columns(column_types(reduced_e)) ==
          canonical_columns(column_types(TEMPLATES["singleton_triangle"])),
          "old E reduces to the singleton-triangle type")
    return dict(
        scope="Root functional only: every 3-by-5 rectangle blocker in a 5-by-7 carrier admits a common law with Gamma <= 4; no standalone projection hypothesis",
        classification=classification, laws=laws, A_shared_numerator_table=table,
        total_independent_layouts=sum(row["independent_layouts"] for row in laws),
        old_E_reduction=list(reduced_e),
    )


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2, sort_keys=True))
