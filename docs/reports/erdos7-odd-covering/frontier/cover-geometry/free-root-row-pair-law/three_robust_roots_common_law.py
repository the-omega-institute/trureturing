#!/usr/bin/env python3
"""Exact local laws for the three-robust-root height-two construction.

Reuses the ten support types of report 395. Four cap families cover its
nonexceptional constructions. The explicit laws and their admissible
transposes are checked against all independent original local phases.
One changed law is needed for the transpose of type A. All 81 allocations
of the four positive-five labels satisfy the common 46/3 mask budget.

This is a standard-library arithmetic check, not Lean certification or an
arbitrary-source theorem. All checks remain active under -O.
"""

from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import importlib.util
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


SPEC = importlib.util.spec_from_file_location(
    'root_rectangle_second_moment',
    Path(__file__).with_name('root_rectangle_second_moment.py'))
ROOT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ROOT)

# Bits name the original labels 5,35,25,175, respectively.
ENVELOPE = tuple(map(F, (
    '2', '17/3', '11/3', '8', '29/9', '68/9', '46/9', '91/9',
    '17/6', '41/6', '29/6', '19/2', '4', '77/9', '19/3', '34/3')))
CAP_FAMILIES = ((9, 3, 3), (8, 3, 2), (7, 2, 2), (5, 1, 1))


def parameters(mask):
    return 1 + bool(mask & 1), 1 + bool(mask & 2), bool(mask & 4), bool(mask & 8)


def cap_bound(mask, denominator, row_cap, column_cap):
    c, t, e, f = parameters(mask)
    return (F(c*c) + F(t*(2*c+t)*column_cap, denominator)
            + F(e*(2*c+1)*row_cap, denominator)
            + F(2*t*e + f*(2*c+1+2*t+2*e), denominator))


def explicit_laws():
    laws = {}
    for name, rows in ROOT.TEMPLATES.items():
        support = ROOT.edges(rows)
        if name == 'B':
            weights = {(a, b): 2 if b == 1 else 3 for a, b in support}
        elif name == 'A_shared':
            weights = {p: 3 if p in ((0, 0), (3, 3)) else 2 for p in support}
        else:
            weights = {p: 1 for p in support}
        laws[name] = weights
        # The transposed support must fit in the five actual child rows.
        if max(b for a, b in support) < 5:
            transposed = {(b, a): weight for (a, b), weight in weights.items()}
            if name == 'A':
                transposed = {
                    (0, 0): 6, (1, 1): 3, (2, 1): 3, (0, 2): 4,
                    (1, 2): 4, (2, 2): 4, (3, 3): 6, (4, 3): 6,
                }
                require(set(transposed) == {(b, a) for a, b in support},
                        'adjusted transpose-A law has the actual support')
            laws[name + '_transpose'] = transposed
    require(len(laws) == 18, 'ten original types and eight admissible transposes')
    return laws


def local_prices(weights):
    denominator = sum(weights.values())
    require(denominator > 0 and all(type(w) is int and w > 0 for w in weights.values()),
            'positive integer mass numerators')
    row_mass = [sum(w for (a, b), w in weights.items() if a == row) for row in range(5)]
    col_mass = [sum(w for (a, b), w in weights.items() if b == col) for col in range(7)]
    prices, witnesses, original_count, merged_count = [], [], 0, 0
    for mask in range(16):
        c, t, e, f = parameters(mask)
        best, witness = -1, None
        for col, row, point_row, point_col in product(
                range(7), range(5) if e else range(1),
                range(5) if f else range(1), range(7) if f else range(1)):
            direct = sum(w*(c+t*(b == col)+e*(a == row)
                            + f*((a, b) == (point_row, point_col)))**2
                         for (a, b), w in weights.items())
            expanded = (c*c*denominator + t*(2*c+t)*col_mass[col]
                        + e*(2*c+1)*row_mass[row]
                        + 2*t*e*weights.get((row, col), 0)
                        + f*(2*c+1+2*t*(point_col == col)+2*e*(point_row == row))
                        * weights.get((point_row, point_col), 0))
            require(direct == expanded, 'literal square and mass expansion')
            if direct > best:
                best, witness = direct, (col, row, point_row, point_col)
            merged_count += 1
        # The original label-7 and label-35 columns remain independent.
        # Exhaustion independently checks the column-merging argument.
        original_best = -1
        for col0, col1, row, point_row, point_col in product(
                range(7), range(7) if mask & 2 else range(1),
                range(5) if e else range(1), range(5) if f else range(1),
                range(7) if f else range(1)):
            direct = sum(w*(c+(b == col0)+bool(mask & 2)*(b == col1)
                            + e*(a == row)+f*((a, b) == (point_row, point_col)))**2
                         for (a, b), w in weights.items())
            original_best = max(original_best, direct)
            original_count += 1
        require(best == original_best, 'merging preserves the full independent-phase maximum')
        price = F(best, denominator)
        require(price <= ENVELOPE[mask], 'explicit local law obeys the common mask envelope')
        prices.append(price)
        witnesses.append(witness)
    require(original_count == 24192 and merged_count == 6048, 'complete local phase counts')
    return prices, witnesses, original_count, merged_count


def source_examples():
    def crt(point):
        r, a, y = point
        x = r+5*a
        residue = x+25*((y-x)*2 % 7)
        require(0 <= residue < 175 and residue % 25 == x and residue % 7 == y,
                'literal CRT source encoding')
        return residue

    labels = (1, 5, 25, 7, 35, 175)
    # A source satisfying the original product-tree and standalone tests,
    # but with no robust allowed root. This is a scope witness only.
    boundary = {(r, a, y) for r in range(1, 5) for a in range(3)
                for y in ((0, r) if a == 0 else (0, 1, 2))}
    bad = {r: [] for r in range(1, 5)}
    for pair in combinations(range(7), 2):
        good_roots = 0
        for r in range(1, 5):
            active = sum(any((r, a, y) in boundary for y in range(7) if y not in pair)
                         for a in range(5))
            if active >= 3:
                good_roots += 1
            else:
                bad[r].append(pair)
        require(good_roots >= 3, 'boundary source meets the product-tree condition')
    require(len(boundary) == 32 and len({y for r, a, y in boundary}) == 5,
            'boundary support size and standalone seven condition')
    require(all(bad[r] == [(0, r)] for r in range(1, 5)),
            'four disjoint singleton bad sets and no robust root')
    require(len({crt(point) for point in boundary}) == 32,
            'distinct actual CRT residues for the boundary source')

    old_fibre = tuple((b, a) for a, b in ROOT.edges(ROOT.TEMPLATES['A']))
    old_source = tuple((r, a, y) for r in range(1, 4) for a, y in old_fibre)
    center = crt((1, 0, 2))
    old_price = F(sum(sum(crt(point) % d == center % d for d in labels)**2
                      for point in old_source), len(old_source))
    require(old_price == F(127, 24) and old_price-F(46, 9) == F(13, 72),
            'the old uniform transpose-A law fails the height-two target')

    sharp = tuple(product(range(1, 4), range(3), range(3)))
    prices = []
    for r, a, y in sharp:
        total = sum(((1+(r == u)+((r, a) == (u, v)))*(1+(y == z)))**2
                    for u, v, z in sharp)
        literal = sum(sum(crt((r, a, y)) % d == crt(center) % d for d in labels)**2
                      for center in sharp)
        require(total == literal, 'centered factorization agrees with all six literal CRT labels')
        prices.append(F(total, len(sharp)))
    require(len(sharp) == 27 and all(price == F(46, 9) for price in prices),
            'uniform centered-layout certificate for the sharpness source')
    return dict(boundary_points=len(boundary), boundary_bad_pairs=bad,
                boundary_seven_columns=5, sharpness_points=len(sharp),
                sharpness_centered_layout_point_checks=len(sharp)**2,
                sharpness_constant_price='46/9',
                old_uniform_transpose_A_layout_price=str(old_price),
                old_uniform_transpose_A_excess='13/72')


def verify():
    cap_tables = {}
    for denominator, row_cap, column_cap in CAP_FAMILIES:
        table = [cap_bound(mask, denominator, row_cap, column_cap) for mask in range(16)]
        require(all(value <= ENVELOPE[mask] for mask, value in enumerate(table)),
                'generic cap family obeys the common mask envelope')
        cap_tables[f'{denominator}:{row_cap}:{column_cap}'] = list(map(str, table))

    law_tables = {}
    original_count = merged_count = 0
    for name, weights in explicit_laws().items():
        prices, witnesses, original, merged = local_prices(weights)
        original_count += original
        merged_count += merged
        law_tables[name] = dict(
            denominator=sum(weights.values()),
            weights=[[a, b, w] for (a, b), w in weights.items()],
            exact_prices=list(map(str, prices)), attaining_merged_phases=witnesses)

    allocations = []
    for assignment in product(range(3), repeat=4):
        masks = tuple(sum(1 << label for label in range(4) if assignment[label] == root)
                      for root in range(3))
        require(sum(masks) == 15 and all(masks[i] & masks[j] == 0
                                      for i in range(3) for j in range(i)),
                'each positive-five label enters exactly one selected root')
        value = sum(ENVELOPE[mask] for mask in masks)
        require(value <= F(46, 3), 'three-root allocation budget')
        allocations.append((value, masks))
    maximum = max(value for value, masks in allocations)
    require(len(allocations) == 81 and maximum == F(46, 3), 'complete and sharp envelope budget')
    return dict(
        scope='H5=2,K7=1; actual source with three root fibres meeting every 3-by-5 rectangle',
        labels=[1, 5, 25, 7, 35, 175], common_law_upper='46/9',
        cap_families=cap_tables, local_laws=law_tables,
        common_mask_envelope=list(map(str, ENVELOPE)),
        original_independent_local_phases=original_count, merged_local_phases=merged_count,
        allocations=len(allocations), largest_allocation_sum=str(maximum),
        attaining_allocations=[masks for value, masks in allocations if value == maximum],
        source_examples=source_examples(),
    )


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2, sort_keys=True))
