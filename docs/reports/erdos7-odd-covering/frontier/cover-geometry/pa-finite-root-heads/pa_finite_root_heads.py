#!/usr/bin/env python3
"""Exact finite-head consumers for Report568's actual first13 union bound.

Arbitrary finite two-copy originals on Q={5,7,11,13,17,19}, fixed phases,
unchanged PA caps, arbitrary old source and all original/query heights.
The proofs of the cap and geometric tail bounds are in Report568.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json


checks = {}


def check(name, condition):
    if name in checks or not condition:
        raise ValueError(name)
    checks[name] = True


def coordinate(p, mass, cap):
    # Full mass and first moment; only products strictly below four are stored.
    return mass, mass + cap / (p - 1), {
        1: mass - cap / p,
        2: cap * F(p - 1, p ** 2),
        3: cap * F(p - 1, p ** 3),
    }


def tensor(left, right):
    low = defaultdict(F)
    for i, a in left[2].items():
        for j, b in right[2].items():
            if i * j < 4:
                low[i * j] += a * b
    return left[0] * right[0], left[1] * right[1], low


def hinge(law, threshold):
    return law[1] - threshold * law[0] + sum(
        ((threshold - n) * mass for n, mass in law[2].items()
         if n < threshold), F())


def complete_hinges(x, y):
    law = tensor(coordinate(5, x, F(1)), coordinate(7, y, F(1)))
    result = {}
    for p, threshold, cap in ((11, 2, F(5, 3)), (13, 2, F(3, 2)),
                              (17, 4, F(2)), (19, 4, F(9, 5))):
        result[p] = hinge(law, threshold)
        law = tensor(law, coordinate(p, F(1), cap))
    return result, hinge(law, 3)


def label(exponents):
    return prod(p ** e for p, e in zip((5, 7, 11, 13), exponents))


def label_charge(exponents, x, y):
    a, b, c, d = exponents
    return 3 * (x if a == 0 else F(1, 5 ** a)) * (
        y if b == 0 else F(1, 7 ** b)) * (
        F(1) if c == 0 else F(5, 3 * 11 ** c)) / 13 ** d


def full_charge(x, y):
    return F(1, 4) * (x + F(1, 4)) * (y + F(1, 6)) * F(7, 6)


def box_head(max5):
    return tuple(product(range(max5 + 1), range(3), range(3), (1, 2)))


TARGET = F(257, 51)
ANCHOR = (F(1, 2), F(2, 3))
CORNERS = tuple(product((F(1, 2), F(1)), (F(2, 3), F(1))))


def evaluate(head, x, y):
    hs, phi = complete_hinges(x, y)
    prefix = x * y - F(1, 12) - hs[11] / 3
    tail = full_charge(x, y) - sum((label_charge(e, x, y) for e in head), F())
    mass = F(21, 26) * prefix - tail - hs[17] / 4 - hs[19] / 5
    margin = mass - phi / (TARGET - 2)
    return dict(x=x, y=y, hinges=hs, Phi=phi, A11=prefix, Theta=tail,
                M=mass, D=margin, eta=F(26, 3) * margin,
                query_bound=2 + phi / mass if mass > 0 else None)


def consumer(name, head):
    rows = [evaluate(head, x, y) for x, y in CORNERS]
    d00, d01, d10, d11 = (row['D'] for row in rows)
    coefficients = [d00, 2 * (d10 - d00), 3 * (d01 - d00),
                    6 * (d11 - d10 - d01 + d00)]
    check(name + '_labels_unique', len(set(map(label, head))) == len(head))
    for i, coefficient in enumerate(coefficients):
        check(name + '_positive_deficit_coefficient_' + str(i), coefficient > 0)
    for i, row in enumerate(rows):
        check(name + '_positive_mass_' + str(i), row['M'] > 0)
        check(name + '_positive_tail_' + str(i), row['Theta'] > 0)
        check(name + '_corner_query_bound_' + str(i),
              row['query_bound'] <= rows[0]['query_bound'] < TARGET)
        check(name + '_F11_formula_' + str(i),
              row['hinges'][11] == row['x'] / 42 + row['y'] / 20 + F(59, 840))
    maxima = [max(e[i] for e in head) for i in range(4)]
    return dict(name=name, label_count=len(head), labels=list(map(label, head)),
                exponents=head, old_cell_count=prod(p ** e for p, e in
                    zip((5, 7, 11), maxima[:3])),
                corners=rows, deficit_coefficients=coefficients,
                uniform_query_bound=rows[0]['query_bound'],
                uniform_query_bound_decimal=float(rows[0]['query_bound']),
                uniform_D=rows[0]['D'], uniform_eta=rows[0]['eta'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()

    for r in range(14):
        value = min(F(1), F(3, 2) * (1 - F(r, 13)))
        expansion = F(21, 26) - F(3, 26) * max(r - 6, 0) + F(1, 26) * min(5, 3 * max(6 - r, 0))
        check('root_mass_identity_' + str(r), value == expansion)

    # Each coordinate charge decreases with a positive exponent; the zeroth
    # charge also exceeds the first. An outside label is therefore bounded
    # by one of the four first-outside axial labels, not an uncomputed tail.
    candidates = tuple(product(range(4), range(4), range(3), range(1, 4)))
    ranked = sorted(candidates, key=lambda e: (-label_charge(e, *ANCHOR), label(e)))
    head26 = tuple(ranked[:26])
    cutoff = label_charge(head26[-1], *ANCHOR)
    outside_axes = ((4, 0, 0, 1), (0, 4, 0, 1), (0, 0, 3, 1), (0, 0, 0, 4))
    for i, exponent in enumerate(outside_axes):
        check('outside_axis_below_26th_' + str(i), label_charge(exponent, *ANCHOR) < cutoff)
    check('strict_26th_cutoff', label_charge(ranked[26], *ANCHOR) < cutoff)
    top25 = evaluate(ranked[:25], *ANCHOR)
    check('best_25_fails_anchor_mass_certificate', top25['D'] < 0)
    check('top_26_passes_anchor_mass_certificate', evaluate(head26, *ANCHOR)['D'] > 0)

    heads = [('W26', head26), ('W54', box_head(2)), ('W72', box_head(3))]
    results = [consumer(name, head) for name, head in heads]
    for max5 in (2, 3):
        for i, (x, y) in enumerate(CORNERS):
            finite5 = x + sum((F(1, 5 ** a) for a in range(1, max5 + 1)), F())
            formula = F(1, 4) * ((x + F(1, 4)) * (y + F(1, 6)) * F(7, 6)
                        - finite5 * (y + F(8, 49)) * F(141, 121) * F(168, 169))
            check(f'box_tail_formula_{max5}_{i}',
                  evaluate(box_head(max5), x, y)['Theta'] == formula)
    check('54_anchor_margin', results[1]['uniform_D'] == F(182314388214850909, 1650097635185615616000))
    check('72_anchor_margin', results[2]['uniform_D'] == F(3355083383746643293, 1650097635185615616000))
    check('26_anchor_tail', results[0]['corners'][0]['Theta'] == F(9534947837, 2188370184000))
    check('72_query_below_five', results[2]['uniform_query_bound'] < 5)

    result = dict(consumers=results, cardinality_comparison=dict(
        scope='Minimum head cardinality for this fixed six-root lower-mass certificate using the complete scalar cap tail and no H11 or below-six-root credit. Not minimum DP memory or minimum for other bounds.',
        finite_rank_box_size=len(candidates), first_outside_axes=outside_axes,
        first_outside_axis_charges=[label_charge(e, *ANCHOR) for e in outside_axes],
        cutoff26=cutoff, best25=top25), checks=checks, check_count=len(checks),
        scope='Conditional finite-head consumers of Report568, arbitrary actual source, all heights and phases outside each head. No unrestricted covering conclusion, no Lean verification.')
    args.output.write_text(json.dumps(result, default=lambda x: str(x) if isinstance(x, F) else x,
                                     indent=2) + '\n', encoding='utf-8')
    for row in results:
        print(row['name'], 'labels', row['label_count'], 'old_cells', row['old_cell_count'],
              'R', row['uniform_query_bound'], row['uniform_query_bound_decimal'],
              'D', row['uniform_D'], 'eta', row['uniform_eta'])
    print('checks', len(checks))


if __name__ == '__main__':
    main()
