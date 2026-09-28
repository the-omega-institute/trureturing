#!/usr/bin/env python3
"""Exact query certificates for the full public-singleton common laws.

The proof supplies fixed actual laws and their support exclusions.  This
program enumerates all query partitions or coarse root/column layouts under
those hypotheses; it does not enumerate sources or certify Lean statements.
"""
from fractions import Fraction as Q
from itertools import product
from math import lcm
from pathlib import Path
import argparse
import json


D = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
P75 = dict(zip(D, (75, 25, 45, 15, 15, 15, 9, 5, 3)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def two_components(private_count, weight, target):
    eta = {d: Q(1) if d in (1, 5, 7, 35) else Q(1, private_count)
           for d in D}
    values = []
    for bits in product((0, 1), repeat=8):
        first = (1,) + tuple(d for d, bit in zip(D[1:], bits) if bit)
        second = (1,) + tuple(d for d, bit in zip(D[1:], bits) if not bit)
        a = sum((Q(P75[lcm(u, v)], 75) for u in first for v in first), Q(0))
        b = sum((eta[lcm(u, v)] for u in second for v in second), Q(0))
        values.append((weight * a + (1 - weight) * b, bits, a, b))
    maximum = max(row[0] for row in values)
    require(maximum == target and maximum < 9, 'two-component target')
    active = [dict(psi_queries=[d for d, bit in zip(D[1:], bits) if bit],
                   component_envelopes=[str(a), str(b)])
              for value, bits, a, b in values if value == maximum]
    require(len(active) == 2, 'exactly the two endpoint partitions maximize')
    require({tuple(row['psi_queries']) for row in active} == {(), D[1:]},
            'endpoint identities')
    return dict(private_J_labels=private_count, psi_weight=str(weight),
                eta_weight=str(1 - weight), partitions=len(values),
                maximum=str(maximum), active=active)


def three_components():
    root_indices = [i for i, d in enumerate(D) if d % 5 == 0]
    column_indices = [i for i, d in enumerate(D) if d % 7 == 0]
    require(len(root_indices) == len(column_indices) == 6, 'query coordinates')
    weights = (104, 50, 63)
    rows = set()
    maximum = -1
    active = []
    count = 0
    # Root 0 is R, root 1 merges all other original roots. Columns 0,1,2
    # are H,J,other. None is a wildcard for a missing prime coordinate.
    for roots in product(range(2), repeat=6):
        r = [None] * len(D)
        for i, value in zip(root_indices, roots):
            r[i] = value
        for columns in product(range(3), repeat=6):
            g = [None] * len(D)
            for i, value in zip(column_indices, columns):
                g[i] = value
            total = [0, 0, 0]
            for i, a in enumerate(D):
                for j, b in enumerate(D):
                    if r[i] is not None and r[j] is not None and r[i] != r[j]:
                        continue
                    if g[i] is not None and g[j] is not None and g[i] != g[j]:
                        continue
                    rr = r[i] if r[i] is not None else r[j]
                    gg = g[i] if g[i] is not None else g[j]
                    d = lcm(a, b)
                    if rr != 0:
                        if gg != 1:
                            total[0] += P75[d]
                        if gg != 0:
                            total[1] += P75[d]
                    if rr != 1 and gg != 2:
                        if d in (1, 5):
                            cap = 75
                        elif d in (7, 35):
                            require(gg in (0, 1), 'eta column is specified')
                            cap = 30 if gg == 0 else 45
                        else:
                            cap = 15
                        total[2] += cap
            row = tuple(total)
            rows.add(row)
            score = sum(x * w for x, w in zip(row, weights))
            require(score <= 136395, 'every original coarse layout obeys bound')
            if score > maximum:
                maximum = score
                active = []
            if score == maximum:
                active.append(dict(vector_over75=list(row),
                                   root_layout=list(roots), column_layout=list(columns)))
            count += 1
    require(count == 46656 and len(rows) == 31410, 'complete layout counts')
    require(maximum == 136395, 'attained upper-vector bound')
    expected = {(285, 75, 1635), (75, 285, 1815), (855, 855, 75)}
    require(len(active) == 3 and {tuple(x['vector_over75']) for x in active} == expected,
            'three exact active vectors')
    bound = Q(maximum, 75 * sum(weights))
    require(bound == Q(1299, 155) and bound < 9, 'three-component strict bound')
    return dict(weights=list(weights), weight_denominator=sum(weights),
                layouts=count, distinct_vectors=len(rows), maximum_numerator=maximum,
                cap_denominator=75, maximum=str(bound), active=active)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = dict(result='PASS', divisor_order=list(D),
                  two_components=[two_components(5, Q(35, 48), Q(103, 12)),
                                  two_components(4, Q(625, 833), Q(7333, 833))],
                  three_components=three_components(),
                  scope='Exact query upper certificates at fixed common-law weights; '
                        'actual support and cap premises are supplied by the proof. '
                        'Not source enumeration, minimum-cut certification or Lean verification.')
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(result='PASS', partitions=512, coarse_layouts=46656,
                          bounds=['103/12', '7333/833', '1299/155'])))


if __name__ == '__main__':
    main()
