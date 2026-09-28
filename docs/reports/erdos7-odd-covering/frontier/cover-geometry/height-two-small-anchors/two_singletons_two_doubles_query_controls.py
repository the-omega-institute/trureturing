#!/usr/bin/env python3
"""Exact finite query certificates for monochromatic anchors and full1122*.

All caps are premises of the mathematical proof, not inferred from source
enumeration.  Checks remain active with Python -O.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import lcm

D = (1, 5, 7, 25, 35, 49, 175, 245, 1225)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def partitions(puncture, eta, weight):
    rows = []
    for bits in product((0, 1), repeat=8):
        left = [1] + [d for d, bit in zip(D[1:], bits) if bit]
        right = [1] + [d for d, bit in zip(D[1:], bits) if not bit]
        p = sum((puncture[lcm(d, e)] for d in left for e in left), Q(0))
        q = sum((eta[lcm(d, e)] for d in right for e in right), Q(0))
        rows.append((bits, weight*p + (1-weight)*q))
    return rows


def roots(n, m, weight):
    positive = tuple(d for d in D if d % 5 == 0)
    other = {5: weight/3, 25: weight/5, 35: weight/5,
             175: 3*weight/25, 245: weight/15, 1225: weight/25}
    at_r = {5: 1-weight, 25: 2*(1-weight)/n, 35: m*(1-weight)/n,
            175: 2*(1-weight)/n, 245: (1-weight)/n, 1225: (1-weight)/n}
    pure = {1: Q(1), 7: 3*weight/5, 49: weight/5}
    rows = []
    for layout in product((0, 1), repeat=6):
        bits = dict(zip(positive, layout))
        bound = Q(0)
        for d in D:
            for e in D:
                labels = {bits[v] for v in (d, e) if v in bits}
                modulus = lcm(d, e)
                if len(labels) == 2:
                    continue
                if not labels:
                    bound += pure[modulus]
                elif next(iter(labels)):
                    bound += at_r[modulus]
                else:
                    bound += other[modulus]
        rows.append((layout, bound))
    return rows


def summarize(name, rows, expected):
    maximum = max(value for _, value in rows)
    require(maximum == expected, name + ': unexpected exact maximum')
    return {'name': name, 'count': len(rows), 'maximum': str(maximum),
            'maximizers': [list(layout) for layout, value in rows if value == maximum],
            'all_bounds': [{'layout': list(layout), 'bound': str(value)}
                           for layout, value in rows]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    ia3 = dict(zip(D, (Q(1), Q(1,3), Q(1,2), Q(1,5), Q(1,6),
                      Q(1,6), Q(1,10), Q(1,18), Q(1,30))))
    np2 = dict(zip(D, (Q(1), Q(1,3), Q(3,5), Q(1,5), Q(1,5),
                      Q(1,5), Q(3,25), Q(1,15), Q(1,25))))
    eta2 = {d: Q(1) if d in (1,5,7,35) else Q(1,2) for d in D}
    eta4 = {d: Q(1) if d in (1,5,7,35) else Q(1,4) for d in D}
    cases = [
        summarize('monochromatic_anchor_two_points',
                  partitions(ia3, eta2, Q(95,113)), Q(968,113)),
        summarize('two_doubles_five_labels_three_per_column',
                  roots(5, 3, Q(61,80)), Q(893,100)),
        summarize('two_doubles_six_labels_four_per_column',
                  roots(6, 4, Q(3,4)), Q(44,5)),
        summarize('cross_star_four_points_in_one_column',
                  partitions(np2, eta4, Q(625,833)), Q(7333,833)),
    ]
    for case in cases:
        require(Q(case['maximum']) <= Q(893,100), 'overall envelope exceeded')
    result = {'status': 'PASS', 'divisor_order': list(D),
              'cases': cases, 'layouts_checked': sum(c['count'] for c in cases),
              'scope': 'Finite exact common-query cap certificate, not actual-source enumeration or Lean.'}
    with open(args.output, 'w', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({'status': 'PASS', 'layouts_checked': result['layouts_checked'],
                      'maxima': [c['maximum'] for c in cases]}))


if __name__ == '__main__':
    main()
