#!/usr/bin/env python3
"""Bounded exact query checks for two actual-source cap interfaces.

Reads no input files and writes only the explicit --output file.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import lcm

D = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
ROOT_D = tuple(d for d in D if d % 5 == 0)
COL_D = tuple(d for d in D if d % 7 == 0)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def balanced_five():
    pure = {1: Q(1), 7: Q(137,319), 49: Q(61,319)}
    outside = dict(zip(ROOT_D, (Q(244,957), Q(244,1595), Q(122,957),
                               Q(122,1595), Q(61,957), Q(61,1595))))
    inside = dict(zip(ROOT_D, (Q(75,319), Q(30,319), Q(45,319),
                              Q(30,319), Q(15,319), Q(15,319))))
    rows = []
    for layout in product((0,1), repeat=6):
        bits = dict(zip(ROOT_D, layout))
        total = Q(0)
        for d in D:
            for e in D:
                roots = {bits[v] for v in (d,e) if v in bits}
                m = lcm(d,e)
                if len(roots) == 2:
                    continue
                total += pure[m] if not roots else (inside if next(iter(roots)) else outside)[m]
        rows.append((layout,total))
    maximum = max(value for _,value in rows)
    return {'layouts': len(rows), 'maximum': str(maximum),
            'maximizers': [list(layout) for layout,value in rows if value == maximum],
            'all_bounds': [{'root_bits': list(layout), 'bound': str(value)} for layout,value in rows]}


def cross_matching():
    # Each cap is in units 1/400. H=0, J=1, outside=2; root R=1.
    pure = {7: (100,120,180), 49: (20,75,60)}
    root_only = {5: (80,160), 25: (48,35)}
    combined = {
        35: ((0,20,60),(100,60,0)),
        175: ((0,12,36),(20,15,0)),
        245: ((0,20,20),(20,15,0)),
        1225: ((0,12,12),(20,15,0)),
    }
    root_index = {d:i for i,d in enumerate(ROOT_D)}
    col_index = {d:i for i,d in enumerate(COL_D)}
    pairs = [(lcm(d,e), root_index.get(d,-1), root_index.get(e,-1),
              col_index.get(d,-1), col_index.get(e,-1)) for d in D for e in D]
    maximum = -1
    maximizers = []
    values = set()
    count = 0
    for roots in product((0,1), repeat=6):
        root_pairs = []
        for m,rd,re,cd,ce in pairs:
            if rd >= 0 and re >= 0 and roots[rd] != roots[re]:
                continue
            root = roots[rd] if rd >= 0 else roots[re] if re >= 0 else -1
            root_pairs.append((m,root,cd,ce))
        for columns in product(range(3), repeat=6):
            total = 0
            for m,root,cd,ce in root_pairs:
                if cd >= 0 and ce >= 0 and columns[cd] != columns[ce]:
                    continue
                col = columns[cd] if cd >= 0 else columns[ce] if ce >= 0 else -1
                if m == 1:
                    total += 400
                elif root == -1:
                    total += pure[m][col]
                elif col == -1:
                    total += root_only[m][root]
                else:
                    total += combined[m][root][col]
            count += 1
            values.add(total)
            if total > maximum:
                maximum = total
                maximizers = []
            if total == maximum:
                maximizers.append({'roots': list(roots), 'columns': list(columns)})
    return {'layouts': count, 'maximum_numerator': maximum, 'denominator': 400,
            'maximum': str(Q(maximum,400)), 'maximizers': maximizers,
            'distinct_bounds': len(values), 'next_distinct': str(Q(sorted(values)[-2],400))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    balanced = balanced_five()
    cross = cross_matching()
    require(balanced['layouts'] == 64 and cross['layouts'] == 46656, 'incomplete layout enumeration')
    require(balanced['maximum'] == '2865/319', 'balanced-five maximum changed')
    require(cross['maximum'] == '691/80', 'cross-matching maximum changed')
    result = {'status': 'PASS', 'divisors': D, 'root_divisors': ROOT_D,
              'column_divisors': COL_D, 'balanced_five': balanced, 'cross_matching': cross,
              'scope': 'Exact cap-interface maxima. Complete-source hypotheses require the accompanying mathematical proof.'}
    with open(args.output, 'w', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({'status': 'PASS', 'balanced_five': balanced['maximum'],
                      'cross_matching': cross['maximum'], 'layouts': 46720,
                      'cross_maximizers': cross['maximizers']}))


if __name__ == '__main__':
    main()
