#!/usr/bin/env python3
"""Exact root-sensitive query upper bounds for the normalized 11222 puncture.

The input cap tables are proved in the companion mathematical note.  This
enumerates all 64 coarse root layouts, not sources and not actual phases.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import lcm

D = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
POSITIVE_FIVE = tuple(d for d in D if d % 5 == 0)
OTHER = {5: Q(1, 4), 25: Q(3, 20), 35: Q(3, 20),
         175: Q(9, 100), 245: Q(1, 20), 1225: Q(3, 100)}
PURE = {1: Q(1), 7: Q(9, 20), 49: Q(3, 20)}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def evaluate(n, m):
    distinguished = {5: Q(1, 4), 25: Q(1, 2*n), 35: Q(m, 4*n),
                     175: Q(1, 2*n), 245: Q(1, 4*n), 1225: Q(1, 4*n)}
    rows = []
    for layout in product((0, 1), repeat=len(POSITIVE_FIVE)):
        bits = dict(zip(POSITIVE_FIVE, layout))
        total = Q(0)
        for d in D:
            for e in D:
                roots = {bits[v] for v in (d, e) if v in bits}
                modulus = lcm(d, e)
                if len(roots) == 2:
                    continue
                if not roots:
                    total += PURE[modulus]
                elif next(iter(roots)) == 1:
                    total += distinguished[modulus]
                else:
                    total += OTHER[modulus]
        rows.append((layout, total))
    maximum = max(value for _, value in rows)
    return {
        'distinct_labels': n, 'maximum_distinct_column': m,
        'maximum': str(maximum),
        'maximizers': [list(layout) for layout, value in rows if value == maximum],
        'layout_count': len(rows),
        'all_bounds': [{'root_bits': list(layout), 'bound': str(value)}
                       for layout, value in rows],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    supplied = [evaluate(n, m) for n, m in ((8, 5), (7, 5), (6, 4))]
    for case in supplied:
        require(case['maximum'] == '44/5', 'unexpected exact maximum')
        require(case['maximizers'] == [[0]*6], 'unexpected maximizing root layout')
    boundaries = [evaluate(n, m) for n, m in ((6, 5), (5, 4), (5, 3))]
    require([case['maximum'] for case in boundaries] ==
            ['1087/120', '193/20', '46/5'], 'boundary check changed')
    result = {
        'status': 'PASS', 'divisor_order': list(D),
        'positive_five_order': list(POSITIVE_FIVE),
        'other_root_caps': {str(k): str(v) for k, v in OTHER.items()},
        'whole_law_pure_caps': {str(k): str(v) for k, v in PURE.items()},
        'supplied_cases': supplied, 'interface_boundaries': boundaries,
        'scope': 'Finite exact root-layout upper certificate; no source enumeration or Lean claim.',
    }
    with open(args.output, 'w', encoding='utf-8') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({'status': 'PASS', 'layouts_checked': sum(c['layout_count'] for c in supplied+boundaries),
                      'supplied_maxima': [c['maximum'] for c in supplied]}))


if __name__ == '__main__':
    main()
