#!/usr/bin/env python3
"""Exact premises for positive outer-seven compatibility gaps at theta404.

The ordinary argument in profile60 uses unit-event stability and shallow
root separation. Finite branch arithmetic is not an enumeration of the
arbitrary original residue families covered by that argument.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'frontier/allocated_seven_thresholds.py': 'b467824a30899cd14ab35ab4a1383c4a3848e5c9dcbdaebd6f4074e9a1d8e78d',
    'frontier/positive_seven_source_extrema.py': '5b1c932ea1017d9ad98c6d3391edf7c0aea37faea4462fd8e9fd33c04f11fd6e',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def calculate(base):
    for name, pin in PINS.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Pinned input '+name)
    s = load('outer_source', base/'verify_joint_frontier.py')
    a = load('outer_allocated', base/'frontier/allocated_seven_thresholds.py')
    p = load('outer_positive', base/'frontier/positive_seven_source_extrema.py')
    dat = s.data(list(s.vertices())[404])
    d, masses, eta, total, minimum = dat
    require((total, minimum) == (F(1, 4), F(3, 20)), 'Same off-diagonal endpoint')
    rows, positive = [], {}
    for t in (4, 5):
        op = a.AllocatedCost(s, t, tuple(F(t, j) for j in range(2, t)),
                             0, (1, 2, 0, 0, 0))
        values = [sum(masses[l]*op.gs[l, b[l]]+eta[l]*op.bs[l, b[l]] for l in range(5))
                  +max(d[l]*op.dg[l, b[l]]+op.db[l, b[l]] for l in range(5))
                  +op.positive(eta) for b in s.BASES]
        gaps = [max(values)-v for v in values]
        require(gaps[9] == 0 and min(gaps[:9]) == (F(1, 420) if t == 4 else F(1, 735)),
                'Unique sharp absorbed zero baseline and its exact alternative gap')
        rows.append({'threshold': t, 'block': 0, 'sharp_value': max(values), 'baseline_gaps': gaps})
        for e in range(1, t-1):
            cost = p.ScalarCost(s, ('seven_block', (('h', F(t)), e)))
            old, sharp, pairs = cost.envelopes(dat)
            upper = [max(row['value'] for row in pairs if row['zero'] == j) for j in range(10)]
            gaps = [sharp-v for v in upper]
            gamma = cost.slope-cost.f(2)
            if (t, e) != (5, 1):
                require(all(cost.f(v) == cost.slope*(v-1)-gamma for v in range(2, cost.cut+2)),
                        'Exact affine-away-from-one cost identity including its affine tail')
                require((sharp-cost.slope/2+gamma/4)/gamma == F(7, 120),
                        'Sharp scalar norm forces unit-event mass')
            positive[t, e] = {'sharp_value': sharp, 'baseline_gaps': gaps, 'gamma': gamma,
                              'tensor_minus_value': cost.actual_integral(dat, 'minus')}
            rows.append({'threshold': t, 'block': e, 'old_value': old,
                         **positive[t, e]})
    lower4, lower5 = F(7, 8575), F(31, 72030)
    p3, p4 = F(36, 5*7**3), F(36, 5*7**4)
    require(min(positive[4, 1]['baseline_gaps'][5:]) == F(69, 34300) > lower4,
            'Threshold4 first positive block cannot move units to root0 cheaply')
    require(p3/3 <= min(positive[4, e]['gamma'] for e in (1, 2))
            and 2*(p3/3)*F(7, 120) == lower4, 'Both threshold4 positive blocks pay unit mass')
    require(min(positive[5, 1]['baseline_gaps'][:9]) == F(1, 735) > lower5,
            'Sharp threshold5 first positive block stays on minus baseline')
    second = positive[5, 2]['baseline_gaps']
    require(second[6] == F(59, 144060)
            and min(second[j] for j in (5, 7, 8, 9)) == F(151, 308700) > lower5,
            'Only one cheap root0 baseline for threshold5 second positive block')
    require(2*p3/3 <= positive[5, 2]['gamma']
            and (2*p3/3)*F(7, 120) == F(1, 1225) > lower5,
            'Opposite-root units pay the threshold5 three-block defect')
    require(p4/4 == positive[5, 3]['gamma']
            and second[6]+p4*F(7, 480) > lower5,
            'Fourth block cannot leave its units in the opposite root cheaply')
    require(min(positive[5, 3]['baseline_gaps'][5:]) == F(1, 48020)
            and second[6]+F(1, 48020) == lower5,
            'Both root0 source penalties sum to the threshold5 lower bound')
    upper = {t: sum(positive[t, e]['sharp_value']-positive[t, e]['tensor_minus_value']
                    for e in range(1, t-1)) for t in (4, 5)}
    require(upper == {4: F(24, 8575), 5: F(39, 60025)},
            'Actual equal-block tensor constructions give the stated upper brackets')
    return {'schema': 'erdos7-finite-outer-jensen-compatibility-v1', 'source_vertex': 404,
            'carrier': (0, 1), 'rows': rows, 'gap_lower': {4: lower4, 5: lower5},
            'gap_upper': upper, 'old_positive5_correction': F(831, 1200500),
            'old_threshold5_total_gap': F(831, 1200500)+lower5,
            'source_sha256': PINS, 'scope': 'Positive gaps for the fixed absorbed carrier source '
            'comparison. Exact optima and global K improvement are not claimed.'}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(Path(__file__).resolve().parents[1])
    if args.output is not None:
        args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print('PASS: all baseline alternatives, exact unit-mass stability constants and actual upper witnesses.')
    print('Outer gap lower bounds: 7/8575 and31/72030; fixed absorbed carrier only.')


if __name__ == '__main__':
    main()
