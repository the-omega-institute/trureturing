"""Exact240-query pair/third-moment repair of the774 actual dictionary.

All coefficients and caps are recomputed by standard-library arithmetic.
The240 count describes this static sufficient-cost interface, not a DP
state count or closure under arbitrary future fixed-phase deletions.
"""
import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from math import prod
from pathlib import Path

D = tuple(d for d in range(1, 316) if 315 % d == 0)
P = (11, 13, 17, 19, 23)
Q = tuple(p - 1 for p in P)
SOURCE_SHA256 = '3233f1c82a405ae6018bcad76b0274f14bce7f19a2bcf3bac741657452eec630'
INPUT_SHA256 = '7f36de92b6217d6f86ee3742336dc0619e490fa0e20978a68da60a35d6d7fed0'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def kappa(d):
    return prod((F(p, p - 1) for p, top in ((3, 9), (5, 5), (7, 7))
                 if d % top == 0), start=F(1)) - 1


def verify(source, data):
    need(set(data) == {'source_input_sha256', 'scales', 'denominator_lower_bounds',
                      'row_weights'}, 'Complete certificate schema')
    need(data['source_input_sha256'] == SOURCE_SHA256, 'Same774 actual dictionary')
    need(source['divisor_order'] == list(D[1:]), 'Complete old numerical labels')
    core, phases = source['core_phases'], source['singleton_old_phases']
    need(len(core) == 11 and len(phases) == 5 and all(len(row) == 11 for row in phases),
         'One core and five complete globally phased dictionaries')
    need(all(type(a) is int and 0 <= a < d for row in [core] + phases
             for d, a in zip(D[1:], row)), 'Valid globally fixed phases')
    rows = [x for x in range(315) if all(x % d != a for d, a in zip(D[1:], core))]
    lower = {x: [Q[j] - sum(x % d == a for d, a in zip(D[1:], phases[j]))
                 for j in range(5)] for x in rows}
    need(len(rows) == 75 and all(min(v) > 0 for v in lower.values()),
         'All75 actual rows have positive conservative denominators')
    scales, minimum = data['scales'], data['denominator_lower_bounds']
    need(len(scales) == len(minimum) == 5
         and all(type(x) is int and x > 0 for x in scales + minimum),
         'Positive exact scales and denominator bounds')
    need(scales == list(Q), 'Literal fixed scales')
    need(minimum == [min(lower[x][j] for x in rows) for j in range(5)]
         == [3, 4, 8, 8, 15], 'Bounds are the minima over ALL75 source rows')
    pairs = data['row_weights']
    need(all(type(pair) is list and len(pair) == 2 and type(pair[0]) is int
             and type(pair[1]) is int and pair[1] >= 0 for pair in pairs),
         'Exact nonnegative common weights')
    need([x for x, w in pairs] == rows, 'One ordered weight for every source row')
    mass = sum(w for x, w in pairs)
    need(mass == 1000 and sum(w > 0 for x, w in pairs) == 65
         and max(w for x, w in pairs) == 23, 'Literal common law')
    need(all(w == 0 or all(lower[x][j] >= minimum[j] for j in range(5))
             for x, w in pairs), 'Declared bounds hold on every positive-weight row')
    moments = {}
    for j in range(5):
        for k in range(3, 6):
            value = sum((F(scales[j] ** k, k * prod(scales[i] for i in subset))
                         for subset in combinations(range(5), k) if j in subset), F(0))
            moments[j, k] = value
    coefficient = [sum((moments[j, k] * F(minimum[j]) ** (3 - k)
                        for k in range(3, 6)), F(0)) for j in range(5)]
    need(coefficient == list(map(F, ('6425/7776', '5833/4400', '59656/22275',
                                    '1016847/281600', '13826791/2430000'))),
         'All five exact high-order debit coefficients')
    # Each tuple is (d, kind, j, k, coefficient). kind0 is empty,
    # kind1 a single-axis power, kind2 a product of two different axes.
    slots = [(d, 0, -1, 0, kappa(d)) for d in D if kappa(d)]
    slots += [(d, 1, j, 1, kappa(d)) for j in range(5) for d in D if kappa(d)]
    slots += [(d, 2, i, j, kappa(d) + 1) for i, j in combinations(range(5), 2) for d in D]
    slots += [(d, 1, j, 3, (kappa(d) + 1) * coefficient[j]) for j in range(5) for d in D]
    need(len(slots) == 240, '10empty +50singleton +120pair +60third-moment slots')
    caps, cost, block_costs = [], F(0), [F(0)] * 4
    for index, (d, kind, j, k, beta) in enumerate(slots):
        bins = [F(0)] * d
        for x, w in pairs:
            value = F(w) if kind == 0 else (F(w, lower[x][j] * lower[x][k])
                    if kind == 2 else F(w, lower[x][j] ** k))
            bins[x % d] += value
        cap = max(bins)
        cost += beta * cap
        block = 0 if index < 10 else 1 if index < 60 else 2 if index < 180 else 3
        block_costs[block] += beta * cap
        caps.append([d, kind, j, k, str(beta), str(cap), bins.index(cap)])
    ratio = cost / mass
    need(ratio == F(21272859590351218471954789974856121,
                    21297758225879710395684864000000000)
         and ratio < F(999, 1000), 'Exact strict240-query sufficient certificate')
    # This reference computation is for comparison; the sufficient interface
    # above uses only240 caps and does not need the372 reference values.
    joint = F(0)
    joint_caps = []
    for mask in range(32):
        axes = [j for j in range(5) if mask & (1 << j)]
        for d in D:
            beta = kappa(d) + (len(axes) >= 2)
            if beta:
                bins = [F(0)] * d
                for x, w in pairs:
                    bins[x % d] += F(w, prod(lower[x][j] for j in axes))
                cap = max(bins)
                joint += beta * cap
                joint_caps.append([d, mask, str(cap), bins.index(cap)])
    need(len(joint_caps) == 372 and joint <= cost < mass,
         'Reference372 cost is dominated by the240 sufficient cost')
    point_cap = max(F(w, prod(lower[x])) for x, w in pairs)
    haar = (mass - cost) / (315 * prod(P) * point_cap)
    need(haar > 0, 'Positive Haar bound through the758 source normalization')
    return {
        'scope': 'Static240-query sufficient bound for the same actual dictionary as774; '
                 'one common integer law, global75-row denominator minima. '
                 'Not DP-state cardinality, update closure, universal feasibility, or Erdos7.',
        'source_input_sha256': SOURCE_SHA256, 'scales': scales,
        'global_denominator_minima': minimum, 'source_rows': rows,
        'source_row_count': len(rows), 'positive_weight_rows': 65, 'mass': mass,
        'maximum_weight': 23, 'coefficient_by_axis': list(map(str, coefficient)),
        'moment_coefficients': [[str(moments[j, k]) for k in range(3, 6)] for j in range(5)],
        'sufficient_cap_count': len(caps), 'sufficient_caps': caps,
        'block_costs': list(map(str, block_costs)), 'sufficient_cost': str(cost),
        'sufficient_cost_ratio': str(ratio), 'sufficient_reserve': str(mass - cost),
        'comparison_joint_cap_count': len(joint_caps), 'comparison_joint_caps': joint_caps,
        'comparison_joint_cost_ratio': str(joint / mass),
        'conservative_point_mass_cap': str(point_cap), 'Haar_lower': str(haar),
        'lean_verification': False,
    }


def self_test(source, data):
    mutations = []
    def add(name, edit):
        changed = deepcopy(data)
        edit(changed)
        mutations.append((name, changed))
    add('wrong source pin', lambda d: d.__setitem__('source_input_sha256', '0' * 64))
    add('zero scale', lambda d: d['scales'].__setitem__(0, 0))
    add('altered scales', lambda d: d['scales'].__setitem__(0, 11))
    add('inflated denominator bound', lambda d: d['denominator_lower_bounds'].__setitem__(0, 4))
    add('zero denominator bound', lambda d: d['denominator_lower_bounds'].__setitem__(0, 0))
    add('negative weight', lambda d: d['row_weights'][0].__setitem__(1, -1))
    add('boolean weight', lambda d: d['row_weights'][0].__setitem__(1, True))
    add('missing row', lambda d: d['row_weights'].pop())
    add('duplicate row', lambda d: d['row_weights'].append(d['row_weights'][0]))
    add('forged supplied coefficient', lambda d: d.__setitem__('coefficient', [0] * 5))
    rejected = []
    for name, changed in mutations:
        try:
            verify(source, changed)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('Malformed certificate accepted: ' + name)
    need(len(rejected) == 10, 'All malformed input checks rejected')
    return rejected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-input', type=Path, default=Path(__file__).with_name(
        'fibre_credit_depth_two_single_axis_obstruction_input.json'))
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name(
        Path(__file__).stem + '_input.json'))
    parser.add_argument('--write-result', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    source_raw = args.source_input.read_bytes()
    need(sha256(source_raw).hexdigest() == SOURCE_SHA256, 'Exact774 source bytes')
    source = json.loads(source_raw)
    raw = args.input.read_bytes()
    data = json.loads(raw)
    result = verify(source, data)
    need(sha256(raw).hexdigest() == INPUT_SHA256, 'Pinned new integer weights and bounds')
    result['input_sha256'] = sha256(raw).hexdigest()
    if args.self_test:
        print(json.dumps({'malformed_inputs_rejected': self_test(source, data),
                          'optimization_safe_guards': True}, indent=2))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    else:
        expected = json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result == expected, 'Retained result equals exact recomputation')
    print(json.dumps({k: v for k, v in result.items() if k not in
                      ('source_rows', 'sufficient_caps', 'comparison_joint_caps')}, indent=2))


if __name__ == '__main__':
    main()
