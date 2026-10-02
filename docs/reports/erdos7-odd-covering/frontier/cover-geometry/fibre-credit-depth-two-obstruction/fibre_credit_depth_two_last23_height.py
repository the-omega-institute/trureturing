"""One actual dictionary supports arbitrary finite23-height with exact caps.

The finite arithmetic verifies a saturated geometric sufficient bound,
not an imposed finite-height cutoff. Every guard survives Python -O.
"""
import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import json
from math import prod
from pathlib import Path

D = tuple(d for d in range(1, 316) if 315 % d == 0)
P = (11, 13, 17, 19, 23)
SOURCE_SHA256 = '3233f1c82a405ae6018bcad76b0274f14bce7f19a2bcf3bac741657452eec630'
INPUT_SHA256 = '323c0afab93d3f95a35f01ecbf22702def1a94491de0c61ed63c30a94ea63b17'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def kappa(d):
    return prod((F(p, p - 1) for p, h in ((3, 9), (5, 5), (7, 7))
                 if d % h == 0), start=F(1)) - 1


def coefficient(d, mask, flags):
    if mask == 0:
        return kappa(d)
    factors = [F(p, p - 1) if flags & (1 << j) else F(1)
               for j, p in enumerate(P) if mask & (1 << j)]
    return (kappa(d) + 1) * prod(factors, start=F(1)) - (mask.bit_count() == 1)


def geometry(source):
    need(source['divisor_order'] == list(D[1:]), 'Complete old315 divisor labels')
    core, phases = source['core_phases'], source['singleton_old_phases']
    need(len(core) == 11 and len(phases) == 5 and all(len(row) == 11 for row in phases),
         'Complete core and five singleton old dictionaries')
    need(all(type(a) is int and 0 <= a < d for row in [core] + phases
             for d, a in zip(D[1:], row)), 'Actual globally fixed old phases')
    rows = [x for x in range(315) if all(x % d != a for d, a in zip(D[1:], core))]
    lower = {x: [p - 1 - sum(x % d == a for d, a in zip(D[1:], phases[j]))
                 for j, p in enumerate(P)] for x in rows}
    need(len(rows) == 75 and all(min(v) > 0 for v in lower.values()),
         '75 actual source rows, each with positive conservative denominators')
    return rows, lower


def verify(source, data):
    need(set(data) == {'source_input_sha256', 'released_flags', 'row_weights'},
         'Complete positive-certificate schema')
    need(data['source_input_sha256'] == SOURCE_SHA256, 'Pinned774 actual source')
    flags = data['released_flags']
    need(type(flags) is int and flags == 16, 'Only the fifth outside axis is full-height')
    rows, lower = geometry(source)
    pairs = data['row_weights']
    need(all(type(pair) is list and len(pair) == 2 and type(pair[0]) is int
             and type(pair[1]) is int and pair[1] >= 0 for pair in pairs),
         'One nonnegative integer law')
    need([x for x, w in pairs] == rows, 'Exactly one ordered weight for each actual row')
    mass = sum(w for x, w in pairs)
    need(mass == 50001 and sum(w > 0 for x, w in pairs) == 67
         and max(w for x, w in pairs) == 1129, 'Literal positive common mass')
    # Formerly zero d=1,3 singleton slots are necessary for pure higher
    # powers and for3*p^e. The complete infinite geometric sums pay them.
    need(coefficient(1, 16, flags) == coefficient(3, 16, flags) == F(1, 22),
         'Pure higher powers and3*23^e are included')
    cost, caps = F(0), []
    shallow_cost = F(0)
    for mask in range(32):
        axes = [j for j in range(5) if mask & (1 << j)]
        for d in D:
            beta = coefficient(d, mask, flags)
            if beta:
                bins = [F(0)] * d
                for x, w in pairs:
                    bins[x % d] += F(w, prod(lower[x][j] for j in axes))
                cap = max(bins)
                cost += beta * cap
                shallow_cost += coefficient(d, mask, 0) * cap
                caps.append([d, mask, str(beta), str(cap), bins.index(cap)])
    need(len(caps) == 374, 'All372 inherited plus2 newly nonzero query slots')
    ratio = cost / mass
    need(ratio == F(35736603059510325866351, 35776201636903343616000)
         and ratio < F(999, 1000), 'Positive full23-height saturated reserve')
    need(shallow_cost <= cost < mass, 'The same law also pays the all-shallow case')
    point_cap = max(F(w, prod(lower[x])) for x, w in pairs)
    need(point_cap == F(43, 6160), 'Conservative physical-source point cap')
    margin = mass - cost
    haar = margin / (315 * prod(P) * point_cap)
    need(haar == F(1721677277957293463, 72669537547485566688000)
         and haar > F(1, 42500), 'Exact Haar conversion after all geometric debits')
    return {
        'scope': 'Same774 actual core and singleton old phases; arbitrary actual first-root '
                 'choices and arbitrary globally fixed later phases. All core3/5/7 heights '
                 'and fifth outside height arbitrary finite; other outside heights<=1. '
                 'Static sufficient source certificate, not unrestricted Erdos7 or new prime frontier.',
        'source_input_sha256': SOURCE_SHA256, 'source_rows': rows,
        'source_row_count': len(rows), 'released_flags': flags, 'full_reference_primes': [23],
        'outside_geometric_factors': ['1', '1', '1', '1', '23/22'],
        'minimum_conservative_denominators': [min(lower[x][j] for x in rows) for j in range(5)],
        'mass': mass, 'positive_rows': 67, 'maximum_weight': 1129,
        'query_cap_count': len(caps), 'query_caps': caps, 'cost': str(cost),
        'cost_ratio': str(ratio), 'distorted_reserve': str(margin),
        'same_law_shallow_cost_ratio': str(shallow_cost / mass),
        'conservative_point_mass_cap': str(point_cap), 'Haar_lower': str(haar),
        'simple_Haar_lower': '1/42500', 'lean_verification': False,
    }


def self_test(source, data):
    mutations = []
    def add(name, edit):
        changed = deepcopy(data)
        edit(changed)
        mutations.append((name, changed))
    add('wrong source pin', lambda d: d.__setitem__('source_input_sha256', '0' * 64))
    add('undeclared all-height axes', lambda d: d.__setitem__('released_flags', 31))
    add('negative flags', lambda d: d.__setitem__('released_flags', -1))
    add('boolean flags', lambda d: d.__setitem__('released_flags', True))
    add('negative weight', lambda d: d['row_weights'][0].__setitem__(1, -1))
    add('boolean weight', lambda d: d['row_weights'][0].__setitem__(1, True))
    add('missing row', lambda d: d['row_weights'].pop())
    add('duplicate row', lambda d: d['row_weights'].append(d['row_weights'][0]))
    add('forged cap data', lambda d: d.__setitem__('query_caps', []))
    add('altered weight', lambda d: d['row_weights'][0].__setitem__(1, d['row_weights'][0][1] + 1))
    rejected = []
    for name, changed in mutations:
        try:
            verify(source, changed)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('Malformed certificate accepted: ' + name)
    need(len(rejected) == 10, 'All malformed certificates rejected')
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
    need(sha256(raw).hexdigest() == INPUT_SHA256, 'Pinned law and height scope')
    result['input_sha256'] = sha256(raw).hexdigest()
    if args.self_test:
        print(json.dumps({'malformed_inputs_rejected': self_test(source, data),
                          'optimization_safe_guards': True}, indent=2))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    else:
        expected = json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result == expected, 'Retained result equals exact recomputation')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('source_rows', 'query_caps')}, indent=2))


if __name__ == '__main__':
    main()
