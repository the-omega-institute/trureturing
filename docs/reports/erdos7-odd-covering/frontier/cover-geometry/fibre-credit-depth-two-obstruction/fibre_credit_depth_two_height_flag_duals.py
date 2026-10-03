"""Exact classification of32 saturated height-flag envelopes at reference primes.

Four nonnegative rational duals exclude every flag containing11,13,17or19.
A fresh replay of the776 common law handles flags0and16. This does not
exclude actual survivors, other constructions, or larger-prime certificates.
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
POSITIVE_SHA256 = '323c0afab93d3f95a35f01ecbf22702def1a94491de0c61ed63c30a94ea63b17'
INPUT_SHA256 = '138f004cd53b15a0e855ded9c36f3cd421bb753ca4fc48f4b44b80e0300df6fb'
EXPECTED = {
    1: F(170752588300591, 163296000000000),
    2: F(4193009390192663, 4084080000000000),
    4: F(244211160455359, 241920000000000),
    8: F(971999240425747, 967680000000000),
}


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
    need(source['divisor_order'] == list(D[1:]), 'Complete old numerical labels')
    core, phases = source['core_phases'], source['singleton_old_phases']
    need(len(core) == 11 and len(phases) == 5 and all(len(row) == 11 for row in phases),
         'Complete actual dictionaries')
    need(all(type(a) is int and 0 <= a < d for row in [core] + phases
             for d, a in zip(D[1:], row)), 'Globally valid original phases')
    rows = [x for x in range(315) if all(x % d != a for d, a in zip(D[1:], core))]
    lower = {x: [p - 1 - sum(x % d == a for d, a in zip(D[1:], phases[j]))
                 for j, p in enumerate(P)] for x in rows}
    need(len(rows) == 75 and all(min(v) > 0 for v in lower.values()),
         'Same75 actual rows, all admissible')
    return rows, lower


def verify(source, positive, data):
    need(set(data) == {'source_input_sha256', 'positive_input_sha256', 'dual_scale', 'duals'},
         'Complete dual schema')
    need(data['source_input_sha256'] == SOURCE_SHA256
         and data['positive_input_sha256'] == POSITIVE_SHA256, 'Exact dependency pins')
    rows, lower = geometry(source)
    slots = [(d, mask) for mask in range(32) for d in D if mask or kappa(d)]
    need(len(slots) == 382, 'All possibly nonzero height-query slots')
    coeffs = {flag: [coefficient(d, mask, flag) for d, mask in slots] for flag in range(32)}
    need(all(sum(c > 0 for c in coeffs[flag]) == 372 + 2 * flag.bit_count()
             for flag in range(32)), 'Correct nonzero slot count in every scenario')
    scale = data['dual_scale']
    need(type(scale) is int and scale > 0, 'Exact positive multiplier scale')
    certificates = data['duals']
    need([cert['flags'] for cert in certificates] == [1, 2, 4, 8],
         'Exactly four distinct singleton flag certificates')
    checked = []
    for cert in certificates:
        need(set(cert) == {'flags', 'entries'}, 'Dual certificate shape')
        flag = cert['flags']
        need(type(flag) is int, 'Integer flag identity')
        budgets = [F(0)] * len(slots)
        loads = {x: F(0) for x in rows}
        seen = set()
        for entry in cert['entries']:
            need(type(entry) is list and len(entry) == 3, 'Three coordinates per dual query')
            slot, a, numerator = entry
            need(type(slot) is int and 0 <= slot < len(slots) and type(a) is int
                 and type(numerator) is int and numerator > 0, 'Valid positive dual multiplier')
            d, mask = slots[slot]
            need(0 <= a < d and (slot, a) not in seen, 'Valid distinct phase query')
            seen.add((slot, a))
            value = F(numerator, scale)
            budgets[slot] += value
            for x in rows:
                if x % d == a:
                    loads[x] += value / prod(lower[x][j] for j in range(5) if mask & (1 << j))
        need(all(b <= c for b, c in zip(budgets, coeffs[flag])),
             'Every exact multiplier budget, including zero-coefficient slots')
        bound = min(loads.values())
        need(bound == EXPECTED[flag] and bound > F(251, 250),
             'Every actual row exceeds the saturated budget threshold')
        checked.append({
            'flags': flag, 'full_prime': P[flag.bit_length() - 1],
            'nonzero_entries': len(seen), 'budget_checks': len(slots), 'row_inequalities': len(rows),
            'lower_bound': str(bound), 'minimum_row': min(loads, key=loads.get),
            'budgets': [[d, mask, str(c), str(b), str(c - b)]
                        for (d, mask), c, b in zip(slots, coeffs[flag], budgets)],
            'row_loads': [[x, str(loads[x])] for x in rows],
        })
    need(positive['source_input_sha256'] == SOURCE_SHA256 and positive['released_flags'] == 16,
         'Positive witness uses the same source and fifth-axis scope')
    pairs = positive['row_weights']
    need([x for x, w in pairs] == rows and all(type(w) is int and w >= 0 for x, w in pairs),
         'Positive witness is one nonnegative law over the same rows')
    mass = sum(w for x, w in pairs)
    need(mass == 50001, 'Positive common mass')
    costs = {0: F(0), 16: F(0)}
    for slot, (d, mask) in enumerate(slots):
        if coeffs[16][slot]:
            bins = [F(0)] * d
            for x, w in pairs:
                bins[x % d] += F(w, prod(lower[x][j] for j in range(5) if mask & (1 << j)))
            cap = max(bins)
            for flag in costs:
                costs[flag] += coeffs[flag][slot] * cap
    need(costs[0] <= costs[16] < F(999, 1000) * mass,
         'Same exact law certifies both positive scenarios')
    need(costs[16] / mass == F(35736603059510325866351, 35776201636903343616000),
         'Fresh positive776 replay')
    classification = []
    for flag in range(32):
        primes = [p for j, p in enumerate(P) if flag & (1 << j)]
        if flag in costs:
            classification.append({'flags': flag, 'full_primes': primes,
                                   'saturated_envelope_status': 'strictly feasible',
                                   'common_law_cost_ratio': str(costs[flag] / mass)})
        else:
            witness = next(single for single in (1, 2, 4, 8) if flag & single)
            need(all(a <= b for a, b in zip(coeffs[witness], coeffs[flag])),
                 'Larger flag scenario dominates its certified singleton')
            classification.append({'flags': flag, 'full_primes': primes,
                                   'saturated_envelope_status': 'strict feasibility excluded',
                                   'dominated_singleton_flag': witness,
                                   'all_law_cost_ratio_lower_bound': str(EXPECTED[witness])})
    return {
        'scope': 'Exact classification of the specified saturated geometric envelope '
                 'on the774 actual dictionary at reference primes11,13,17,19,23. '
                 'Not actual covering, failure of all source methods, or a negative '
                 'statement at larger primes or every finite truncation.',
        'source_input_sha256': SOURCE_SHA256, 'positive_input_sha256': POSITIVE_SHA256,
        'reference_primes': list(P), 'actual_rows': rows, 'dual_certificates': checked,
        'total_budget_checks': sum(c['budget_checks'] for c in checked),
        'total_row_inequalities': sum(c['row_inequalities'] for c in checked),
        'classification': classification, 'feasible_flags': [0, 16],
        'excluded_flag_count': 30, 'lean_verification': False,
    }


def self_test(source, positive, data):
    mutations = []
    def add(name, edit):
        changed = deepcopy(data)
        edit(changed)
        mutations.append((name, changed))
    add('wrong source pin', lambda d: d.__setitem__('source_input_sha256', '0' * 64))
    add('wrong positive pin', lambda d: d.__setitem__('positive_input_sha256', '0' * 64))
    add('zero scale', lambda d: d.__setitem__('dual_scale', 0))
    add('missing axis certificate', lambda d: d['duals'].pop())
    add('wrong singleton flag', lambda d: d['duals'][0].__setitem__('flags', 31))
    add('invalid slot', lambda d: d['duals'][0]['entries'][0].__setitem__(0, 382))
    add('negative multiplier', lambda d: d['duals'][0]['entries'][0].__setitem__(2, -1))
    add('duplicate query', lambda d: d['duals'][0]['entries'].append(d['duals'][0]['entries'][0]))
    add('excess budget', lambda d: d['duals'][0]['entries'][0].__setitem__(2, 10 ** 20))
    add('empty dual', lambda d: d['duals'][0].__setitem__('entries', []))
    rejected = []
    for name, changed in mutations:
        try:
            verify(source, positive, changed)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('Malformed dual accepted: ' + name)
    need(len(rejected) == 10, 'All malformed dual mutations rejected')
    return rejected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-input', type=Path, default=Path(__file__).with_name(
        'fibre_credit_depth_two_single_axis_obstruction_input.json'))
    parser.add_argument('--positive-input', type=Path, default=Path(__file__).with_name(
        'fibre_credit_depth_two_last23_height_input.json'))
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name(
        Path(__file__).stem + '_input.json'))
    parser.add_argument('--write-result', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    source_raw, positive_raw = args.source_input.read_bytes(), args.positive_input.read_bytes()
    need(sha256(source_raw).hexdigest() == SOURCE_SHA256, 'Exact774 source bytes')
    need(sha256(positive_raw).hexdigest() == POSITIVE_SHA256, 'Exact776 positive witness bytes')
    source, positive = json.loads(source_raw), json.loads(positive_raw)
    raw = args.input.read_bytes()
    data = json.loads(raw)
    result = verify(source, positive, data)
    need(sha256(raw).hexdigest() == INPUT_SHA256, 'Pinned four exact duals')
    result['input_sha256'] = sha256(raw).hexdigest()
    if args.self_test:
        print(json.dumps({'malformed_inputs_rejected': self_test(source, positive, data),
                          'optimization_safe_guards': True}, indent=2))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
             'Retained result equals complete recomputation')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('actual_rows', 'dual_certificates', 'classification')}, indent=2))


if __name__ == '__main__':
    main()
