"""Check the actual eight-label pure-unit conditioning control and pair margin.

The general conditional transport and same-source theorem is an ordinary
proof. This consumer verifies actual finite phase counts, all matrix payments,
the old unit obstructions and the scalar strictness used by that proof.
"""
from pathlib import Path
from fractions import Fraction as F
from math import lcm
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PINS = {
    'pure_unit_conditioned_transport_input.json': '21994097c7cc482519360623f61a95b9c74f8ee7e0424fc3dd81127607578d8b',
    'finite_prefix_template_source.json': 'c10b0d8461922287211b930ea4fffe19938cf68c5a4640af29a266963898a91c',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def group_part(n, primes):
    result = 1
    for p in primes:
        while n % p == 0:
            n //= p
            result *= p
    return result


def exponent(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def verify(input_dir):
    data = {}
    for name, digest in PINS.items():
        raw = (Path(input_dir) / name).read_bytes()
        need(hashlib.sha256(raw).hexdigest() == digest, 'pinned input: ' + name)
        data[name] = json.loads(raw)
    control = data['pure_unit_conditioned_transport_input.json']
    need(control['schema'] == 'pure-unit-conditioned-transport-control-v1'
         and control['old_primes'] == [3, 5, 7, 11, 13, 17, 19]
         and control['R'] == [23] and control['S'] == [29, 31],
         'declared old primes and fixed outside partition')
    classes = []
    seen = set()
    for row in control['classes']:
        m, a = row['modulus'], row['residue']
        need(type(m) is int and m > 1 and m % 2 == 1 and m not in seen,
             'distinct original odd numerical moduli')
        need(type(a) is int and 0 <= a < m and row['selector'] in ('A', 'B'),
             'actual canonical residue and fixed selector')
        seen.add(m)
        d = group_part(m, control['old_primes'])
        r = group_part(m, control['R'])
        s = group_part(m, control['S'])
        need(d * r * s == m and r * s > 1, 'literal later-label factorization')
        for p, depth, ref_a, ref_b in control['split_prefixes']:
            ref = ref_a if row['selector'] == 'A' else ref_b
            need(ref_a % p != ref_b % p
                 and (a - ref) % p ** min(depth, exponent(d, p)) == 0,
                 'one selector meets every split prefix')
        for p, depth, ref in control['common_prefixes']:
            need((a - ref) % p ** min(depth, exponent(d, p)) == 0,
                 'actual common prefix')
        classes.append({**row, 'd': d, 'n_R': r, 'n_S': s})
    need(len(classes) == 8, 'eight original labels')
    labels = control['old_labels']
    need(labels == [1, 3, 9]
         and all(row['d'] in labels for row in classes)
         and all(e in labels for d in labels for e in range(1, d + 1) if d % e == 0),
         'one divisor-closed old-label inventory')
    periods = {'R': lcm(*(row['n_R'] for row in classes)),
               'S': lcm(*(row['n_S'] for row in classes))}
    unit = {
        'R': [row for row in classes if row['d'] == 1 and row['n_S'] == 1],
        'S': [row for row in classes if row['d'] == 1 and row['n_R'] == 1],
    }
    survivors = {}
    masses = {}
    for side in ('R', 'S'):
        survivors[side] = tuple(x for x in range(periods[side])
                               if all((x - row['residue']) % row['n_' + side] != 0
                                      for row in unit[side]))
        need(survivors[side], 'positive common unit-pure survivor base')
        masses[side] = F(len(survivors[side]), periods[side])
    need(masses == {'R': F(22, 23), 'S': F(840, 899)},
         'literal unit phase counts')

    def query(side, n, a):
        return F(sum((x - a) % n == 0 for x in survivors[side]), len(survivors[side]))

    accounts = {side: {d: F() for d in labels} for side in ('R', 'S', 'M')}
    phase_rows = []
    for row in classes:
        d, r, s, a = row['d'], row['n_R'], row['n_S'], row['residue']
        q_r, q_s = query('R', r, a), query('S', s, a)
        removed = d == 1 and (r == 1 or s == 1)
        if removed:
            need(q_r * q_s == 0, 'predeleted original unit pure class is inactive')
            account, charge = None, F()
        elif s == 1:
            account, charge = 'R', 22 * q_r
        elif r == 1:
            account, charge = 'S', 28 * q_s
        else:
            account, charge = 'M', 616 * q_r * q_s
        if account:
            accounts[account][d] += charge
        phase_rows.append({**row, 'q_R': str(q_r), 'q_S': str(q_s),
                           'predeleted_unit_pure': removed,
                           'account': account, 'scaled_charge': str(charge)})
    need(accounts == {'R': {1: F(), 3: F(1), 9: F()},
                      'S': {1: F(), 3: F(29, 15), 9: F()},
                      'M': {1: F(1), 3: F(), 9: F(1)}},
         'actual conditional expense accounts')
    transport_results = {}
    for side, entries in control['transports'].items():
        row_sums = {d: F() for d in labels}
        col_sums = {d: F() for d in labels}
        used = set()
        for d, e, value in entries:
            amount = F(value)
            need(d in labels and e in labels and d % e == 0
                 and amount >= 0 and (d, e) not in used,
                 'nonnegative unique divisor-supported payment')
            used.add((d, e))
            row_sums[d] += amount
            col_sums[e] += amount
        need(all(row_sums[d] >= accounts[side][d] for d in labels), 'every expense paid')
        need(all(col_sums[e] <= 1 for e in labels), 'one capacity per ancestor column')
        transport_results[side] = {
            'entries': entries,
            'row_sums': {str(d): str(v) for d, v in row_sums.items()},
            'column_sums': {str(d): str(v) for d, v in col_sums.items()},
        }
    need(set(transport_results) == {'R', 'S', 'M'}, 'all three transport accounts')
    outside = [23, 29, 31]
    raw_obstructions = []
    for mask in range(8):
        group_r = [p for i, p in enumerate(outside) if mask & (1 << i)]
        group_s = [p for p in outside if p not in group_r]
        raw = {'R': F(), 'S': F(), 'M': F()}
        for row in classes:
            if row['d'] != 1:
                continue
            r, s = group_part(row['modulus'], group_r), group_part(row['modulus'], group_s)
            if s == 1:
                raw['R'] += F(22, r)
            elif r == 1:
                raw['S'] += F(28, s)
            else:
                raw['M'] += F(616, r * s)
        overloaded = [side for side in ('R', 'S') if raw[side] > 1]
        need(overloaded, 'raw unit account fails for each global partition')
        raw_obstructions.append({'R': group_r, 'S': group_s,
                                 'raw_unit_accounts': {k: str(v) for k, v in raw.items()},
                                 'overloaded_pure_accounts': overloaded})
    corners = []
    for a in (F(13), F(440, 21)):
        for b in (F(9), F(21)):
            gap = (22 - a) * (28 - b) + (a - 13) * (b - 7) - 35
            corners.append({'a': str(a), 'b': str(b), 'gap': str(gap)})
    gap = min(F(row['gap']) for row in corners)
    need(gap == F(17, 21) and gap / 616 > 2 * F(1, 3696),
         'conditional pair excludes two uniformly small fibres')
    source = data['finite_prefix_template_source.json']
    need(source['schema'] == 'finite-prefix-template-source-v1'
         and len(source['roles']) == 5
         and all(F(row['remaining_margin']) > F(1, 20000) for row in source['roles']),
         'retained five same-source template margins')
    lambda_r_lower = 1 - F(1, 22)
    lambda_s_lower = 1 - (F(29, 28) * F(31, 30) - 1)
    haar_floor = lambda_r_lower * lambda_s_lower * F(1, 3696) * F(1, 20000) / F(27, 2)
    need(lambda_r_lower * lambda_s_lower == F(71, 80)
         and haar_floor == F(71, 79833600000)
         and haar_floor > F(1, 1200000000), 'conditional uniform density arithmetic')
    return {
        'schema': 'pure-unit-conditioned-transport-control-result-v1',
        'inputs': PINS,
        'original_class_count': len(classes),
        'outside_periods': periods,
        'unit_pure_survivor_counts': {k: len(v) for k, v in survivors.items()},
        'lambda': {k: str(v) for k, v in masses.items()},
        'literal_phase_rows': phase_rows,
        'conditional_accounts': {k: {str(d): str(v) for d, v in a.items()} for k, a in accounts.items()},
        'transports': transport_results,
        'raw_unit_obstructions_all_partitions': raw_obstructions,
        'strict_pair_corners': corners,
        'strict_pair_minimum': str(gap),
        'conditional_pair_survival_sum_lower': str(gap / 616),
        'conditional_uniform_theta': '1/3696',
        'uniform_lambda_lower': {'R': str(lambda_r_lower), 'S': str(lambda_s_lower), 'product': '71/80'},
        'conditional_theorem_strict_Haar_lower': str(haar_floor),
        'simple_strict_Haar_lower': '1/1200000000',
        'scope': 'Actual eight-label control: every raw global-partition unit test fails, while the supplied phase-sensitive conditional matrices satisfy all three ancestor accounts. Four-corner and density arithmetic support the separate ordinary conditional theorem. No claim that arbitrary families pass the matrices, no integer covering counterexample, and no new geometry, optimizer or Lean verification.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.input_dir)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    else:
        expected = json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result == expected, 'retained control result mismatch')
    print(json.dumps({
        'original_classes': result['original_class_count'],
        'raw_partitions_obstructed': len(result['raw_unit_obstructions_all_partitions']),
        'conditional_accounts_checked': len(result['transports']),
        'strict_pair_minimum': result['strict_pair_minimum'],
        'conditional_theorem_strict_Haar_lower': result['conditional_theorem_strict_Haar_lower'],
    }, indent=2))


if __name__ == '__main__':
    main()
