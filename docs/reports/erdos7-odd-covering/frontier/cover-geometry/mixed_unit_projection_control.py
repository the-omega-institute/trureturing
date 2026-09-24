"""Exact nine-label control for fixed mixed-unit projections and a unit reserve.

This checks one actual phase/account entry and the scalar reserve arithmetic.
The common-source row-transfer argument is supplied separately as ordinary proof.
"""
from pathlib import Path
from fractions import Fraction as F
from math import gcd, lcm
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
INPUT = 'mixed_unit_projection_input.json'
PIN = '6cbd07f21774f4145b9ebc576725baf8703ff65eb14db18e35cd807ee7921017'


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


def verify(input_dir):
    raw = (Path(input_dir) / INPUT).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PIN, 'pinned actual input')
    d = json.loads(raw)
    need(d['schema'] == 'mixed-unit-projection-control-v1', 'schema')
    rows = []
    seen = set()
    for row in d['classes']:
        m, a = row['modulus'], row['residue']
        need(type(m) is int and m > 1 and m % 2 == 1 and m not in seen,
             'distinct actual odd numerical modulus')
        need(type(a) is int and 0 <= a < m and row['selector'] in ('A', 'B'),
             'canonical actual phase and fixed selector')
        seen.add(m)
        old = group_part(m, d['old_primes'])
        r, s = group_part(m, d['R']), group_part(m, d['S'])
        need(old * r * s == m and r * s > 1, 'actual complete label')
        for p, depth, ref_a, ref_b in d['split_prefixes']:
            ref = ref_a if row['selector'] == 'A' else ref_b
            need(ref_a % p != ref_b % p
                 and (a - ref) % gcd(old, p ** depth) == 0,
                 'one fixed selector satisfies actual old split prefixes')
        for p, depth, ref in d['common_prefixes']:
            need((a - ref) % gcd(old, p ** depth) == 0,
                 'actual old common prefix')
        rows.append({**row, 'old': old, 'R': r, 'S': s})
    labels = d['old_labels']
    need(labels == [1, 3, 9] and all(row['old'] in labels for row in rows),
         'divisor-closed old-label inventory')
    periods = {side: lcm(*(row[side] for row in rows)) for side in ('R', 'S')}
    pure_masks = {side: set() for side in ('R', 'S')}
    for row in rows:
        if row['old'] == 1 and (row['R'] == 1 or row['S'] == 1):
            side = 'R' if row['S'] == 1 else 'S'
            pure_masks[side].add((row[side], row['residue'] % row[side]))
    masks = {side: set(v) for side, v in pure_masks.items()}
    assignment_sources = set()
    for item in d['projection_assignments']:
        m, side = item['source_modulus'], item['side']
        row = next((x for x in rows if x['modulus'] == m), None)
        need(row is not None and row['old'] == 1 and row['R'] > 1 and row['S'] > 1
             and side in ('R', 'S') and m not in assignment_sources,
             'one fixed side assignment for an actual mixed unit label')
        assignment_sources.add(m)
        masks[side].add((row[side], row['residue'] % row[side]))
    need(assignment_sources == {row['modulus'] for row in rows
                               if row['old'] == 1 and row['R'] > 1 and row['S'] > 1},
         'all actual mixed units assigned')

    def survivors(mask):
        return {side: tuple(x for x in range(periods[side])
                            if all(x % n != a for n, a in mask[side]))
                for side in ('R', 'S')}

    pure, core = survivors(pure_masks), survivors(masks)
    need(all(core.values()), 'positive fixed product subcarrier')

    def query(base, side, n, a):
        return F(sum(x % n == a % n for x in base[side]), len(base[side]))

    old_mixed_unit = sum((616 * query(pure, 'R', row['R'], row['residue'])
                         * query(pure, 'S', row['S'], row['residue'])
                         for row in rows if row['old'] == 1
                         and row['R'] > 1 and row['S'] > 1), F())
    need(old_mixed_unit == F(29, 15) and old_mixed_unit > 1,
         '521 mixed unit account cannot fit its sole ancestor')
    accounts = {side: {old: F() for old in labels} for side in ('R', 'S', 'M')}
    phase_rows = []
    for row in rows:
        qr, qs = (query(core, side, row[side], row['residue']) for side in ('R', 'S'))
        account = 'R' if row['S'] == 1 else 'S' if row['R'] == 1 else 'M'
        charge = 22 * qr if account == 'R' else 28 * qs if account == 'S' else 616 * qr * qs
        if row['old'] == 1:
            need(qr * qs == 0, 'every original unit class is inactive in core')
        accounts[account][row['old']] += charge
        phase_rows.append({**row, 'q_R': str(qr), 'q_S': str(qs),
                           'account': account, 'scaled_charge': str(charge)})
    need(accounts == {'R': {1: F(), 3: F(22, 21), 9: F()},
                      'S': {1: F(), 3: F(29, 15), 9: F()},
                      'M': {1: F(), 3: F(), 9: F(22, 21)}},
         'literal conditional accounts')
    eta = F(d['eta'])
    payments = {}
    for side in ('R', 'S', 'M'):
        row_sums, col_sums = ({old: F() for old in labels} for _ in range(2))
        used = set()
        for old, dest, value in d['transports'][side]:
            amount = F(value)
            need(old in labels and dest in labels and old % dest == 0
                 and amount >= 0 and (old, dest) not in used, 'divisor-supported payment')
            used.add((old, dest))
            row_sums[old] += amount
            col_sums[dest] += amount
        need(all(row_sums[old] >= accounts[side][old] for old in labels)
             and all(v <= 1 for v in col_sums.values()), 'expense and shared-column capacities')
        if side == 'R':
            need(0 < eta <= 1 and col_sums[1] <= 1 - eta, 'pure-R unit-column reserve')
        payments[side] = {'rows': {str(k): str(v) for k, v in row_sums.items()},
                          'columns': {str(k): str(v) for k, v in col_sums.items()}}
    corners = [(22 - a) * (28 - b) + (a - 13) * (b - 7) - 35
               for a in (F(13), 21 - eta) for b in (F(9), F(21))]
    need(min(corners) == 17 * eta, 'exact reserve pair corners')
    theta = min(F(1, 3696), 17 * eta / 1232)
    masses = {side: F(len(core[side]), periods[side]) for side in ('R', 'S')}
    haar_floor = masses['R'] * masses['S'] * theta / 270000
    need(masses == {'R': F(21, 23), 'S': F(840, 899)}
         and eta == F(20, 21) and theta == F(1, 3696), 'actual reserve and threshold')
    return {'schema': 'mixed-unit-projection-control-result-v1',
            'input_sha256': PIN, 'original_class_count': len(rows),
            'periods': periods, 'projection_masks': {k: sorted(v) for k, v in masks.items()},
            'projected_class_count': len(assignment_sources),
            'distinct_added_projection_count': sum(len(masks[k] - pure_masks[k]) for k in masks),
            'core_counts': {k: len(v) for k, v in core.items()},
            'lambda': {k: str(v) for k, v in masses.items()},
            'old_521_mixed_unit_account': str(old_mixed_unit),
            'actual_phase_rows': phase_rows,
            'accounts': {k: {str(a): str(v) for a, v in b.items()} for k, b in accounts.items()},
            'payments': payments, 'eta': str(eta), 'pair_corners': [str(v) for v in corners],
            'theta': str(theta), 'conditional_strict_Haar_floor': str(haar_floor),
            'scope': 'One actual entry beyond521 for the fixed R={23},S={29,31} partition; projection deletes extra points, so full survivor mass is bounded below by core survivor mass. General source/row transfer remains an ordinary conditional argument, and no unrestricted transport or covering theorem is claimed.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.input_dir)
    encoded = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    else:
        need(encoded == Path(__file__).with_suffix('.json').read_text(), 'retained result mismatch')
    print(json.dumps({key: result[key] for key in
                      ('original_class_count', 'old_521_mixed_unit_account', 'eta',
                       'theta', 'conditional_strict_Haar_floor')}, indent=2))


if __name__ == '__main__':
    main()
