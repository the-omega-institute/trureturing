"""Check actual correlated-unit phase, defect and shared-account controls.

This verifies the two finite inputs and arithmetic of the separate ordinary
bridge. It does not reconstruct the old source or rerun geometric certificates.
"""
from pathlib import Path
from fractions import Fraction as F
from math import gcd, lcm
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
INPUT = 'correlated_unit_defect_input.json'
PIN = 'ca3fa3812a76d82e116eade4bf7a44690903fce03c7d8a34c4a4e3eaf29c054f'


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


def family_result(data, fixture):
    need(fixture['defect_mode'] in ('uniform', 'generated'), 'declared defect query scope')
    rows, seen = [], set()
    for row in fixture['classes']:
        m, a = row['modulus'], row['residue']
        need(type(m) is int and m > 1 and m % 2 == 1 and m not in seen,
             'distinct original odd numerical moduli')
        need(type(a) is int and 0 <= a < m and row['selector'] in ('A', 'B'),
             'canonical original residue and fixed selector')
        seen.add(m)
        old, r, s = (group_part(m, data[key]) for key in ('old_primes', 'R', 'S'))
        need(old * r * s == m and r * s > 1, 'actual complete numerical label')
        for p, depth, aa, bb in data['split_prefixes']:
            ref = aa if row['selector'] == 'A' else bb
            need(aa % p != bb % p and (a - ref) % gcd(old, p ** depth) == 0,
                 'one selector satisfies all finite old split prefixes')
        for p, depth, ref in data['common_prefixes']:
            need((a - ref) % gcd(old, p ** depth) == 0, 'old common prefix')
        need(old in (1, 3, 9) and (a - 1) % old == 0,
             'these fixtures already equal full-comparison old phase1')
        rows.append({**row, 'old': old, 'R': r, 'S': s})
    labels = fixture['old_labels']
    need(labels[0] == 1 and all(row['old'] in labels for row in rows)
         and all(e in labels for d in labels for e in range(1, d + 1) if d % e == 0),
         'one divisor-closed old-label inventory')
    periods = {side: lcm(*(row[side] for row in rows)) for side in ('R', 'S')}
    old_period = lcm(*(row['old'] for row in rows))
    units = [row for row in rows if row['old'] == 1]
    pure = {}
    for side, other in (('R', 'S'), ('S', 'R')):
        masks = [row for row in units if row[other] == 1]
        pure[side] = tuple(x for x in range(periods[side])
                           if all(x % row[side] != row['residue'] % row[side] for row in masks))
    mixed_units = [row for row in units if row['R'] > 1 and row['S'] > 1]

    def hit(row, r, s):
        return r % row['R'] == row['residue'] % row['R'] and s % row['S'] == row['residue'] % row['S']

    live, holes = [], []
    for r in pure['R']:
        for s in pure['S']:
            (holes if any(hit(row, r, s) for row in mixed_units) else live).append((r, s))
    need(live, 'positive complement of the complete actual unit union')
    hole_r, hole_s = {r for r, _ in holes}, {s for _, s in holes}
    p, q, rr, ss = len(pure['R']), len(pure['S']), len(hole_r), len(hole_s)
    z = len(live)
    need(len(holes) == rr * ss and z == p * q - rr * ss,
         'actual mixed-unit union is exactly one rectangular hole')
    uniform_defect = F(rr * (p - rr) * ss * (q - ss), z * z)
    accounts = {side: {d: F() for d in labels} for side in ('R', 'S', 'M')}
    old_raw_mixed = {d: F() for d in labels}
    phase_rows = []
    for row in rows:
        qr = F(sum(r % row['R'] == row['residue'] % row['R'] for r, _ in live), z)
        qs = F(sum(s % row['S'] == row['residue'] % row['S'] for _, s in live), z)
        joint = F(sum(hit(row, r, s) for r, s in live), z)
        side = 'R' if row['S'] == 1 else 'S' if row['R'] == 1 else 'M'
        charge = 22 * qr if side == 'R' else 28 * qs if side == 'S' else 616 * joint
        accounts[side][row['old']] += charge
        if row['old'] == 1:
            need(joint == 0, 'all actual unit classes have zero joint probability')
        if side == 'M':
            qr_pure = F(sum(r % row['R'] == row['residue'] % row['R'] for r in pure['R']), p)
            qs_pure = F(sum(s % row['S'] == row['residue'] % row['S'] for s in pure['S']), q)
            old_raw_mixed[row['old']] += 616 * qr_pure * qs_pure
        phase_rows.append({**row, 'rho_R': str(qr), 'rho_S': str(qs),
                           'rho_joint': str(joint), 'account': side, 'scaled_charge': str(charge)})
    obstructed = fixture['old_521_obstructed_labels']
    need(all(d in labels for d in obstructed)
         and all(e in obstructed for d in obstructed for e in labels if d % e == 0)
         and sum(old_raw_mixed[d] for d in obstructed) > len(obstructed),
         'old521 mixed expenses exceed all available ancestors of this subset')
    patterns = []
    for old_x in range(old_period):
        active = [row for row in rows if row['old'] > 1 and old_x % row['old'] == row['residue'] % row['old']]
        pure_r = [row for row in active if row['S'] == 1]
        pure_s = [row for row in active if row['R'] == 1]
        mixed = [row for row in active if row['R'] > 1 and row['S'] > 1]
        ar = {r for r in pure['R'] if all(r % row['R'] != row['residue'] % row['R'] for row in pure_r)}
        bs = {s for s in pure['S'] if all(s % row['S'] != row['residue'] % row['S'] for row in pure_s)}
        mr = F(sum(r in ar for r, _ in live), z)
        ms = F(sum(s in bs for _, s in live), z)
        joint = F(sum(r in ar and s in bs for r, s in live), z)
        cov = joint - mr * ms
        formula = -F((p * len(ar & hole_r) - rr * len(ar))
                     * (q * len(bs & hole_s) - ss * len(bs)), z * z)
        need(cov == formula, 'literal cell counts equal rectangle covariance formula')
        actual = F(sum(r in ar and s in bs and all(not hit(row, r, s) for row in mixed)
                       for r, s in live), z)
        raw_mixed = sum((F(sum(hit(row, r, s) for r, s in live), z) for row in mixed), F())
        patterns.append({'old_residue': old_x, 'active_moduli': [row['modulus'] for row in active],
                         'pure_R_survivor_count': len(ar), 'pure_S_survivor_count': len(bs),
                         'marginal_R_survival': str(mr), 'marginal_S_survival': str(ms),
                         'joint_pure_survival': str(joint), 'defect': str(max(F(), -cov)),
                         'raw_joint_mixed_load': str(raw_mixed), 'actual_survival': str(actual)})
    generated_defect = max(F(row['defect']) for row in patterns)
    need(generated_defect <= uniform_defect, 'generated queries obey global rectangle bound')
    charged = uniform_defect if fixture['defect_mode'] == 'uniform' else generated_defect
    augmented = {side: dict(values) for side, values in accounts.items()}
    augmented['M'][1] += 616 * charged
    payments = {}
    eta = F(fixture['eta'])
    for side, entries in fixture['transports'].items():
        row_sums, col_sums = ({d: F() for d in labels} for _ in range(2))
        seen_entries = set()
        for d, e, value in entries:
            amount = F(value)
            need(d in labels and e in labels and d % e == 0 and amount >= 0
                 and (d, e) not in seen_entries, 'nonnegative divisor-supported unique payment')
            seen_entries.add((d, e))
            row_sums[d] += amount
            col_sums[e] += amount
        need(all(row_sums[d] >= augmented[side][d] for d in labels)
             and all(amount <= 1 for amount in col_sums.values()), 'shared rows and columns pay all expenses')
        if side == 'R':
            need(0 < eta <= 1 and col_sums[1] <= 1 - eta, 'pureR unit reserve')
        payments[side] = {'row_sums': {str(k): str(v) for k, v in row_sums.items()},
                          'column_sums': {str(k): str(v) for k, v in col_sums.items()}}
    need(set(payments) == {'R', 'S', 'M'}, 'all three accounts checked')
    for row in patterns:
        product = F(row['marginal_R_survival']) * F(row['marginal_S_survival'])
        proxy = max(F(), product - F(row['raw_joint_mixed_load']) - charged)
        need(0 <= proxy <= F(row['actual_survival']), 'clipped proxy is a genuine lower bound')
        row['proxy_survival'] = str(proxy)
    theta = min(F(1, 3696), 17 * eta / 1232)
    mass = F(z, periods['R'] * periods['S'])
    return {'name': fixture['name'], 'class_count': len(rows), 'periods': periods,
            'pure_carrier_sizes': {'R': p, 'S': q}, 'hole_sizes': {'R': rr, 'S': ss},
            'all_unit_survivor_count': z, 'lambda': str(mass), 'actual_phase_rows': phase_rows,
            'old_521_mixed_accounts': {str(k): str(v) for k, v in old_raw_mixed.items()},
            'obstructed_ancestor_set': obstructed,
            'uniform_scaled_defect': str(616 * uniform_defect),
            'generated_scaled_defect': str(616 * generated_defect),
            'charged_scaled_defect': str(616 * charged), 'old_activation_patterns': patterns,
            'augmented_accounts': {k: {str(a): str(v) for a, v in b.items()} for k, b in augmented.items()},
            'payments': payments, 'eta': str(eta), 'theta': str(theta),
            'conditional_strict_Haar_coefficient': str(mass * theta / 270000)}


def verify(input_dir):
    raw = (Path(input_dir) / INPUT).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PIN, 'pinned actual two-family input')
    data = json.loads(raw)
    need(data['schema'] == 'correlated-unit-defect-input-v1', 'input schema')
    cases = [family_result(data, fixture) for fixture in data['families']]
    need(len(cases) == 2 and cases[0]['name'] == 'one_cell' and cases[1]['name'] == 'generated_queries', 'two declared controls')
    need(cases[0]['uniform_scaled_defect'] == '38808/42025'
         and cases[0]['conditional_strict_Haar_coefficient'] == '41/45853315200', 'onecell exact scalar conclusion')
    need(cases[1]['uniform_scaled_defect'] == '7127736/4190209'
         and F(cases[1]['uniform_scaled_defect']) > 1
         and cases[1]['generated_scaled_defect'] == '322168/113135643'
         and cases[1]['conditional_strict_Haar_coefficient'] == '89/99681120000', 'generated-query distinction')
    return {'schema': 'correlated-unit-defect-result-v1', 'input_sha256': PIN, 'families': cases,
            'scope': 'Actual finite phase/account/proxy controls with one joint law per family. Source constants are premises of the separate ordinary bridge; no source producer, geometry, optimizer, Lean run or claim beyond all522 certificates.'}


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
        need(encoded == Path(__file__).with_suffix('.json').read_text(), 'retained exact result mismatch')
    print(json.dumps([{key: case[key] for key in ('name', 'class_count', 'lambda', 'charged_scaled_defect',
                                                 'eta', 'conditional_strict_Haar_coefficient')}
                      for case in result['families']], indent=2))


if __name__ == '__main__':
    main()
