"""Check an actual endpoint-pair defect certificate without old-state enumeration.

The fixed outside kernel includes forbidden joint cells. Pair expenses share
the actual mixed-class column capacities. The general implication is ordinary
proof; only one old point is used here to witness scalar-unit failure.
"""
from pathlib import Path
from fractions import Fraction as F
from math import gcd, lcm
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
INPUT = 'paired_original_defect_input.json'
PIN = 'e578ef5973c6f032325a13a147dac0c25fe972e0900d9a403ef2edc00fea2c2a'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def group_part(n, primes):
    out = 1
    for p in primes:
        while n % p == 0:
            n //= p
            out *= p
    return out


def verify(input_dir):
    raw = (Path(input_dir) / INPUT).read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PIN, 'pinned actual input')
    data = json.loads(raw)
    need(data['schema'] == 'paired-original-defect-input-v1', 'schema')
    rows, seen = [], set()
    for row in data['classes']:
        m, a = row['modulus'], row['residue']
        need(type(m) is int and m > 1 and m % 2 == 1 and m not in seen,
             'distinct actual odd numerical modulus')
        need(type(a) is int and 0 <= a < m and row['selector'] in ('A', 'B'),
             'canonical original phase and fixed selector')
        seen.add(m)
        old, r, s = (group_part(m, data[k]) for k in ('old_primes', 'R', 'S'))
        need(old * r * s == m and r * s > 1, 'actual complete factorization')
        for p, depth, aa, bb in data['split_prefixes']:
            ref = aa if row['selector'] == 'A' else bb
            need(aa % p != bb % p and (a - ref) % gcd(old, p ** depth) == 0,
                 'one selector meets all finite split prefixes')
        for p, depth, ref in data['common_prefixes']:
            need((a - ref) % gcd(old, p ** depth) == 0, 'actual common prefix')
        need(old in (1, 3, 9) and (a - 1) % old == 0,
             'main fixture equals its full-comparison old reference1')
        rows.append({**row, 'old': old, 'R': r, 'S': s})
    labels = data['old_labels']
    need(labels == [1, 3, 9] and all(row['old'] in labels for row in rows),
         'divisor-closed old inventory')
    periods = {side: lcm(*(row[side] for row in rows)) for side in ('R', 'S')}

    def hit(row, r, s):
        return r % row['R'] == row['residue'] % row['R'] and s % row['S'] == row['residue'] % row['S']

    units = [row for row in rows if row['old'] == 1]
    live = {(r, s) for r in range(periods['R']) for s in range(periods['S'])
            if all(not hit(row, r, s) for row in units)}
    need(live, 'positive exact complement of all original units')
    z = len(live)
    rc = [sum(rr == r for rr, _ in live) for r in range(periods['R'])]
    sc = [sum(ss == s for _, ss in live) for s in range(periods['S'])]
    negative = {(r, s): max(0, rc[r] * sc[s] - z * ((r, s) in live))
                for r in range(periods['R']) for s in range(periods['S'])}
    need(all(sum(z * ((r, s) in live) - rc[r] * sc[s] for s in range(periods['S'])) == 0
             for r in range(periods['R']))
         and all(sum(z * ((r, s) in live) - rc[r] * sc[s] for r in range(periods['R'])) == 0
                 for s in range(periods['S'])), 'centred joint kernel has zero row and column sums')
    accounts = {side: {d: F() for d in labels} for side in ('R', 'S', 'M')}
    phase_rows = []
    for row in rows:
        qr = F(sum(rc[r] for r in range(periods['R']) if r % row['R'] == row['residue'] % row['R']), z)
        qs = F(sum(sc[s] for s in range(periods['S']) if s % row['S'] == row['residue'] % row['S']), z)
        joint = F(sum(hit(row, r, s) for r, s in live), z)
        side = 'R' if row['S'] == 1 else 'S' if row['R'] == 1 else 'M'
        charge = 22 * qr if side == 'R' else 28 * qs if side == 'S' else 616 * joint
        accounts[side][row['old']] += charge
        if row['old'] == 1:
            need(joint == 0, 'predeleted actual unit cylinder has zero joint probability')
        phase_rows.append({**row, 'rho_R': str(qr), 'rho_S': str(qs),
                           'rho_joint': str(joint), 'account': side, 'scaled_charge': str(charge)})
    pure_r = [row for row in rows if row['old'] > 1 and row['S'] == 1]
    pure_s = [row for row in rows if row['old'] > 1 and row['R'] == 1]
    pair_prices = {}
    for left in pure_r:
        for right in pure_s:
            numerator = sum(negative[r, s] for r in range(periods['R']) for s in range(periods['S'])
                            if r % left['R'] == left['residue'] % left['R']
                            and s % right['S'] == right['residue'] % right['S'])
            live_only = sum(negative[r, s] for r, s in live
                            if r % left['R'] == left['residue'] % left['R']
                            and s % right['S'] == right['residue'] % right['S'])
            pair_prices[left['modulus'], right['modulus']] = {
                'old_R': left['old'], 'old_S': right['old'],
                'scaled_price': F(616 * numerator, z * z),
                'incorrect_live_only_scaled_price': F(616 * live_only, z * z)}
    eta = F(data['eta'])
    payment_results = {}
    for side in ('R', 'S', 'M'):
        row_sums, col_sums = ({d: F() for d in labels} for _ in range(2))
        used = set()
        for d, e, value in data['transports'][side]:
            amount = F(value)
            need(d in labels and e in labels and d % e == 0 and amount >= 0
                 and (d, e) not in used, 'unique nonnegative divisor-supported original payment')
            used.add((d, e))
            row_sums[d] += amount
            col_sums[e] += amount
        need(all(row_sums[d] >= accounts[side][d] for d in labels), 'all original expenses paid')
        if side == 'R':
            need(0 < eta <= 1 and col_sums[1] <= 1 - eta, 'pure-R unit reserve')
        payment_results[side] = {'rows': row_sums, 'columns': col_sums}
    pair_payment_rows, handled = [], set()
    for item in data['pair_transports']:
        key = item['R_modulus'], item['S_modulus']
        need(key in pair_prices and key not in handled, 'one actual pair payment row')
        handled.add(key)
        pair, total, used = pair_prices[key], F(), set()
        for e, value in item['payments']:
            amount = F(value)
            need(e in labels and (pair['old_R'] % e == 0 or pair['old_S'] % e == 0)
                 and amount >= 0 and e not in used, 'either-endpoint ancestor payment')
            used.add(e)
            total += amount
            payment_results['M']['columns'][e] += amount
        need(total >= pair['scaled_price'], 'entire pair negative-kernel expense paid')
        pair_payment_rows.append({'R_modulus': key[0], 'S_modulus': key[1],
                                  **{k: str(v) for k, v in pair.items()},
                                  'paid': str(total), 'payments': item['payments']})
    need(handled == set(pair_prices), 'every actual pure-R/pure-S pair accounted')
    need(all(v <= 1 for result in payment_results.values() for v in result['columns'].values()),
         'one shared capacity including all pair and mixed expenses')
    old_x = data['comparison_witness_old_residue']
    active = [row for row in rows if row['old'] > 1 and old_x % row['old'] == row['residue'] % row['old']]
    deleted_r = {r for r in range(periods['R']) if any(r % row['R'] == row['residue'] % row['R']
                                                                    for row in active if row['S'] == 1)}
    deleted_s = {s for s in range(periods['S']) if any(s % row['S'] == row['residue'] % row['S']
                                                                    for row in active if row['R'] == 1)}
    dr, ds = F(sum(rc[r] for r in deleted_r), z), F(sum(sc[s] for s in deleted_s), z)
    dj = F(sum(r in deleted_r and s in deleted_s for r, s in live), z)
    scaled_defect = 616 * max(F(), dr * ds - dj)
    need(scaled_defect == F(7127736, 4190209) and scaled_defect > 1,
         'one actual full-comparison query refutes every constant-to-unit charge')
    active_pair_sum = sum(pair['scaled_price'] for (a, b), pair in pair_prices.items()
                          if any(row['modulus'] == a for row in active)
                          and any(row['modulus'] == b for row in active))
    need(scaled_defect <= active_pair_sum == F(7252784, 4190209), 'actual witness pair bound')
    need(all(pair['incorrect_live_only_scaled_price'] == 0 for pair in pair_prices.values()),
         'restricting negative kernel to live support would wrongly erase both positive pair expenses')
    mixed = [row for row in active if row['R'] > 1 and row['S'] > 1]
    raw_mixed = sum((F(sum(hit(row, r, s) for r, s in live), z) for row in mixed), F())
    actual = F(sum(r not in deleted_r and s not in deleted_s and all(not hit(row, r, s) for row in mixed)
                   for r, s in live), z)
    proxy = max(F(), (1 - dr) * (1 - ds) - raw_mixed - active_pair_sum / 616)
    need(0 <= proxy <= actual, 'clipped proxy lower-bound witness')
    counter = data['lcm_countercontrol']
    xx, aa, bb = counter['old_point'], counter['reference_A'], counter['reference_B']
    di, dj_old = counter['old_R'], counter['old_S']
    mi, ai = counter['R_original']
    mj, aj = counter['S_original']
    pp, qq = counter['outside_primes']
    need(mi == di * pp and mj == dj_old * qq and ai % di == aa % di and aj % dj_old == bb % dj_old
         and xx % di == ai % di and xx % dj_old == aj % dj_old, 'actual compatible mixed-selector endpoints')
    common = lcm(di, dj_old)
    need(xx % common not in (aa % common, bb % common), 'lcm has neither declared old reference')
    small_live = {(r, s) for r in range(pp) for s in range(qq)
                  if all(not (r % gcd(m, pp) == a % gcd(m, pp)
                              and s % gcd(m, qq) == a % gcd(m, qq)) for m, a in counter['unit_originals'])}
    sz = len(small_live)
    rr, ss = ai % pp, aj % qq
    rk, sk = sum(r == rr for r, _ in small_live), sum(s == ss for _, s in small_live)
    lcm_pair_price = F(max(0, rk * sk - sz * ((rr, ss) in small_live)), sz * sz)
    need(lcm_pair_price == F(1, 615 ** 2), 'lcm failure carries positive actual pair price')
    theta = min(F(1, 3696), 17 * eta / 1232)
    mass = F(z, periods['R'] * periods['S'])
    need(payment_results['M']['columns'][1] == F(9226618, 12570627)
         and payment_results['M']['columns'][3] == 1, 'literal combined mixed capacity')
    return {'schema': 'paired-original-defect-result-v1', 'input_sha256': PIN,
            'original_class_count': len(rows), 'periods': periods, 'all_unit_live_count': z,
            'lambda': str(mass), 'actual_phase_rows': phase_rows,
            'accounts': {k: {str(d): str(v) for d, v in b.items()} for k, b in accounts.items()},
            'pair_expenses_and_payments': pair_payment_rows,
            'combined_payments': {k: {kind: {str(d): str(v) for d, v in vals.items()}
                                     for kind, vals in result.items()} for k, result in payment_results.items()},
            'single_comparison_witness': {'old_residue': old_x, 'active_moduli': [row['modulus'] for row in active],
                                          'scalar_scaled_defect': str(scaled_defect), 'pair_scaled_bound': str(active_pair_sum),
                                          'actual_survival': str(actual), 'proxy_survival': str(proxy)},
            'eta': str(eta), 'theta': str(theta), 'conditional_strict_Haar_coefficient': str(mass * theta / 270000),
            'lcm_countercontrol': {**counter, 'lcm': common, 'joint_activation': 1, 'h_lcm': 0,
                                  'h_endpoint_R': 1, 'h_endpoint_S': 1, 'positive_pair_price': str(lcm_pair_price)},
            'scope': 'Fixed outside-kernel and original-label pair checks; no enumeration of old activations. A single comparison witness rejects scalar-to-unit accounting for this law. The ordinary pair-implication proof covers all activations. No source producer, geometry, optimizer or Lean run, and no claim outside all522 methods.'}


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
    print(json.dumps({'original_classes': result['original_class_count'], 'lambda': result['lambda'],
                      'scalar_scaled_defect': result['single_comparison_witness']['scalar_scaled_defect'],
                      'pair_scaled_bound': result['single_comparison_witness']['pair_scaled_bound'],
                      'shared_M_unit_use': result['combined_payments']['M']['columns']['1'],
                      'eta': result['eta'], 'conditional_strict_Haar_coefficient': result['conditional_strict_Haar_coefficient']}, indent=2))


if __name__ == '__main__':
    main()
