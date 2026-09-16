#!/usr/bin/env python3
"""Complete PG1 11/13 criterion with one source event and every root floor.

Consumes hash-bound, previously verified profile tables and the exact zero
depth square improvement. All original labels and complete tails remain in
those tables. Recomputes the new grouped deletion queries and exhausts all
10000 independent root combinations, using rigorous separate bounds to prune.
The default action verifies; --write rebuilds the adjacent certificate.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import lcm
from pathlib import Path
import argparse
import importlib.util
import json
import numpy as np

HERE = Path(__file__).resolve().parent
NAMES = ('mod3_conditioned_geometry_certificate.json',
         'original9_conditioned_geometry_certificate.json',
         'pg1_joint_tail_certificate.json',
         'original9_convex_transfer_certificate.json',
         'pg1_signed_g2_certificate.json',
         'pg1_exact_zero_depth_certificate.json')


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def evaluate(directory):
    raw = {name: (directory / name).read_bytes() for name in NAMES}
    hashes = {name: sha256(value).hexdigest() for name, value in raw.items()}
    data = {name: json.loads(value) for name, value in raw.items()}
    source, old, joint, convex, signed, exact = (data[name] for name in NAMES)
    for name, stamp in joint['source_sha256'].items():
        require(hashes[name] == stamp, 'joint source hash: ' + name)
    require(signed['source_joint_sha256'] == hashes[NAMES[2]], 'signed source hash')
    for name, stamp in exact['source_sha256'].items():
        require(hashes[name] == stamp, 'exact zero source hash: ' + name)
    m, j, cx, sg, ex = (entry['result'] for entry in (old, joint, convex, signed, exact))
    spec = importlib.util.spec_from_file_location('pg1_common_floor_geometry', directory / 'verify_point_geometry.py')
    require(spec is not None and spec.loader is not None, 'explicit geometry module')
    pg = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(pg)
    case = next(row for row in source['cases'] if row['name'] == 'PG1')
    x = np.array(case['points'], dtype=np.int64)
    w = np.array(case['weight_numerators'], dtype=np.int64)
    den = case['weight_denominator']
    require(len(x) == len(w) == 75 and sum(map(int, w)) == den and np.all(w > 0), 'unchanged PG1 probability')
    require(case['points'] == [a for a in range(315) if all(a % d != r for d, r in case['family'])], 'actual PG1 support')
    require(len(case['family']) == len({d for d, _ in case['family']}) == 11, 'distinct original low labels')
    require(j['depth_box'] == [8, 5, 4], 'complete inherited source depth box')
    q0 = F(m['survival_lower'])
    require(q0 == F(j['source_survival_lower']) == F(ex['source_survival_lower']) > 0, 'one unchanged source survival')
    require(F(j['independent_tail_survival_lower']) > 0, 'positive independent physical 11/13 survival')
    prior = F(sg['Gamma13_upper'])
    C, K = F(149), F(297, 2)
    M, P = F(4, 3), F(1403, 630)
    c1, c2, ch, ck = F(4, 33), F(50, 2541), F(31, 5082), F(2, 847)
    require(ch == F(j['new_multiplier_Nge3_mean']) / 7
            and ck == (2 * F(j['new_multiplier_Nge3_mean']) - 5 * F(j['new_multiplier_Nge3_mass'])) / 7,
            'complete N>=3 multiplier tail')
    roots = [(i, a) for a in (1, 2, 5, 7, 8) for i in (1, 2)]
    square_rows = {(r['root3'], r['root9']): r for r in m['records']}
    exact_rows = {(r['root3'], r['root9']): r for r in ex['records']}
    hinge_rows = {(r['root3'], r['root9']): r for r in m['hinge2']['records']}
    joint_rows = {(r['final_root3'], r['final_root9']): r for r in j['records']}
    whole = {(r['charge_root3'], r['charge_root9']): r for r in j['unweighted_whole_cost']['records']}
    require(all(set(rows) == set(roots) and len(rows) == 10 for rows in (square_rows, exact_rows, hinge_rows, joint_rows, whole)),
            'all independent original-root pairs')
    sqU = {k: F(exact_rows[k]['new_U']) for k in roots}
    require(all(sqU[k] <= F(square_rows[k]['U']) for k in roots), 'improved unconditional square bounds')
    bs = {k: 1 + (x % 3 == k[0]).astype(int) + (x % 9 == k[1]).astype(int) for k in roots}
    gs = {k: ((x % 3 == k[0]) & (x % 9 == k[1])).astype(int) for k in roots}
    baseH = {k: F(hinge_rows[k]['lambda_upper']) for k in roots}
    U4base = q0 * F(cx['H4_upper'])
    ds, _, _, rem, *_ = pg.coeffs((8, 5, 4))
    rem[ds.index(35)] -= F(1, 4)
    require(min(rem) >= 0, 'complete nonnegative higher357 deletion remainder')
    group = pg.group_setup({'survivors': x.tolist(), 'points': case['old_points']}, (9, 45), 35)
    cylinders = [np.array([x % d == a for a in sorted(set(map(int, x % d)))], dtype=np.int64) for d in ds]
    cache, observations = {}, []

    def mean(values):
        return sum((F(int(a), den) * b for a, b in zip(w, values)), F())

    def retain(cost, upper):
        key = tuple(map(F, cost))
        if key in cache:
            require(cache[key] == upper, 'consistent inherited deletion value')
        cache[key] = upper

    def deletion(cost):
        key = tuple(map(F, cost))
        if key in cache:
            return cache[key]
        require(len(key) == len(x) and min(key) >= 0, 'nonnegative deletion cost')
        scale = lcm(*(a.denominator for a in key))
        integers = [int(a * scale) * int(b) for a, b in zip(key, w)]
        require(48 * sum(integers) < 2**63, 'exact signed64 grouped arithmetic')
        measure = np.array(integers, dtype=np.int64)
        best, _, _ = pg.group_oracle(measure, group)
        caps = [int((cy @ measure).max()) for cy in cylinders]
        upper = F(best['value'], 48 * den * scale) + sum((r * F(a, den * scale) for r, a in zip(rem, caps)), F())
        retain(key, upper)
        observations.append({'point_costs': list(map(str, key)), 'upper': str(upper),
                             'integer_scale': scale, 'group_numerator48': best['value'], 'cap_numerators': caps})
        return upper

    retain([1] * len(x), 1 - q0)
    for k in roots:
        r = square_rows[k]
        loss = F(r['criterion_excess']) + 33 - F(r['U'])
        require(sqU[k] + loss - 33 == F(exact_rows[k]['new_signed_excess']), 'same source square deletion')
        retain([33 - int(b * b) for b in bs[k]], loss)
        retain([444 - 148 * int(g) for g in gs[k]], 148 * F(hinge_rows[k]['weighted_deletion_upper']))
    for k, row in joint_rows.items():
        if 'geometry' not in row:
            continue
        weight = 149 - bs[k]**2
        for r in row['geometry']['records']:
            u = r['charge_root3'], r['charge_root9']
            retain([444 - int(a * g) for a, g in zip(weight, gs[u])], F(r['costs']['h2']['weighted_deletion']['upper']))
        retain([int(b * b - 1) for b in bs[k]], F(row['floor_increment_deletion']['upper']))

    Esq = {k: sqU[k] + deletion([33 - int(b * b) for b in bs[k]]) - 33 for k in roots}
    # Every summand uses this same source Q. The coefficient is negative,
    # so replacing Q by its lower bound q0 gives an upper pruning bound.
    A = 33 * P + (c2 + ch) * 444 + ck * 148 - K
    require(A < 0, 'negative source-Q coefficient')
    parameters, candidates = {}, []
    for final in roots:
        row = joint_rows[final]
        weight = 149 - bs[final]**2
        require(np.all(weight >= 0) and int(weight.max()) <= 148, 'actual final-root weight')
        if 'geometry' in row:
            geo = {(r['charge_root3'], r['charge_root9']): r for r in row['geometry']['records']}
            require(set(geo) == set(roots), 'complete weighted charge-root domain')
            H = {k: F(geo[k]['costs']['h2']['lambda_upper']) for k in roots}
            N2 = {k: F(geo[k]['costs']['n2']['lambda_upper']) for k in roots}
            U4, U1 = F(row['selected_lambda_H4']), F(row['selected_lambda_G1'])
        else:
            require(row['method'] == 'uniform final floor', 'known source cost method')
            H = {k: 148 * baseH[k] for k in roots}
            N2 = {k: 148 * F(whole[k]['costs']['n2']['lambda_upper']) for k in roots}
            U4 = 148 * U4base
            U1 = 148 * max(F(r['costs']['n1']['lambda_upper']) for r in whole.values())
        # Even when U is bounded by148 times the ordinary table, the actual
        # W-weighted cost still has the genuine floor W*g of its charge test.
        Rg = {k: deletion([444 - int(a * g) for a, g in zip(weight, gs[k])]) for k in roots}
        Rmass = deletion([int(b * b - 1) for b in bs[final]])
        EN = {k: N2[k] + Rg[k] - 444 for k in roots}
        EH = {k: H[k] + Rg[k] - 444 for k in roots}
        weight_mean = mean(list(map(int, weight)))
        EW = weight_mean + Rmass - 148
        constant = M * Esq[final] + U4 / 6 + c1 * U1 + ck * EW
        parameters[final] = (weight, H, N2, U4, U1, weight_mean)
        for h, u, v in product(roots, repeat=3):
            B = constant + (P - M) * Esq[h] + c2 * EN[u] + ch * EH[v]
            candidates.append((A * q0 + B, final, h, u, v, B))
    require(len(candidates) == 10000, 'four independent root pairs, no root identification')
    candidates.sort(reverse=True)
    observed_maximum = None
    examined, pruned = [], []
    for separate, final, h, u, v, B in candidates:
        if observed_maximum is not None and separate <= observed_maximum:
            pruned.append((separate, final, h, u, v))
            continue
        weight, H, N2, U4, U1, weight_mean = parameters[final]
        floor = [M * int(a*a) + (P-M) * int(b*b) + c2 * int(ww*g) + ch * int(ww*hh) + ck * int(ww)
                 for a, b, ww, g, hh in zip(bs[final], bs[h], weight, gs[u], gs[v])]
        require(max(floor) < K, 'positive complete source deletion score')
        U = M * sqU[final] + (P-M) * sqU[h] + U4 / 6 + c1 * U1 + c2 * N2[u] + ch * H[v] + ck * weight_mean
        value = U - K + deletion([K - f for f in floor])
        require(value <= separate, 'joint deletion dominated by its complete split bound')
        observed_maximum = value if observed_maximum is None else max(observed_maximum, value)
        examined.append({'final_roots': list(final), 'other_head_roots': list(h), 'G2_charge_roots': list(u), 'H2_charge_roots': list(v),
                         'source_integral_upper': str(U), 'split_upper': str(separate), 'joint_upper': str(value)})
    require(observed_maximum is not None and len(examined) + len(pruned) == 10000, 'complete finite maximization')
    maximum = observed_maximum
    Bmax = max(row[-1] for row in candidates)
    require(Bmax > 0, 'decreasing complete split bound after division by Q')
    # Q(E Z-K) has both upper bounds maximum and A*Q+Bmax. Preserve
    # this common Q: their quotient envelope is maximized at an endpoint
    # or their unique crossing, not by dividing a negative maximum by q0.
    survival_candidates = {q0, F(1)}
    crossing = (maximum - Bmax) / A
    if q0 <= crossing <= 1:
        survival_candidates.add(crossing)
    values = [(K + min(maximum, A * q + Bmax) / q, q) for q in sorted(survival_candidates)]
    upper, worst_q = max(values)
    require(upper < prior < C, 'strict improvement and negative final physical criterion')
    pruned_digest = sha256(json.dumps([[str(a), b, c, d, e] for a, b, c, d, e in pruned], separators=(',', ':')).encode()).hexdigest()
    return {'schema': 'erdos7-pg1-common-source-floor-v1', 'source_sha256': hashes,
            'source_survival_lower': str(q0), 'physical_floor_reference': str(C), 'source_reference': str(K),
            'depth_box': [8, 5, 4], 'coefficients': {'zero_head': str(M), 'other_heads': str(P-M),
            'H4': '1/6', 'G1': str(c1), 'G2': str(c2), 'H2_full_tail': str(ch), 'weight_mass': str(ck)},
            'root_pairs': list(map(list, roots)), 'root_combinations': len(candidates), 'joint_queries': examined,
            'separate_bound_pruned': len(pruned), 'pruned_bounds_sha256': pruned_digest,
            'new_deletions': observations, 'new_deletion_count': len(observations),
            'maximum_source_excess_upper': str(maximum), 'split_Q_coefficient': str(A), 'split_constant_max': str(Bmax),
            'common_Q_candidates': [{'Q': str(q), 'bound': str(v)} for v, q in values], 'worst_Q': str(worst_q),
            'Gamma13_upper': str(upper), 'prior_Gamma13_upper': str(prior), 'improvement': str(prior-upper),
            'scope': 'Unchanged PG1 probability and physical11/13 kernels; one actual higher357 event F and survival Q; all original labels and full357/11/13 tails; independent final, other-head, G2-charge and H2-charge roots. Input geometry is a separately verified hash-bound prerequisite.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE / 'pg1_common_source_floor_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = evaluate(args.source_directory)
    if args.write:
        args.certificate.write_text(json.dumps(result, indent=2) + '\n')
    else:
        require(result == json.loads(args.certificate.read_text()), 'complete deterministic common-floor replay')
    print(json.dumps({'status': 'verified', 'Gamma13_upper': result['Gamma13_upper'],
                      'Gamma13_decimal': float(F(result['Gamma13_upper'])),
                      'root_combinations': result['root_combinations'], 'joint_queries': len(result['joint_queries']),
                      'new_deletion_count': result['new_deletion_count']}))


if __name__ == '__main__':
    main()
