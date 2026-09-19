#!/usr/bin/env python3
"""Exact arithmetic for a quantitative neighborhood of square469/100.

The ordinary proof supplies arbitrary-label weighted deletion and all-depth
validity. This checks every finite dual coefficient, exact full tail formulas,
the complete error inventory and a strict nonzero neighborhood. No optimizer,
finite truncation claim or Lean verification is involved. Use python3 -I -O.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {
    'frontier/endpoint_linear_neighborhood.py': 'e9d1eb6487f95874b2c577496b41083ff140138ef5a59d630144d1c72aae279a',
    'certificates/source_norms/endpoint_linear_neighborhood.json': '58dbc7cfd2ee535340c6b73bf44bf2df25d9949303052600f6f88a2504f73221',
    'frontier/endpoint_square_common_pure3.py': '0e8f5204d947d3652178ff060be6c10539185a7f15666738249f67e3e229b4df',
    'certificates/source_norms/endpoint_square_common_pure3.json': '8b23c3cc87d5ddc40c0084ce42d6464f3c18d295451b5da994fa828cd21f1b69',
    'frontier/shared_square_barrier.py': '6bc57d9b93bc583bbced72092f722a4369743013e0dd9eeea0703f01a3bf10a1',
}
CERTIFICATE = 'certificates/source_norms/endpoint_square_neighborhood.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable mathematical dependency')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def weighted_geometric(q, start, offset):
    require(0 < q < 1 and start >= 0 and 2*start+offset >= 0, 'Positive weighted geometric tail')
    return q**start/(1-q)*(2*(start+q/(1-q))+offset)


def weighted_min_tail(epsilon, factor, coefficient, prime, start, offset):
    """Complete sum (2j+offset)*min(factor*epsilon, coefficient*prime^-j)."""
    require(epsilon >= 0 and factor > 0 and coefficient > 0, 'Nonnegative mass-defect tail')
    if epsilon == 0:
        return F(0), start
    level = factor*epsilon
    entrance = start
    while coefficient*F(1, prime**entrance) > level:
        entrance += 1
        require(entrance <= 10000, 'Finite exact tail entrance found')
    prefix = level*(entrance-start)*(start+entrance-1+offset)
    rest = coefficient*weighted_geometric(F(1, prime), entrance, offset)
    return prefix+rest, entrance


def dual_checks(base, common):
    linear = common.load(base, 'frontier/endpoint_linear_numerator.py', 'square_neighborhood_linear59')
    head = common.load(base, 'frontier/endpoint_square_coherent_head.py', 'square_neighborhood_head63')
    ends = [linear.slot_matrices(x) for x in linear.LATE_INTERVAL]
    entries = [head.scaled(max(t[1][c][j] for t in ends)) for c, j in product(range(5), repeat=2)]
    rows = [head.scaled(x) for x in linear.endpoint_tables()['all_positive5_cell_caps']]
    total = head.scaled(F(3, 20))
    digest, maximum, count = sha256(), 0, 0
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        coefficients = head.coefficients(layout, linear.ROOT)
        require(1 <= min(coefficients) <= max(coefficients) <= 36, 'Every shallow square is bounded by36')
        dual = head.primal_dual([x-1 for x in coefficients], entries, rows, total)
        multipliers = [dual['gamma']]+dual['beta']+dual['alpha']
        require(min(multipliers) >= 0 and max(multipliers) <= 35, 'Every inherited feasible dual coefficient at most35')
        maximum = max(maximum, max(multipliers))
        digest.update(json.dumps([layout, dual], separators=(',', ':'), sort_keys=True).encode())
        count += 1
    old = json.loads((base/'certificates/source_norms/endpoint_square_coherent_head.json').read_text())
    require(count == 12500 and digest.hexdigest() == old['layout_bounds']['all_primal_dual_sha256'],
            'All inherited exact dual and primal equalities recovered')
    return {'count': count, 'maximum_multiplier': maximum, 'sha256': digest.hexdigest()}


def calculate(base):
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin, 'Pinned source '+path)
    common = module('square_neighborhood_common64', base/'frontier/endpoint_square_common_pure3.py')
    linear66 = module('square_neighborhood_linear66', base/'frontier/endpoint_linear_neighborhood.py')
    barrier = module('square_neighborhood_square_barrier', base/'frontier/shared_square_barrier.py')
    for path, pin in common.PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin, 'Inherited endpoint input '+path)
        used[path] = pin
    square = json.loads((base/'certificates/source_norms/endpoint_square_common_pure3.json').read_text())
    require(square['source_vertex'] == 404 and square['carrier'] == [0, 1]
            and F(square['full_square_upper']) == F(469, 100)
            and F(square['surviving_mass']) == F(3, 20), 'Identical endpoint class')
    dual = dual_checks(base, common)
    delta_entry = (F(14), F(277), F(2, 5))
    delta_rows = (F(10), F(20), F(2))
    delta_mass = (F(8, 5), F(1), F(0))
    head_error = tuple(35*(a+b+c) for a, b, c in zip(delta_entry, delta_rows, delta_mass))
    require(head_error == (F(896), F(10430), F(84)), 'Whole-matrix LP capacity perturbation')
    require(weighted_geometric(F(1, 3), 3, 7) == F(7, 9), 'Complete unbounded-head affine weight')
    beta = (F(2), F(60), F(0))
    g = (F(2), F(260), F(2, 5))
    require(200+60 <= g[1] and F(35, 6)*10 <= beta[1], 'Weighted source and selected-deletion errors')
    zero_error = tuple(a+F(7, 9)*b for a, b in zip(head_error, g))
    zero_rounded = (F(900), F(10700), F(85))
    require(all(x <= y for x, y in zip(zero_error, zero_rounded)), 'Complete surviving expanded-head perturbation')
    raw_error = (36*14+F(7, 9)*2, 36*76+F(7, 9)*60, F(0))
    raw_rounded = (F(510), F(2800), F(0))
    require(all(x <= y for x, y in zip(raw_error, raw_rounded)), 'Complete raw expanded-head perturbation')
    cap_categories = {
        'unit': (F(8, 5), F(1), F(0)),
        '3': (F(6), F(12), F(6, 5)),
        '9': (F(10), F(20), F(2)),
        '5': (F(42), F(900), F(3)),
        '15': (F(126), F(2700), F(9)),
        'deep3': (F(4, 9), F(0), F(8, 45)),
        'deep5': (F(11, 40), F(0), F(11, 100)),
        '3_times_deep5': (F(33, 40), F(0), F(0)),
        '9_times5': (F(35, 8), F(0), F(0)),
        'deep35': (F(0), F(0), F(0)),
    }
    raw_cap_change = 1+3+5+F(4, 9)+F(7, 8)+F(21, 8)+F(35, 8)
    require(raw_cap_change == F(1247, 72), 'Complete raw35 weighted cap perturbation')
    cap_categories['positive7'] = (F(2, 3)*raw_cap_change, F(0), F(0))
    cap_totals = tuple(sum(v[j] for v in cap_categories.values()) for j in range(3))
    cap_rounded = (F(204), F(3633), F(16))
    require(all(x <= y for x, y in zip(cap_totals, cap_rounded)), 'Complete unreplaced-pair perturbation')
    Rstar = F(square['raw_head_upper'])
    require(F(1, 4) <= Rstar < F(5, 2) and Rstar/F(1, 4) <= 10,
            'Common-layout Cauchy perturbation ratio')
    require(F(2, 5)*2+F(4, 15) == F(16, 15), 'Complete cross-depth perturbation coefficient')
    exact_total = tuple(a+b+F(16, 15)*c for a, b, c in zip(cap_rounded, zero_rounded, raw_rounded))
    require(exact_total == (F(1648), F(51959, 3), F(101)), 'Combined exact rational perturbation coefficients')
    rounded_total = (F(1650), F(17400), F(101))
    require(all(x <= y for x, y in zip(exact_total, rounded_total)), 'Simple neighborhood coefficients')
    root_bound_T = 4*weighted_geometric(F(3, 5), 3, 7)
    root_bound_3 = weighted_geometric(F(29, 50), 3, 1)
    root_bound_5 = weighted_geometric(F(1, 2), 2, 1)/4
    require(3*F(3, 5)**2 > 1 and 11 < 4**2 and root_bound_T == F(864, 25) < 35,
            'Complete head-tail square-root estimate')
    require(3*F(29, 50)**2 > 1 and F(4, 5) < 1 and root_bound_3 < 5,
            'Complete pure3 pair-tail square-root estimate')
    require(5*F(1, 2)**2 > 1 and 18 > 4**2 and root_bound_5 == F(7, 8) < 1,
            'Complete pure5 pair-tail square-root estimate')
    tail_cases = []
    for denominator in (100, 1000, 10000, 1000000, 1000000000):
        root_epsilon = F(1, denominator)
        epsilon = root_epsilon**2
        entries = []
        for factor, coefficient, prime, start, offset, root_bound in (
                (F(11), F(1), 3, 3, 7, 35),
                (F(4), F(1, 5), 3, 3, 1, 5),
                (F(1), F(1, 18), 5, 2, 1, 1)):
            value, entrance = weighted_min_tail(epsilon, factor, coefficient, prime, start, offset)
            cut = entrance+4
            direct = sum((2*j+offset)*min(factor*epsilon, coefficient*F(1, prime**j))
                         for j in range(start, cut))
            direct += coefficient*F(1, prime**cut)*F(prime, prime-1)*(2*cut+offset+F(2, prime-1))
            require(value == direct and value <= root_bound*root_epsilon, 'Independent full weighted minimum tail')
            entries.append({'value': value, 'entrance': entrance})
        tail_cases.append({'epsilon': epsilon, 'sqrt_epsilon': root_epsilon, 'T_T3_T5': entries})
    require(weighted_min_tail(F(0), F(11), F(1), 3, 3, 7)[0] == 0, 'Zero-defect complete tail')
    tau, epsilon, kappa, root_epsilon = F(1, 10**6), F(1, 10**12), F(1, 10**6), F(1, 10**6)
    phi = 1650*tau+17400*epsilon+101*kappa+41*root_epsilon
    G = barrier.SOURCE_NORM
    require(G == F(102715, 2916), 'Specified inherited uniform square norm')
    gain = G*F(3, 20)-F(469, 100)-F(8, 5)*G*tau-phi
    require(gain > F(1, 2), 'Strict full-box improvement over the inherited uniform norm')
    witness = None
    for height in range(3, 61):
        value = linear66.finite_approach(height)
        if value['tau'] <= tau and value['epsilon'] <= epsilon and value['kappa'] <= kappa:
            witness = value
            break
    require(witness is not None, 'An explicit actual finite construction enters the new box')
    return {'schema': 'erdos7-endpoint-square-neighborhood-v1', 'source_vertex': 404, 'carrier': [0, 1],
            'source_sha256': used, 'baseline_square_upper': F(469, 100),
            'guard': {'tau': F(1, 1000), 'epsilon': F(1, 10000)},
            'all_dual_coefficients': dual, 'head_error': head_error,
            'expanded_zero_head_error': zero_error, 'expanded_raw_head_error': raw_error,
            'pair_cap_categories': cap_categories, 'pair_cap_error': cap_totals,
            'common_cauchy_error_coefficient': F(16, 15),
            'exact_tau_epsilon_kappa_coefficients': exact_total,
            'Phi': {'tau': 1650, 'epsilon': 17400, 'kappa': 101, 'sqrt_epsilon': 41},
            'tail_sqrt_bounds': (root_bound_T, root_bound_3, root_bound_5), 'complete_tail_cases': tail_cases,
            'improvement_box': {'tau': tau, 'epsilon': epsilon, 'kappa': kappa},
            'box_Phi': phi, 'inherited_uniform_square_norm': G,
            'box_improvement_over_inherited_norm': gain, 'actual_finite_box_witness': witness,
            'signed_margin': '45*S - 469/100 - Phi(tau,epsilon,kappa)',
            'scope': ('Exact arithmetic for an ordinary uniform finite-neighborhood square theorem. '
                      'All original residues remain independent; weighted min-geometric tails are complete. '
                      'The witness uses the closed profile50 construction formulas, not its huge CRT period. '
                      'No global K, physical denominator bound, Lean result or unrestricted Erdos7 resolution.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    if args.check:
        require(json.loads((args.base/CERTIFICATE).read_text()) == result, 'Exact canonical certificate reconstruction')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS:12500 bounded exact LP duals, complete weighted geometric tails and explicit square neighborhood.')
    print('Square469/100+Phi; specified box improves inherited G*S by more than1/2; actual finite witness height '
          +str(result['actual_finite_box_witness']['height'])+'.')


if __name__ == '__main__':
    main()
