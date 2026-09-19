#!/usr/bin/env python3
"""Exact constants for the quantitative endpoint linear-neighborhood proof.

The ordinary proof supplies arbitrary-label geometry and all-depth bounds.
This program verifies the rational constants, retained geometric tails,
the inherited actual identity-cost formula, and a nonempty neighborhood.
It neither enumerates all covering families nor proves the ordinary argument.
Run with python3 -I -O. No third-party packages or assert validation.
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
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'frontier/endpoint_linear_numerator.py': '5c83f0a6277079323120ce0a31ac220c884f92ff555506f9dcaf926d3335e133',
    'frontier/full_linear_carrier_frontier.py': '98cbec50d807ed9208504c8cd2384659a4300d6909d54414e5e2156285298888',
    'frontier/source_barrier_saturation.py': '92076ee71a6be16655bbe5c2ac223db6502da1ab5c3553a7f83bb555dbbb8363',
    'frontier/sharp_source_mass_endpoints.py': '79bb947d96c36895069f58568d7a5de2c22aa561753f03352e9eb741313147d9',
}
ROOT = (0, 0, 1, 1, 1)
ETA = tuple(map(F, ('1/18', '1/9', '1/9', '1/9', '1/9')))
MASS = tuple(map(F, ('1/24', '1/12', '1/36', '1/24', '1/18')))
DENSITY = tuple(map(F, ('3/4', '3/4', '1/4', '1/2', '1/2')))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(base, name, key):
    path = base/name
    require(sha256(path.read_bytes()).hexdigest() == PINS[name], 'Pinned source '+name)
    spec = importlib.util.spec_from_file_location(key, path)
    require(spec is not None and spec.loader is not None, 'Loadable source '+name)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def roots(values):
    return max(sum(values[:2]), sum(values[2:]))


def complete_cap(dat):
    d, n, eta, _, _ = dat
    return roots(n)+max(n)+max(d)/18+(sum(eta)+roots(eta)+max(eta))/4+F(1, 72)


def min_geometric(constant, geometric, prime, start):
    """Exact sum from start to infinity of min(constant, geometric*p^-j)."""
    require(constant >= 0 and geometric > 0 and prime > 1 and start >= 0, 'Tail domain')
    if constant == 0:
        return F(0), start
    entrance = start
    while geometric*F(1, prime**entrance) > constant:
        entrance += 1
        require(entrance <= 10000, 'Finite exact geometric crossing')
    tail = geometric*F(1, prime**entrance)/(1-F(1, prime))
    return (entrance-start)*constant+tail, entrance


def exact_old_U(dat, b, c, bases):
    d, n, eta, s, _ = dat
    return (6*s/5+complete_cap(dat)/5
            +sum(x*(v-1) for x, v in zip(n, b))+max(d)/18
            +sum(x*v for x, v in zip(eta, c))/5
            +max(sum(x*v for x, v in zip(eta, t)) for t in bases)/20+F(1, 72))


def old_identity_checks(base):
    saturation = load(base, 'frontier/source_barrier_saturation.py', 'neighborhood_saturation')
    full = load(base, 'frontier/full_linear_carrier_frontier.py', 'neighborhood_full49')
    engine = saturation.Experiment(base)
    source = engine.source
    ci = 40
    spec = engine.specs[ci]
    require([source.zero5_cost(spec['tag'], v) for v in range(1, 20)] == list(range(1, 20)),
            'Actual live cost is identity f(v)=v')
    require(F(engine.thresholds[ci]['constant']) == 6, 'Actual live barrier is6')
    parameters = [engine.parameters[j] for j in (404, 398, 402)]
    left, right = engine.parameters[398], engine.parameters[404]
    parameters.append(tuple(tuple((a+b)/2 for a, b in zip(x, y)) if isinstance(x, tuple)
                            else (x+y)/2 for x, y in zip(left, right)))
    checked, rows = 0, []
    for parameter in parameters:
        dat = source.data(parameter)
        d, n, eta, s, D = dat
        require(complete_cap(dat) == 5*(s-D), 'Complete old cap formula')
        positive = engine.positive(ci, eta)
        common = source.zero7_raw(spec['tag'], dat)-source.zero5_raw(spec['zero'], dat)
        require(common == 6*s/5+complete_cap(dat)/5, 'Identity positive-seven complement')
        rebuilt = [None]*18
        for item in spec['layouts']:
            b = item['baseline']
            base_U = common+sum(n[j]*item['psi'][j]+eta[j]*item['correction'][j]
                                for j in range(5))
            base_U += max(source.zero5_common_deep(spec['zero'], b[j], d[j]) for j in range(5))
            for li, c in enumerate(source.BASES):
                U = exact_old_U(dat, b, c, source.BASES)
                require(U == base_U+positive[li], 'Exact identity layout formula')
                k = tuple(F(6-v) for v in b)
                a = tuple(k[j]*n[j]-c[j]*eta[j]/5 for j in range(5))
                z = tuple(k[j]*d[j]-F(c[j], 5) for j in range(5))
                w = tuple(9*eta[j]*k[j] for j in range(5))
                T = F(13, 243)*max(z)+F(1, 486)*max(k[j]*d[j] for j in range(5))
                T += (sum(w)+roots(w)+max(w))/36+max(k)/72
                for pos, (root, cell) in enumerate(full.CARRIERS):
                    carrier = ((sum(a[j] for j in range(5) if ROOT[j] == root) if root >= 0 else 0)
                               +(a[cell] if cell >= 0 else 0))
                    margin = 6*s-U-(carrier+T)/5
                    rebuilt[pos] = margin if rebuilt[pos] is None else min(rebuilt[pos], margin)
                checked += 1
        actual = full.linear_direction(engine, dat, ci)
        require(rebuilt == actual['conditional'], 'All18 actual full49 conditional margins recovered')
        rows.append({'source_data': dat, 'conditional_margins': rebuilt})
    require(checked == 400 and rows[0]['conditional_margins'][8] == F(4507, 24300),
            'Published endpoint old margin and all400 layout checks')
    return {'layout_checks': checked, 'carrier_checks': 18*len(rows), 'rows': rows}


def finite_approach(height):
    """Profile50's closed formulas for its actual finite off-diagonal family."""
    t = F(1, 18)-F(1, 2*3**height)
    q = F(1, 4)-F(1, 4*5**height)
    eta = (F(1, 9)-t,)+(F(1, 9),)*4
    d = (1-q, 1-q, 1-3*q, 1-2*q, 1-2*q)
    n = tuple(eta[j]*d[j]-(t*q if j == 3 else 0) for j in range(5))
    s = sum(n)
    require(s == F(5, 9)-t-q, 'Independent complete finite source-mass formula')
    dat = (d, n, eta, s, F(0))
    D = s-complete_cap(dat)/5
    seven = (1-F(1, 7**height))/(5+F(1, 7**height))
    S = s-seven*(F(1, 3)+2*q/3)
    delta_s = 3*(F(1, 4)-q)
    delta_L = F(1, 72)-t*q
    tau = (sum(abs(a-b) for a, b in zip(eta, ETA))
           +sum(abs(a-b) for a, b in zip(n, MASS))
           +sum(abs(a-b) for a, b in zip(d, DENSITY))+delta_s+delta_L)
    epsilon, kappa = S-D, F(1, 7**height)
    require(min(tau, epsilon, kappa) > 0, 'Finite family stays off the limiting endpoint')
    return {'height': height, 'original_nonunit_labels': (height+1)**3-1,
            's': s, 'S': S, 'D': D,
            'tau': tau, 'epsilon': epsilon, 'kappa': kappa,
            'inside_improvement_box': tau <= F(1, 1000) and epsilon <= F(1, 1000000)
                                      and kappa <= F(1, 1000)}


def calculate(base):
    endpoint = load(base, 'frontier/endpoint_linear_numerator.py', 'neighborhood_endpoint59')
    endpoint_result = endpoint.endpoint_tables()
    require(endpoint_result['linear_numerator_upper'] == F(1157, 1800), 'Exact endpoint recovered')
    tau, eps = F(1, 1000), F(1, 10000)
    eta2, h1, rootgap, h = F(1, 9)-tau, F(1, 3)-tau, F(1, 6)-tau, F(1, 2)
    ell = 35*eps/6
    require(tau < F(1, 25) and eta2 >= F(1, 10) and rootgap >= F(1, 9),
            'Strict shallow-slot and ternary-root neighborhood guards')
    require(ell < min(h/5, h1/5, eta2/5, h/25), 'H differs from all four source parents')
    require(F(6, 35)*h/5 > eps, 'First forbidden cofactor5 cannot be missing')
    gaps = (h/5, h1/5, eta2/5, h/25, rootgap/5, h1/25)
    require(min(gaps) >= F(1, 100) and F(1, 3) <= 3*rootgap,
            'Bad-carrier loss and arbitrary ternary transfer constants')
    require(12*F(35, 6) == 70 and 9 <= 14 and 70 <= 76, 'Source-table error bound')
    require(76+201 <= 300 and F(2, 5) <= 1, 'Two selected test-cap error bounds')
    categories = {
        'test3': (F(11, 120), F(2), F(4), F(2, 5)),
        'test9': (F(2, 45), F(2), F(4), F(2, 5)),
        'test5': (F(1, 18), F(14), F(300), F(1)),
        'test15': (F(1, 25), F(14), F(300), F(1)),
        'deep3': (F(11, 360), F(1, 18), F(0), F(1, 45)),
        'deep5': (F(1, 45), F(1, 20), F(0), F(1, 50)),
        '3_times_deep5': (F(1, 60), F(1, 20), F(0), F(0)),
        '9_times5': (F(1, 36), F(1, 4), F(0), F(0)),
        'deep35': (F(1, 72), F(0), F(0), F(0)),
        'positive7': (F(3, 20), F(4, 5), F(0), F(0)),
    }
    totals = tuple(sum(row[j] for row in categories.values()) for j in range(4))
    require(totals[0] == F(887, 1800) and totals[1] <= 34
            and totals[2] == 608 and totals[3] <= 3, 'Complete test inventory and errors')
    require(F(3, 20)+totals[0] == F(1157, 1800), 'Absolute endpoint numerator')
    require(34+F(8, 5) <= 36 and 34+5*F(8, 5) == 42, 'Absolute numerator and margin errors')
    require(F(3) > F(25, 9), 'sum a>=3 of 3^-a/2 is less than1/2')
    require(F(5) > 4, 'sum b>=2 of 5^-b/2 is less than1/2')
    tail_rows = []
    for den in (100, 1000, 10000, 100000, 1000000):
        square_root = F(1, den)
        epsilon = square_root**2
        r3, n3 = min_geometric(4*epsilon, F(1, 5), 3, 3)
        r5, n5 = min_geometric(epsilon, F(1, 18), 5, 2)
        require(r3 <= square_root and r5 <= square_root, 'Complete rational min-geometric tail')
        # Independent tail order: split after both exact entrances and sum
        # the prefix explicitly; the remaining tail is geometric there.
        cut = max(n3, n5)+3
        independent3 = sum(min(4*epsilon, F(1, 5*3**a)) for a in range(3, cut))
        independent3 += F(1, 5*3**cut)/(1-F(1, 3))
        independent5 = sum(min(epsilon, F(1, 18*5**b)) for b in range(2, cut))
        independent5 += F(1, 18*5**cut)/(1-F(1, 5))
        require((r3, r5) == (independent3, independent5), 'Independent complete-tail evaluation')
        tail_rows.append({'epsilon': epsilon, 'R3': r3, 'R5': r5, 'sqrt_epsilon': square_root,
                          'geometric_entrances': (n3, n5)})
    require(min_geometric(F(0), F(1, 5), 3, 3)[0] == 0, 'Zero slack tail')
    lipschitz_U = (F(18, 5), F(1, 15), F(9, 10))
    lipschitz_cap = (F(2), F(1, 18), F(99, 100))
    require(max(lipschitz_U) <= 4 and max(lipschitz_cap) <= 2, 'Uniform layout Lipschitz bounds')
    require((F(20, 9)+F(4, 15))/5 == F(112, 225) < F(1, 2), 'Whole carrier oscillation')
    old = old_identity_checks(base)
    gap = F(3487, 48600)
    corner_error = 54*F(1, 1000)+608*F(1, 1000000)+F(7, 2)*F(1, 1000)+2*F(1, 1000)
    remaining_gap = gap-corner_error
    require(corner_error == F(15027, 250000) and remaining_gap == F(707189, 60750000)
            and remaining_gap > F(1, 100), 'Strict rational whole-neighborhood improvement')
    approaches = [finite_approach(height) for height in range(3, 14)]
    require(any(row['inside_improvement_box'] for row in approaches), 'Explicit finite families enter the box')
    constructor = load(base, 'frontier/sharp_source_mass_endpoints.py', 'neighborhood_actual_family')
    finite_checks = []
    for height in (3, 4):
        actual = constructor.check(height, 'off-diagonal')
        formula = next(row for row in approaches if row['height'] == height)
        require(all(F(actual[key]) == formula[key] for key in ('s', 'S', 'D')),
                'Actual finite source and original mixed-seven deletion match the formulas')
        require(F(actual['empty_cap_weight']) == formula['kappa'], 'Actual carrier deviation')
        finite_checks.append(actual)
    return {'schema': 'erdos7-endpoint-linear-neighborhood-v1', 'source_sha256': PINS,
            'source_vertex': 404, 'carrier': [0, 1], 'cost': 'f(v)=v', 'barrier': 6,
            'guards': {'tau': tau, 'epsilon': eps, 'eta2_lower': eta2,
                       'root_gap_lower': rootgap, 'H_loss_upper': ell, 'bad_carrier_gaps': gaps},
            'test_categories': categories, 'summed_constants': totals,
            'numerator_errors': {'tau': 36, 'epsilon': 609, 'kappa': 3, 'sqrt_epsilon': 2},
            'margin_errors': {'tau': 42, 'epsilon': 608, 'kappa': 3, 'sqrt_epsilon': 2},
            'complete_tail_checks': tail_rows, 'old_U_lipschitz': lipschitz_U,
            'old_cap_lipschitz': lipschitz_cap, 'old_identity_formula': old,
            'improvement_box': {'tau': F(1, 1000), 'epsilon': F(1, 1000000), 'kappa': F(1, 1000)},
            'box_corner_error': corner_error, 'box_guaranteed_margin_improvement': remaining_gap,
            'finite_approaching_parameters': approaches,
            'finite_original_label_checks': finite_checks,
            'scope': ('Exact arithmetic for an ordinary explicit-neighborhood proof preserving arbitrary '
                      'original test residues and complete exponent tails. Finite approach rows evaluate '
                      'the closed profile50 construction formulas, not giant-period CRT enumerations. '
                      'No global K improvement, unrestricted Erdos7 resolution, or Lean verification.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    if args.check:
        certificate = args.base/'certificates/source_norms/endpoint_linear_neighborhood.json'
        require(json.loads(certificate.read_text()) == result, 'Exact certificate reconstruction')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    first = next(row for row in result['finite_approaching_parameters'] if row['inside_improvement_box'])
    print('PASS: explicit neighborhood numerator and margin, complete tails, 400 actual old layout checks.')
    print('Whole-box margin improvement707189/60750000 >1/100; first tested finite height '+str(first['height'])+'.')


if __name__ == '__main__':
    main()
