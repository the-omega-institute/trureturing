#!/usr/bin/env python3
"""Exact arithmetic for the ordinary whole-J source-neighborhood theorem."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_source_labelwise_neighborhood.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/j-geometry/j_face_alignment.py': '05074f0937efcb2cccc1a172e0717b89656f976d3e50543d31a27e7591b927ab',
    'frontier/j-geometry/j_face_surplus_transport.py': '8caed7decd0cd0f61536433b48118d97cdd96bb302f4bf4835b1fac428a31d05',
    'frontier/retained-transport/finite_source_face_transport.py': '04c99f1a0c6e1781734531923705863fbc9843c610f6d4933a81c89429aa5291',
    'frontier/endpoint-bounds/endpoint_linear_neighborhood.py': 'f8921b87de7b31cf834ef0c1fdd3df4802266e0dc990b19d86bf666221df235d',
    'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def complete_B1(e):
    """Finite correction to the entire geometric sum, excluding the unit."""
    e = F(e)
    require(e >= 0, 'Nonnegative shared error')
    if e == 0:
        return {'value': F(0), 'correction_labels': 0}
    value, count, a = F(7, 8), 0, 0
    while F(1, 3**a) >= e:
        b = 0
        while F(1, 3**a*5**b) >= e:
            if a+b:
                value -= F(1, 3**a*5**b)-e
                count += 1
            b += 1
        a += 1
    return {'value': value, 'correction_labels': count}


def independent_B1(e):
    """Sum each retained a-row with its full b-tail, then the full a-tail."""
    e = F(e)
    if e == 0:
        return F(0)
    value, a = F(0), 0
    while F(1, 3**a) > e:
        b = int(a == 0)
        while F(1, 3**a*5**b) > e:
            value += e
            b += 1
        value += F(5, 4*3**a*5**b)
        a += 1
    value += F(15, 8*3**a)
    # If a=0 all rows were placed in the tail, including the unit.
    if a == 0:
        value -= 1
    return value


def guard_and_prices():
    d = F(1, 1000)
    hmin, hmax = F(1, 2), F(1, 2)+d/18
    h0max, h1min = F(1, 6)+d/18, F(1, 3)-d/18
    emin = F(1, 9)-d/18
    require(h1min > h0max and F(1, 3) <= 3*(h1min-h0max),
            'Uniform wrong-root deficiency multiplier three')
    require(d/4 < F(1, 25) and 3*d/4 < F(1, 18),
            'Original first5/15/45/25 and existing packing domain')
    gaps5 = (hmin/5, h1min/5, emin/5, hmin/25)
    gaps15 = (h1min/5, emin/5, h1min/25, (h1min-h0max)/5)
    require(min(gaps5) >= F(1, 50) and min(gaps15) >= F(1, 100),
            'Four actual source slots force positive wrong-carrier gaps')
    require(5*d < min(F(1, 50), hmin/5, h1min/5, emin/5)
            and h1min >= F(1, 4) and hmax <= F(5, 9),
            'Best H, packing guard and root-wide Q prices')
    require(F(50, 9) <= 10 and F(100, 15) <= 10,
            'Actual missing target sections fit the two ten-times prices')
    require(F(1, 90)+F(5, 12) <= 1 and F(20, 9) <= 3
            and F(5, 72) <= 1, 'Weighted Q and incomplete late-B source prices')
    require(F(17, 90)+F(1, 180) == F(7, 36) <= 1,
            'Single enlarged capacity budget')
    prices = {'test3': (2, 3), 'test9': (2, 3), 'pure3_deep': (3, 3),
              'test5': (4, 35), 'test15': (3, 30), 'pure5_deep': (1, 1)}
    for name, (dcost, rcost) in prices.items():
        require(dcost+rcost <= 100, 'Uniform original-label excess '+name)
    require(F(1, 18)+F(1, 90)+F(1, 15) == F(2, 15),
            'Deep5 coefficient perturbation')
    norm_price = F(1, 2)+F(1, 9)+F(13, 4)
    old_price = 12*norm_price+F(1, 2)
    require(norm_price == F(139, 36) and old_price < 47 < 50,
            'Full-source fixed-layout and actual carrier continuity')
    cap_price = 2*F(1, 2)+F(5, 4)/18+3*F(1, 9)/4
    positive7_price = (F(1, 2)+cap_price)/5
    D_price = F(1, 2)+cap_price/5
    require((cap_price, positive7_price, D_price) ==
            (F(83, 72), F(119, 360), F(263, 360)), 'Complete source cap perturbations')
    require(5*D_price+positive7_price == F(239, 60)
            and F(239, 60)+50 <= 54, 'Margin and old49 replacement prices')
    return {'domain_delta_plus_rho': d, 'wrong5_gaps': gaps5, 'wrong15_gaps': gaps15,
            'label_delta_R_prices': prices, 'uniform_error_coefficient': 100,
            'capacity_extra_delta': F(7, 36), 'source_cap_delta': cap_price,
            'positive7_delta': positive7_price, 'mass_lower_delta': D_price,
            'old_margin_delta': old_price, 'rounded_replacement_delta': 54}


def finite_family(source, N):
    """Profile50's genuine finite original family with all nominal tails."""
    t3 = F(1, 18)-F(1, 2*3**N)
    q5 = F(1, 4)-F(1, 4*5**N)
    v7 = F(1, 7**N)
    parameter = ((9*t3, F(0), F(0), F(0), F(0)), (F(0), q5),
                 (F(0), F(0), q5, F(0), F(0)),
                 (F(0), F(0), F(0), t3*q5, F(0)), 1-q5)
    d, n, eta, s, D = source.data(parameter)
    require(s == F(5, 9)-t3-q5, 'Original finite source mass')
    C = 5*(s-D)
    rmax = max(sum(n[:2]), sum(n[2:]))
    pure_tail_cap = C-rmax-max(n)
    chosen_carrier = sum(n[:2])+n[1]
    Cpi = pure_tail_cap+(1-v7)*chosen_carrier
    S0 = s-Cpi/5
    S = s-(1-v7)/(5+v7)*(F(1, 3)+2*q5/3)
    delta = 1-(18*t3)**2*(4*q5)**4*(1-v7)
    rho = S-S0
    require(0 <= S0-D <= 17*delta/90 and rho >= 0,
            'Actual common carrier and survivor slack')
    inside = delta <= F(1, 10**8) and rho <= F(1, 10**8)
    require(inside, 'Explicit finite family enters the full source rectangle')
    reserve = F(79, 1944)-54*delta-complete_B1(100*(delta+rho))['value']
    require(reserve > F(1, 25), 'Positive old49 replacement on actual finite source')
    return {'height': N, 'original_labels': (N+1)**3-1, 'delta': delta, 'rho': rho,
            'S': S, 'S0': S0, 'D': D, 'inside_source_surplus_box': inside,
            'old49_replacement_reserve_lower': reserve}


def calculate(base):
    for path, pin in PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin, 'Pinned input '+path)
    face = module('j136_face', base/'frontier/j-geometry/j_face_alignment.py')
    face_result = face.calculate(base)
    require(face_result['linear_upper'] == '16/25'
            and face_result['old49_replacement_reserve'] == '79/1944',
            'Complete whole-face caps and old-layout comparison')
    surplus = module('j136_surplus', base/'frontier/j-geometry/j_face_surplus_transport.py')
    surplus.coefficient_checks()
    source = module('j136_source', base/'verify_joint_frontier.py')
    prices = guard_and_prices()
    errors = (F(0), F(1, 10**12), F(1, 500000), F(1, 10000),
              F(1, 1000), F(2, 45), F(1, 3), F(1), F(2))
    tails = []
    for e in errors:
        result = complete_B1(e)
        require(result['value'] == independent_B1(e), 'Two complete infinite-tail evaluations')
        tails.append({'error': e, **result})
    ebox = F(1, 500000)
    B = complete_B1(ebox)
    reserve = F(79, 1944)-F(54, 10**8)-B['value']
    require(B['value'] == F(296704261, 2214337500000)
            and reserve == F(358752149987, 8857350000000)
            and reserve > F(1, 25), 'Whole nonzero rectangle by monotonicity')
    return encode({'schema': 'erdos7-j-source-labelwise-neighborhood-v1', 'source_sha256': PINS,
                   'domain_and_prices': prices, 'complete_B1_checks': tails,
                   'box': {'delta_max': F(1, 10**8), 'rho_max': F(1, 10**8),
                           'shared_error_max': ebox, 'tail_at_corner': B,
                           'reserve_lower': reserve},
                   'actual_finite_sources': [finite_family(source, N) for N in (20, 21, 24)],
                   'scope': 'Ordinary continuous whole-J-source theorem with exact arithmetic checks, all original labels and tails. No common-reference-measure assumption, new global K, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j136_io', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result,
                'Whole J source labelwise certificate')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: whole J source bounds, four-slot guards, complete labelwise tails and nonzero reserve box.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
