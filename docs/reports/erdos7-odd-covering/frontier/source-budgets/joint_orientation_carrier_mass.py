#!/usr/bin/env python3
"""Use the actual two-orientation coupling to extend the signed mass bound."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/joint_orientation_carrier_mass.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/source-budgets/monotone_product_carrier_mass.py': '320fb41c8422ac579e18563d2f776470d9caf109ff5cd84248080b5f285160ac', 'certificates/source_norms/source-budgets/monotone_product_carrier_mass.json': '2b0d5a9eff59a3c44fa1c5f9f8854f2471e0d1dc14607817ac9980395a7a5e93'}
EARLY_LIMIT, SLOPE, FACE_MASS = F(1, 3), F(1, 10), F(53, 360)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def bound_S0(sigma):
    sigma = F(sigma)
    require(0 <= sigma <= EARLY_LIMIT, 'Proved actual joint-orientation domain')
    return FACE_MASS+SLOPE*sigma


def bound_E(sigma, rho):
    rho = F(rho)
    require(rho >= 0, 'One actual residual')
    return bound_S0(sigma)+rho


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('joint_orientation_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    old = module('joint_orientation_prior', base/'frontier/source-budgets/monotone_product_carrier_mass.py')
    prior = old.calculate(base)
    require(prior == json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/monotone_product_carrier_mass.json')),
            'Exact signed-source expansion and monotonicity predecessor')
    add, mul, scale = old.add, old.mul, old.scale
    one = {(): F(1)}
    a, z, b, d, l, p, sigma, y, x, u, v = ({(k,): F(1)} for k in
        ('alpha', 'z', 'beta', 'deficit', 'late', 'carrier', 'sigma', 'y', 'x', 'u', 'v'))
    minus = lambda q: add(one, scale(q, -1))
    common_product = mul(mul(minus(a), minus(z)), minus(b))
    common_y = add(one, scale(common_product, -1))
    common = add(scale(a, 24), scale(z, 36), scale(b, 8))
    common_gap = add(scale(mul(a, add(one, scale(z, -3))), 12),
                     mul(b, add(scale(mul(minus(a), minus(z)), 36), scale(one, -8))))
    require(add(scale(common_y, 36), scale(common, -1)) == common_gap,
            'Common product gap has nonnegative factors when y<=1/3')
    C = add(scale(one, 16), scale(z, 8), scale(a, 6), scale(b, 2))
    C_minus_deficit = add(C, scale(add(scale(one, 14), scale(z, 5)), -1))
    require(C_minus_deficit == add(scale(one, 2), scale(z, 3), scale(a, 6), scale(b, 2)),
            'The carrier-product coefficient dominates the deficit coefficient')
    product_loss = add(l, p, scale(mul(l, p), -1))
    pair_gap = add(mul(C, product_loss), scale(l, -5), scale(mul(C, p), -1))
    require(pair_gap == mul(l, add(mul(C, minus(p)), scale(one, -5))),
            'Collapse late and carrier without spending two independent budgets')
    orientation = add(mul(minus(u), minus(v)), mul(u, v))
    loss = add(u, v, scale(mul(u, v), -2))
    require(orientation == add(one, scale(loss, -1)), 'Both actual orientation terms')
    support_gap = add(loss, scale(mul(minus(x), add(u, v)), -1))
    require(support_gap == add(mul(u, add(x, scale(v, -1))), mul(v, add(x, scale(u, -1)))),
            'Joint pair loss dominates (1-x)(u+v) when u,v<=x')
    cleared_slack = add(scale(mul(add(sigma, scale(y, -1)), minus(sigma)), 36),
                        scale(mul(add(one, y), add(sigma, scale(y, -1))), -16))
    factored_slack = mul(add(sigma, scale(y, -1)), add(scale(one, 20), scale(sigma, -36), scale(y, -16)))
    require(cleared_slack == factored_slack, 'Exact final target gap after multiplying by1-sigma')
    require(20-52*EARLY_LIMIT == F(8, 3) > 0 and 16*(1-EARLY_LIMIT)-5 > 0,
            'Uniform positive compression margins through sigma=1/3')
    examples = []
    for s in (F(0), F(1, 50), F(1, 27), F(6, 49), F(1, 8), F(1, 4), EARLY_LIMIT):
        slacks = []
        for j in range(5):
            yy = s*j/4
            xx = (s-yy)/(1-yy)
            require(xx/(1-xx) == (s-yy)/(1-s), 'Exact common/pair budget conversion')
            gap = 36*s-36*yy-16*(1+yy)*(s-yy)/(1-s)
            require(gap == (s-yy)*(20-36*s-16*yy)/(1-s) >= 0, 'Factored target gap')
            slacks.append(gap)
        examples.append({'sigma': s, 'S0_upper': bound_S0(s), 'factor_slacks': slacks})
    # The old two-product witness is excluded by the actual sum constraint.
    ws, wy, wu = F(1, 8), F(123, 1000), F(2, 877)
    q_upper = (1-wy)*(1-2*wu+2*wu*wu)
    require(q_upper < 1-ws, 'The old non-extension witness violates the new necessary coupling')
    return encode({'schema': 'erdos7-joint-orientation-carrier-mass-v1', 'source_sha256': PINS,
                   'sigma_limit': EARLY_LIMIT, 'face_mass': FACE_MASS, 'S0_sigma_coefficient': SLOPE,
                   'E_rho_coefficient': F(1), 'uniform_final_factor_margin': F(8, 3),
                   'examples': examples,
                   'excluded_old_relaxation_witness': {'sigma': ws, 'common_loss': wy, 'pair_losses': (wu, wu),
                                                       'qK_upper': q_upper, 'concentration_gap': 1-ws-q_upper},
                   'scope': 'Ordinary actual-source theorem S0<=53/360+sigma/10 and E<=S0+rho through sigma=1/3. Retains the signed-source polynomial and the common two-orientation concentration. Algebra checks supplement the continuum proof. No actual-source optimality, global comparison, Lean or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('joint_orientation_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact joint-orientation certificate')
    print('PASS: actual joint-orientation mass bound with1/10 slope through sigma=1/3.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
