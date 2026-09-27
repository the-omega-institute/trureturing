#!/usr/bin/env python3
"""Exact endpoint survival bound and sharp boundary of the fixed57 scalar costs.

Two finite rational laws verify sharpness of the scalar relaxation only.
They are not asserted to arise from actual original congruence families.
All comparison tails are complete; no numerical optimizer is used.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/endpoint_survival_scalar_barrier.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/endpoint-bounds/endpoint_numerator_common_costs.py': '1b665058c35f8aaadc60d4513939e6c4255cff212b6289d8c0e3beb7bd1d02d6',
    'certificates/source_norms/endpoint-bounds/endpoint_numerator_common_costs.json': '75154048adef87983ab5c776537f73e74f9864714b5cc24b54bfa674dcca26f6',
    'certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json': '3b8afa03444fe045c9dba7e1a74ac051c3d4032eddfeae106a47e360ad0d34e2',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def hinge(t, v):
    return max(F(v)-t, F(0))


def integral(law, fn):
    return sum(mass*fn(v) for v, mass in law)


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('survival_scalar_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    numerator = read('certificates/source_norms/endpoint-bounds/endpoint_numerator_common_costs.json')
    survival = read('certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json')
    for prior in (numerator, survival):
        for path, pin in prior['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pin: '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    require(numerator['source_vertex'] == 404 and numerator['carrier'] == [0, 1], 'Same endpoint')
    D, L, Q = (F(numerator[k]) for k in ('mass', 'linear_upper', 'square_upper'))
    require((D, L, Q) == (F(3, 20), F(1157, 1800), F(469, 100)), 'Fixed65 scalar relaxation')
    source = module('survival_scalar_source', base/'verify_joint_frontier.py')
    schedule = module('survival_scalar_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('survival_scalar_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    majorant = module('survival_scalar_majorant', base/'frontier/endpoint-bounds/endpoint_numerator_common_costs.py')
    specs, _, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    require(len(specs) == 46, 'All46 old transformed cost directions')
    tags = [('h', F(0)), ('s', F(0))]+[spec['tag'] for spec in specs]
    tags += [('s', F(81, n*n)) for n in range(1, 7)]
    bounds = [F(v) for v in numerator['universal_cost_constraint_bounds']]
    require(len(bounds) == len(tags) == 54 and bounds[:2] == [L, Q], 'All54 original scalar bounds')
    original46 = read('certificates/source_norms/moments-survival/joint_survival_carriers.json')
    row = next(r for a in original46['joint_survival']['row_blocks'] for b in a for r in b if r['index'] == 404)
    carrier = next(c for c in row['conditional'] if c['carrier'] == [0, 1])
    gains = next(r for r in survival['allocation_statistics']['control_gains'] if r['index'] == 404)
    require(gains['carrier'] == [0, 1] and F(carrier['D_c']) == D, 'Same original53 mass and carrier')
    margins = [F(carrier['m25']), F(carrier['m4'])+F(gains['gain4']), F(carrier['m5'])+F(gains['gain5'])]
    old_upper = [F(7, 2)*D-margins[0], D-margins[1], D-margins[2]]
    require(old_upper == [F(81281, 220500), F(2701424, 12403125), F(2028798479, 12155062500)], 'Exact53 hinge bounds')
    tags += [('h', t) for t in (F(5, 2), F(4), F(5))]
    bounds += old_upper
    functions = [lambda v, tag=tag: source.zero5_cost(tag, v) for tag in tags]
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    require(len(bounds) == 57, 'Exactly54 plus three survival constraints')
    W = [(1, F(17366767, 297675000)), (4, F(5673091, 297675000)), (7, F(2701424, 37209375))]
    V = [(1, D-old_upper[2]/4), (9, old_upper[2]/4)]
    laws = {}
    for name, law in (('W', W), ('V', V)):
        require(all(isinstance(v, int) and v >= 1 and mass > 0 for v, mass in law), 'Positive integer support and rational masses')
        require(sum(mass for _, mass in law) == D, 'Exact total mass')
        slacks = [cap-integral(law, fn) for fn, cap in zip(functions, bounds)]
        require(min(slacks) >= 0, 'Both primal laws satisfy every fixed57 constraint')
        laws[name] = {'support': law, 'constraint_slacks': slacks,
                      'first_moment': integral(law, lambda v: F(v)),
                      'second_moment': integral(law, lambda v: F(v*v))}
    require(laws['W']['first_moment'] == L and integral(W, lambda v: hinge(F(4), v)) == old_upper[1], 'W simultaneously saturates first moment and h4')
    require(integral(V, lambda v: hinge(F(5), v)) == old_upper[2], 'V saturates h5')
    thresholds = (F(5, 2), F(4), F(5), F(5, 3), F(5, 4), F(1))
    upper, duals = {}, []
    for t in thresholds:
        if t in (4, 5):
            alpha, weights = F(0), [(55 if t == 4 else 56, F(1))]
        else:
            lam = (t-1)/3
            alpha, weights = -(1-lam), [(0, 1-lam), (55, lam)]
        require(all(w >= 0 for _, w in weights), 'Nonnegative universal upper multipliers')
        target_fn = lambda v, t=t: hinge(t, v)
        target_meta = source.zero5_cost_metadata(('h', t))
        proof = majorant.verify_majorant(57, alpha, weights, functions+[target_fn], metadata+[target_meta], bounds+[F(0)], D)
        optimum = integral(V if t == 5 else W, target_fn)
        require(proof['bound'] == optimum, 'Primal equals exact all-integer dual')
        proof['threshold'], proof['primal_law'] = t, 'V' if t == 5 else 'W'
        duals.append(proof)
        upper[t] = optimum
    den_old = F(23, 42)*D+sum(w*m for w, m in zip((F(1, 22), F(1, 6), F(4, 33)), margins))
    require([404, [0, 1], 'D_c'] in survival['controllers']['rho'] and den_old == F(survival['rho'])*D, 'Original53 endpoint denominator exactly reconstructed')
    den_three = F(919, 924)*D-upper[F(5, 2)]/22-upper[F(4)]/6-F(4, 33)*upper[F(5)]
    require(den_three == F(235, 231)*D-L/44-F(25, 132)*old_upper[1]-F(4, 33)*old_upper[2], 'Independent three-hinge coefficient identity')
    r = F(1, 11)
    p = {1: F(28, 33), **{n: F(50, 3*11**n) for n in (2, 3, 4)}}
    tail0 = F(50, 3)*r**5/(1-r)
    tail1 = F(50, 3)*r**5*(5-4*r)/(1-r)**2
    require(sum(p.values())+tail0 == 1 and sum(n*pn for n, pn in p.items())+tail1 == F(7, 6), 'Complete AP11 probability and first moment')
    finite = p[1]*upper[F(5)]+sum(p[n]*n*upper[F(5, n)] for n in (2, 3, 4))
    complete_cost = finite+tail1*L-5*tail0*D
    den_exact = D-upper[F(4)]/6-complete_cost/7
    finite_linear = sum(p[n]*F(4*n-5, 21) for n in (2, 3, 4))
    coefficients = {'mass': 1+finite_linear+F(5, 7)*tail0,
                    'first': finite_linear+tail1/7,
                    'h4': F(1, 6)+sum(p[n]*F(5-n, 21) for n in (2, 3, 4)),
                    'h5': F(4, 33)}
    require(den_exact == coefficients['mass']*D-coefficients['first']*L-coefficients['h4']*old_upper[1]-coefficients['h5']*old_upper[2], 'Independent complete AP11 coefficient expansion')
    primal_cost = (p[1]*integral(V, lambda v: hinge(F(5), v))
                   +sum(p[n]*integral(W, lambda v, n=n: hinge(F(5), n*v)) for n in (2, 3, 4))
                   +integral(W, lambda v: tail1*v-5*tail0))
    require(primal_cost == complete_cost and den_exact == D-integral(W, lambda v: hinge(F(4), v))/6-primal_cost/7, 'Two primal laws attain complete denominator functional')
    required = F(numerator['numerator_upper'])/(403-F(numerator['offset']))
    require(0 < den_old < den_three < den_exact < required, 'Strict useful gain and remaining scalar obstruction')
    return {'schema': 'erdos7-endpoint-survival-scalar-barrier-v1', 'source_vertex': 404, 'carrier': (0, 1),
            'source_sha256': used, 'mass': D, 'constraint_count': 57, 'constraint_bounds': bounds,
            'original53_margins': margins, 'original53_hinge_uppers': old_upper, 'laws': laws,
            'all_integer_duals': duals, 'original53_denominator': den_old,
            'three_hinge_optimal_scalar_denominator': den_three,
            'exact_AP11_optimal_scalar_denominator': den_exact,
            'exact_AP11_endpoint_rho_lower': den_exact/D,
            'complete_AP11_tail': {'entrance': 5, 'mass': tail0, 'first_moment': tail1},
            'exact_AP11_coefficients': coefficients,
            'three_hinge_gain_over53': den_three-den_old, 'exact_AP11_gain_over53': den_exact-den_old,
            'fixed65_numerator': F(numerator['numerator_upper']), 'required_denominator_for_fixed65': required,
            'gap_to_required': required-den_exact,
            'fixed65_endpoint_comparison': F(numerator['offset'])+F(numerator['numerator_upper'])/den_exact,
            'scope': ('Uniform survival comparison at the fixed65 endpoint. Sharp only for the57 '
                      'independent scalar constraints; W and V are abstract laws, not original-family '
                      'witnesses. No global K update, actual-family impossibility or Lean verification.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('survival_scalar_output_io', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical exact scalar certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:57 exact constraints, two rational primal laws, six complete-domain duals and the full AP11 tail.')
    print('Endpoint survival denominator '+str(float(F(result['exact_AP11_optimal_scalar_denominator'])))+
          '; fixed65 required denominator '+str(float(F(result['required_denominator_for_fixed65'])))+'.')
    print('The sharp obstruction concerns this scalar relaxation, not actual original congruence families.')


if __name__ == '__main__':
    main()
