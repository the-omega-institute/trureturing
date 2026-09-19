#!/usr/bin/env python3
"""Exact capacity of the present isotropic face-neighborhood K certificate.

Analytic monotonicity reduces the two-variable reserve optimization to one
strictly decreasing scalar function. Complete geometric tails identify an
exact rational crossing. This is a bound on a specified proof template,
not an obstruction to stronger actual-family inequalities.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/k_neighborhood_route_limit.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/global_k_face_gain.py': '8dff98877cccfad0329b5a3f1ba7af5b48c156a8029839f221e497888de1dc2b',
    'certificates/source_norms/global_k_face_gain.json': '65442cfe3920ac934b71ca9c335ae0aa5559f7f6d37a0c5d910eb2c39af1566b',
    'frontier/endpoint_k_face_neighborhood.py': 'c2f2f107ec6bedfe7f7c7880f80ae080347bf262accb9d02162fc0f191f33d21',
    'certificates/source_norms/endpoint_k_face_neighborhood.json': 'f3f0f82d9a4d0d2d58fa1c310efb6cd97d8c12155ae4d557d2d473df6ec69dd3',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module: '+str(path))
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


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('route_limit_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    global74 = read('certificates/source_norms/global_k_face_gain.json')
    local73 = read('certificates/source_norms/endpoint_k_face_neighborhood.json')
    used = dict(PINS)
    for record in (global74, local73):
        for path, pin in record['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pins')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    prior = module('route_limit_tail', base/'frontier/endpoint_linear_neighborhood.py')
    gamma, a, beta, conversion, denominator = (F(global74[k]) for k in (
        'gamma_K', 'signed_mass_coefficient', 'identity_cost_coefficient',
        'tau_conversion_coefficient', 'comparison_denominator_upper'))
    require(min(gamma, a, beta) > 0 and conversion == F(37, 8) and denominator == F(5, 9),
        'Exact existing scalar template')
    mass_bridge = F(4, 45)
    k = mass_bridge+gamma/a
    delta_guard = min(F(local73['guards']['tau'])/conversion, F(1, 18))
    eps_guard = F(local73['guards']['epsilon'])
    require(delta_guard == F(1, 4625), 'Current uniform radius guard')

    # FN11 plus FN12: (3*tau+60*eps)+(201*eps+2*kappa/5).
    tight_5 = (F(3), F(60)+F(201), F(2, 5))
    categories = {name: [F(x) for x in row] for name, row in local73['complete_test_categories'].items()}
    for name in ('test5', 'test15'):
        categories[name][1:] = tight_5
    totals = [sum(row[j] for row in categories.values()) for j in range(4)]
    require(totals == [F(233, 450), F(2017, 180), F(530), F(739, 450)],
        'All disjoint test categories retain the sharper first-five errors')
    gap0 = F(local73['guaranteed_gain']['constant'])
    tau_exact = totals[1]+5*F(8, 5)+F(local73['old_margin_errors']['tau'])
    kappa_exact = totals[3]+F(local73['old_margin_errors']['kappa'])
    require((gap0, tau_exact, kappa_exact) == (F(677, 24300), F(5617, 180), F(482, 225)),
        'Signed margin and live old-direction errors')

    def tails(eps):
        R3, n3 = prior.min_geometric(4*eps, F(1, 20), 3, 3)
        R5, n5 = prior.min_geometric(eps, F(4, 45), 5, 2)
        return R3, R5, n3, n5

    results = {}
    for name, tau_error, kappa_error in (
        ('rounded_tight_errors', F(32), F(5, 2)),
        ('unrounded_tight_errors', tau_exact, kappa_exact)):
        A = tau_error*conversion+kappa_error
        # Candidate crossing has entrances n3=7 and n5=6. Verify those
        # inequalities exactly below; no numerical search is trusted.
        tail_slope = F(4*(7-3)+(6-2))
        tail_constant = F(1, 20*3**7)/(1-F(1, 3))+F(4, 45*5**6)/(1-F(1, 5))
        require(tail_slope == 20 and tail_constant == F(1, 29160)+F(1, 140625), 'Complete affine tail piece')
        delta = beta*(gap0-tail_constant)/(gamma+beta*(A+(totals[2]+tail_slope)*k))
        eps = k*delta
        R3, R5, n3, n5 = tails(eps)
        require((n3, n5) == (7, 6) and R3+R5 == tail_slope*eps+tail_constant,
            'Exact crossing lies inside the asserted full-tail piece')
        require(F(1, 20*3**7) <= 4*eps < F(1, 20*3**6)
            and F(4, 45*5**6) <= eps < F(4, 45*5**5), 'Both exact geometric entrances')
        require(0 < delta < delta_guard and 0 < eps < eps_guard,
            'Scalar crossing is admissible before either inherited guard')
        local_gain = gap0-A*delta-totals[2]*eps-R3-R5
        reserves = (gamma*delta, a*(eps-mass_bridge*delta), beta*local_gain)
        require(reserves[0] == reserves[1] == reserves[2] > 0, 'All three reserves balance exactly')
        reserve = reserves[0]
        maximum_decrease = reserve/denominator
        require(maximum_decrease < F(12, 1000000), 'Even unhalved route gain is below twelve millionths')
        results[name] = {'tau_error': tau_error, 'epsilon_error': totals[2], 'kappa_error': kappa_error,
            'radius_error_coefficient': A, 'optimal_delta': delta, 'optimal_epsilon': eps,
            'optimal_tau_upper': conversion*delta, 'tail_entrances': [n3, n5], 'complete_R3': R3, 'complete_R5': R5,
            'local_identity_gain': local_gain, 'maximum_signed_reserve': reserve,
            'maximum_decrease_nonnegative_final_margin': maximum_decrease,
            'decrease_retaining_half_margin': maximum_decrease/2}
    require(F(results['unrounded_tight_errors']['maximum_signed_reserve']) >=
        F(results['rounded_tight_errors']['maximum_signed_reserve']), 'Unrounded errors weakly improve the exact optimum')
    radius_ceiling = gamma*delta_guard/denominator
    require(radius_ceiling < F(1, 50000), 'Even unlimited local gain has a radius ceiling below twenty millionths')
    return encode({'schema': 'erdos7-k-neighborhood-route-limit-v1', 'source_sha256': used,
        'gamma_K': gamma, 'mass_coefficient': a, 'identity_coefficient': beta,
        'mass_bridge_coefficient': mass_bridge, 'epsilon_per_delta_at_balanced_reserve': k,
        'tau_conversion': conversion, 'delta_guard': delta_guard, 'epsilon_guard': eps_guard,
        'denominator_upper': denominator, 'tight_test_categories': categories,
        'tight_summed_coefficients': totals, 'local_zero_error_gain': gap0,
        'complete_tail_piece': {'epsilon_coefficient': 20, 'constant': F(1, 29160)+F(1, 140625)},
        'optima': results, 'unlimited_local_gain_radius_ceiling': radius_ceiling,
        'scope': 'Exact maximum for the fixed isotropic barycentric-radius certificate using gamma_K*delta, actual-mass escape, these local error bounds, and denominator upper5/9. No bound on improvements from sharper global tables, anisotropic neighborhoods, actual-source cuts, other costs, or different comparisons. No new canonical K target or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('route_limit_writer', args.base/'certificate_io.py')
    rendered = json.dumps(result, indent=2)+'\n'
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact scalar route-capacity certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, rendered)
    elif args.output is not None:
        args.output.write_text(rendered)
    else:
        print(rendered)
    print('PASS: exact monotone scalar crossings, complete tails, both global reserve optima; full route gain below0.000012.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
