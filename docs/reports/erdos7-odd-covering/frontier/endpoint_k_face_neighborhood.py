#!/usr/bin/env python3
"""Exact constants for a uniform neighborhood of both controlling beta faces.

The ordinary proof carries the assigned-budget geometry and all-family
quantifiers. This verifies guards, complete tails, original comparison
constants, the strict box gap and an actual finite family entering the box.
No optimizer, exponent truncation inference or Lean result is used.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint_k_face_neighborhood.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/endpoint_linear_neighborhood.py': 'e9d1eb6487f95874b2c577496b41083ff140138ef5a59d630144d1c72aae279a',
    'certificates/source_norms/endpoint_linear_neighborhood.json': '58dbc7cfd2ee535340c6b73bf44bf2df25d9949303052600f6f88a2504f73221',
    'frontier/endpoint_k_face_linear.py': '6b810c62d92e5ea86e121b4068dd7f5f8523b18bdb61b42c36188a8dd09a5054',
    'certificates/source_norms/endpoint_k_face_linear.json': '218357073476592f25d3644e84eba2fa0719d27123fa3f37981b96a44302fec1',
    'frontier/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645',
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


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def finite_approach(prior, height):
    t = F(1, 18)-F(1, 2*3**height)
    q = F(1, 4)-F(1, 4*5**height)
    eta = (F(1, 9)-t,)+(F(1, 9),)*4
    d = (1-q, 1-q, 1-3*q, 1-2*q, 1-2*q)
    n = tuple(eta[j]*d[j]-(t*q if j == 0 else 0) for j in range(5))
    s = sum(n)
    require(s == F(5, 9)-t-q, 'Actual398 finite raw source mass')
    C = prior.complete_cap((d, n, eta, s, F(0)))
    D = s-C/5
    seven = (1-F(1, 7**height))/(5+F(1, 7**height))
    H = F(4, 9)+t+q/9-t*q
    S = s-seven*H
    eta0 = (F(1, 18),)+(F(1, 9),)*4
    n0 = tuple(map(F, ('1/36', '1/12', '1/36', '1/18', '1/18')))
    d0 = tuple(map(F, ('3/4', '3/4', '1/4', '1/2', '1/2')))
    tau_upper = (sum(abs(x-y) for x, y in zip(eta, eta0))
                 +sum(abs(x-y) for x, y in zip(n, n0))
                 +sum(abs(x-y) for x, y in zip(d, d0))
                 +3*(F(1, 4)-q)+F(1, 72)-t*q)
    epsilon, kappa = S-D, F(1, 7**height)
    require(min(tau_upper, epsilon, kappa) > 0, 'Finite actual family has positive deviations')
    return {'height': height, 'original_nonunit_labels': (height+1)**3-1,
            's': s, 'S': S, 'D': D, 'tau_upper_at_vertex398': tau_upper,
            'epsilon': epsilon, 'kappa': kappa,
            'inside_box': tau_upper <= F(1, 10000) and epsilon <= F(1, 10**8) and kappa <= F(1, 10000)}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('k_face_neighborhood_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    endpoint = read('certificates/source_norms/endpoint_k_face_linear.json')
    old = read('certificates/source_norms/endpoint_linear_neighborhood.json')
    for previous in (endpoint, old):
        for path, pin in previous['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent source pin')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
            used[path] = pin
    require(endpoint['face_vertices'] == [398, 410, 422] and endpoint['carrier'] == [1, 1], 'Same entire beta face')
    prior = module('k_face_neighborhood_prior66', base/'frontier/endpoint_linear_neighborhood.py')
    guard_tau, guard_epsilon = F(1, 1000), F(1, 10000)
    etaL = F(1, 9)-guard_tau
    h1 = F(1, 3)-guard_tau
    root_gap = F(1, 6)-guard_tau
    h = F(1, 2)
    ell = F(35, 6)*guard_epsilon
    require(guard_tau < F(1, 25) and etaL >= F(1, 10) and root_gap >= F(1, 9), 'All possible first-beta cells obey uniform geometric guards')
    require(F(6, 35)*h/5 > guard_epsilon, 'First forbidden cofactor5 must exist')
    require(ell < min(h/5, h1/5, etaL/5), 'H distinct from P,A,B')
    assigned_one = F(1, 20)-guard_tau-ell/etaL
    assigned_both = F(1, 10)-guard_tau-ell/etaL
    require(assigned_one > 0 and assigned_both > 0, 'Positive assigned deep source mass in Q')
    gaps = (h/5, h1/5, etaL/5, h*assigned_one,
            root_gap/5, h1*assigned_both)
    require(min(gaps) >= F(1, 100), 'Every bad cofactor5 or15 pays at least1/100')
    require(F(1, 3) <= 3*root_gap and F(35, 6)*10 <= 60, 'Wrong-root and H-transfer constants')
    require(1+2 <= 14 and 60+201 <= 300 and F(2, 5) <= 1, 'Conservative two first-slot test bounds')
    categories = {
        'test3': (F(31, 360), F(2), F(4), F(2, 5)),
        'test9': (F(11, 180), F(2), F(4), F(2, 5)),
        'test5': (F(29, 450), F(14), F(300), F(1)),
        'test15': (F(8, 225), F(14), F(300), F(1)),
        'deep3': (F(7, 180), F(1, 18), F(0), F(1, 45)),
        'deep5': (F(37, 1800), F(1, 20), F(0), F(1, 50)),
        '3_times_deep5': (F(1, 60), F(1, 20), F(0), F(0)),
        '9_times5': (F(1, 36), F(1, 4), F(0), F(0)),
        'deep35': (F(1, 72), F(0), F(0), F(0)),
        'positive7': (F(11, 72), F(4, 5), F(0), F(0)),
    }
    totals = tuple(sum(row[j] for row in categories.values()) for j in range(4))
    D0, Mnew, Mold = F(53, 360), F(endpoint['margin_lower']), F(endpoint['old_margin_upper'])
    require(totals[0] == F(233, 450) and D0+totals[0] == F(endpoint['linear_upper']) == F(133, 200), 'Complete endpoint test categories')
    require(totals[1] <= 34 and totals[2] == 608 and totals[3] <= 3, 'Conservative complete numerator errors')
    require(34+F(8, 5) <= 36 and 34+5*F(8, 5) == 42, 'Absolute numerator and signed-margin errors')
    tail_checks = []
    for denominator in (100, 1000, 10000, 100000, 1000000):
        root = F(1, denominator)
        epsilon = root*root
        R3, n3 = prior.min_geometric(4*epsilon, F(1, 20), 3, 3)
        R5, n5 = prior.min_geometric(epsilon, F(4, 45), 5, 2)
        cut = max(n3, n5)+4
        independent3 = sum(min(4*epsilon, F(1, 20*3**a)) for a in range(3, cut))+F(1, 20*3**cut)/(1-F(1, 3))
        independent5 = sum(min(epsilon, F(4, 45*5**b)) for b in range(2, cut))+F(4, 45*5**cut)/(1-F(1, 5))
        require((R3, R5) == (independent3, independent5) and max(R3, R5) <= root, 'Independent full min-geometric tails')
        tail_checks.append({'epsilon': epsilon, 'sqrt_epsilon': root, 'R3': R3, 'R5': R5, 'entrances': (n3, n5)})
    require(prior.min_geometric(0, F(1, 20), 3, 3)[0] == prior.min_geometric(0, F(4, 45), 5, 2)[0] == 0, 'Zero-slack complete tails')
    require(max(map(F, old['old_U_lipschitz'])) <= 4 and max(map(F, old['old_cap_lipschitz'])) <= 2, 'Same uniform fixed-layout Lipschitz estimates')
    require(F(112, 225) < F(1, 2), 'Carrier oscillation bound')
    gain = Mnew-Mold
    tau_box, epsilon_box, kappa_box = F(1, 10000), F(1, 10**8), F(1, 10000)
    error = 54*tau_box+608*epsilon_box+F(7, 2)*kappa_box+2*F(1, 10000)
    remaining = gain-error
    require(gain == F(677, 24300) and remaining == F(66533407, 3037500000) > F(1, 50), 'Strict whole-box margin gain')
    approaches = [finite_approach(prior, height) for height in range(3, 26)]
    witness = next(row for row in approaches if row['inside_box'])
    constructor = module('k_face_neighborhood_constructor48', base/'frontier/source_mass_compatibility.py')
    actual3 = constructor.check(3, 398)
    formula3 = approaches[0]
    require(all(F(actual3[key]) == formula3[key] for key in ('s', 'S', 'D')), 'Independent actual original-label union agrees with finite398 formula')
    return {'schema': 'erdos7-endpoint-k-face-neighborhood-v1', 'source_sha256': used,
            'face_vertices': endpoint['face_vertices'], 'carrier': [1, 1],
            'symmetric_face_vertices': endpoint['symmetric_face_vertices'], 'symmetric_carrier': [1, 0],
            'guards': {'tau': guard_tau, 'epsilon': guard_epsilon, 'etaL_lower': etaL,
                       'root_gap_lower': root_gap, 'H_loss_upper': ell,
                       'assigned_one_deep_family_Q_lower': assigned_one,
                       'assigned_both_deep_families_Q_lower': assigned_both, 'bad_carrier_gaps': gaps},
            'complete_test_categories': categories, 'summed_constants': totals,
            'endpoint_linear_upper': F(133, 200), 'endpoint_margin_lower': Mnew,
            'old_face_margin_upper': Mold,
            'numerator_errors': {'tau': 36, 'epsilon': 609, 'kappa': 3, 'sqrt_epsilon': 2},
            'margin_errors': {'tau': 42, 'epsilon': 608, 'kappa': 3, 'sqrt_epsilon': 2},
            'old_margin_errors': {'tau': 12, 'kappa': F(1, 2)},
            'guaranteed_gain': {'constant': gain, 'tau': -54, 'epsilon': -608, 'kappa': F(-7, 2), 'sqrt_epsilon': -2},
            'complete_tail_checks': tail_checks, 'improvement_box': {'tau': tau_box, 'epsilon': epsilon_box, 'kappa': kappa_box},
            'box_corner_error': error, 'box_guaranteed_gain': remaining,
            'finite_box_witness': witness, 'actual_height3_validation': actual3,
            'scope': ('Uniform finite-neighborhood identity-cost improvement along both entire controlling '
                      'beta faces. Tau minimizes over the compact face and does not penalize internal beta '
                      'variation. Ordinary proof; no global K update or Lean verification.')}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('k_face_neighborhood_output_io', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical exact face-neighborhood certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:whole-face guards, assigned-budget gaps, complete tails and strict gain66533407/3037500000>1/50.')
    print('An actual finite398 family enters the box at tested height '+str(result['finite_box_witness']['height'])+'.')
    print('The global K consumer is a separate obligation; this proof has no Lean claim.')


if __name__ == '__main__':
    main()
