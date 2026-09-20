#!/usr/bin/env python3
"""Verify an exact sharp obstruction for the AP(4,5) row17 moment relaxation.

Only the four published scalar caps are imported. The cubic cap is an explicit
additional constraint of this abstract model, not a certified actual AP moment.
The all-real-domain dual has an elementary interval proof in profile36.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b'
PARENT = 'certificates/ap_schedule_frontier_certificate.json'
PARENT_PIN = '15a1d0d493358c52947a5d7ac7b5362b24f933c1641150f4d4e9fcdda131fa05'
PARENT_VERIFIER = 'frontier/cover-geometry/verify_ap_schedule.py'
PARENT_VERIFIER_PIN = '70dee971ec6f6ab6042e7c765e196bc0da6aba858e400190f2240acb985106c6'
CERTIFICATE = 'certificates/moment_obstructions/row17.json'
CUBIC_CAP = F(18967452734315727, 3954501738752)
SUPPORT = ((4, 5), (4, 6), (9, 14), (12, 9),
           (19, 12), (35, 19), (49, 52), (87, 8))
W17 = ((5, F(5, 11)), (6, F(10, 99)),
       (7, F(5, 36)), (8, F(3577, 72)))
W19 = ((5, F(112, 351)), (6, F(224, 3861)),
       (7, F(112, 1485)), (8, F(39449, 990)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def features(x):
    return (F(max(x*x - 16, 0)),
            sum(w * max(x-k, 0) for k, w in W17),
            sum(w * max(x-k, 0) for k, w in W19),
            F(max(x-5, 0)), F(x**3))


def kappa(z):
    return F(16) / (16-min(z, 8))


def objective(y, z):
    return F(403, 8)*max(z-8, 0) + F(25, 128)*kappa(z)*y*y


def solve(matrix, rhs):
    n = len(rhs)
    require(len(matrix) == n and all(len(row) == n for row in matrix),
            'Square exact probability system')
    rows = [list(map(F, row)) + [F(b)] for row, b in zip(matrix, rhs)]
    for j in range(n):
        candidates = [i for i in range(j, n) if rows[i][j]]
        require(bool(candidates), 'Nonsingular exact probability system')
        pivot = candidates[0]
        rows[j], rows[pivot] = rows[pivot], rows[j]
        divisor = rows[j][j]
        rows[j] = [v/divisor for v in rows[j]]
        for i in range(n):
            if i != j:
                multiple = rows[i][j]
                rows[i] = [a-multiple*b for a, b in zip(rows[i], rows[j])]
    return [row[-1] for row in rows]


def verify_dual():
    # H(z)=50/11+phi17(z)-403/8*(z-8)+-(25/8)*kappa(z).
    # Below5: H=50*(5-z)/(11*(16-z)); above8: H=0.
    # On[k,k+1],k=5,6,7,t=z-k: H=50*t*(1-t)/
    # ((16-k)*(15-k)*(16-k-t)). This covers real z, not a sample grid.
    require(sum(w for _, w in W17) == F(403, 8), 'phi17 terminal slope')
    require(sum(w for _, w in W19) == F(403, 10), 'phi19 terminal slope')
    require(features(8)[1] == F(75, 44), 'phi17 terminal intercept')
    knots = []
    for k in range(5, 9):
        value = F(50, 11) + features(k)[1]
        require(value == F(25, 8)*kappa(k), 'Exact dual contact at ' + str(k))
        knots.append({'z': k, 'value': str(value)})
    for k in range(5, 8):
        slope = sum(w for knot, w in W17 if knot <= k)
        require(slope == F(25, 8)*(kappa(k+1)-kappa(k)),
                'Exact affine secant on complete interval ' + str(k))
        require(15-k > 0, 'Positive denominator over complete interval')
    require(F(50, 11) + F(75, 44) == F(25, 4), 'Zero full tail residual')
    return {'intercept': '50/11', 'Y_h16': '25/64', 'Z_phi17': '1',
            'other_multipliers': '0', 'domain': 'all real y,z >= 1',
            'contact_knots': knots,
            'residual_1_to_5': '50*(5-z)/(11*(16-z))',
            'residual_k_to_k1': '50*t*(1-t)/((16-k)*(15-k)*(16-k-t)), k=5,6,7; t=z-k',
            'residual_8_to_infinity': '0'}


def reconstruct(parent):
    rho = F(parent['source_inputs']['rho13'])
    require(rho > 0, 'Positive AP45 survival lower bound')
    costs = parent['linear_costs']
    require([row['name'] for row in costs] == ['R17', 'R19', 'R5'],
            'Published scalar cost order')
    square_hinge_cap = F(parent['H16'])/rho
    require(square_hinge_cap == F(parent['Gamma13'])-16,
            'Published square hinge and Gamma13 normalization agree')
    caps = [square_hinge_cap] + [F(row['H'])/rho for row in costs]
    require(min(caps) >= 0, 'Nonnegative imported scalar caps')
    limits = tuple(caps + [CUBIC_CAP])*2
    columns = [features(y)+features(z) for y, z in SUPPORT]
    active = (0, 2, 4, 5, 6, 7, 8)
    probabilities = solve([[F(1)]*len(SUPPORT)] +
                          [[column[i] for column in columns] for i in active],
                          [F(1)] + [limits[i] for i in active])
    require(min(probabilities) > 0 and sum(probabilities) == 1,
            'Eight positive exact probabilities with total mass one')
    values = [sum(q*column[i] for q, column in zip(probabilities, columns))
              for i in range(10)]
    require(all(value <= cap for value, cap in zip(values, limits)),
            'All ten marginal constraints')
    dual = verify_dual()
    upper = F(50, 11) + F(25, 64)*caps[0] + caps[1]
    primal = sum(q*objective(y, z) for q, (y, z) in zip(probabilities, SUPPORT))
    require(primal == upper, 'Exact primal-dual equality')
    require(all(objective(y, z) == F(50, 11)+F(25, 64)*features(y)[0]+features(z)[1]
                for y, z in SUPPORT), 'Pointwise dual equality throughout support')
    return {'model': 'AP45-row17-joint-marginal-obstruction-v1',
            'scope': 'Abstract joint laws of integer Y>=1 and real Z>=1. No AP realizability assertion; no probabilistic independence requirement.',
            'cubic_cap_status': 'Explicit model constraint; not a published uniform actual AP cubic-moment theorem.',
            'feature_order_per_marginal': ['h16', 'phi17', 'phi19', 'g5', 'cube'],
            'caps_per_marginal': list(map(str, limits[:5])),
            'support': [{'Y': y, 'Z': z, 'probability': str(q)}
                        for (y, z), q in zip(SUPPORT, probabilities)],
            'moments_Y_then_Z': list(map(str, values)),
            'slack_Y_then_Z': [str(cap-value) for cap, value in zip(limits, values)],
            'dual': dual, 'optimum': str(upper)}


def main():
    base = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-directory', type=Path, default=base)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = args.source_directory.resolve()
    require(sha256((src/'certificate_io.py').read_bytes()).hexdigest() == IO_PIN,
            'Certificate IO source pin')
    spec = importlib.util.spec_from_file_location('joint_moment_io', src/'certificate_io.py')
    require(spec is not None and spec.loader is not None, 'Loadable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    raw = io.read_artifact_bytes(src/PARENT)
    require(sha256(raw).hexdigest() == PARENT_PIN, 'Complete logical AP45 parent pin')
    parent = json.loads(raw, object_pairs_hook=unique)
    require(parent['verifier_sha256'] == PARENT_VERIFIER_PIN and
            sha256((src/PARENT_VERIFIER).read_bytes()).hexdigest() == PARENT_VERIFIER_PIN,
            'AP45 parent verifier source pin')
    pins = parent['source_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(src/name)).hexdigest() == pin,
                'AP45 parent mathematical source pin: ' + name)
    result = reconstruct(parent)
    result['source_sha256'] = pins | {PARENT: PARENT_PIN, PARENT_VERIFIER: PARENT_VERIFIER_PIN}
    result['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    certificate = base/CERTIFICATE
    if args.write:
        certificate.parent.mkdir(parents=True, exist_ok=True)
        io.write_certificate_text(certificate, json.dumps(result, indent=2)+'\n')
    else:
        require(json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=unique) == result,
                'Complete joint-moment certificate matches exact reconstruction')
    print('PASS: eight-point law, all ten caps, complete-domain dual and exact equality.')
    print('Optimum ' + result['optimum'] + ' = ' + str(float(F(result['optimum']))))
    print('Ordinary proof and exact arithmetic; actual realization and unrestricted #7 remain open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
