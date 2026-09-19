#!/usr/bin/env python3
"""Complete branch-specific AP(4,4) costs, cores and continuous threshold bound."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import importlib.util
import json
from math import isqrt, prod
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/branch_threshold_fallback_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/comparison-bounds/branch_local_fallback_comparison.py': 'a29b0b695e2dbffd4d8e6b012cfedf5010fc35fc77be6ad2d856a3a1f2a46fb2', 'certificates/source_norms/comparison-bounds/branch_local_fallback_comparison.json': 'f984e85fbcc1be6994b9209dffff6688e93a7b9c5dd73435b653ec8195c2aa43', 'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f', 'verify_killed_core_continuity.py': 'e6b3e9631aa3d4e16093fc5ea51017e16d021486bca96240f87a01771f940023', 'frontier/cover-geometry/ap_schedule_core.py': '365b6c1f9a70dff5378a7d3a73a06879ee6193fbc69a4ac68ecfed1972e95617', 'profile-notes/001-064/21-physical-and-killed-kernel-comparisons-at11-and13.md': 'd88c38267788e487955df148425b44ba2adde0766d6d4575f788e890ef3d6e10', 'profile-notes/001-064/32-unequal-source-norms-sharpen-the-uniform357-input.md': '039c03bf76c3f3e4070639cf0a97dcfd5865fa7678c8caeeecd7224ad96be5c0', 'profile-notes/001-064/35-ap45-layout-costs-and-complete-core-tails.md': '5b7569bc8a8ac2c03287e8cba51140c390327405126ea2291d7b3073e14f1c20', 'profile-notes/001-064/37-three-original-five-events-strengthen-the-source.md': '00312b546b9f4fd8738ddd7ad57433f813bce88b0a4e2e33d7d9ee604ce8e234'}
SOURCE_CAPS = ((3, F(3, 2)), (5, F(5, 4)), (7, F(7, 6)))
SOURCE_FACTOR = F(432, 73)*F(2, 3)*F(4, 5)*F(6, 7)
SOURCE_G = F(14543, 438)
AC, C0 = F(2371, 2880), F(185694867601, 8599322160)
W17 = ((5, F(5, 11)), (6, F(10, 99)), (7, F(5, 36)), (8, F(3577, 72)))
W19 = ((5, F(112, 351)), (6, F(224, 3861)), (7, F(112, 1485)), (8, F(39449, 990)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original provider')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


@lru_cache(None)
def probability(caps, n):
    """Independent divisor convolution of complete geometric count laws."""
    if not caps:
        return F(n == 1)
    p, c = caps[-1]
    return sum(((1-c/p if k == 1 else c*F(p-1, p**k))*probability(caps[:-1], n//k)
                for k in range(1, n+1) if n % k == 0), F(0))


def moment(caps, degree):
    require(degree in (0, 1, 2), 'Available complete moments')
    if degree == 0:
        return F(1)
    return prod(1+c/F(p-1) if degree == 1 else 1+c*F(3*p-1, (p-1)**2) for p, c in caps)


def product_hinge(caps, threshold, degree=1):
    n, correction = 1, F(0)
    while n**degree < threshold:
        correction += probability(caps, n)*(threshold-n**degree)
        n += 1
    return moment(caps, degree)-threshold+correction


@lru_cache(None)
def source_hinge(threshold, degree=1):
    return SOURCE_FACTOR*product_hinge(SOURCE_CAPS, threshold, degree)


def ingredients(a, c, G=SOURCE_G):
    # T=1 is only a limiting corner in the optimization, never the chosen law.
    require(1 <= a < 10 and 1 <= c < 12, 'Physical threshold domain or lower limiting corner')
    c11, c13 = 10/(10-a), 12/(12-c)
    require(c11 <= 11 and c13 <= 13, 'Nonnegative geometric comparison probabilities')
    caps = ((11, c11), (13, c13))
    bad11 = source_hinge(a)/(10-a)
    bad13 = ((1-c11/11)*source_hinge(c)+F(21, 110)*c11*source_hinge(c/2)+c11*c/220)/(12-c)
    rho = 1-bad11-bad13
    energies, tails = {}, {}
    for t in (16, 81):
        finite = {n: probability(caps, n) for n in range(1, isqrt(t))}
        q0 = 1-sum(finite.values())
        q2 = moment(caps, 2)-sum(n*n*p for n, p in finite.items())
        require(min(q0, q2) > 0 and all(F(t, n*n) > 1 for n in finite), 'Complete exact quadratic tail')
        energies[t] = G*q2-t*q0+sum(p*n*n*min(source_hinge(F(t, n*n), 2), G-1) for n, p in finite.items())
        tails[t] = {'finite_probabilities': finite, 'complete_tail_mass': q0, 'complete_tail_square': q2}
    hinges = {h: SOURCE_FACTOR*product_hinge(SOURCE_CAPS+caps, F(h)) for h in (5, 6, 7, 8)}
    numerator = AC*energies[16]+sum(w*hinges[h] for h, w in W17)
    numerator += F(15, 17)*sum(w*hinges[h] for h, w in W19)+F(13299, 1360)*hinges[5]+energies[81]
    require(numerator > 0 and min(energies.values()) > 0, 'Positive complete numerator')
    return {'thresholds': [a, c], 'caps': caps, 'source_G': G, 'bad11_upper': bad11,
            'bad13_upper': bad13, 'survival_lower': rho, 'quadratic_numerators': energies,
            'hinge_numerators': hinges, 'complete_quadratic_tails': tails, 'positive_numerator': numerator}


def evaluate(a, c, G=SOURCE_G):
    row = ingredients(a, c, G)
    rho = row['survival_lower']
    require(rho > 0, 'Positive new-law conditioning')
    return row | {'Gamma13': 16+row['quadratic_numerators'][16]/rho,
                  'T13_81': row['quadratic_numerators'][81]/rho,
                  'complete_hinges': {h: v/rho for h, v in row['hinge_numerators'].items()},
                  'complete_bound': C0+row['positive_numerator']/rho}


def core_errors(row, kc):
    a, c = row['thresholds']
    require(1 < a < 10 and 1 < c < 12, 'Strictly admissible physical core kernels')
    c11, c13 = (x[1] for x in row['caps'])
    rho, gamma = row['survival_lower'], row['Gamma13']
    D0, G0 = F(432, 53), F(3849, 106)
    D = c11*c13*D0/rho
    m11, m13 = 1+c11*(kc.phi(11, 0)-1), 1+c13*(kc.phi(13, 0)-1)
    rows = []
    for heights, current in (([20]*7, (8, 8)), ([17, 10, 8, 7, 6, 6, 6], (6, 6))):
        box = list(zip((3, 5, 7, 11, 13, 17, 19), heights))
        b3, b4 = box[:3], box[:4]
        e0w = D0*(G0*kc.factors(b3, False)[0]+kc.factors(b3, True)[0])
        e0m = 2*D0*kc.factors(b3, False)[0]
        ew = m13*(m11*e0w+kc.step(11, a, b3, heights[3], D0, G0, True))
        ew += kc.step(13, c, b4, heights[4], c11*D0, m11*G0, True)
        em = e0m+kc.step(11, a, b3, heights[3], D0, F(1), False)
        em += kc.step(13, c, b4, heights[4], c11*D0, F(1), False)
        incoming_w, incoming_m = (ew+gamma*em)/rho, 2*em/rho
        a2 = kc.step(17, 8, box[:5], current[0], D, gamma, True)
        a0 = kc.step(17, 8, box[:5], current[0], D, F(1), False)
        b2 = kc.step(19, 8, box[:6], current[1], 2*D, F(89, 64)*gamma, True)
        b0 = kc.step(19, 8, box[:6], current[1], 2*D, F(1), False)
        mask = F(59, 45)*a2+b2+483*(a0+b0)
        incoming = F(5251, 2880)*incoming_w+242*incoming_m
        full = prod(F(p*(p+1), (p-1)**2) for p, _ in box)
        head = prod(1+sum(F(2*j+1, p**j) for j in range(1, k+1)) for p, k in box)
        test = F(18, 5)*D*(full-head)
        error = mask+incoming+test
        require(error > 0, 'Positive complete core error')
        rows.append({'box': box, 'current': current, 'D13': D, 'weighted_propagation': [m11, m13],
                     'steps': [a2, a0, b2, b0], 'incoming_source': [incoming_w, incoming_m],
                     'mask': mask, 'incoming': incoming, 'test': test, 'error': error,
                     'complete_bound_with_error': row['complete_bound']+error,
                     'gap403': row['complete_bound']+error-403,
                     'test_labels': prod(k+1 for _, k in box)})
    return rows


def continuous_comparison():
    xs = tuple(map(F, range(1, 10)))+(F(100, 11),)
    ys = tuple(map(F, range(1, 12)))+(F(144, 13),)
    corners, positive = [], []
    for a in xs:
        for c in ys:
            row = ingredients(a, c)
            rho = row['survival_lower']
            bound = C0+row['positive_numerator']/rho if rho > 0 else None
            corners.append({'thresholds': [a, c], 'survival_lower': rho,
                            'positive_numerator': row['positive_numerator'], 'complete_bound': bound})
            if bound is not None:
                positive.append((bound, a, c))
    best = min(positive)
    require(sum(v[0] == best[0] for v in positive) == 1 and best[1:] == (F(4), F(4)),
            'Unique minimum corner at the new admissible law')
    def scaled(a, c):
        r = ingredients(a, c)
        factor = (10-a)*(12-c)
        return r['survival_lower']*factor, r['positive_numerator']*factor
    checks = 0
    for a0, a1 in zip(xs, xs[1:]):
        for c0, c1 in zip(ys, ys[1:]):
            vertices = [scaled(a, c) for a, c in ((a0, c0), (a0, c1), (a1, c0), (a1, c1))]
            value = scaled((2*a0+a1)/3, (c0+3*c1)/4)
            weights = (F(1, 6), F(1, 2), F(1, 12), F(1, 4))
            for j in range(2):
                require(value[j] == sum(w*v[j] for w, v in zip(weights, vertices)), 'Biaffine cell arithmetic identity')
                checks += 1
    require(len(corners) == 120 and len(positive) == 95 and checks == 198, 'Complete knot-cell inventory')
    return {'threshold_domain': [[F(1), xs[-1]], [F(1), ys[-1]]], 'lower_endpoints_are_limits': True,
            'corners': corners, 'positive_survival_corners': len(positive), 'biaffine_identity_checks': checks,
            'minimum_thresholds': list(best[1:]), 'minimum_complete_bound': best[0],
            'gap403': best[0]-403,
            'scope': 'The ordinary polynomial-degree and positive linear-fractional argument extends the corner minimum throughout the nonnegative geometric-count domain. Higher-cap saturated comparison laws and stronger source estimates are outside this conclusion.'}


def calculate(base):
    require(PINS, 'Final input pins')
    io = module('threshold_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    provider = module('threshold_original', base/'frontier/comparison-bounds/branch_local_fallback_comparison.py')
    original = provider.calculate(base)
    stored = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/branch_local_fallback_comparison.json'))
    require(original == stored and len(original['fallbacks']) == 8, 'All eight original232 complete fallback records')
    source = module('threshold_source', base/'verify_joint_frontier.py')
    kc = module('threshold_core', base/'verify_killed_core_continuity.py')
    core = module('threshold_original_core', base/'frontier/cover-geometry/ap_schedule_core.py')
    last = original['fallbacks'][-1]
    require(last['branch'] == '9-absent-or-ineffective/5-present/7-present'
            and tuple(map(F, last['original_pure_masses'])) == (F(2, 3), F(4, 5), F(6, 7))
            and F(last['original_density_bound']) == F(432, 73), 'The same original final fallback source')
    require(source.AC == AC and source.WHOLE_CONST == C0 and source.WEIGHT17 == W17
            and source.WEIGHT19 == W19, 'Unchanged later17/19 row-potential constants')
    for _, pure, density in source.FALLBACK_INPUTS[4:]:
        require(density*prod(pure) <= SOURCE_FACTOR
                and all(1/u <= cap for u, (_, cap) in zip(pure, SOURCE_CAPS)), 'All full/core missing9 subcases are contained')
    old = evaluate(F(4), F(5), F(102715, 2916))
    require(old['complete_bound'] == F(last['complete_bound'])
            and old['Gamma13'] == F(last['branch_Gamma13'])
            and old['T13_81'] == F(last['complete_T13_81']), 'Independent232 final-branch reproduction')
    same_law = evaluate(F(4), F(5))
    reference_cores = core.core_errors(kc, {'G': '3849/106', 'survivor_density_lower': '53/432'},
        same_law['Gamma13'], same_law['survival_lower'], same_law['T13_81'], same_law['complete_bound']-same_law['T13_81'])[1]
    for generic, prior in zip(core_errors(same_law, kc), reference_cores):
        require(all(generic[k] == prior[k] for k in ('mask', 'incoming', 'test'))
                and generic['error'] == prior['total'], 'General core formula specializes exactly to AP(4,5)')
    changed = evaluate(F(4), F(4))
    changed['complete_cores'] = core_errors(changed, kc)
    require(403 < changed['complete_bound'] < same_law['complete_bound'] < old['complete_bound'], 'Strict improvement and remaining403 gap')
    delta, C, s = F(3, 11), F(11, 8), F(11, 12)
    ell = max(C*C, C/delta)
    require((ell, ell/s**2, (ell+C)/s**2) == (F(121, 24), F(6), F(84, 11))
            and changed['complete_cores'][0]['weighted_propagation'] == [F(23, 15), F(67, 48)], 'New physical13 sensitivities and propagation')
    changed['physical13_sensitivity'] = {'delta': delta, 'C': C, 'pure_lower': s,
                                       'ell': ell, 'ell_over_s_square': ell/s**2, 'ell_plus_C_over_s_square': (ell+C)/s**2}
    optimization = continuous_comparison()
    require(optimization['minimum_complete_bound'] == changed['complete_bound'], 'The complete continuous-domain minimum')
    fallbacks = [{'branch': r['branch'], 'thresholds': [4, 5], 'complete_bound': F(r['complete_bound'])}
                 for r in original['fallbacks'][:-1]]
    fallbacks.append({'branch': last['branch'], 'thresholds': [4, 4], 'complete_bound': changed['complete_bound']})
    require(all(r['complete_bound'] < 403 for r in fallbacks[:-1]) and fallbacks[-1]['complete_bound'] > 403,
            'All eight cases and their exact403 signs')
    pins = dict(original['source_sha256'])
    require(all(path not in pins or pins[path] == pin for path, pin in PINS.items()), 'Consistent original source closure')
    pins.update(PINS)
    return encode({'schema': 'erdos7-branch-threshold-fallback-comparison-v1', 'source_sha256': pins,
                   'fallbacks': fallbacks, 'original232_last_complete_bound': old['complete_bound'],
                   'same_law_branch_norm_comparison': same_law, 'new_last_branch_comparison': changed,
                   'continuous_threshold_comparison': optimization,
                   'unchanged_global_bound': original['unchanged_global_bound'],
                   'scope': 'Seven original232 fallback bounds retain AP(4,5). Only the last missing9 branch uses the actual AP(4,4) law, its same-source norm, complete count tails and both recomputed cores. The inherited threshold interface stays above403 throughout the stated continuous domain. No effective9/global improvement, complete52-cost comparison, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('threshold_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact complete threshold certificate')
    new = result['new_last_branch_comparison']
    print('Last fallback AP(4,4): '+str(float(F(new['complete_bound'])))+', gap403='+str(float(F(new['complete_bound'])-403)))
    print('Complete core errors: '+str([float(F(r['error'])) for r in new['complete_cores']]))
    print('PASS: all eight fallbacks, complete changed-law tails/cores and120 continuous-domain corners;403 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
