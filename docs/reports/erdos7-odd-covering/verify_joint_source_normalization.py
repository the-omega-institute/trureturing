#!/usr/bin/env python3
"""Exact shared-geometry numerator and survival normalization for actual AP13.

Reuses pinned HC/SQ infinite-tail formulae. The ordinary proof supplies the
continuous separately concave margin; this checks every product vertex,
its required coefficient sign, and all other original missing-class branches.
Python 3.9+ standard library only; this is not Lean verification.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

BASE = Path(__file__).resolve().parent
G = F(3849, 106)
PINS = {
    'verify_shared_cell_hinges.py': '6011ceedba7ae157c8aa9f51d7f272901465114cdcf3a31bad276f0631cd94ad',
    'verify_shared_cell_square.py': '5c8bf6f4cdfcc939c6b74fcf1811f8b94712932c956d1e1d3990790e66aaccd0',
    'certificates/pure_root_profile_certificate.json': '045445deb47f22f4be3d06a8843a87b8ae4e8e19840aecd580c03e5ce3386d1a',
    'certificates/shared_cell_hinges_certificate.json': '7e7227e0b859ad6e30fd17915f40571eacea82cd9aadce09984ed6b7bd790674',
    'certificates/shared_cell_square_certificate.json': '5018f24fd0766b33591eeedf4889cd6c7e8881ef7223f1fe63092e192c373a3b',
    'certificates/shared_square_continuation_certificate.json': 'a6c71f4c41d87171956ba67343e571f3dae1bc510b5143544dd9f89b6d31f6a4',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def unique(pairs):
    out = {}
    for key, value in pairs:
        need(key not in out, 'duplicate JSON key: ' + key)
        out[key] = value
    return out


def module(directory, filename):
    spec = importlib.util.spec_from_file_location('jsn_' + filename[:-3], directory / filename)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def survival(hinges):
    # Exact simplification of HC9 with H1 <= H3+2 and H2 <= H3+1.
    direct = 1 - hinges[4] / 6 - (
        F(28, 33) * hinges[6] + F(100, 363) * hinges[3]
        + F(19300, 483153) * (hinges[3] + 1)
        + F(887, 322102) * (hinges[3] + 2) + F(1, 966306)) / 6
    simple = F(131, 132) - hinges[4] / 6 - F(14, 99) * hinges[6] - F(7, 132) * hinges[3]
    need(direct == simple, 'same full-tail charge coefficients')
    return simple


def raw_square(sq, threshold, dat, cache):
    def f(t):
        if t not in cache:
            cache[t] = sq.f35(t, dat)
        return cache[t]
    start = max(2, sq.ceilroot(threshold))
    mass, _, second = sq.tails(7, start)
    return (F(29, 35) * f(threshold)
            + sum((F(36 * n * n, 5 * 7**n) * f(threshold / (n * n))
                   for n in range(2, start)), F())
            + F(36, 5) * (second * f(F()) - threshold * mass * dat[3]))


def run_target(h, weights, source_rows, branches, sq):
    pm = sq.product_mass(((11, F(5, 3)), (13, F(2))), h)
    tail0 = 1 - sum(pm.values())
    tail2 = F(253, 108) - sum(n*n*p for n, p in pm.items())
    thresholds = {F(h*h, n*n) for n in pm}
    need(set(weights) <= thresholds, 'fixed weights on exactly relevant thresholds')
    need(all(0 <= a <= 1 for a in weights.values()), 'convex mixture weights')
    fixed = G*tail2 - h*h*tail0 + sum(
        p*n*n*weights.get(F(h*h, n*n), F())*(G-1) for n, p in pm.items())
    values = []
    for par, dat, delta, rho in source_rows:
        cache = {}
        raw = dat[4] * fixed
        for n, p in pm.items():
            t = F(h*h, n*n)
            a = weights.get(t, F())
            if a != 1:
                raw += p*n*n*(1-a)*raw_square(sq, t, dat, cache)
        values.append((raw / delta, par, raw, delta))
    maximum, witness, _, _ = max(values, key=lambda row: row[0])
    coefficient = maximum*F(131, 132) - fixed
    need(coefficient >= 0, 'continuous concavity coefficient, not only vertex tests')
    margin = min(maximum*delta - raw for _, _, raw, delta in values)
    need(margin == 0, 'nonnegative margins with an attained vertex')
    fallbacks = []
    for branch in branches:
        if branch['ternary_case'] == 'modulus9_effective':
            continue
        hinges = {k: F(branch['profile'][str(k)]) for k in (3, 4, 6)}
        rho = survival(hinges)
        need(rho > 0, 'fallback survival')
        raw = G*tail2 - h*h*tail0 + sum(
            p*n*n*min(sq.fallback(branch, F(h*h, n*n)), G-1)
            for n, p in pm.items())
        bound = raw / rho
        need(bound <= maximum, 'every other original missing-class branch')
        fallbacks.append({
            'ternary_case': branch['ternary_case'],
            'modulus5_present': branch['modulus5_present'],
            'modulus7_present': branch['modulus7_present'],
            'survival_lower': rho, 'supported_hinge': bound,
        })
    need(len(fallbacks) == 8 and len(values) == 1296, 'full branch and vertex counts')
    return {
        'h': h, 'tau': h*h, 'uniform_cap_weights': weights,
        'AP_tail_mass': tail0, 'AP_tail_second_moment': tail2,
        'D_coefficient_in_numerator': fixed,
        'continuous_concavity_coefficient': coefficient,
        'minimum_vertex_margin': margin, 'relaxed_maximum_vertex': witness,
        'supported_hinge': maximum, 'shift_square': h*h + maximum,
        'other_eight_branches': fallbacks,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-directory', type=Path, default=BASE)
    parser.add_argument('--certificate', type=Path, default=BASE/'certificates/joint_source_normalization_certificate.json')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    sources = {}
    for name, pin in PINS.items():
        raw = read_artifact_bytes(args.source_directory/name)
        need(hashlib.sha256(raw).hexdigest() == pin, 'pinned input: ' + name)
        if name.endswith('.json'):
            sources[name] = json.loads(raw, object_pairs_hook=unique)
    hc = module(args.source_directory, 'verify_shared_cell_hinges.py')
    sq = module(args.source_directory, 'verify_shared_cell_square.py')
    source_rows = []
    for par in hc.params():
        hinges, den = hc.exact(par)
        dat = sq.data(par)
        need(den == F(5, 6)*dat[4], 'HC and SQ share the exact source denominator')
        rho = survival(hinges)
        delta = dat[4]*rho
        need(delta > 0, 'joint raw survival denominator at each vertex')
        source_rows.append((par, dat, delta, rho))
    pr = sources['certificates/pure_root_profile_certificate.json']
    old = sources['certificates/shared_cell_square_certificate.json']['targets']
    need(F(pr['source_inputs']['G']) == G and len(pr['branches']) == 12, 'original source scope')
    targets = [
        run_target(4, {F(16, 9): F(1)}, source_rows, pr['branches'], sq),
        run_target(9, {F(81, 64): F(1), F(81, 49): F(1), F(9, 4): F(1)},
                   source_rows, pr['branches'], sq),
    ]
    need(targets[0]['shift_square'] < F(old[0]['shift_square']), 'strict same-law square improvement')
    need(targets[1]['supported_hinge'] < F(old[1]['supported_hinge']), 'strict same-law tail improvement')
    budgets = []
    for prior, safe in zip(sources['certificates/shared_square_continuation_certificate.json']['killed_frontier_budgets'],
                           (F(299923, 1000), F(299661, 1000))):
        need(prior['W'] == 403 and prior['tau'] == 81, 'unchanged signed objective')
        error = F(prior['previous_KC_safe_error'])
        available = 403 - targets[1]['supported_hinge'] - error
        need(available > safe > F(prior['sufficient_frontier_bound']), 'strictly larger sufficient allowance')
        budgets.append({'box': prior['box'], 'current': prior['current'], 'W': 403,
                        'previous_KC_safe_error': error, 'available_frontier': available,
                        'sufficient_frontier_bound': safe, 'slack': available-safe})
    need(len(budgets) == 2, 'both existing finite cores')
    result = sq.encode({
        'schema': 'erdos7-joint-source-normalization-v1', 'source_sha256': PINS,
        'source_square': G, 'vertex_count': len(source_rows), 'original_branch_count': 12,
        'minimum_D': min(row[1][4] for row in source_rows),
        'minimum_Delta': min(row[2] for row in source_rows),
        'minimum_vertex_survival': min(row[3] for row in source_rows),
        'targets': targets,
        'killed_frontier_budgets': budgets,
        'scope': 'Same actual uniform357, AP11/T4, AP13/T6 and sole conditioning. All original labels, residues, missing classes and finite heights; complete tails. Ordinary continuous-domain proof, not Lean or actual-layout sharpness.',
    })
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2)+'\n')
    else:
        need(json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique) == result,
             'whole certificate mismatch')
    print('PASS 1296 common vertices, 12 branches, full tails and concavity coefficients; Gamma13 <= '
          + str(float(targets[0]['shift_square'])) + '; T13(81) <= '
          + str(float(targets[1]['supported_hinge'])))


if __name__ == '__main__':
    main()
