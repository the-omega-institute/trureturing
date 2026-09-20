#!/usr/bin/env python3
"""Six actual source cells, exact signed margins and complete last fallback."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import isqrt, prod
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/cover-geometry/missing9_six_cell_fallback.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/comparison-bounds/branch_threshold_fallback_comparison.py': 'b82537eed7ddaeea563f301cb2801f30c35b4d66626a8dba4d1367b193ecfe6e', 'certificates/source_norms/comparison-bounds/branch_threshold_fallback_comparison.json': '1ea3d89dd46f9d77bfb93e20efec3f60cc4013bf45f264874c8621451630a130', 'verify_killed_core_continuity.py': '6de7cb0f3aafa1d6db95017dd82c99d756e89b398996017ea1c1d77808f65226', 'profile-notes/001-064/32-unequal-source-norms-sharpen-the-uniform357-input.md': '039c03bf76c3f3e4070639cf0a97dcfd5865fa7678c8caeeecd7224ad96be5c0', 'profile-notes/001-064/35-ap45-layout-costs-and-complete-core-tails.md': '5b7569bc8a8ac2c03287e8cba51140c390327405126ea2291d7b3073e14f1c20', 'profile-notes/193-256/236-the-last-missing9-branch-uses-a-better-ap-threshold.md': '7a6d5134f82edb5333df58a8a843de53d274b13fc31e7aa3f61b8fa0f026bad5', 'problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md': 'b22079eb61c26a2bafd5310f075754ea1f78cca5582fc46f6dc75513e2d09b4d'}
ROOTS = (0, 0, 0, 1, 1, 1)
SOURCE_G, SOURCE_MASS = F(13591, 468), F(19, 108)
PURE_MASSES = (F(2, 3), F(4, 5), F(6, 7))


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


def simplex(dimension, budget):
    return [tuple(budget if j == i else F(0) for j in range(dimension))
            for i in range(-1, dimension)]


def source_margins():
    layouts = [(r, j, tuple(1+int(ROOTS[l] == r)+int(l == j) for l in range(6)))
               for r in range(2) for j in range(6)]
    groups = (simplex(6, F(1, 2)), simplex(2, F(1, 4)), simplex(6, F(1, 4)),
              simplex(6, F(1, 72)), (F(3, 4), F(1)))
    require(prod(map(len, groups)) == 2058 and len(layouts) == 12, 'Complete product domain')
    square_min, mass_min, s_min = F(100), F(100), F(100)
    square_witnesses, mass_witnesses, count = [], [], 0
    square_digest, mass_digest = sha256(), sha256()
    for vid, (delta, alpha, beta, late, z) in enumerate(product(*groups)):
        w = tuple(1-v for v in delta)
        eta = tuple(v/9 for v in w)
        d = tuple(z-alpha[ROOTS[l]]-beta[l] for l in range(6))
        n = tuple(eta[l]*d[l]-late[l] for l in range(6))
        s = sum(n)
        require(min(w) >= F(1, 2) and min(d) >= F(1, 4) and min(n) >= 0,
                'Nonnegative actual-cell containing parameters')
        pure_heads = [sum(x*b*b for x, b in zip(eta, B)) for _, _, B in layouts]
        M = max(head+F(max(Bi+1 for Bi in B), 9) for head, (_, _, B) in zip(pure_heads, layouts))
        heads = [sum(x*b*b for x, b in zip(n, B))+head/4
                 +max((dd+F(1, 4))*(b+1)/9 for dd, b in zip(d, B))+F(5, 8)*M
                 for head, (_, _, B) in zip(pure_heads, layouts)]
        U = max(heads)
        # Independent unweighted cylinder reconstruction for the actual mass.
        root_n = tuple(sum(n[l] for l in range(6) if ROOTS[l] == r) for r in range(2))
        root_w = tuple(sum(w[l] for l in range(6) if ROOTS[l] == r) for r in range(2))
        raw_components = (max(root_n), max(n), max(d)/18, sum(w)/36,
                          max(root_w)/36, max(w)/36, F(1, 72))
        raw = sum(raw_components)
        mass = F(5, 6)*s-raw/6
        require(mass >= SOURCE_MASS, 'Every complete actual357 mass margin')
        s_min = min(s_min, s)
        mass_record = {'vertex': vid, 'delta': delta, 'alpha': alpha, 'beta': beta,
                       'late': late, 'z': z, 'w': w, 'd': d, 'n': n, 's': s,
                       'raw_cofactor_components': raw_components, 'raw_cofactor_sum': raw,
                       'complete_source_mass_lower': mass, 'margin': mass-SOURCE_MASS}
        mass_digest.update(json.dumps(encode(mass_record), separators=(',', ':')).encode())
        if mass < mass_min:
            mass_min, mass_witnesses = mass, [mass_record]
        elif mass == mass_min:
            mass_witnesses.append(mass_record)
        for bid, ((r, j, B), Uj) in enumerate(zip(layouts, heads)):
            k = tuple(SOURCE_G-b*b for b in B)
            require(min(k) >= 0 and max(k) == SOURCE_G-1, 'Actual nonnegative test floor')
            weighted = (max(sum(k[l]*n[l] for l in range(6) if ROOTS[l] == root) for root in range(2)),
                        max(k[l]*n[l] for l in range(6)), max(k[l]*d[l] for l in range(6))/18,
                        sum(k[l]*w[l] for l in range(6))/36,
                        max(sum(k[l]*w[l] for l in range(6) if ROOTS[l] == root) for root in range(2))/36,
                        max(k[l]*w[l] for l in range(6))/36, (SOURCE_G-1)/72)
            W = sum(weighted)
            margin = SOURCE_G*s-F(6, 5)*Uj-F(7, 15)*U-W/5
            require(margin >= 0, 'Every fixed-C signed square margin')
            record = {'vertex': vid, 'layout': bid, 'root': r, 'cell': j, 'baseline': B,
                      'w': w, 'd': d, 'n': n, 's': s, 'pure_square': M,
                      'selected_square': Uj, 'global_square': U,
                      'weighted_cofactor_components': weighted, 'weighted_cofactor_sum': W,
                      'margin': margin}
            square_digest.update(json.dumps(encode(record), separators=(',', ':')).encode())
            count += 1
            if margin < square_min:
                square_min, square_witnesses = margin, [record]
            elif margin == square_min:
                square_witnesses.append(record)
    require(vid+1 == 2058 and count == 24696 and s_min == F(1, 3)
            and mass_min == SOURCE_MASS and square_min == 0, 'Exact complete source extrema')
    return {'roots': ROOTS, 'group_vertex_counts': list(map(len, groups)), 'vertices': vid+1,
            'layouts': [(r, j) for r, j, _ in layouts], 'source_square': SOURCE_G,
            'source_mass': SOURCE_MASS, 'source_density': 1/SOURCE_MASS,
            'minimum_two_prime_mass': s_min, 'square_margin_count': count,
            'square_minimum_margin': square_min, 'square_margin_sha256': square_digest.hexdigest(),
            'square_equality_witnesses': square_witnesses,
            'mass_margin_count': vid+1, 'mass_minimum_margin': mass_min-SOURCE_MASS,
            'mass_margin_sha256': mass_digest.hexdigest(), 'mass_equality_witnesses': mass_witnesses}


def changed_consumer(provider, kc):
    a = c = F(4)
    G, factor = SOURCE_G, prod(PURE_MASSES)/SOURCE_MASS
    source_caps = tuple((p, 1/u) for p, u in zip((3, 5, 7), PURE_MASSES))
    require(source_caps == provider.SOURCE_CAPS, 'Same actual first forbidden roots')
    H = lambda threshold, degree=1: factor*provider.product_hinge(source_caps, threshold, degree)
    c11, c13 = F(10, 10-a), F(12, 12-c)
    caps = ((11, c11), (13, c13))
    bad11 = H(a)/(10-a)
    bad13 = ((1-c11/11)*H(c)+F(21, 110)*c11*H(c/2)+c11*c/220)/(12-c)
    rho = 1-bad11-bad13
    require(0 < rho < 1, 'Positive sole final conditioning')
    energies, tails = {}, {}
    for t in (16, 81):
        finite = {n: provider.probability(caps, n) for n in range(1, isqrt(t))}
        q0 = 1-sum(finite.values())
        q2 = provider.moment(caps, 2)-sum(n*n*p for n, p in finite.items())
        require(q0 > 0 and q2 >= t*q0, 'Complete quadratic count tails')
        heads = {n: min(H(F(t, n*n), 2), G-1) for n in finite}
        energies[t] = G*q2-t*q0+sum(finite[n]*n*n*v for n, v in heads.items())
        tails[t] = {'finite_probabilities': finite, 'source_square_hinges': heads,
                    'complete_tail_mass': q0, 'complete_tail_square': q2}
    hinges = {h: factor*provider.product_hinge(source_caps+caps, F(h)) for h in (5, 6, 7, 8)}
    numerator = provider.AC*energies[16]+sum(v*hinges[h] for h, v in provider.W17)
    numerator += F(15, 17)*sum(v*hinges[h] for h, v in provider.W19)
    numerator += F(13299, 1360)*hinges[5]+energies[81]
    row = {'thresholds': [a, c], 'caps': caps, 'source_G': G, 'source_density': 1/SOURCE_MASS,
           'source_factor': factor, 'source_pure_masses': PURE_MASSES, 'source_caps': source_caps,
           'bad11_upper': bad11, 'bad13_upper': bad13, 'survival_lower': rho,
           'quadratic_numerators': energies, 'hinge_numerators': hinges,
           'complete_quadratic_tails': tails, 'positive_numerator': numerator,
           'Gamma13': 16+energies[16]/rho, 'T13_81': energies[81]/rho,
           'complete_hinges': {h: value/rho for h, value in hinges.items()},
           'complete_bound': provider.C0+numerator/rho}
    row['complete_cores'] = provider.core_errors(row, kc)
    row['core_initial_constants'] = {'density': F(432, 53), 'square': F(3849, 106),
                                     'basis': 'Unchanged valid global full/core comparison from236'}
    require(0 < row['complete_bound'] < 403
            and all(r['complete_bound_with_error'] < 403 for r in row['complete_cores']),
            'Both complete last-branch finite-core criteria close')
    return row


def calculate(base):
    require(PINS, 'Final input pins')
    io = module('six_cell_io', base/'certificate_io.py')
    pins = dict(PINS)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/branch_threshold_fallback_comparison.json'))
    for path, pin in previous['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent236 dependency closure')
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical input '+path)
    require(previous['schema'] == 'erdos7-branch-threshold-fallback-comparison-v1'
            and len(previous['fallbacks']) == 8, 'Complete original236 fallback inventory')
    provider = module('six_cell_thresholds', base/'frontier/comparison-bounds/branch_threshold_fallback_comparison.py')
    kc = module('six_cell_core', base/'verify_killed_core_continuity.py')
    geometry = source_margins()
    row = changed_consumer(provider, kc)
    fallbacks = previous['fallbacks'][:-1]+[{'branch': previous['fallbacks'][-1]['branch'],
                                          'thresholds': [4, 4], 'complete_bound': row['complete_bound']}]
    require(fallbacks[-1]['branch'] == '9-absent-or-ineffective/5-present/7-present'
            and all(F(r['complete_bound']) < 403 for r in fallbacks), 'Every complete fallback is below403')
    return encode({'schema': 'erdos7-missing9-six-cell-fallback-v1', 'source_sha256': pins,
                   'six_cell_source': geometry, 'new_last_branch_comparison': row,
                   'fallbacks': fallbacks, 'previous_last_complete_bound': previous['fallbacks'][-1]['complete_bound'],
                   'scope': 'Six actual missing/ineffective9 source cells; fixed-C full continuous-domain ordinary proof supported by24696 exact signed margins and2058 mass margins. Complete same-source AP(4,4) last fallback and both full core errors are below403. The other seven236 fallback records retain their own AP(4,5) laws and exact bounds. No effective9/global conclusion, new threshold optimization, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('six_cell_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact complete six-cell certificate')
    row = result['new_last_branch_comparison']
    print('Six-cell source square='+str(SOURCE_G)+'; actual mass>='+str(SOURCE_MASS))
    print('Last AP(4,4) fallback='+str(float(F(row['complete_bound'])))
          +'; core errors='+str([float(F(r['error'])) for r in row['complete_cores']]))
    print('PASS:24696 square margins,2058 mass margins,all8 complete fallbacks and both last-branch core criteria.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
