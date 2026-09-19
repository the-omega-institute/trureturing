#!/usr/bin/env python3
"""Whole actual J-face alignment and complete original-label identity caps.

The accompanying ordinary proof supplies labelwise saturation and geometry.
This exact program checks its affine tables, existing cost interface, and
an existing finite labelled construction. It does not enumerate all families.
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
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_alignment.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/endpoint-bounds/endpoint_linear_neighborhood.py': 'f8921b87de7b31cf834ef0c1fdd3df4802266e0dc990b19d86bf666221df235d',
}
ROOT = (0, 0, 1, 1, 1)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
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


def calculate(base):
    for path, pin in PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin, 'Pinned input '+path)
    prior = module('j_face_prior', base/'frontier/endpoint-bounds/endpoint_linear_neighborhood.py')
    for path, pin in prior.PINS.items():
        require(sha256((base/path).read_bytes()).hexdigest() == pin, 'Inherited input '+path)
    saturation = prior.load(base, 'frontier/source-budgets/source_barrier_saturation.py', 'j_face_source')
    engine = saturation.Experiment(base)
    eta = (F(1, 18),)+(F(1, 9),)*4
    h0, h1, h = sum(eta[:2]), sum(eta[2:]), sum(eta)
    late1 = F(1, 18)*F(1, 5)
    later = F(1, 18)*F(1, 20)
    gap5 = (h/5, h1/5, eta[2]/5, h/25)
    gap15 = (h1/5, h1/5, eta[2]/5, h1/25, (h1-h0)/5)
    require(late1 == F(1, 90) and later == F(1, 360), 'Complete late depth families')
    require(min(gap5+gap15) >= late1, 'Every other slot/root loses at least the entire aligned budget')
    alignment_price = 2*F(1, 5)
    require(alignment_price*F(1, 135) == F(2, 675), 'First late label gives a positive sector gap')
    slots = []
    for L in (2, 3, 4):
        for M in (j for j in (2, 3, 4) if j != L):
            pre = [[eta[l]*x for x in
                    (F(0), F(1, 5) if l < 2 else F(0),
                     F(0) if l == L else F(1, 5),
                     F(3, 20) if l < 2 else F(1, 10), F(1, 5))]
                   for l in range(5)]
            pre[M][2] -= late1
            kept = [[pre[l][j]*(1-F(int(l < 2)+int(l == 1)
                                    +int(j == 4)+int(l >= 2 and j == 4), 5))
                     for j in range(5)] for l in range(5)]
            require(min(map(min, kept)) >= 0, 'Positive source majorant after mandatory late deletion')
            qslots = tuple(map(F, ('0', '1/5', '1/5', '3/20', '1/5')))
            columns = [sum(kept[l][j] for l in range(5))-qslots[j]/90 for j in range(5)]
            roots = [[sum(kept[l][j] for l in range(5) if ROOT[l] == r)
                      for j in range(5)] for r in (0, 1)]
            require(columns == list(map(F, ('0', '1/50', '4/75', '29/600', '4/75'))),
                    'All beta locations and all late-allocation vertices have the same column caps')
            require(max(map(max, roots)) == F(1, 25), 'Every independent original15 root/slot')
            slots.append({'first_beta_cell': L, 'late_allocation_vertex': M,
                          'source_upper': pre, 'kept': kept,
                          'five_caps': columns, 'fifteen_caps': roots})
    b, c = (2, 3, 1, 1, 1), (1, 2, 2, 2, 2)
    k = tuple(F(6-x) for x in b)
    vertices = []
    for B, L in product(range(3), repeat=2):
        index = 402+12*B+2*L
        dat = engine.source.data(engine.parameters[index])
        d, n, et, s, D = dat
        require(et == eta and s == F(1, 4) and D == F(3, 20), 'J-face source data')
        require(prior.complete_cap(dat) == F(1, 2) and max(n) == n[1]
                and sum(n[:2]) == sum(n[2:]) == F(1, 8), 'Fixed affine cap branches')
        cells = [n[j]*(1-F(int(j < 2)+int(j == 1), 5))
                 -eta[j]*F(1+int(j >= 2), 20) for j in range(5)]
        roots = (sum(cells[:2]), sum(cells[2:]))
        deep = [d[j]*(1-F(int(j < 2)+int(j == 1), 5))
                -F(1+int(j >= 2), 20) for j in range(5)]
        require(roots == (F(3, 40), F(11, 120)) and max(cells) == F(2, 45)
                and min(deep) >= 0 and max(deep) == F(11, 20), 'Complete ternary caps')
        z = tuple(k[j]*d[j]-F(c[j], 5) for j in range(5))
        w = tuple(9*eta[j]*k[j] for j in range(5))
        a = tuple(k[j]*n[j]-c[j]*eta[j]/5 for j in range(5))
        require(max(z) == z[0] == F(14, 5)
                and max(k[j]*d[j] for j in range(5)) == 3, 'Fixed old-cost branches on the whole product simplex')
        T = (F(13, 243)*max(z)+F(1, 486)*3
             +(sum(w)+prior.roots(w)+max(w))/36+max(k)/72)
        U = prior.exact_old_U(dat, b, c, engine.source.BASES)
        carrier = a[0]+2*a[1]
        margin = 6*s-U-(carrier+T)/5
        require((U, T, carrier, margin) == (F(9, 10), F(12991, 9720), F(17, 30), F(10661, 48600)),
                'Same fixed-layout witness for every beta/late face vertex')
        vertices.append({'index': index, 'data': dat, 'ternary_caps': cells, 'root_caps': roots,
                         'deep3_coefficients': deep, 'U': U, 'T': T,
                         'carrier': carrier, 'old_margin_upper': margin})
    deep5 = h-(h0+eta[1])/5-F(1, 90)
    require(deep5 == F(13, 30), 'Complete deep3 deletion lowers the pure5 tail')
    categories = {'unit': F(3, 20), 'test3': F(11, 120), 'test9': F(2, 45),
                  'pure3_deep': F(11, 20)/18, 'test5': F(4, 75),
                  'pure5_deep': deep5/20, 'test15': F(1, 25),
                  '3_times_deep5': h1/20, '9_times5': max(eta)/4,
                  'deep35': F(1, 72), 'positive7': (F(1, 4)+F(1, 2))/5}
    upper = sum(categories.values())
    margin = 6*F(3, 20)-upper
    gain = margin-F(10661, 48600)
    require((upper, margin, gain) == (F(16, 25), F(13, 50), F(79, 1944)), 'Complete sum and old49 replacement reserve')
    constructor = prior.load(base, 'frontier/source-budgets/sharp_source_mass_endpoints.py', 'j_face_constructor')
    actual = constructor.check(3, 'off-diagonal')
    t, q = F(1, 18), F(1, 4)
    limit_s = F(5, 9)-t-q
    limit_H = F(1, 3)+2*q/3
    require(limit_s-limit_H/5 == F(3, 20), 'Existing actual off-diagonal construction saturates J')
    return encode({'schema': 'erdos7-j-face-alignment-v1', 'source_sha256': {**PINS, **prior.PINS},
                   'alignment': {'complete_b1': late1, 'complete_b_ge2': later,
                                 'five_other_slot_losses': gap5, 'fifteen_other_slot_losses': gap15,
                                 'price': alignment_price, 'aligned_first_label_gap': F(2, 675)},
                   'slot_tables': slots, 'affine_product_face_checks': vertices,
                   'complete_categories': categories, 'linear_upper': upper, 'margin_lower': margin,
                   'old49_margin_upper': F(10661, 48600), 'old49_replacement_reserve': gain,
                   'direction40_weight': engine.weights[40], 'weighted_old49_reserve': engine.weights[40]*gain,
                   'finite_off_diagonal_height3': actual,
                   'off_diagonal_limit': {'s': limit_s, 'H': limit_H, 'S': F(3, 20)},
                   'scope': 'Whole actual saturated J faces only, ordinary proof. No off-face or global-K update; relaxed source simplex need not be realizable.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j_face_io', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical J-face certificate')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: whole J-face alignment, six late-slot tables, nine affine source witnesses, complete tails and original construction.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
