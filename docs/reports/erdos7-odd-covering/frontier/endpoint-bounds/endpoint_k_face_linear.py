#!/usr/bin/env python3
"""Exact cap arithmetic for a linear gap on the actual controlling beta face.

The ordinary proof supplies the arbitrary-source geometry. All beta values
in the simplex are covered by affine formulas and fixed max branches.
Independent original test residues and complete exponent tails are retained.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
PIN = 'f8921b87de7b31cf834ef0c1fdd3df4802266e0dc990b19d86bf666221df235d'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    name = 'frontier/endpoint-bounds/endpoint_linear_neighborhood.py'
    require(sha256((base/name).read_bytes()).hexdigest() == PIN, 'Pinned exact identity source')
    spec = importlib.util.spec_from_file_location('k_face_neighborhood', base/name)
    require(spec is not None and spec.loader is not None, 'Loadable identity source')
    prior = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(prior)
    saturation = prior.load(base, 'frontier/source-budgets/source_barrier_saturation.py', 'k_face_saturation')
    engine = saturation.Experiment(base)
    eta = (F(1, 18),)+(F(1, 9),)*4
    root = (0, 0, 1, 1, 1)
    multiplier = [[1-F(int(c >= 2)+int(c == 1)+int(s == 4)+int(c >= 2 and s == 4), 5)
                   for s in range(5)] for c in range(5)]
    slots = []
    for L in (2, 3, 4):
        pre = [[F(0), F(1, 5) if c < 2 else F(0), F(0) if c == L else F(1, 5),
                F(3, 20) if c < 2 else F(1, 10), F(1, 5)] for c in range(5)]
        kept = [[eta[c]*pre[c][s]*multiplier[c][s] for s in range(5)] for c in range(5)]
        columns = [sum(kept[c][s] for c in range(5)) for s in range(5)]
        rooted = [[sum(kept[c][s] for c in range(5) if root[c] == r) for s in range(5)] for r in range(2)]
        require(max(columns) == F(29, 450) and max(map(max, rooted)) == F(8, 225), 'Same caps for every first-beta source cell')
        slots.append({'first_beta_cell': L, 'pre_coefficients': pre, 'columns': columns, 'root_columns': rooted})
    b, c = (2, 3, 1, 1, 1), (1, 2, 2, 2, 2)
    k = tuple(F(6-x) for x in b)
    vertices = []
    for index in (398, 410, 422):
        dat = engine.source.data(engine.parameters[index])
        d, n, et, s, D = dat
        require(et == eta and s == F(1, 4) and D == F(53, 360), 'Exact controlling face vertex')
        require(prior.complete_cap(dat) == F(37, 72) and max(n) == n[1] and max(d) == d[0], 'Fixed cap max branches across the whole simplex')
        cells = [n[j]*(1-F(int(j >= 2)+int(j == 1), 5))-eta[j]*F(1+int(j >= 2), 20) for j in range(5)]
        roots = (sum(cells[:2]), sum(cells[2:]))
        require(roots == (F(31, 360), F(7, 90)) and max(cells) == F(11, 180), 'Uniform ternary caps')
        deep = [d[j]*(1-F(int(j >= 2)+int(j == 1), 5))-F(1+int(j >= 2), 20) for j in range(5)]
        require(min(deep) >= 0 and max(deep) == F(7, 10), 'Nonnegative deep3 coefficients and common maximum')
        a = tuple(k[j]*n[j]-c[j]*eta[j]/5 for j in range(5))
        z = tuple(k[j]*d[j]-F(c[j], 5) for j in range(5))
        w = tuple(9*eta[j]*k[j] for j in range(5))
        kd = tuple(k[j]*d[j] for j in range(5))
        require(max(z) == z[0] == F(14, 5) and max(kd) == kd[0] == 3
                and w == (2, 3, 5, 5, 5), 'Fixed old-cost max branches; affine continuation covers the face')
        T = F(13, 243)*z[0]+F(1, 486)*kd[0]+(sum(w)+prior.roots(w)+max(w))/36+max(k)/72
        U = prior.exact_old_U(dat, b, c, engine.source.BASES)
        carrier = sum(a[2:])+a[1]
        margin = 6*s-U-(carrier+T)/5
        require(margin == F(9257, 48600), 'One fixed layout bounds the old margin throughout the face')
        vertices.append({'index': index, 'data': dat, 'ternary_cell_caps': cells,
                         'deep3_coefficients': deep, 'old_layout_U': U, 'old_layout_T': T,
                         'old_layout_carrier': carrier, 'old_margin_upper': margin})
    require(len({v['old_layout_U'] for v in vertices}) == len({v['old_layout_T'] for v in vertices})
            == len({v['old_layout_carrier'] for v in vertices}) == 1, 'Constant affine old-layout witness')
    deep5 = sum(eta)-(sum(eta[2:])+eta[1])/5
    require(deep5 == F(37, 90), 'Complete pure5 surviving coefficient')
    categories = {'unit': F(53, 360), 'test3': F(31, 360), 'test9': F(11, 180),
                  'test5': F(29, 450), 'test15': F(8, 225), 'pure3_deep': F(7, 10)*F(1, 18),
                  'pure5_deep': deep5*F(1, 20), '3_times_deep5': F(1, 60),
                  '9_times5': F(1, 36), 'deep35': F(1, 72), 'positive7': F(11, 72)}
    upper = sum(categories.values())
    margin = 6*F(53, 360)-upper
    gain = margin-F(9257, 48600)
    require((upper, margin, gain) == (F(133, 200), F(131, 600), F(677, 24300)), 'Whole original-label linear sum and strict gain')
    return encode({'schema': 'erdos7-endpoint-k-face-linear-v1',
                   'source_sha256': {name: PIN, **prior.PINS},
                   'face_vertices': [398, 410, 422], 'carrier': [1, 1],
                   'symmetric_face_vertices': [616, 628, 640], 'symmetric_carrier': [1, 0],
                   'beta_simplex_mass': F(1, 4), 'actual_first_beta_mass': F(1, 5),
                   'first_beta_slot_tables': slots, 'affine_vertex_checks': vertices,
                   'old_fixed_layouts': [b, c], 'complete_test_categories': categories,
                   'linear_upper': upper, 'signed_barrier': 6, 'margin_lower': margin,
                   'old_margin_upper': F(9257, 48600), 'strict_margin_gain': gain,
                   'scope': 'Ordinary actual endpoint theorem uniform along both full controlling beta faces at saturated mass. No assertion that all relaxed beta points are realizable, no neighborhood or global K update.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(args.base)
    if args.check:
        require(json.loads((args.base/'certificates/source_norms/endpoint-bounds/endpoint_k_face_linear.json').read_text()) == result, 'Canonical exact face certificate')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS:three first-beta tables, exact affine face witnesses, all original-label tails; linear133/200, gain677/24300.')


if __name__ == '__main__':
    main()
