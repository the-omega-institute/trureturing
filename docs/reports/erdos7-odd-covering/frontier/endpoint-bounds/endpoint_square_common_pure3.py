#!/usr/bin/env python3
"""A common zero-seven layout and complete pure3 tails give square469/100.

Every shallow layout retains its own surviving and raw-source bounds.
The final common-layout comparison uses exact rational quadratic tests,
not numerical square roots. Read-only unless --output is supplied.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
PINS = {
    'frontier/endpoint-bounds/endpoint_linear_numerator.py': '646c6dce65185917554f77441c8c9d6373bb20021c1204cce01fd71f9a95e314',
    'certificates/source_norms/endpoint-bounds/endpoint_linear_numerator.json': 'c6d20392e71b3fb73b87d40b390b02fe50e9b92bd3245831bfa4d0b96e4875be',
    'frontier/endpoint-bounds/endpoint_square_numerator.py': '5973de37d2d74e2ddb7783baa514709e236f9a894000ca79ec8d66db79174235',
    'certificates/source_norms/endpoint-bounds/endpoint_square_numerator.json': 'a3cb0072765f1e10ce4642f1d46b1bd49ab71de339941a4065938ab59e7fcbea',
    'frontier/endpoint-bounds/endpoint_square_coherent_head.py': '49a216c2e61faddb88a914fb4d8338cdc5df05fbaa50435cff7be5c32f30e5de',
    'certificates/source_norms/endpoint-bounds/endpoint_square_coherent_head.json': '3108dafb33924ea416b59fb7c493531f2d35c3d69304c6e37398ddd8af70ecd6',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(base, relative, name):
    path = base/relative
    require(sha256(path.read_bytes()).hexdigest() == PINS[relative], 'Pinned source: '+relative)
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned source')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def affine_tail(lines):
    """Exact sum of3^(-a)*max_l(p_l*a+q_l), for all integers a>=3."""
    pstar, qstar = max(lines)
    cut = 3
    for p, q in lines:
        require(p >= 0 and 3*p+q >= 0, 'Nonnegative endpoint test-tail coefficient')
        if p < pstar:
            crossing = (q-qstar)/(pstar-p)
            cut = max(cut, -(-crossing.numerator//crossing.denominator))
    require(all(pstar >= p and pstar*cut+qstar >= p*cut+q for p, q in lines),
            'A single affine line dominates the entire remaining infinite tail')
    prefix = sum(max(p*a+q for p, q in lines)*F(1, 3**a) for a in range(3, cut))
    mass, first = F(1, 2*3**(cut-1)), F(2*cut+1, 4*3**(cut-1))
    return prefix+pstar*first+qstar*mass, cut


def tail_lines(B, pre, kept, roots):
    zero, raw = [], []
    for cell in range(5):
        values = B[5*cell:5*cell+5]
        loss = F(1+int(roots[cell] == 1), 100)
        require(kept[cell][3]+kept[cell][4] >= loss, 'Q/H weighted subtraction has a nonnegative remainder')
        zero_mass = sum(kept[cell])-loss
        zero_weight = sum(k*(2*b-5) for k, b in zip(kept[cell], values))
        zero_weight -= loss*(2*min(values[3], values[4])-5)
        raw_weight = sum(c*(2*b-5) for c, b in zip(pre[cell], values))
        require(zero_mass == F((11, 8, 3, 8, 8)[cell], 20), 'Same complete deep3 cylinder cap as59')
        zero.append((2*zero_mass, zero_weight))
        raw.append((2*sum(pre[cell]), raw_weight))
    return zero, raw


def cubic_tail(p, start):
    z = F(1, p)
    mass = z**start/(1-z)
    first = start+z/(1-z)
    second = start*start+2*start*z/(1-z)+z*(1+z)/(1-z)**2
    return mass*(3*second+3*first+1)


def third_moment():
    t3, t5 = cubic_tail(3, 3), cubic_tail(5, 1)
    raw = (F(1, 4)+7*F(1, 8)+19*F(1, 12)+F(3, 4)*t3
           +F(1, 2)*t5+F(7, 3)*t5+F(19, 9)*t5+t3*t5)
    loss = (F(1, 10)+7*F(1, 30)+19*F(7, 180)+7*F(2, 45)
            +49*F(2, 75)+F(1, 5)*t3+F(1, 18)*cubic_tail(5, 2))
    value = (1+F(6, 5)*cubic_tail(7, 1))*raw-loss
    require(value == F(3874891, 57600), 'Auxiliary complete cubic original-label cap sum')
    return value


def calculate(base):
    for relative, pin in PINS.items():
        require(sha256((base/relative).read_bytes()).hexdigest() == pin, 'Current dependency hash: '+relative)
    linear = load(base, 'frontier/endpoint-bounds/endpoint_linear_numerator.py', 'common_pure3_linear')
    square = load(base, 'frontier/endpoint-bounds/endpoint_square_numerator.py', 'common_pure3_square')
    head = load(base, 'frontier/endpoint-bounds/endpoint_square_coherent_head.py', 'common_pure3_head')
    old63 = json.loads((base/'certificates/source_norms/endpoint-bounds/endpoint_square_coherent_head.json').read_text())
    old62 = json.loads((base/'certificates/source_norms/endpoint-bounds/endpoint_square_numerator.json').read_text())
    require(square.encode(square.complete_sums()) == old62['complete_pair_sums'], 'Inherited complete square comparison')
    ends = [linear.slot_matrices(x) for x in linear.LATE_INTERVAL]
    entry_caps = [head.scaled(max(t[1][c][s] for t in ends)) for c, s in product(range(5), repeat=2)]
    raw_matrices = [[head.scaled(t[0][c][s]) for c, s in product(range(5), repeat=2)] for t in ends]
    row_caps = [head.scaled(v) for v in linear.endpoint_tables()['all_positive5_cell_caps']]
    mass_cap = head.scaled(F(3, 20))
    require([str(F(x, head.SCALE)) for x in entry_caps] == old63['layout_bounds']['entry_caps']
            and [str(F(x, head.SCALE)) for x in row_caps] == old63['layout_bounds']['row_caps'],
            'Identical inherited actual-source relaxation')
    pre = [[F(0), F(1, 5) if c < 2 else F(0), F(0) if c == 2 else F(1, 5),
            F(3, 20) if c < 2 else F(1, 20) if c == 2 else F(1, 10), F(1, 5)] for c in range(5)]
    kept = [[pre[c][s]*(1-F(int(c < 2)+int(c == 1)+int(s == 4)+int(c >= 2 and s == 4), 5))
             for s in range(5)] for c in range(5)]
    records, cuts = [], Counter()
    primal_digest, tail_digest = sha256(), sha256()
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        coefficients = head.coefficients(layout, linear.ROOT)
        B = list(map(isqrt, coefficients))
        require(all(b*b == c for b, c in zip(B, coefficients)), 'Exact integer shallow load')
        witness = head.primal_dual([c-1 for c in coefficients], entry_caps, row_caps, mass_cap)
        primal_digest.update(json.dumps([layout, witness], separators=(',', ':'), sort_keys=True).encode())
        zhead = F(witness['scaled_value'], head.SCALE)
        rhead = max(F(sum(w*c for w, c in zip(row, coefficients)), head.SCALE) for row in raw_matrices)
        zlines, rlines = tail_lines(B, pre, kept, linear.ROOT)
        ztail, zcut = affine_tail(zlines)
        rtail, rcut = affine_tail(rlines)
        cuts[zcut] += 1
        cuts[rcut] += 1
        Z, R = zhead+ztail, rhead+rtail
        tail_digest.update(json.dumps(encode([layout, zlines, rlines, zcut, rcut, Z, R]), separators=(',', ':')).encode())
        records.append((layout, Z, R))
    require(len(records) == 12500 and sum(cuts.values()) == 25000 and max(cuts) == 10,
            'All layouts and both complete affine tails')
    require(primal_digest.hexdigest() == old63['layout_bounds']['all_primal_dual_sha256'],
            'All inherited feasible primal/dual equalities reconstructed exactly')
    zmax, rmax = max(row[1] for row in records), max(row[2] for row in records)
    require(zmax == F(6068947, 3936600) and rmax == F(212153, 87480), 'Complete expanded-head source bounds')
    deep_pair_weight, deep_mass = square.geometric_weight(3, 3), F(1, 18)
    zero_extension = F(11, 20)*deep_pair_weight+F(6, 5)*deep_mass
    raw_extension = F(3, 4)*deep_pair_weight+F(6, 5)*deep_mass
    require(zero_extension == F(14, 45) and raw_extension == F(2, 5), 'All expanded-head lcm-pair counts and complete tails')
    old_zero = F(old63['old_zero7_head_budget'])+zero_extension
    old_raw = F(old63['old_raw35_head_budget'])+raw_extension
    require(old_zero == F(1001, 600) and old_raw == F(107, 40), 'Disjoint expanded-head ordered-pair budgets')
    remainder = F(old62['complete_pair_sums']['full_square_upper'])-old_zero-F(2, 3)*old_raw
    one_zero_factor = 2*F(6, 5)*F(1, 6)
    both_positive_factor = F(6, 5)*square.geometric_weight(7, 1)-one_zero_factor
    require(one_zero_factor == F(2, 5) and both_positive_factor == F(4, 15), 'Disjoint complete seven-depth pair classes')
    target = F(469, 100)
    threshold = target-remainder-F(4, 15)*rmax
    require(threshold == F(3187861, 1312200), 'Exact common-zero comparison threshold')
    minimum = None
    controllers = []
    selected_witness = None
    common_digest = sha256()
    for layout, Z, R in records:
        gap = threshold-Z
        quadratic_slack = (F(5, 2)*gap)**2-R*rmax
        require(gap >= 0 and quadratic_slack >= 0, 'Exact rational proof of the common-layout square-root inequality')
        common_digest.update(json.dumps(encode([layout, Z, R, gap, quadratic_slack]), separators=(',', ':')).encode())
        if minimum is None or quadratic_slack < minimum:
            minimum, controllers = quadratic_slack, [layout]
            selected_witness = {'layout': layout, 'Z': Z, 'R': R, 'threshold_minus_Z': gap,
                                'product_R_Rmax': R*rmax, 'quadratic_slack': quadratic_slack}
        elif quadratic_slack == minimum:
            controllers.append(layout)
    require(minimum == F(8715944851, 619872782400) > 0, 'Strict exact minimum over all12500 quadratic comparisons')
    margin = 45*F(3, 20)-target
    require(margin == F(103, 50), 'Current barrier45 absolute margin')
    return {'schema': 'erdos7-endpoint-square-common-pure3-v1', 'source_vertex': 404, 'carrier': [0, 1],
            'source_sha256': PINS, 'barrier': 45, 'surviving_mass': F(3, 20),
            'head': 'all pure3 labels, including the unit, plus5,15,45',
            'layout_count': len(records), 'primal_dual_equality_checks': len(records),
            'affine_tail_checks': sum(cuts.values()), 'affine_tail_entrance_counts': dict(sorted(cuts.items())),
            'maximum_affine_tail_entrance': max(cuts), 'zero_head_upper': zmax, 'raw_head_upper': rmax,
            'zero_head_maximizers': [layout for layout, Z, R in records if Z == zmax],
            'raw_head_maximizers': [layout for layout, Z, R in records if R == rmax],
            'old_zero_head_budget': old_zero, 'old_raw_head_budget': old_raw,
            'unreplaced_pair_remainder': remainder, 'one_zero_depth_pair_factor': F(2, 5),
            'both_positive_depth_pair_factor': F(4, 15), 'common_layout_threshold': threshold,
            'rational_common_layout_checks': len(records), 'minimum_quadratic_slack': minimum,
            'minimum_quadratic_slack_layouts': controllers, 'one_common_layout_witness': selected_witness,
            'all_primal_dual_sha256': primal_digest.hexdigest(), 'all_affine_tail_bounds_sha256': tail_digest.hexdigest(),
            'all_rational_common_checks_sha256': common_digest.hexdigest(), 'full_square_upper': target,
            'absolute_square_margin': margin, 'improvement_over63': F(old63['full_square_upper'])-target,
            'auxiliary_third_moment_upper': third_moment(),
            'third_moment_scope': 'Auxiliary ordered-triple cap bound; not used in the square theorem.',
            'scope': ('Ordinary uniform endpoint and approaching-sequence theorem over arbitrary '
                      'independent original357 labels. Complete pure3 and positive7 tails are retained; '
                      'all final comparisons are rational. No quantitative neighborhood, global K '
                      'replacement, physical denominator bound or Lean verification is claimed.')}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    if args.check:
        certificate = args.base/'certificates/source_norms/endpoint-bounds/endpoint_square_common_pure3.json'
        require(json.loads(certificate.read_text()) == result, 'Exact canonical certificate reconstruction')
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('PASS:12500 exact common-layout comparisons and25000 complete affine tails; maximal tail entrance10.')
    print('Uniform endpoint square469/100 and barrier45 margin103/50; no numerical square roots used.')


if __name__ == '__main__':
    main()
