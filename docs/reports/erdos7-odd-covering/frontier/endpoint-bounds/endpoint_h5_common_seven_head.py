#!/usr/bin/env python3
"""Uniform endpoint h5 bound with one common old head and two seven labels.

The ordinary proof uses a pointwise ordered-indicator bound, not alignment
of independent seven residues. Exact LP duals and complete geometric tails
check all12500 old layouts and10 choices of the additional old projections.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/endpoint_h5_common_seven_head.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/endpoint-bounds/endpoint_linear_numerator.py': 'c95c2df2ec24e5c38f0dc75ed1019cbbd2fdeb057d299f6160db6f5c8a1fc8f5',
    'frontier/endpoint-bounds/endpoint_square_coherent_head.py': '24229193f185d132d2ef0917b0257ddcd20d374b6333dfae327cc70d665ceedb',
    'frontier/endpoint-bounds/endpoint_square_positive5.py': 'e6d4a2ae2ac9f369048603d328da7e73cb719e9a622c2a6633ddd61e5609b00d',
    'certificates/source_norms/endpoint-bounds/endpoint_square_positive5.json': 'feb9333e4714f3408029d9e24711fb2886d016c0c4265c0f039ab99419b99405',
    'certificates/source_norms/endpoint-bounds/endpoint_survival_scalar_barrier.json': 'a4a4092e9d198b126b85afe96d00b399105a35e73c1e309f3d364e19633ec430',
}
ORDER = ((0, 2), (3, 0), (1, 2), (4, 0))
U1 = F(6, 35)
TARGET = F(30941653, 194481000)


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


def seven_increment(v, m):
    k = max(5-v, 0)
    return F(1, 5*7**max(k-m, 0))+U1*max(m-k, 0)


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('h5_seven_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    used = dict(PINS)
    for previous in (read('certificates/source_norms/endpoint-bounds/endpoint_square_positive5.json'),
                     read('certificates/source_norms/endpoint-bounds/endpoint_survival_scalar_barrier.json')):
        for path, pin in previous['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pins')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    linear = module('h5_seven_linear', base/'frontier/endpoint-bounds/endpoint_linear_numerator.py')
    head = module('h5_seven_head', base/'frontier/endpoint-bounds/endpoint_square_coherent_head.py')
    ends = [linear.slot_matrices(x) for x in linear.LATE_INTERVAL]
    entries = [max(tab[1][c][s] for tab in ends) for c, s in product(range(5), repeat=2)]
    row_caps = linear.endpoint_tables()['all_positive5_cell_caps']
    integer_entries, integer_rows = [head.scaled(v) for v in entries], [head.scaled(v) for v in row_caps]
    mass = F(3, 20)
    pre = [[F(0), F(1, 5) if c < 2 else F(0), F(0) if c == 2 else F(1, 5),
            F(3, 20) if c < 2 else F(1, 20) if c == 2 else F(1, 10), F(1, 5)] for c in range(5)]
    w = [[1-F(int(c < 2)+int(c == 1)+int(s == 4)+int(c >= 2 and s == 4), 5)
          for s in range(5)] for c in range(5)]
    descendant = [[F(0) if s == 0 or (s == 1 and c >= 2) or (s == 2 and c == 2)
                   else linear.ETA[c]-F(1, 18) if (c, s) == (3, 2) else linear.ETA[c]
                   for s in range(5)] for c in range(5)]
    weighted_descendant = [[descendant[c][s]*w[c][s] for s in range(5)] for c in range(5)]
    require(encode(weighted_descendant) == read('certificates/source_norms/endpoint-bounds/endpoint_square_positive5.json')['descendant5_cell_caps'],
        'Identical complete descendant-five coefficients from69')
    wf = [x for row in w for x in row]
    for weight in set(wf):
        require(weight >= U1 > 0, 'Every retained-deletion density supports the convex increment')
        for m in range(3):
            costs = [weight*max(v-5, 0)+seven_increment(v, m) for v in range(1, 10)]
            increments = [y-x for x, y in zip(costs, costs[1:])]
            require(all(x >= 0 for x in increments) and all(x <= y for x, y in zip(increments, increments[1:])),
                'Exact nonnegative increasing integer increments')
            require(all(x == weight for x in increments[4:]), 'Affine tail from argument5 onward')

    # The same prefix-removal bound handles arbitrary original seven events.
    seven_checks = []
    for m in range(3):
        for k in range(8):
            caps = [U1]*(m+1)+[F(6, 5*7**e) for e in range(2, 12)]
            remaining = sum(caps[k:])+F(1, 5*7**11)
            expected = F(1, 5*7**max(k-m, 0))+U1*max(m-k, 0)
            require(remaining == expected, 'Complete tail after deleting the k largest cap labels')
            seven_checks.append((m, k, expected))

    def tail_cap(coefficients, a, b):
        require(len(coefficients) == 25 and min(coefficients) >= 0, 'Nonnegative common-layout cylinder cost')
        if b == 0:
            require(a >= 3, 'Pure3 tail starts at27')
            return F(1, 3**a)*max(sum(pre[c][s]*coefficients[5*c+s] for s in range(5)) for c in range(5))
        if a == 0:
            return F(1, 5**b)*max(sum(descendant[c][s]*coefficients[5*c+s] for c in range(5)) for s in range(5))
        if a == 1:
            return F(1, 5**b)*max(sum(descendant[c][s]*coefficients[5*c+s]
                for c in range(5) if linear.ROOT[c] == root) for root in range(2) for s in range(5))
        if a == 2:
            return F(1, 5**b)*max(descendant[c][s]*coefficients[5*c+s] for c, s in product(range(5), repeat=2))
        return F(1, 3**a*5**b)*max(coefficients)

    categories = {'pure3': F(3, 2)*tail_cap(wf, 3, 0),
        'pure5': F(5, 4)*tail_cap(wf, 0, 2), '3_times5': F(5, 4)*tail_cap(wf, 1, 2),
        '9_times5': F(5, 4)*tail_cap(wf, 2, 2), 'deep35': F(1, 72)}
    complete_tail = sum(categories.values())
    remaining_tail = complete_tail-sum(tail_cap(wf, a, b) for a, b in ORDER)
    remaining_seven = F(1, 10)-U1*(F(1, 8)+F(1, 10))
    require((complete_tail, remaining_tail, remaining_seven) == (F(161, 1800), F(497, 16200), F(43, 700)),
        'Each selected old and seven label removed from its previous linear budget exactly once')
    best, controls, witness_best = None, [], None
    table_digest, dual_digest = sha256(), sha256()
    checks = 0
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        squares = head.coefficients(layout, linear.ROOT)
        B = list(map(isqrt, squares))
        require(all(x*x == y for x, y in zip(B, squares)), 'Exact integer old-head load')
        hB = [max(v-5, 0) for v in B]
        dual = head.primal_dual(hB, integer_entries, integer_rows, head.scaled(mass))
        dual_digest.update(json.dumps([layout, dual], sort_keys=True, separators=(',', ':')).encode())
        zero_head = F(dual['scaled_value'], head.SCALE)
        for root, slot in product(range(2), range(5)):
            counts = [int(linear.ROOT[c] == root)+int(s == slot) for c, s in product(range(5), repeat=2)]
            raw_head = max(sum(tab[0][c][s]*seven_increment(B[5*c+s], counts[5*c+s])
                for c, s in product(range(5), repeat=2)) for tab in ends)
            increments = [[weight*int(v+i-1 >= 5)+seven_increment(v+i, m)-seven_increment(v+i-1, m)
                for v, m, weight in zip(B, counts, wf)] for i in range(1, 5)]
            selected_tail = sum(tail_cap(increments[j], a, b) for j, (a, b) in enumerate(ORDER))
            value = remaining_seven+zero_head+raw_head+remaining_tail+selected_tail
            require(value <= TARGET, 'Every common old-head and additional-seven layout obeys the exact target')
            table_digest.update(json.dumps(encode([layout, root, slot, zero_head, raw_head, selected_tail, value]), separators=(',', ':')).encode())
            checks += 1
            if best is None or value > best:
                best, controls = value, [(layout, root, slot)]
                witness_best = {'layout': layout, 'extra_root3': root, 'extra_slot5': slot,
                    'old_head': B, 'extra_counts': counts, 'old_head_h5_upper': zero_head,
                    'raw_seven_increment_upper': raw_head, 'selected_old_tail_upper': selected_tail,
                    'remaining_old_tail_upper': remaining_tail, 'remaining_positive7_upper': remaining_seven,
                    'old_head_primal_dual': dual}
            elif value == best:
                controls.append((layout, root, slot))
    require(checks == 125000 and best == TARGET, 'Complete12500 by10 common-layout enumeration')
    require(controls == [((1, 4, 4, 1, 4, 4, 4), 1, 4)], 'Complete maximizing layout inventory')
    old_scalar = read('certificates/source_norms/endpoint-bounds/endpoint_survival_scalar_barrier.json')
    old_h5 = F(old_scalar['original53_hinge_uppers'][2])
    V = [(v, F(p)) for v, p in old_scalar['laws']['V']['support']]
    V_h5 = sum(p*max(v-5, 0) for v, p in V)
    require(V_h5 == old_h5 == F(2028798479, 12155062500) > TARGET,
        'The new universal hinge constraint strictly excludes scalar law V')
    simple_bridge_lower = F(1, 10)+F(23, 360)+F(1, 225)
    require(simple_bridge_lower == F(101, 600) > old_h5,
        'The original all-linear positive7-nonunit bridge is insufficient on an actual endpoint subregion')
    return encode({'schema': 'erdos7-endpoint-h5-common-seven-head-v1', 'source_sha256': used,
        'source_vertex': 404, 'carrier': [0, 1], 'mass': mass, 'threshold': 5,
        'old_head_moduli': [1, 3, 9, 5, 15, 45], 'additional_positive7_moduli': [21, 35],
        'first_old_tail_exponents': ORDER, 'retained_density': w, 'raw_descendant5_coefficients': descendant,
        'complete_linear_tail_categories': categories, 'complete_linear_old_tail': complete_tail,
        'remaining_linear_old_tail': remaining_tail, 'remaining_positive7_linear_budget': remaining_seven,
        'complete_seven_tail_checks': seven_checks, 'old_layout_count': 12500, 'joint_layout_checks': checks,
        'all_old_head_primal_dual_sha256': dual_digest.hexdigest(), 'all_joint_layout_values_sha256': table_digest.hexdigest(),
        'maximizing_layouts': controls, 'maximizing_witness': witness_best, 'uniform_h5_upper': TARGET,
        'old_h5_upper': old_h5, 'strict_h5_improvement': old_h5-TARGET,
        'scalar_V_h5': V_h5, 'scalar_V_violation': V_h5-TARGET,
        'survival_denominator_gain_at_weight4over33': F(4, 33)*(old_h5-TARGET),
        'simple_bridge_actual_subregion_lower': simple_bridge_lower,
        'scope': 'Uniform endpoint404 original-label h5 bound with arbitrary independent residues and complete exponent tails. No unit-tail saturation or first-moment equality assumed. Excludes abstract scalar law V; no unrestricted Erdos7, neighborhood, global K, or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('h5_seven_writer', args.base/'certificate_io.py')
    rendered = json.dumps(result, indent=2)+'\n'
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical endpoint h5 certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, rendered)
    elif args.output is not None:
        args.output.write_text(rendered)
    else:
        print(rendered)
    print('PASS:125000 common layouts, exact old-head LP duals, all tails; H5<=30941653/194481000, scalar V excluded.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
