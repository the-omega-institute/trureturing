#!/usr/bin/env python3
"""Reconstruct the complete profile53 J/K gap tables and their zero faces.

Exact rational arithmetic; original source and survival providers are pinned.
The resulting Cartesian faces obstruct vertex-only certificate patching.
They are not assertions of actual-family realization or true-margin flatness.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/global_control_faces.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/allocated_seven_thresholds.py': 'b467824a30899cd14ab35ab4a1383c4a3848e5c9dcbdaebd6f4074e9a1d8e78d',
}
SIZES = (6, 3, 6, 6, 2)


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
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def digest(value):
    return sha256(json.dumps(encode(value), sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def maximal_boxes(zero):
    """Exhaust all legal single-coordinate expansions from singleton boxes."""
    zero = frozenset(zero)
    choices = [sorted({z[j] for z in zero}) for j in range(6)]
    pending = {tuple((x,) for x in z) for z in zero}
    seen, maximal = set(), set()
    while pending:
        box = pending.pop()
        if box in seen:
            continue
        seen.add(box)
        expanded = False
        for j in range(6):
            for x in choices[j]:
                if x in box[j]:
                    continue
                candidate = box[:j]+(tuple(sorted((*box[j], x))),)+box[j+1:]
                if all(z in zero for z in product(*candidate)):
                    expanded = True
                    if candidate not in seen:
                        pending.add(candidate)
        if not expanded:
            maximal.add(box)
    require(all(all(z in zero for z in product(*box)) for box in maximal), 'Every maximal box is zero')
    require(set().union(*(set(product(*box)) for box in maximal)) == zero, 'Maximal boxes cover all zero controls')
    return sorted(maximal)


def reconstruct(base, read, source, allocated):
    def load(name):
        return module('control_'+name, base/'frontier'/f'{name}.py')
    profiles, fixed, layout, ap = (load(n) for n in ('shared_source_deficits', 'fixed_cost', 'layout_gap', 'ap_schedule'))
    linear, square = (load(n) for n in ('shared_linear_refinement', 'shared_square_barrier'))
    previous39 = read('certificates/source_norms/shared_source_deficits.json')
    previous49 = read('certificates/source_norms/full_linear_carrier_frontier.json')

    def progress(label):
        def update(done, total):
            if done % 216 == 0:
                print(f'{label} {done}/{total}', flush=True)
        return update

    rows, stats = profiles.aggregate(source, fixed, layout, ap,
        read('certificates/ap_schedule_frontier_certificate.json'),
        read('certificates/source_norms/retained_quadratic_tests.json'),
        read('certificates/source_norms/retained_quadratic_inputs.json'),
        read('certificates/ap_schedule_norms.json'), progress('Source'))
    rows, linear_stats = linear.refine(source, fixed, ap, read('certificates/ap_schedule_norms.json'), rows)
    rows, square_stats = square.refine(source, fixed, rows, stats['quadratic_tail_weight'])
    require(encode(stats) == previous39['source_profiles']
        and encode(linear_stats) == previous39['linear_refinement']
        and encode(square_stats) == previous39['square_barrier_refinement'], 'All source39 provider statistics')
    require(digest(rows) == previous39['source_profile_sha256'] == previous49['predecessor_source_profile_sha256'],
        'Complete source39 row hash')
    rows, allocation_stats = allocated.reconstruct(source,
        read('certificates/source_norms/joint_survival_carriers.json'), rows, progress('Allocated survival'))
    require(encode(allocation_stats) == read('certificates/source_norms/allocated_seven_thresholds.json')['allocation_statistics'],
        'All profile53 allocated margins')
    return rows


def analyze(source, allocated, previous53, previous47, previous49, rows):
    vertices = list(source.vertices())
    indices = list(product(*(range(n) for n in SIZES)))
    require(len(vertices) == len(indices) == len(rows) == 1296, 'Complete source product')
    for vertex, idx in zip(vertices, indices):
        for block, n, cap, selected in zip(vertex[:4], (5, 2, 5, 5), (F(1, 2), F(1, 4), F(1, 4), F(1, 72)), idx[:4]):
            require(block == tuple(cap if selected == j+1 else F(0) for j in range(n)), 'Every simplex factor decoded')
        require(vertex[4] == (F(3, 4), F(1))[idx[4]], 'Every z endpoint decoded')
    carriers = allocated.CARRIERS
    old47 = [r for a in previous47['six_linear']['row_blocks'] for b in a for r in b]
    refined = {r['index']: r for b in previous49['frontier']['row_blocks'] for r in b}
    H16, H41, A81, cG = (F(previous53[k]) for k in ('H16', 'H41', 'A81', 'cG'))
    require(all(F(previous49[k]) == F(previous53[k]) for k in ('H16', 'H41', 'A81', 'cG')), 'Same complete numerator slopes')
    slopes = {'J': source.AC*H16+H41, 'K': source.AC*H16+H41+A81}
    targets = {'J': F(previous53['bound']), 'K': F(previous53['combined'])}
    coefficients = {k: allocated.Q*(targets[k]-source.WHOLE_CONST)-slopes[k] for k in targets}
    require(all(a > 0 for a in coefficients.values()), 'Both signed targets use lower mass endpoint')
    finite, _ = source.ap_product_distribution(allocated.CAPS, 9)
    tables = {k: [] for k in targets}
    for i, row in enumerate(rows):
        require(row['index'] == i, 'All row indices ordered')
        dat = source.data(vertices[i])
        raw81 = sum(p*n*n*source.square357(F(81, n*n), dat) for n, p in finite.items() if n < 7)
        for j, cond in enumerate(row['conditional']):
            require(tuple(cond['carrier']) == carriers[j], 'All carrier indices ordered')
            ml = F((refined[i] if i in refined else old47[i])['conditional_M41'][j])
            mq = F(refined[i]['conditional_Mquad'][j]) if i in refined else row['Mquad']
            correction = {'J': source.AC*mq+ml, 'K': source.AC*mq+ml+cG*row['source_margin']-raw81}
            for endpoint, mass in (('D_c', cond['D_c']), ('s', row['s'])):
                denominator = allocated.Q*mass+cond['M']
                require(denominator > 0, 'Every denominator strictly positive')
                for k, target in targets.items():
                    gap = coefficients[k]*mass+(target-source.WHOLE_CONST)*cond['M']+correction[k]
                    require(gap >= 0, 'Every reconstructed exact target gap nonnegative')
                    tables[k].append((i, j, endpoint, gap))
    result = {}
    for k, table in tables.items():
        require(len(table) == 1296*18*2, 'Both endpoints at every source and carrier')
        zero = [r for r in table if r[3] == 0]
        reported = [[i, list(carriers[j]), endpoint] for i, j, endpoint, _ in zero]
        require(reported == previous53['controllers']['bound' if k == 'J' else 'combined'], 'Complete zero set equals published53 controls')
        require(all(endpoint == 'D_c' for _, _, endpoint, _ in zero), 'No upper-mass zero endpoint')
        gamma = min(r[3] for r in table if r[3] > 0)
        lower = [r for r in table if r[2] == 'D_c']
        gamma_lower = min(r[3] for r in lower if r[3] > 0)
        zero_product = {indices[i]+(j,) for i, j, _, _ in zero}
        edge = [(a, b) for a, b in combinations(sorted(zero_product), 2) if sum(x != y for x, y in zip(a, b)) == 1]
        boxes = maximal_boxes(zero_product)
        result[k] = {'target': targets[k], 'mass_coefficient': coefficients[k], 'signed_endpoint_checks': len(table),
            'all_signed_gaps_sha256': digest(table), 'minimum_positive_signed_gap_both_endpoints': gamma,
            'minimum_positive_signed_gap_lower_endpoint': gamma_lower,
            'minimum_positive_gap_controls': [[i, carriers[j], e] for i, j, e, g in table if g == gamma],
            'zero_controls': [{'index': i, 'factors': indices[i], 'carrier': carriers[j], 'carrier_index': j,
                               'raw_mass': rows[i]['s'], 'D': rows[i]['D'], 'D_c': rows[i]['conditional'][j]['D_c']}
                              for i, j, _, _ in zero],
            'zero_hamming_edges': edge, 'maximal_cartesian_zero_boxes': boxes,
            'maximal_source_face_dimensions': [sum(len(f)-1 for f in box[:5]) for box in boxes]}
    require(len(result['J']['zero_controls']) == 18 and len(result['K']['zero_controls']) == 6,
        'Separate J and K zero inventories')
    require(len(result['J']['zero_hamming_edges']) == 36 and len(result['K']['zero_hamming_edges']) == 6,
        'Separate zero Hamming graphs')
    require(result['J']['maximal_source_face_dimensions'] == [4, 4]
        and result['K']['maximal_source_face_dimensions'] == [2, 2], 'Full product-face dimensions')
    return {'factor_names': ['deficit', 'alpha', 'beta', 'late', 'z'], 'factor_sizes': SIZES,
        'factor_convention': 'Simplex index0 is the zero vector; j>0 is cap times basis vector j-1; z0=3/4,z1=1.',
        'carriers': carriers, 'all1296_factor_indices_sha256': digest(indices), 'targets': result}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Certificate IO pin')
    io = module('control_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    previous53 = read('certificates/source_norms/allocated_seven_thresholds.json')
    pins = previous53['source_sha256'] | previous53['helper_sha256'] | PINS
    pins['certificates/source_norms/allocated_seven_thresholds.json'] = '9400e4fae0a400edcc7ee7459103af677e512592823b683f67e7c896f8d345b8'
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    source = module('control_source', base/'verify_joint_frontier.py')
    allocated = module('control_allocated', base/'frontier/allocated_seven_thresholds.py')
    rows = reconstruct(base, read, source, allocated)
    result = analyze(source, allocated, previous53,
        read('certificates/source_norms/joint_linear_carriers.json'),
        read('certificates/source_norms/full_linear_carrier_frontier.json'), rows)
    return encode({'schema': 'erdos7-global-control-faces-v1', 'source_sha256': pins, **result,
        'scope': 'Exact complete J/K certificate zero faces and next signed gaps. No actual-family realization, true-margin flatness, strict global target gain, or Lean claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('control_output_io', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact global control-face certificate')
    elif args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: all1296 vertices,18 carriers,two mass endpoints; J18 zeros/two4D faces; K6 zeros/two2D faces.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
