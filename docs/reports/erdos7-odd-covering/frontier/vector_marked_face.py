#!/usr/bin/env python3
"""Fixed source duals give a uniform retained-deep gain on all actual K faces.

The continuum step is concavity of the same branch formulas and constancy
of their dual data, not interpolation of independently optimized LP values.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import permutations
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/vector_marked_face.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/vector_marked_source.py': 'd4fb958ac95a62a766debf18b8a7079081d922430e471d594725274acf321fbc',
    'certificates/source_norms/vector_marked_source.json': 'c1784b408f95d83f2e2868049b57ae92dadf40436fc5442abd27cb886f696f60',
}
VERTICES = ((F(1, 4), F(0), F(0)), (F(1, 5), F(1, 20), F(0)),
            (F(1, 5), F(0), F(1, 20)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input: '+str(path))
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


def digest(value):
    return sha256(json.dumps(encode(value), sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def dual_signature(row):
    return [{'slot': item['slot'], 'ordinary_duals': item['ordinary_duals'],
             'deep_duals': [{'chosen_cell': alt['chosen_cell'], 'capacity_duals': alt['capacity_duals']}
                            for alt in item['deep_alternatives']]}
            for item in row['marker']['capacity_duals']]


def constant_raw_support(source, tag, dat):
    """A beta-independent active lower support for one convex raw block."""
    d, n, eta, _, _ = dat
    raw = source.zero5_raw(tag, dat)
    positive = source.zero5_positive_with_constant(tag, eta)
    supports = []
    for baseline in source.BASES:
        if len(set(baseline[2:])) != 1:
            continue
        shallow = sum(n[j]*source.zero5_cost(tag, baseline[j])
                      +eta[j]*source.zero5_centered_correction(tag, baseline[j]) for j in range(5))
        for cell in range(2):
            deep = source.zero5_common_deep(tag, baseline[cell], d[cell])
            if shallow+deep+positive == raw:
                supports.append({'baseline': baseline, 'deep_cell': cell, 'value': raw})
    require(supports, 'An active constant support for every common zero-five block')
    return supports[0]


def common_support(source, spec, dat):
    """Cancel original block e=0 before proving convexity and taking supports."""
    tag = spec['tag']
    require(spec['zero'] == ('seven_block', (tag, 0)), 'Exact common-block cancellation')
    degree, slope, offset, cutoff = source.zero5_cost_metadata(tag)
    require(degree == 1 and slope >= 0 and cutoff >= 2, 'Positive complete affine-tail decomposition')
    tails = tuple(F(36, 5)*x for x in source.geom(7, cutoff))
    expectation = (sum(source.zero7_probability(n)*source.zero5_cost(tag, n) for n in range(1, cutoff))
                   +slope*tails[degree]+offset*tails[0])
    tail_weight = slope*(tails[degree]-(cutoff-1)*tails[degree-1])
    require(tail_weight >= 0, 'Nonnegative common tail weight')
    rows = []
    for exponent in range(1, cutoff-1):
        tt = ('seven_block', (tag, exponent))
        require(source.zero5_cost_metadata(tt)[0] == 1, 'Every retained block is eventually affine')
        rows.append({'seven_block': exponent, 'weight': F(1),
                     'support': constant_raw_support(source, tt, dat)})
    rows.append({'seven_block': 'complete_tail', 'weight': tail_weight,
                 'support': constant_raw_support(source, ('h', F(0)), dat)})
    value = dat[3]*(expectation-tail_weight)+sum(row['weight']*row['support']['value'] for row in rows)
    require(value == source.zero7_raw(tag, dat)-source.zero5_raw(spec['zero'], dat),
            'The fixed common supports attain the exact canonical common source')
    return {'constant': value, 'affine_source_coefficient': expectation-tail_weight,
            'raw_supports': rows, 'cutoff': cutoff}


def constant_old_support(engine, spec, index, dat, records):
    """An upper bound on the old minimum, constant throughout the beta triangle."""
    source, d = engine.source, dat[0]
    common = common_support(source, spec, dat)
    supports = []
    for row in records['all_branches']:
        if row['old_branch'] != records['old_carrier_average'] or len(set(row['b'][2:])) != 1:
            continue
        b, c5 = row['b'], row['c5']
        costs = tuple(source.zero5_cost(spec['tag'], x) for x in b)
        v = row['marker']['v']
        k = tuple(F(engine.thresholds[index]['constant'])-x for x in costs)
        z = tuple(k[j]*d[j]-v[j]*c5[j]/5 for j in range(5))
        own_deep = tuple(source.zero5_common_deep(spec['zero'], b[j], d[j]) for j in range(5))
        if max(z[:2]) != max(z) or max(k[j]*d[j] for j in range(2)) != max(k[j]*d[j] for j in range(5)):
            continue
        if max(own_deep[:2]) != max(own_deep):
            continue
        item = next(x for x in spec['layouts'] if x['baseline'] == b)
        require(len(set(item['psi'][2:])) == 1 and len(set(k[2:])) == 1,
                'The fixed carrier and shallow terms use only the root1 total mass')
        supports.append({'b': b, 'c5': c5,
                         'own_deep_cell': max(range(2), key=lambda j: own_deep[j]),
                         'z_cell': max(range(2), key=lambda j: z[j]),
                         'kd_cell': max(range(2), key=lambda j: k[j]*d[j]),
                         'constant': row['old_branch']})
    require(supports, 'A constant upper support for the complete old branch minimum')
    return {'common': common, 'old_branch_support': supports[0]}


def symmetry_check(engine, broad):
    """Check the finite index relabellings used by the ordinary covariance proof."""
    source = engine.source
    mappings = [(root0+tail) for root0 in ((0, 1), (1, 0)) for tail in permutations((2, 3, 4))]
    for perm in mappings:
        require(tuple(broad.ROOT[j] for j in perm) == broad.ROOT, 'Relabelling preserves roots')
        require({tuple(b[j] for j in perm) for b in source.BASES} == set(source.BASES), 'Every old layout is retained')
        for spec in engine.specs:
            items = {item['baseline']: item for item in spec['layouts']}
            for b, item in items.items():
                moved = items[tuple(b[j] for j in perm)]
                require(all(moved[key] == tuple(item[key][j] for j in perm) for key in ('psi', 'correction'))
                        and moved['joint'][1] == tuple(item['joint'][1][j] for j in perm),
                        'All branch cell coefficients covary under the full face symmetries')
    return mappings


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('face_vector_io', base/'certificate_io.py')
    vector = module('face_vector', base/'frontier/vector_marked_source.py')
    used = PINS | vector.PINS
    for path, pin in used.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    engine = module('face_vector_engine', base/'frontier/source_barrier_saturation.py').Experiment(base)
    broad = module('face_vector_source', base/'frontier/broad_weighted_identity_source.py')
    full = module('face_vector_old', base/'frontier/full_linear_carrier_frontier.py')
    for path, pin in engine.pins.items():
        require(path not in used or used[path] == pin, 'Consistent inherited pin')
        used[path] = pin
    parent = json.loads(io.read_artifact_bytes(base/PINS_PATH))
    source, canonical = engine.source, engine.parameters[398]
    parameters = [canonical[:2]+((F(0), F(0))+beta,)+canonical[3:] for beta in VERTICES]
    data = [source.data(p) for p in parameters]
    pi = broad.point_carrier(1, 1)
    states = [vector.geometry(broad, p, dat, pi, F(0), 2) for p, dat in zip(parameters, data)]
    require(all(not state['necessary_condition_failures'] for state in states), 'All triangle vertices pass actual-source conditions')
    expected_eta = (F(1, 18), F(1, 9), F(1, 9), F(1, 9), F(1, 9))
    expected_masses = (F(1, 36), F(1, 12), F(5, 36))
    for dat, state in zip(data, states):
        require(dat[2] == expected_eta and (dat[1][0], dat[1][1], sum(dat[1][2:])) == expected_masses,
                'Three source groups have constant masses throughout the affine triangle')
        require(max(dat[0]) == F(3, 4) and dat[3] == F(1, 4), 'Constant dmax and source mass')
        require(state['caps'] == states[0]['caps'] and state['a'] == states[0]['a']
                and state['G'] == states[0]['G'], 'One fixed source-cap system on the whole triangle')
    costs = []
    for index, spec in enumerate(engine.specs):
        records = [vector.cost_bound(engine, broad, full, p, pi, index,
                                    partitions=('three_groups',), details=True) for p in parameters]
        old = records[0]['old_carrier_average']
        require(all(rec['old_carrier_average'] == old for rec in records), 'Equal old values at all three vertices')
        require(all(rec['source_gain'] == records[0]['source_gain'] > 0 for rec in records), 'The same positive gain at all vertices')
        for position, row in enumerate(records[0]['all_branches']):
            for rec in records[1:]:
                moved = rec['all_branches'][position]
                require((moved['b'], moved['c5']) == (row['b'], row['c5'])
                        and dual_signature(moved) == dual_signature(row),
                        'The exact same capacity duals are used for every branch across the whole triangle')
        support = constant_old_support(engine, spec, index, data[0], records[0])
        gain = min(rec['new_layout_min'] for rec in records)-old
        require(gain == F(parent['canonical_face_costs'][index]['source_gain']), 'The whole-face bound extends the certified canonical gain')
        costs.append({'index': index, 'name': spec['name'], 'tuple': spec['tuple'], 'weight': engine.weights[index],
                      'constant_old_margin': old, 'uniform_source_gain': gain,
                      'uniform_residual_coefficient': records[0]['uniform_residual_coefficient'],
                      'constant_old_support': support,
                      'vertex_new_minima': [rec['new_layout_min'] for rec in records],
                      'vertex_branch_and_dual_sha256': [rec['all_branches_and_duals_sha256'] for rec in records],
                      'fixed_capacity_duals_sha256': digest([dual_signature(row) for row in records[0]['all_branches']])})
    gain = sum(row['weight']*row['uniform_source_gain'] for row in costs)
    require(gain == F(parent['weighted_face_gain']) and gain > F(1, 25), 'Uniform weighted gain exceeds 1/25')
    return {'schema': 'erdos7-vector-marked-face-v1', 'source_sha256': used,
            'vertices': VERTICES, 'source_group_masses': expected_masses,
            'non_H_group_budgets': (F(1, 60), F(11, 180), F(13, 180)),
            'constant_geometry': states[0], 'relabellings': symmetry_check(engine, broad),
            'costs': costs, 'weighted_uniform_face_gain': gain,
            'weighted_residual_coefficient': sum(row['weight']*row['uniform_residual_coefficient'] for row in costs),
            'comparison': 'On every actual K-control beta face: margin_i>=m_i+[g_i-P_i*rho]_+; all g_i>0.',
            'scope': 'Ordinary continuum proof with exact arithmetic. All three actual first-beta triangles and both root0 orientations, always with the fixed actual carrier and r=0; in particular this covers the rho=0 saturated faces. The residual comparison allows rho>=0 only while these r=0 face conditions hold. No neighborhood extension, new global K or Lean verification.'}


PINS_PATH = 'certificates/source_norms/vector_marked_source.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('face_vector_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical whole-face certificate')
    elif args.write or args.output is not None:
        io.write_certificate_text(args.output or args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: identical fixed duals, all 41 costs, three affine-triangle vertices and constant old supports; uniform gain on all six actual K faces.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
