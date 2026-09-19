#!/usr/bin/env python3
"""Exact late-factor Jensen obstruction and a fixed-zero-dual line repair."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/heavy_margin_vertex_obstruction.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/vector_marked_source.py': 'd4fb958ac95a62a766debf18b8a7079081d922430e471d594725274acf321fbc',
    'frontier/broad_weighted_identity_source.py': 'e0a89669a6b8b6ff732391b4c27dddd21bf5517f8a37928120e75955349dd98f',
    'frontier/full_linear_carrier_frontier.py': '98cbec50d807ed9208504c8cd2384659a4300d6909d54414e5e2156285298888',
    'frontier/source_barrier_saturation.py': '92076ee71a6be16655bbe5c2ac223db6502da1ab5c3553a7f83bb555dbbb8363',
}
TIMES = (F(0), F(3, 4), F(4, 5), F(17, 20), F(1))
BASELINE = (2, 3, 1, 1, 1)
POSITIVE5 = (1, 1, 3, 2, 2)
V3 = F(298469622484874903, 2311075142665519230)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned source')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def parameter(t):
    require(0 <= t <= 1, 'The original late-simplex segment')
    return ((F(1, 2), F(0), F(0), F(0), F(0)), (F(0), F(1, 4)),
            (F(0), F(0), F(1, 4), F(0), F(0)),
            ((1-t)/72, F(0), F(0), t/72, F(0)), F(3, 4))


def fixed_zero_marker(state, dat, v, sigma):
    """Feasible gamma=0 capacity dual, explicitly not the optimized API."""
    d, _, eta, _, _ = dat
    a, r = state['a'], state['r']
    base = sum(e*aa*vv for e, aa, vv in zip(eta, a, v))/5
    vmax, dmax = max(v), max(d)
    deep_H = sum(eta[c]*(1+int(c >= 2))*v[c] for c in range(5))/25
    deep_H += sigma*min(v[c]*max(F(0), F(1, 5)-r/eta[c])+vmax*(dmax-d[c]) for c in range(5))
    holes = []
    for slot in range(4):
        alternatives = []
        for chosen in range(5):
            coefficients = tuple(v[c]*a[c]-(sigma*v[c]/eta[c] if c == chosen else 0) for c in range(5))
            require(min(coefficients) >= 0, 'Feasible nonnegative fixed capacity-dual coefficients')
            upper = sum(coefficients[c]*state['caps'][5*c+slot] for c in range(5))
            alternatives.append(base+sigma*vmax*(dmax-d[chosen])-upper)
        holes.append(min(alternatives))
    return min(deep_H, *holes)


def calculate(base):
    io = module('vertex_obstruction_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    vector = module('vertex_obstruction_vector', base/'frontier/vector_marked_source.py')
    broad = module('vertex_obstruction_broad', base/'frontier/broad_weighted_identity_source.py')
    full = module('vertex_obstruction_full', base/'frontier/full_linear_carrier_frontier.py')
    engine = module('vertex_obstruction_engine', base/'frontier/source_barrier_saturation.py').Experiment(base)
    pins = {}
    for source in (PINS, vector.PINS, engine.pins):
        for path, pin in source.items():
            require(path not in pins or pins[path] == pin, 'Consistent inherited pin '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Complete original source pin '+path)
    require(parameter(F(0)) == engine.parameters[398] and parameter(F(1)) == engine.parameters[404],
            'The endpoints are original product vertices398 and404')
    require(engine.specs[0]['zero'] == ('seven_block', (engine.specs[0]['tag'], 0)),
            'The original zero block cancels before the late-factor concavity proof')
    pi, records, fixed_vectors = broad.point_carrier(1, 1), [], []
    for t in TIMES:
        par, dat = parameter(t), engine.source.data(parameter(t))
        row = vector.cost_bound(engine, broad, full, par, pi, 0, r=F(0), first_beta=2, details=True)
        state = row['geometry']
        require(not state['necessary_condition_failures'] and state['Delta'] == 0,
                'Every retained point satisfies the original API guards and necessary source conditions')
        branch = next(b for b in row['all_branches'] if b['b'] == BASELINE and b['c5'] == POSITIVE5)
        require(branch['old_branch'] == row['old_common_layout_min']
                and branch['new_branch'] == row['new_layout_min'], 'One unchanged original controller at all five points')
        marker = branch['marker']
        require(marker['v'][3] == V3 and marker['deep_retained_marker'] == marker['deep_holes'][2],
                'Same original derivative and active second nonzero slot')
        deep = marker['capacity_duals'][2]['deep_alternatives'][0]
        require(deep['chosen_cell'] == 0 and deep['lower'] == marker['deep_retained_marker'],
                'The same selected-deep cell controls throughout')
        budget, cap = dat[1][3]-dat[2][3]/5, state['caps'][5*3+2]
        require(budget == F(1, 30)-t/72 and cap == F(1, 45), 'Exact cell3 budget crossing')
        expected_credit = 4*V3/225+V3*max(F(0), t-F(4, 5))/90
        require(branch['new_credit'] == expected_credit and row['source_gain'] == expected_credit,
                'Exact positive-part gain from the optimized five-row capacity bound')
        three, five = deep['capacity_duals']
        require(three['partition'] == 'three_groups' and five['partition'] == 'five_rows'
                and all(g == 0 for g in three['gammas']), 'Original grouped cap dual is gamma0')
        require(three['upper']-five['upper'] == V3*max(F(0), t-F(4, 5))/90,
                'The complete observed convex kink is precisely the five-row improvement')
        fixed, corrections = [], []
        for original in row['all_branches']:
            credit = fixed_zero_marker(state, dat, original['marker']['v'], vector.SIGMA)-original['deep_shift']
            require(credit <= original['new_credit'], 'Every fixed dual gives a valid lower marker than the optimized one')
            fixed.append(original['old_branch']+credit)
            corrections.append(credit)
        fixed_vectors.append(corrections)
        fixed_min = min(fixed)
        require(fixed_min == row['old_common_layout_min']+4*V3/225,
                'Fixed gamma0 restores the same constant credit at the retained points')
        records.append({'t': t, 'parameter': par, 'source_data': dat, 'geometry': state,
                        'old_margin': row['old_common_layout_min'], 'new_margin': row['new_layout_min'],
                        'source_gain': row['source_gain'], 'fixed_zero_dual_margin': fixed_min,
                        'controller': {'baseline': BASELINE, 'positive5': POSITIVE5, 'v': marker['v'],
                                       'deep_shift': branch['deep_shift'], 'credit': branch['new_credit'],
                                       'slot': 2, 'chosen_deep_cell': 0, 'cell3_budget': budget, 'cell3_cap': cap,
                                       'capacity_duals': deep['capacity_duals']},
                        'original_branch_count': row['branch_count'],
                        'all_original_branches_sha256': row['all_branches_and_duals_sha256']})
    require(all(v == fixed_vectors[0] for v in fixed_vectors), 'All100 fixed branch corrections are unchanged along the late line')
    require(all(r['geometry']['caps'] == records[0]['geometry']['caps']
                and r['geometry']['G'] == records[0]['geometry']['G'] for r in records),
            'Only the original late factor and its affine masses move')
    left, middle, right = records[1:4]
    gaps = {k: middle[k]-(left[k]+right[k])/2 for k in
            ('old_margin', 'new_margin', 'source_gain', 'fixed_zero_dual_margin')}
    require(gaps['old_margin'] == gaps['fixed_zero_dual_margin'] == 0
            and gaps['new_margin'] == gaps['source_gain'] == -V3/3600 < 0,
            'Exact separate-concavity counterexample and the fixed-dual repair')
    endpoint_gap = records[1]['new_margin']-((F(1, 4)*records[0]['new_margin'])+F(3, 4)*records[4]['new_margin'])
    require(endpoint_gap < 0, 'The chord between the two original product vertices also fails')
    return vector.encode({'schema': 'erdos7-heavy-margin-vertex-obstruction-v1', 'source_sha256': pins,
                          'index': 0, 'name': engine.specs[0]['name'], 'tuple': engine.specs[0]['tuple'],
                          'pi': pi, 'r': F(0), 'first_beta': 2, 'records': records,
                          'midpoint_jensen_gaps': gaps, 'V3': V3, 'full_endpoint_chord_gap_at_three_quarters': endpoint_gap,
                          'scope': 'Exact counterexample to separate concavity of the original implemented index0 retained-deep margin on its valid source relaxation. The fixed gamma0 construction is a valid, separately concave repair in the late factor with all other inputs fixed. No actual finite covering-family realization, nonconcavity assertion about the full52-cost sum, global comparison, Lean theorem or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('vertex_obstruction_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact original-margin obstruction certificate')
    print('PASS: original heavy margin violates late-factor Jensen; a fixed gamma0 repairs this factor.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
