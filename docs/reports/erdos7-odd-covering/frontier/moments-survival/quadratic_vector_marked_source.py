#!/usr/bin/env python3
"""Quadratic cell-vector marked bounds with all four selected deep cofactors.

The pointwise interface keeps the alpha=6/5 source payment, the original
curvature, independent original tests and one actual residual budget.
Canonical evaluations are not global comparison constants.
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
CERTIFICATE = 'certificates/source_norms/moments-survival/quadratic_vector_marked_source.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/endpoint-bounds/vector_marked_source.py': 'e9917c725b8f910a0524ccae99dfffb5949f3af568980a70b5299e7fb1c71b39',
    'certificates/source_norms/endpoint-bounds/vector_marked_source.json': '01f58d319ca57688a219d24296d8ba8aebba91f6091e6bf1bda0f34ceb10180f',
    'frontier/moments-survival/quadratic_marked_global.py': '71c7b94fa6ca7748481d9415363552402e21dcfdd755c78781dbeffe121d905f',
    'certificates/source_norms/moments-survival/quadratic_marked_global.json': 'ef92b42ce4cc28f7a8d3e9cca5628bb30dd7f3bb9cd3f49fa2bb7dd7cbebcd37',
    'certificates/source_norms/endpoint-bounds/k_face_complete_ratio.json': 'ccb1debedef1dc49cbc6a31e01c712f156992dc238bd0576e4f51ee8dd6f6888',
}
ALPHA, SIGMA = F(6, 5), F(40, 3645)
FACE_VERTICES = ((F(1, 4), F(0), F(0)), (F(1, 5), F(1, 20), F(0)),
                 (F(1, 5), F(0), F(1, 20)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
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


def digest(value):
    return sha256(json.dumps(encode(value), sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def dual_signature(row):
    return [{'slot': item['slot'], 'ordinary_duals': item['ordinary_duals'],
             'deep_duals': [{'chosen_cell': alt['chosen_cell'], 'capacity_duals': alt['capacity_duals']}
                            for alt in item['deep_alternatives']]}
            for item in row['marker']['capacity_duals']]


def quadratic_common_decomposition(source, spec, dat):
    """Cancel e=0 and expose the complete positive quadratic-tail combination."""
    tag = spec['tag']
    require(spec['zero'] == ('seven_block', (tag, 0)), 'Exact original e=0 block cancellation')
    degree, leading, offset, cutoff = source.zero5_cost_metadata(tag)
    require(degree == 2 and leading > 0 and cutoff >= 2, 'Positive quadratic source tail')
    tails = tuple(F(36, 5)*value for value in source.geom(7, cutoff))
    expectation = sum(source.zero7_probability(n)*source.zero5_cost(tag, n) for n in range(1, cutoff))
    expectation += leading*tails[2]+offset*tails[0]
    tail_weight = leading*(tails[2]-(cutoff-1)*tails[1])
    require(tail_weight >= 0, 'Nonnegative weight of the complete square-monomial source block')
    blocks = []
    for exponent in range(1, cutoff-1):
        block = ('seven_block', (tag, exponent))
        require(source.zero5_cost_metadata(block)[0] == 2, 'Every retained finite block has a complete quadratic tail')
        blocks.append({'seven_block': exponent, 'raw_value': source.zero5_raw(block, dat)})
    monomial = source.zero5_raw(('s', F(0)), dat)
    rebuilt = dat[3]*(expectation-tail_weight)+sum(row['raw_value'] for row in blocks)+tail_weight*monomial
    require(rebuilt == source.zero7_raw(tag, dat)-source.zero5_raw(spec['zero'], dat),
            'Exact positive-block decomposition of the full common term, with no difference-convexity assumption')
    return {'cutoff': cutoff, 'affine_source_coefficient': expectation-tail_weight,
            'finite_blocks': blocks, 'complete_tail_weight': tail_weight,
            'square_monomial_raw': monomial, 'reconstructed_common': rebuilt}


def vector_marker(broad, vector, state, dat, v, partitions):
    d, n, eta, _, _ = dat
    a = tuple(ALPHA-score/5 for score in state['score'])
    require(all(F(4, 5) <= value <= ALPHA for value in a), 'Exact quadratic source coefficient after shallow cancellation')
    r, vmax, dmax = state['r'], max(v), max(d)
    base = sum(eta[cell]*a[cell]*v[cell] for cell in range(5))/5
    H = sum(eta[cell]*(1+int(cell >= 2))*v[cell] for cell in range(5))/25
    holes, deep_holes, duals = [], [], []
    for slot in range(4):
        coefficients = tuple(v[cell]*a[cell] for cell in range(5))
        ordinary, ordinary_dual = vector.column_upper(broad, coefficients, slot, state, n, eta, partitions)
        holes.append(base-ordinary)
        alternatives = []
        for chosen in range(5):
            selected = tuple(coefficients[cell]-(SIGMA*v[cell]/eta[cell] if cell == chosen else 0)
                             for cell in range(5))
            require(min(selected) >= 0, 'Every quadratic retained-deep column coefficient is nonnegative')
            upper, witnesses = vector.column_upper(broad, selected, slot, state, n, eta, partitions)
            alternatives.append({'chosen_cell': chosen, 'lower': base+SIGMA*vmax*(dmax-d[chosen])-upper,
                                 'capacity_duals': witnesses})
        deep_holes.append(min(row['lower'] for row in alternatives))
        duals.append({'slot': slot, 'ordinary_duals': ordinary_dual, 'deep_alternatives': alternatives})
    Hdeep = H+SIGMA*min(v[cell]*max(F(0), F(1, 5)-r/eta[cell])+vmax*(dmax-d[cell]) for cell in range(5))
    plain, retained = min(H, *holes), min(Hdeep, *deep_holes)
    require(retained >= plain, 'Retaining the four positive deep families does not weaken the interface')
    penalty = max(vmax, sum(eta[cell]*v[cell] for cell in range(5))/(5*state['G']))
    return {'v': v, 'source_coefficients': a, 'ordinary_marker': plain, 'deep_retained_marker': retained,
            'H_lower': H, 'deep_H_lower': Hdeep, 'ordinary_holes': holes, 'deep_holes': deep_holes,
            'shared_residual_coefficient': penalty, 'selected_deep_coefficient': vmax, 'capacity_duals': duals}


def cost_bound(engine, broad, vector, full, parameter, pi, index, r=F(0), first_beta=2,
               partitions=('three_groups',), details=False):
    source, spec = engine.source, engine.quadratic_specs[index]
    dat = source.data(parameter)
    state = vector.geometry(broad, parameter, dat, pi, r, first_beta)
    record = {'index': index, 'tuple': spec['tuple'], 'parameter': parameter, 'pi': pi,
              'geometry': state, 'partitions': partitions, 'source_payment_multiplier': ALPHA}
    if state['necessary_condition_failures']:
        record['scope'] = 'Excluded by necessary actual-source conditions for these chosen source slots.'
        return record
    d, n, eta, s, _ = dat
    C, tag = engine.quadratic_constants[index], spec['tag']
    zero, psi, curve, _, curve_record = engine.psis[index]
    require(zero == spec['zero'] and curve > 0, 'Same selected source and retained original quadratic curvature')
    common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
    positive, rows = engine.quadratic_positive(index, eta), []
    conditional = [None]*18
    for b in source.BASES:
        costs = tuple(source.zero5_cost(tag, value) for value in b)
        v = tuple(source.zero5_cost(tag, value+1)-source.zero5_cost(tag, value) for value in b)
        marker = vector_marker(broad, vector, state, dat, v, partitions)
        base = common+sum(n[cell]*psi(b[cell])+eta[cell]*source.zero5_centered_correction(zero, b[cell]) for cell in range(5))
        base += max(source.zero5_common_deep(zero, b[cell], d[cell]) for cell in range(5))
        for position, c5 in enumerate(source.BASES):
            curvature_loss = F(4, 25)*curve*engine.distance(eta, b, c5)
            U, k = base+positive[position]-curvature_loss, tuple(C-value for value in costs)
            correction = tuple(v[cell]*c5[cell] for cell in range(5))
            require(all(0 <= correction[cell]-v[cell] <= correction[cell] <= k[cell] for cell in range(5)),
                    'Every original quadratic branch retains nonnegative marked and unmarked floors')
            A = tuple(k[cell]*n[cell]-correction[cell]*eta[cell]/5 for cell in range(5))
            z = tuple(k[cell]*d[cell]-correction[cell]/5 for cell in range(5))
            require(all(z[cell] >= k[cell]/20 >= 0 for cell in range(5)), 'Complete selected deep cap remains nonnegative')
            width = tuple(9*eta[cell]*k[cell] for cell in range(5))
            rest = F(40, 729)*max(z)+F(1, 1458)*max(k[cell]*d[cell] for cell in range(5))
            rest += (sum(width)+max(sum(width[:2]), sum(width[2:]))+max(width))/36+max(k)/72
            old = C*s-U-(sum(weight*x for weight, x in zip(state['score'], A))+rest)/5
            for ci, (root, cell) in enumerate(broad.CARRIERS):
                carrier = sum(A[j] for j in range(5) if broad.ROOT[j] == root)+(A[cell] if cell >= 0 else 0)
                value = C*s-U-(carrier+rest)/5
                conditional[ci] = value if conditional[ci] is None else min(conditional[ci], value)
            deep_shift = SIGMA*(max(z[cell]+v[cell]/5 for cell in range(5))-max(z))
            plain_credit, credit = marker['ordinary_marker']-deep_shift, marker['deep_retained_marker']-deep_shift
            rows.append({'b': b, 'c5': c5, 'old_branch': old, 'curvature_loss': curvature_loss,
                         'deep_shift': deep_shift, 'plain_credit': plain_credit, 'new_credit': credit,
                         'new_branch': old+credit, 'plain_branch': old+plain_credit,
                         'residual_coefficient': marker['shared_residual_coefficient'], 'marker': marker})
    prior = full.quadratic_direction(engine, dat, index)
    require(len(rows) == 100 and conditional == prior['conditional'] and C == prior['constant'],
            'All100 quadratic branches reproduce all18 full49 conditional minima including curvature and tails')
    old_average = sum(weight*value for weight, value in zip(pi, conditional))
    old_common = min(row['old_branch'] for row in rows)
    require(old_common >= old_average, 'Retain common-layout excess over old carrier-averaged minima')
    new_min, plain_min = min(row['new_branch'] for row in rows), min(row['plain_branch'] for row in rows)
    digest = sha256(json.dumps(encode(rows), sort_keys=True, separators=(',', ':')).encode()).hexdigest()

    def controller(row):
        compact = dict(row)
        compact['marker'] = {key: value for key, value in row['marker'].items() if key != 'capacity_duals'}
        compact['capacity_duals_sha256'] = sha256(json.dumps(encode(row['marker']['capacity_duals']),
                                                              sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        return compact

    record.update({'barrier': C, 'curvature_record': curve_record, 'old_carrier_average': old_average,
                   'old_common_layout_min': old_common, 'new_layout_min': new_min,
                   'source_gain': new_min-old_average, 'without_selected_deep_gain': plain_min-old_average,
                   'minimum_branch_credit': min(row['new_credit'] for row in rows),
                   'uniform_residual_coefficient': max(row['residual_coefficient'] for row in rows),
                   'branch_count': len(rows), 'all_branches_and_duals_sha256': digest,
                   'old_controllers': [controller(row) for row in rows if row['old_branch'] == old_common],
                   'new_controllers': [controller(row) for row in rows if row['new_branch'] == new_min]})
    if details:
        record['all_branches'] = rows
    return record


def whole_face(engine, broad, vector, full, canonical_records):
    source, canonical = engine.source, engine.parameters[398]
    parameters = [canonical[:2]+((F(0), F(0))+beta,)+canonical[3:] for beta in FACE_VERTICES]
    data = [source.data(p) for p in parameters]
    pi = broad.point_carrier(1, 1)
    states = [vector.geometry(broad, p, dat, pi, F(0), 2) for p, dat in zip(parameters, data)]
    expected_masses = (F(1, 36), F(1, 12), F(5, 36))
    for dat, state in zip(data, states):
        require(not state['necessary_condition_failures'], 'Every affine triangle vertex satisfies the necessary source conditions')
        require(dat[2] == data[0][2] and max(dat[0]) == F(3, 4) and dat[3] == F(1, 4)
                and (dat[1][0], dat[1][1], sum(dat[1][2:])) == expected_masses,
                'Constant eta, dmax, total mass and three-group source masses')
        require(state['caps'] == states[0]['caps'] and state['score'] == states[0]['score']
                and state['G'] == states[0]['G'], 'The same capacity-dual constraints and residual geometry throughout the triangle')
    costs = []
    for index, spec in enumerate(engine.quadratic_specs):
        records = [canonical_records[index]]+[cost_bound(engine, broad, vector, full, p, pi, index, details=True)
                                               for p in parameters[1:]]
        for pos, row in enumerate(records[0]['all_branches']):
            for record in records[1:]:
                compared = record['all_branches'][pos]
                require((compared['b'], compared['c5']) == (row['b'], row['c5'])
                        and compared['curvature_loss'] == row['curvature_loss']
                        and compared['residual_coefficient'] == row['residual_coefficient']
                        and dual_signature(compared) == dual_signature(row),
                        'Every fixed old branch keeps the identical curvature, penalty and all capacity duals across the triangle')
        lower = min(record['new_layout_min'] for record in records)
        require(all(record['new_layout_min'] == lower for record in records)
                and lower == canonical_records[index]['new_layout_min'], 'The exact same absolute new-margin lower bound at all three vertices')
        decompositions = [quadratic_common_decomposition(source, spec, dat) for dat in data]
        costs.append({'index': index, 'tuple': spec['tuple'], 'barrier': engine.quadratic_constants[index],
                      'uniform_absolute_margin_lower': lower,
                      'uniform_residual_coefficient': max(record['uniform_residual_coefficient'] for record in records),
                      'vertex_new_minima': [record['new_layout_min'] for record in records],
                      'vertex_old_minima': [record['old_carrier_average'] for record in records],
                      'vertex_branch_and_dual_sha256': [record['all_branches_and_duals_sha256'] for record in records],
                      'fixed_capacity_duals_sha256': digest([dual_signature(row) for row in records[0]['all_branches']]),
                      'complete_quadratic_common_decomposition': decompositions,
                      'zero_residual_cost_upper': engine.quadratic_constants[index]*F(53, 360)-lower})
    mappings = [root0+tail for root0 in ((0, 1), (1, 0)) for tail in permutations((2, 3, 4))]
    for perm in mappings:
        require(tuple(broad.ROOT[j] for j in perm) == broad.ROOT
                and {tuple(b[j] for j in perm) for b in source.BASES} == set(source.BASES),
                'All face relabellings preserve roots and the complete original layout inventory')
        for spec in engine.quadratic_specs:
            f = lambda value: source.zero5_cost(spec['tag'], value)
            for b in source.BASES:
                moved = tuple(b[j] for j in perm)
                require(tuple(f(value+1)-f(value) for value in moved)
                        == tuple(f(b[j]+1)-f(b[j]) for j in perm), 'Quadratic cell derivatives covary')
                for c in source.BASES:
                    require(engine.distance(data[0][2], b, c)
                            == engine.distance(tuple(data[0][2][j] for j in perm), moved, tuple(c[j] for j in perm)),
                            'The original curvature term covaries under every face relabelling')
    mid_beta = (F(1, 5), F(1, 40), F(1, 40))
    midpoint = canonical[:2]+((F(0), F(0))+mid_beta,)+canonical[3:]
    witness = cost_bound(engine, broad, vector, full, midpoint, pi, 0)
    require(witness['old_carrier_average'] > canonical_records[0]['old_carrier_average']
            and witness['new_layout_min'] == costs[0]['uniform_absolute_margin_lower'],
            'The00 old minimum is not constant; use the absolute new bound rather than a constant relative gain')
    return {'vertices': FACE_VERTICES, 'source_group_masses': expected_masses,
            'non_H_group_budgets': (F(1, 60), F(11, 180), F(13, 180)), 'constant_geometry': states[0],
            'relabellings': mappings, 'costs': costs,
            'old00_nonconstant_witness': {'beta': mid_beta, 'old_margin': witness['old_carrier_average'],
                                         'new_margin': witness['new_layout_min'], 'relative_gain': witness['source_gain']},
            'comparison': 'On all six K-face triangles with r=0: actual_margin_i >= uniform_absolute_margin_lower_i - P_i*rho. At rho=0: cost_i <= C_i*(53/360)-uniform_absolute_margin_lower_i.',
            'scope': 'Whole-face absolute bounds with r=0 from concavity of the exact improved branches with fixed source duals and unchanged curvature. Cost bounds additionally require rho=0. No constant00 relative gain, neighborhood extension or global K claimed.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('quadratic_vector_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source: '+path)
    predecessors = [json.loads(io.read_artifact_bytes(base/path)) for path in (
        'certificates/source_norms/endpoint-bounds/vector_marked_source.json',
        'certificates/source_norms/moments-survival/quadratic_marked_global.json')]
    for predecessor in predecessors:
        for path, pin in predecessor['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited source')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
            used[path] = pin
    saturation = module('quadratic_vector_engine', base/'frontier/source-budgets/source_barrier_saturation.py')
    engine = saturation.Experiment(base)
    broad = module('quadratic_vector_source', base/'frontier/endpoint-bounds/broad_weighted_identity_source.py')
    vector = module('quadratic_vector_geometry', base/'frontier/endpoint-bounds/vector_marked_source.py')
    full = module('quadratic_vector_old', base/'frontier/source-budgets/full_linear_carrier_frontier.py')
    for path, pin in engine.pins.items():
        require(path not in used or used[path] == pin, 'Consistent complete source engine')
        used[path] = pin
    require(sum(F(1, 3**a) for a in range(3, 7))/5 == SIGMA and SIGMA+F(1, 7290) == F(1, 90),
            'All four selected deep3 cofactors and the unchanged complete remaining tail')
    require(F(4, 5)-18*SIGMA == F(244, 405) > 0 and F(4, 5)-F(2, 5) == F(2, 5),
            'All modified capacity-dual coefficients and the best-column comparison stay positive')
    parameter, pi = engine.parameters[398], broad.point_carrier(1, 1)
    detailed_face = [cost_bound(engine, broad, vector, full, parameter, pi, index, details=True) for index in range(5)]
    face = [{key: value for key, value in row.items() if key != 'all_branches'} for row in detailed_face]
    require(all('source_gain' in row for row in face), 'Canonical source passes every necessary geometry condition')
    gains = (F(85666041658, 7630684936875), F(5209, 725010), F(293, 145002),
             F(379438, 49054005), F(131938, 49054005))
    require(tuple(row['source_gain'] for row in face) == gains and min(gains) > 0,
            'All five exact pointwise quadratic gains are positive, including the formerly discarded00 cost')
    require(all(0 < row['without_selected_deep_gain'] < row['source_gain'] for row in face)
            and face[0]['source_gain'] > face[0]['minimum_branch_credit'],
            'Cell-weighted source data already repairs00; selected deep deletion and its old branch excess give further gains')
    first94 = predecessors[1]['cost_rows'][41]
    scalar_ideal00 = F(first94['vmin'])/50-F(8, 3645)*F(first94['vmax'])
    require(first94['tuple'] == [0, 0] and scalar_ideal00 < 0,
            'The uniform min/max scalar template cannot include00 even at its ideal source credit')
    weighted_gain = engine.source.AC*sum(gains)
    require(weighted_gain == F(6140967005013173, 241740098800200000), 'Exact combined quadratic pointwise gain')
    full_face = whole_face(engine, broad, vector, full, detailed_face)
    old84 = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/endpoint-bounds/k_face_complete_ratio.json'))
    comparison84 = []
    for row, prior in zip(full_face['costs'], old84['improved_cost_bounds'][41:46]):
        saved, new = F(prior), row['zero_residual_cost_upper']
        comparison84.append({'index': row['index'], 'tuple': row['tuple'], 'old84_upper': saved,
                             'new96_upper': new, 'retained_upper': min(saved, new),
                             'signed_improvement': saved-new, 'usable_improvement': max(F(0), saved-new)})
    require([row['tuple'] for row in comparison84 if row['usable_improvement'] > 0] == [[0, 0], [0, 1], [1, 0]],
            'Only three quadratic costs improve the already available84 bounds')
    improvement84 = engine.source.AC*sum(row['usable_improvement'] for row in comparison84)
    require(improvement84 == F(10407081038453971, 483480197600400000), 'Exact usable increment over84, without counting dominated new bounds')
    return {'schema': 'erdos7-quadratic-vector-marked-source-v1', 'source_sha256': used,
            'source_payment_multiplier': ALPHA, 'selected_deep_exponents': [3, 4, 5, 6],
            'selected_deep_coefficient': SIGMA, 'unchanged_unselected_mass_tail_coefficient': F(1, 7290),
            'slab_Delta_upper': F(1, 18), 'r_cutoff_strict': vector.R_CUTOFF,
            'general_comparison': 'actual_margin >= old_carrier_average + [source_gain - uniform_residual_coefficient*(rho-(r+r1)/5)]_+',
            'shared_budget': '(E5-r/5)+(E15-r1/5)+Edeep6+omega<=rho-(r+r1)/5',
            'deep_lemma': 'Vdeep6(v*I_J)>=sigma6*min_l[v_l*X_lJ/eta_l+kappa*(dmax-d_l)]-kappa*Edeep6, kappa>=vmax',
            'canonical_parameter_index': 398, 'canonical_carrier': [1, 1], 'canonical_r': F(0),
            'canonical_quadratic_costs': face, 'comparison_weight': engine.source.AC,
            'weighted_canonical_gain': weighted_gain, 'uniform_scalar_ideal00_gain': scalar_ideal00,
            'weighted_canonical_residual_coefficient': engine.source.AC*sum(row['uniform_residual_coefficient'] for row in face),
            'whole_face': full_face,
            'comparison_to84': comparison84, 'weighted_usable_improvement_over84': improvement84,
            'scope': 'Ordinary pointwise quadratic vector-marker theorem and whole-face absolute-margin bounds retain alpha=6/5 source payment, all original curvature and six cofactor tails. Independent original tests use the same actual source, carrier mixture and residual. Canonical relative gains are not constant whole-face gains. No covering construction, neighborhood extension, new global K or Lean verification.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('quadratic_vector_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact quadratic vector-source certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: five quadratic vector costs, all1500 triangle-endpoint branches, fixed duals, original curvature and complete tails.')
    for row in result['canonical_quadratic_costs']:
        print('Tuple '+str(row['tuple'])+': gain '+row['source_gain']+' = '+str(float(F(row['source_gain'])))+
              '; without selected deep '+str(float(F(row['without_selected_deep_gain']))))
    print('Weighted canonical gain: '+str(float(F(result['weighted_canonical_gain'])))+'. No global bound inferred.')


if __name__ == '__main__':
    main()
