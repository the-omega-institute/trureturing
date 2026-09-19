#!/usr/bin/env python3
"""Actual cell-vector marked bounds, retaining selected deep3 virtual deletion.

Exact pointwise capacity duals preserve the same original test branch and
actual carrier mixture. Direction probes and face values are not global
comparison constants. The ordinary proof supplies arbitrary-source validity.
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
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/vector_marked_source.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f',
    'frontier/source-budgets/source_barrier_saturation.py': '6fe57e39274df1fa4a80ae4d4a22cab7b1d78d28c4f428b789071e3fb7776a64',
    'frontier/source-budgets/full_linear_carrier_frontier.py': '98cbec50d807ed9208504c8cd2384659a4300d6909d54414e5e2156285298888',
    'frontier/endpoint-bounds/broad_weighted_identity_source.py': 'ac969b33f833eb1cea191bdb74434ad6199077cfed1e551f0c5e0e7f286d3df1',
    'certificates/source_norms/endpoint-bounds/broad_weighted_identity_source.json': '6bab3011a7a09305ddac664cf9202a9801fc9dc121ff9de82c36ff4beac2bde0',
    'frontier/endpoint-bounds/broad_five_slot_tradeoff.py': '73a23d45c240ac9cd59216243127030e86f188d7dca930f689c44437799c59c5',
    'certificates/source_norms/endpoint-bounds/broad_five_slot_tradeoff.json': '563dd67bdd067108b08c0f9290d55271104559c1b01af7ba97cb61f97a6dc15c',
}
SIGMA = F(13, 1215)
R_CUTOFF = F(1, 2500)
TARGETS = (0, 16, 32, 40)


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


def geometry(broad, parameter, dat, pi, r, first_beta):
    require(0 <= r < R_CUTOFF, 'General-packing small-r range')
    score = broad.carrier_score(pi)
    # The parent validates the source parameter domain and actual weights.
    # Recompute every r-dependent cap and condition for the larger stated range.
    zero = broad.source_tables(parameter, dat, score, F(0), first_beta)
    Delta, a = zero['Delta'], zero['a']
    d, n, eta, s, _ = dat
    h, h0, h1 = sum(eta), sum(eta[:2]), sum(eta[2:])
    gaps = (h/5-r, h1/5-r, min(eta[2:])/5-r,
            h1*(F(1, 10)-Delta)-2*r, (h1-h0)/5-r)
    G = min(gaps)
    require(G > 0 and r < min(h/5, h1/5, min(eta[2:])/5), 'Common positive5/15 geometry gap')
    require(G >= F(241, 22500), 'Uniform broad-slab general-packing guard')
    caps = list(zero['capacities'])
    for cell in range(5):
        caps[5*cell+3] = eta[cell]*min(F(1, 5), F(3, 20)+Delta+r/h if cell < 2 else F(1, 10)+Delta+r/h1)
    failures = []
    if parameter[4] > F(4, 5):
        failures.append('forced source5 requires z<=4/5')
    beta_deficit = F(1, 4)-sum(parameter[2][2:])
    if parameter[2][first_beta] < F(1, 5)-beta_deficit:
        failures.append('the stipulated first-beta cell lacks its forced first-label mass')
    for cell in range(5):
        if n[cell] < eta[cell]/5-r or n[cell] > sum(caps[5*cell:5*cell+5]):
            failures.append('row'+str(cell)+' violates its necessary H/slot-cap bounds')
    for name, groups in broad.PARTITIONS.items():
        for number, group in enumerate(groups):
            cells = sorted({i//5 for i in group})
            if sum(n[cell]-eta[cell]/5 for cell in cells)+r < 0:
                failures.append(name+str(number)+' has negative non-H budget')
    if s < h/5-r:
        failures.append('total mass is smaller than its H mass')
    return {'Delta': Delta, 'r': r, 'first_beta': first_beta, 'score': score, 'a': a,
            'caps': tuple(caps), 'G': G, 'gap_entries': gaps, 'necessary_condition_failures': failures}


def column_upper(broad, coefficients, slot, state, n, eta, partitions):
    cap = tuple(state['caps'][5*cell+slot] for cell in range(5))
    require(min(coefficients) >= 0, 'Nonnegative weighted-column objective')
    bounds, duals = [], []
    for name in partitions:
        value, gammas = F(0), []
        for group in broad.PARTITIONS[name]:
            cells = tuple(sorted({i//5 for i in group}))
            budget = sum(n[cell]-eta[cell]/5 for cell in cells)+state['r']
            result, gamma = broad.capacity_dual(coefficients, cap, budget, cells)
            value += result
            gammas.append(gamma)
        bounds.append(value)
        duals.append({'partition': name, 'upper': value, 'gammas': gammas})
    return min(bounds), duals


def vector_marker(broad, state, dat, v, partitions):
    d, n, eta, _, _ = dat
    a, r = state['a'], state['r']
    vmax, dmax = max(v), max(d)
    base = sum(eta[cell]*a[cell]*v[cell] for cell in range(5))/5
    H = sum(eta[cell]*(1+int(cell >= 2))*v[cell] for cell in range(5))/25
    holes, deep_holes, duals = [], [], []
    for slot in range(4):
        coefficients = tuple(v[cell]*a[cell] for cell in range(5))
        ordinary, ordinary_dual = column_upper(broad, coefficients, slot, state, n, eta, partitions)
        holes.append(base-ordinary)
        alternatives = []
        for chosen in range(5):
            selected = tuple(coefficients[cell]-(SIGMA*v[cell]/eta[cell] if cell == chosen else 0)
                             for cell in range(5))
            require(min(selected) >= 0, 'The deep-retained column objectives stay nonnegative')
            upper, witnesses = column_upper(broad, selected, slot, state, n, eta, partitions)
            alternatives.append({'chosen_cell': chosen, 'lower': base+SIGMA*vmax*(dmax-d[chosen])-upper,
                                 'capacity_duals': witnesses})
        deep_holes.append(min(row['lower'] for row in alternatives))
        duals.append({'slot': slot, 'ordinary_duals': ordinary_dual, 'deep_alternatives': alternatives})
    Hdeep = H+SIGMA*min(v[cell]*max(F(0), F(1, 5)-r/eta[cell])+vmax*(dmax-d[cell]) for cell in range(5))
    plain, retained = min(H, *holes), min(Hdeep, *deep_holes)
    require(retained >= plain, 'Retaining another positive virtual family cannot weaken the bound')
    penalty = max(vmax, sum(eta[cell]*v[cell] for cell in range(5))/(5*state['G']))
    return {'v': v, 'ordinary_marker': plain, 'deep_retained_marker': retained,
            'H_lower': H, 'deep_H_lower': Hdeep, 'ordinary_holes': holes, 'deep_holes': deep_holes,
            'shared_residual_coefficient': penalty, 'selected_deep_coefficient': vmax, 'capacity_duals': duals}


def cost_bound(engine, broad, full, parameter, pi, index, r=F(0), first_beta=2,
               partitions=('three_groups', 'five_rows'), details=False):
    source, spec = engine.source, engine.specs[index]
    dat = source.data(parameter)
    state = geometry(broad, parameter, dat, pi, r, first_beta)
    record = {'index': index, 'name': spec['name'], 'tuple': spec['tuple'], 'parameter': parameter,
              'pi': pi, 'geometry': state, 'partitions': partitions}
    if state['necessary_condition_failures']:
        record['scope'] = 'Excluded by necessary actual-source conditions for these chosen source slots.'
        return record
    d, n, eta, s, _ = dat
    C, zero, tag = F(engine.thresholds[index]['constant']), spec['zero'], spec['tag']
    score = state['score']
    common = source.zero7_raw(tag, dat)-source.zero5_raw(zero, dat)
    positive, rows = engine.positive(index, eta), []
    conditional = [None]*18
    for item in spec['layouts']:
        b = item['baseline']
        costs = tuple(source.zero5_cost(tag, value) for value in b)
        v = tuple(source.zero5_cost(tag, value+1)-source.zero5_cost(tag, value) for value in b)
        require(v == tuple(item['joint'][1]), 'The actual fixed-branch derivative vector')
        marker = vector_marker(broad, state, dat, v, partitions)
        base = common+sum(n[cell]*item['psi'][cell]+eta[cell]*item['correction'][cell] for cell in range(5))
        base += max(source.zero5_common_deep(zero, b[cell], d[cell]) for cell in range(5))
        for position, c5 in enumerate(source.BASES):
            U, k = base+positive[position], tuple(C-value for value in costs)
            correction = tuple(v[cell]*c5[cell] for cell in range(5))
            A = tuple(k[cell]*n[cell]-correction[cell]*eta[cell]/5 for cell in range(5))
            z = tuple(k[cell]*d[cell]-correction[cell]/5 for cell in range(5))
            width = tuple(9*eta[cell]*k[cell] for cell in range(5))
            rest = F(13, 243)*max(z)+F(1, 486)*max(k[cell]*d[cell] for cell in range(5))
            rest += (sum(width)+max(sum(width[:2]), sum(width[2:]))+max(width))/36+max(k)/72
            old = C*s-U-(sum(weight*x for weight, x in zip(score, A))+rest)/5
            for ci, (root, cell) in enumerate(broad.CARRIERS):
                carrier = sum(A[j] for j in range(5) if broad.ROOT[j] == root)+(A[cell] if cell >= 0 else 0)
                value = C*s-U-(carrier+rest)/5
                conditional[ci] = value if conditional[ci] is None else min(conditional[ci], value)
            deep_shift = SIGMA*(max(z[cell]+v[cell]/5 for cell in range(5))-max(z))
            plain_credit = marker['ordinary_marker']-deep_shift
            credit = marker['deep_retained_marker']-deep_shift
            rows.append({'b': b, 'c5': c5, 'old_branch': old, 'deep_shift': deep_shift,
                         'plain_credit': plain_credit, 'new_credit': credit,
                         'new_branch': old+credit, 'plain_branch': old+plain_credit,
                         'residual_coefficient': marker['shared_residual_coefficient'], 'marker': marker})
    require(len(rows) == 100 and conditional == full.linear_direction(engine, dat, index)['conditional'],
            'All100 original branches recover all18 old conditional margins')
    old_average = sum(weight*value for weight, value in zip(pi, conditional))
    old_common = min(row['old_branch'] for row in rows)
    require(old_common >= old_average, 'Preserve the common-layout excess over the existing carrier average')
    new_min, plain_min = min(row['new_branch'] for row in rows), min(row['plain_branch'] for row in rows)
    digest = sha256(json.dumps(encode(rows), sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    def controller(row):
        compact = dict(row)
        compact['marker'] = {key: value for key, value in row['marker'].items() if key != 'capacity_duals'}
        compact['capacity_duals_sha256'] = sha256(json.dumps(encode(row['marker']['capacity_duals']),
                                                              sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        return compact
    record.update({'old_carrier_average': old_average, 'old_common_layout_min': old_common,
                   'new_layout_min': new_min, 'source_gain': new_min-old_average,
                   'without_selected_deep_gain': plain_min-old_average,
                   'minimum_branch_credit': min(row['new_credit'] for row in rows),
                   'uniform_residual_coefficient': max(row['residual_coefficient'] for row in rows),
                   'branch_count': len(rows), 'all_branches_and_duals_sha256': digest,
                   'old_controllers': [controller(row) for row in rows if row['old_branch'] == old_common],
                   'new_controllers': [controller(row) for row in rows if row['new_branch'] == new_min]})
    if details:
        record['all_branches'] = rows
    return record


def obstruction_matrix(engine, broad):
    base = engine.parameters[398]
    samples = ((F(1, 4), F(0), F(0)), (F(1, 5), F(1, 20), F(0)), (F(1, 5), F(1, 40), F(1, 40)))
    records = []
    for beta in samples:
        parameter = base[:2]+((F(0), F(0))+beta,)+base[3:]
        dat = engine.source.data(parameter)
        state = geometry(broad, parameter, dat, broad.point_carrier(1, 1), F(0), 2)
        X = [(F(0), F(1, 180), F(1, 90), F(0), F(1, 90)),
             (F(0), F(1, 45), F(1, 45), F(1, 60), F(1, 45)),
             (F(0), F(0), F(0), (F(3, 10)-beta[0])/9, F(1, 45)),
             (F(0), F(0), F(1, 45), (F(1, 10)-beta[1])/9, F(1, 45)),
             (F(0), F(0), F(1, 45), (F(1, 10)-beta[2])/9, F(1, 45))]
        require(not state['necessary_condition_failures'], 'The face matrix obeys the stipulated necessary source conditions')
        require(all(sum(X[cell]) == dat[1][cell] and X[cell][4] == dat[2][cell]/5 for cell in range(5))
                and all(0 <= X[cell][slot] <= state['caps'][5*cell+slot] for cell, slot in product(range(5), repeat=2)),
                'Explicit feasible25-cell matrix with full H and full non-beta B entries')
        records.append({'beta': beta, 'matrix': X})
    require(F(4, 225)/F(13, 6075) == F(108, 13), 'Exact derivative-ratio obstruction of the truncated observation')
    return {'matrix_examples': records, 'old_observation_credit': '4*v1/225-13*v2/6075',
            'positivity_ratio_threshold': F(108, 13),
            'scope': 'Feasible weighted-source relaxation, not a claimed covering construction. The ordinary matrix formula covers beta_L>=1/5 with total beta1/4.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('vector_marker_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source: '+path)
    saturation = module('vector_marker_engine', base/'frontier/source-budgets/source_barrier_saturation.py')
    engine = saturation.Experiment(base)
    broad = module('vector_marker_source', base/'frontier/endpoint-bounds/broad_weighted_identity_source.py')
    full = module('vector_marker_old', base/'frontier/source-budgets/full_linear_carrier_frontier.py')
    require(sum(F(1, 3**a) for a in (3, 4, 5))/5 == SIGMA, 'Complete selected deep3 and seven coefficient')
    require(F(3, 5)-18*SIGMA == F(11, 27) > 0, 'Uniform positivity of every modified column coefficient')
    parameter, pi = engine.parameters[398], broad.point_carrier(1, 1)
    face = [cost_bound(engine, broad, full, parameter, pi, index, partitions=('three_groups',)) for index in range(41)]
    require(all(row['source_gain'] > 0 for row in face), 'All41 retained-deep pointwise source gains are positive at the canonical face source')
    require(face[0]['without_selected_deep_gain'] < 0 and face[16]['without_selected_deep_gain'] < 0,
            'The two lost heavy costs still fail with the truncated25-cell observation')
    require(all(face[index]['source_gain'] == face[index]['old_carrier_average'] for index in (0, 16, 32))
            and face[40]['source_gain'] == F(4, 225), 'Selected deep payments recover the three heavy costs and identity')
    probes = []
    for coordinate in ('p', 'a', 'b', 'late3', 'deficit2', 'mixed_pi', 'positive_r'):
        par, pp, r = list(parameter), pi, F(0)
        if coordinate == 'p':
            par[4] = F(4, 5)
        elif coordinate == 'a':
            par[1] = (F(0), F(1, 4)-F(1, 18))
        elif coordinate == 'b':
            par[2] = (F(0), F(0), F(1, 4)-F(1, 18), F(0), F(0))
        elif coordinate == 'late3':
            par[3] = (F(0), F(0), F(0), F(1, 72), F(0))
        elif coordinate == 'deficit2':
            par[0] = (F(0), F(0), F(1, 2), F(0), F(0))
        elif coordinate == 'mixed_pi':
            pp = tuple((x+y)/2 for x, y in zip(pi, broad.point_carrier(-1, 2)))
        else:
            r = F(1, 5000)
        probes.append({'name': coordinate, 'costs': [cost_bound(engine, broad, full, tuple(par), pp, index, r=r) for index in TARGETS]})
    used = dict(PINS)
    for path, pin in engine.pins.items():
        require(path not in used or used[path] == pin, 'Consistent inherited input')
        used[path] = pin
    return {'schema': 'erdos7-vector-marked-source-v1', 'source_sha256': used,
            'selected_deep_exponents': [3, 4, 5], 'selected_deep_coefficient': SIGMA,
            'slab_Delta_upper': F(1, 18), 'r_cutoff_strict': R_CUTOFF,
            'general_comparison': 'actual_margin >= old_carrier_average + [source_gain - uniform_residual_coefficient*(rho-(r+r1)/5)]_+',
            'shared_budget': '(E5-r/5)+(E15-r1/5)+Edeep+omega<=rho-(r+r1)/5',
            'deep_lemma': 'Vdeep(v*I_J)>=sigma*min_l[v_l*X_lJ/eta_l+kappa*(dmax-d_l)]-kappa*Edeep, kappa>=vmax',
            'canonical_face_costs': face, 'direction_probes': probes,
            'weighted_face_gain': sum(engine.weights[index]*row['source_gain'] for index, row in enumerate(face)),
            'truncated_observation_obstruction': obstruction_matrix(engine, broad),
            'scope': 'Ordinary pointwise actual-source theorem on the stated broad slab, with exact branch/dual arithmetic. Face and direction evaluations do not certify a uniform positive source gain, a new global K, or Lean verification. The retained deep families are complete and the actual common residual is charged once.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('vector_marker_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical vector-marker certificate')
    elif args.write or args.output is not None:
        io.write_certificate_text(args.output or args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: vector source duals, retained selected-deep deletion, all original branches and one shared residual. No global improvement inferred from probes.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
