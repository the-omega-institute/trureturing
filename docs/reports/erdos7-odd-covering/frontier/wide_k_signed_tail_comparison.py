#!/usr/bin/env python3
"""Complete all52 original costs on the1/27 source rectangle with signed tails."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/wide_k_signed_tail_comparison.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/shared_loss_signed_k_comparison.py': '90ef7fb11f24f17144a72b99091fc634d0fe0c9b4454fb5b105df1d65e4174cb',
    'certificates/source_norms/shared_loss_signed_k_comparison.json': '163feab0f92b2a82d3e5b087567a4c78345a4ec20d3674b6a3c90a12566e2cc3',
    'frontier/uniform_shallow_indicator_transport.py': 'bdeacf5b810a3c9d4738752e1b15e0044eaddd0b5e471ff609b61d5f4fd44c1c',
    'certificates/source_norms/uniform_shallow_indicator_transport.json': 'edb1a2de1d2662d15eca2d867adf4e1e48c72df984187263be2953dea3260416',
}
DELTA, RHO, A = F(1, 27), F(1, 100000), F(53, 360)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned source')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def parameters(study, delta, rho):
    require(0 <= delta <= F(2, 27), 'Ordinary source and cap dominance domain')
    par = study.uniform.parameters(delta, rho)
    shared = study.get('joint_concentration_loss_budget').total_loss_upper(delta)
    par['v0'] = min(F(1, 20), shared/4+2*par['rbar'])
    par['v1'] = min(F(1, 10), shared/4+par['rbar']/par['h1min'])
    par['budget_increments'] = ((3+delta)*shared/72, delta/36, shared/12)
    root0 = F(1, 9)+par['budget_increments'][0]+par['budget_increments'][1]
    root1 = F(5, 36)+shared/12
    maxn = F(1, 12)+delta/36
    require(root0 <= root1 and F(1, 36)+par['budget_increments'][0] <= maxn
            and F(1, 18)+shared/36 <= maxn, 'All root and cell upper bounds are dominated')
    zplus = (root1/35+maxn/5+(F(3, 4)+delta/4)/90
             +11*(F(1, 2)+delta/18)/700+F(1, 3)/20+F(1, 9)/20+F(1, 360))
    require(zplus == F(779, 12600)+shared/420+29*delta/3150,
            'Complete positive-seven complement after exact common-source cancellation')
    require(zplus <= par['positive7'], 'The retained complement improves its previous uniform upper bound')
    par['positive7'] = zplus
    return par


def reuse_denominator(study, par):
    old = study.read('k_neighborhood_radius_obstruction_1_27')['complete_radius']
    uniform, finite, affine, portfolio = (study.get(n) for n in
        ('uniform_k_neighborhood_cost', 'finite_source_face_transport', 'shared_budget_affine_tail', 'uniform_mean_cost_portfolio'))
    native = uniform.parameters(DELTA, RHO)
    require(old['parameters'] == uniform.encode(native), 'Exact existing1/27 denominator rectangle')
    # Keep the certified native head and selected-source error. Only the
    # independent complete positive-seven complement changes in these five rows.
    denpar = {**native, 'positive7': par['positive7']}
    outputs = []
    for row in old['denominator_costs']:
        record = finite.prepare({int(k): F(v) for k, v in row['coefficients'].items()})
        vertices = [{'q': tuple(map(F, v['q'])), 'residual': F(v['residual']),
                     'head_maxima': tuple(map(F, v['head_maxima']))} for v in row['exhaustive_vertices']]
        cut = tuple(row['selected_support']['cuts'])
        selected = uniform.apply_support(record, denpar, uniform.fixed_tail(affine, record, denpar, cut), vertices)
        saving = sum(record['coefficients'].values())*(native['positive7']-par['positive7'])
        for before, after in zip(row['selected_support']['vertices'], selected['vertices']):
            require(tuple(map(F, before['q'])) == after['q'] and
                    tuple(F(x)-saving for x in before['coordinate_values']) == after['coordinate_values'],
                    'Exact constant transport on every original common q and residual coordinate')
        outputs.append({'name': row['name'], 'weight': F(row['weight']), 'coefficients': record['coefficients'],
                        'selected_support': selected, 'positive7_saving': saving,
                        'reused_original_head_evaluations': sum(v['original_head_evaluations'] for v in row['exhaustive_vertices']),
                        'reused_head_digests': [v['finite_objectives_sha256'] for v in row['exhaustive_vertices']]})
    shared = portfolio.shared_maximum(outputs)
    require(len(outputs) == 5 and sum(r['reused_original_head_evaluations'] for r in outputs) == 1875000,
            'Exactly five previously certified complete denominator objectives')
    return {'parameters': denpar, 'costs': outputs, 'shared_cost': shared,
            'old_shared_cost_upper': F(old['denominator_shared_cost']['upper']),
            'complete_cost_saving': F(old['denominator_shared_cost']['upper'])-shared['upper']}


def scan_missing(study, par):
    uniform, cost, finite, capacity, affine, mean, factorial, tails, outer, portfolio = (study.get(n) for n in
        ('uniform_k_neighborhood_cost', 'complete_off_face_cost', 'finite_source_face_transport',
         'broad_weighted_identity_source', 'shared_budget_affine_tail', 'joint_deep_mean_transport',
         'complete_off_face_factorial_tail', 'complete_off_face_omitted_tails',
         'uniform_factorial_neighborhood', 'uniform_mean_cost_portfolio'))
    face = cost.face_case(finite, study.source)
    point, increments = uniform.enlarged_point(face['point'], par)
    native_point, _ = uniform.enlarged_point(face['point'], uniform.parameters(DELTA, RHO))
    require(all(a <= b for a, b in zip(point['caps'], native_point['caps']))
            and all(a <= b for a, b in zip(point['budgets'], native_point['budgets']))
            and point['score'] == native_point['score'], 'Improved outer box is contained in the original outer box')
    J = outer.UniformFactorialHead(factorial, tails, finite, face, par)
    Jrows = {layout: J.components(layout) for layout in mean.layouts()}
    mean_rows = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, par)
    qvertices = finite.defect_vertices(par['gap'], par['gap'], RHO)
    eps = (par['kbar']*RHO, RHO+DELTA/240, RHO, RHO)
    cut = tuple(uniform.crossing(p, s, H, e) for p, s, H, e in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], eps))
    cuts = sorted(set((cut, (10,)*4, (12,)*4)))

    def scan(index, coefficients, theta=F(0)):
        record = finite.prepare(coefficients)
        a1 = record['coefficients'].get(1, F(0))
        rows = tuple((layout, a1*reference-theta*Jrows[layout]['head_total'], tuple(a1*p for p in prices))
                     for layout, reference, prices in mean_rows)
        vertices = [uniform.exhaustive_vertex(cost, finite, capacity, record, face, point, par, rows, q) for q in qvertices]
        supports = [study.quadratic.constant_support(uniform, record, par,
                    uniform.fixed_tail(affine, record, par, c), vertices, theta*J.pairs['tail_distinct_pairs']) for c in cuts]
        result = {'index': index, 'coefficients': record['coefficients'], 'factorial_tail_coefficient': theta,
                  'weight': F(1) if index == 'H2' else study.weights[index], 'exhaustive_vertices': vertices,
                  'selected_support': min(supports, key=lambda s: s['upper'])}
        print('Complete original objective '+str(index)+': '+str(float(result['selected_support']['upper'])), flush=True)
        return result

    H2 = scan('H2', {2: F(1)})
    mean_jobs = [scan(r['index'], {int(k): F(v) for k, v in r['coefficients'].items()}) for r in study.mean_prior['cost_results']]
    original = study.get('complete_off_face_quadratic_cost')
    targets = original.prepare_rows(study.source, study.get('whole_quadratic_same_head'), study.old, study.quadratic.INDICES)
    quad_jobs = [scan(r['index'], r['expansion']['hinge_coefficients'], r['expansion']['factorial_tail_coefficient'])
                 for r in targets if r['index'] != 47]
    jobs = [H2]+mean_jobs+quad_jobs
    count = sum(v['original_head_evaluations'] for r in jobs for v in r['exhaustive_vertices'])
    checks = sum(v['rational_comparisons'] for r in jobs for v in r['exhaustive_vertices'])
    require(len(mean_jobs) == 11 and len(quad_jobs) == 9 and count == 7875000 and checks == 252,
            'Exactly21 missing objectives and every original head with independent rational LP checks')
    return {'uniform_caps': point['caps'], 'cap_increments': increments, 'uniform_budgets': point['budgets'],
            'H2': H2, 'mean_costs': mean_jobs, 'mean_shared': portfolio.shared_maximum(mean_jobs),
            'quadratic_costs': quad_jobs, 'quadratic_shared': portfolio.shared_maximum(quad_jobs),
            'factorial_pairs': J.pairs, 'factorial_head_digest': sha256(json.dumps(uniform.encode(list(Jrows.items())), separators=(',', ':')).encode()).hexdigest(),
            'original_head_evaluations': count, 'independent_rational_comparisons': checks}


def signed_result(study, signed, head, denominator, H1, square, name):
    native = study.uniform.parameters(DELTA, RHO)
    heavy = signed.heavy_bounds(study, DELTA, RHO)
    raw46 = study.square.retained_raw81(study.source, study.quadratic, study.old, study.read('k_face_complete_ratio'), DELTA)
    raw47 = study.quadratic.retained_raw81_controller(study.source, study.old, DELTA)
    H2 = head['H2']['selected_support']['upper']
    simple = [{'index': r['index'], 'weight': F(r['weight']),
               'endpoint_upper': F(r['at_one'])*A+F(r['first_difference'])*H1['upper']+F(r['second_curvature'])*H2}
              for r in study.simple_prior['radii'][0]['cost_results']]
    require(square['mass_upper'] == A+5*DELTA/9+RHO, 'Both square interfaces expose the same original unit-mass upper')
    cS, cQ, C0 = map(F, (study.old['signed_mass_coefficient'], study.old['complete_square_weight'], study.old['offset']))
    groups = {'mean11': head['mean_shared']['upper'], 'single28_at_mass_floor': sum(r['weight']*r['endpoint_upper'] for r in simple),
              'quadratic9': head['quadratic_shared']['upper'], 'raw81_second': raw47['weight']*raw47['uniform_upper'],
              'heavy2_at_both_mass_floors': sum(r['weight']*(r['face_upper']+r['uniform_G_error']) for r in heavy['costs']),
              'raw81_first': raw46['outside_weight']*raw46['uniform_upper'],
              'square_at_mass_floor': cQ*(A+square['full_square_upper']-square['mass_upper'])}
    endpoint = cS*A+sum(groups.values())
    cE = 1-F(1, 614922)
    d = cE*A-denominator['shared_cost']['upper']-H1['upper']/55902
    require(d > 0 and endpoint > 0, 'Positive actual-denominator lower bound and signed endpoint')
    target = C0+endpoint/d
    coefficient = (target-C0)*cE-cS-heavy['weighted_barrier']-study.weights[40]-cQ
    require(coefficient > 0 and heavy['weighted_barrier'] > 0 and (target-C0)*d-endpoint == 0,
            'Both favorable mass coefficients and the exact full signed target inequality')
    indices = [r['index'] for r in head['mean_costs']+head['quadratic_costs']+simple]+[0, 16, 46, 47]
    require(sorted(indices) == list(range(52)), 'All original52 independent tests, each once')
    require(target < 509, 'The complete expanded rectangle reaches the stated target')
    return {'name': name, 'H1': H1, 'square': square, 'simple_rows': simple, 'heavy': heavy,
            'retained_raw81_first': raw46, 'retained_raw81_second': raw47,
            'cost_groups': groups, 'signed_mass_floor_term': cS*A, 'signed_endpoint': endpoint,
            'denominator_lower': d, 'offset': C0, 'comparison_upper': target,
            'remaining_S_coefficient': coefficient, 'raw_s_coefficient': heavy['weighted_barrier'],
            'target': F(509), 'target_margin': 509-target, 'all_original_indices': sorted(indices)}


def calculate(base):
    io = module('wide_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    signed = module('wide_signed', base/'frontier/shared_loss_signed_k_comparison.py')
    old = module('wide_radius', base/'frontier/k_neighborhood_radius_study.py')
    study = old.Study(base)
    pins = {**study.pins, **signed.PINS, **PINS}
    shallow = study.get('uniform_shallow_indicator_transport')
    shallow_prior = study.read('uniform_shallow_indicator_transport')
    for path, pin in shallow_prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent152 source pin '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned complete source closure '+path)
    native = study.uniform.parameters(DELTA, RHO)
    par = parameters(study, DELTA, RHO)
    denominator = reuse_denominator(study, par)
    head = scan_missing(study, par)
    H1old = study.denominator.uniform_H1(native)
    Qold = study.square.uniform_square(native, study.denominator, study.factorial, study.tails)
    H1new, Qnew = shallow.uniform_H1(native), shallow.uniform_square(native)
    matching = [r for r in shallow_prior['radius_results'] if r['parameters'] == study.uniform.encode(native)]
    require(len(matching) == 1 and study.uniform.encode(H1new) == matching[0]['H1']
            and study.uniform.encode(Qnew) == matching[0]['square'], 'Exact finalized152 API at the same source rectangle')
    results = [signed_result(study, signed, head, denominator, H1old, Qold, 'retained139and143'),
               signed_result(study, signed, head, denominator, H1new, Qnew, 'independent152shallow')]
    return study.uniform.encode({'schema': 'erdos7-wide-k-signed-tail-comparison-v1', 'source_sha256': pins,
                                  'delta': DELTA, 'rho_radius': RHO, 'slot_bound': F(1, 520),
                                  'parameters': par, 'native_parameters': native,
                                  'positive7_improvement': native['positive7']-par['positive7'],
                                  'denominator': denominator, 'missing_head_completion': head, 'comparisons': results,
                                  'scope': 'Complete ordinary source-uniform signed comparison on qK>=26/27,0<=rho<=1/100000,r<=1/520. All52 original tests, five denominator objectives, both orientations, the whole valid first-beta face, every infinite count/exponent tail and one actual residual are retained. Exactly21 missing objectives are recomputed; five exact denominator head certificates are reused by a proved constant transport. No new global K, Lean theorem or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('wide_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete wide-radius certificate')
    for row in result['comparisons']:
        print('PASS: '+row['name']+' complete K <= '+row['comparison_upper'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
