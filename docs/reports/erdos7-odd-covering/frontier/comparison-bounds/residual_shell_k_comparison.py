#!/usr/bin/env python3
"""Complete original costs on a wider residual neighborhood, with two honest shells."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/residual_shell_k_comparison.json'
HEAD_CERTIFICATE = 'certificates/source_norms/cover-geometry/residual_shell_original_heads.json'
PINS = {
    HEAD_CERTIFICATE: '39ba4181d8017340ac46dbdb4e8ddbb146a1b8aa568e27eda69a924484e2159d',
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/endpoint-bounds/k_neighborhood_radius_study.py': 'f5b6d2df57ee047a3d47660812e8fc3ff0a81239db15881634b4ad0b01633b0f',
    'frontier/comparison-bounds/exposed_concentration_prices.py': '9c2e6d7ea0777df07559c90a506dcd19d40e2af6febadaee7833a0d66b20488a',
    'certificates/source_norms/comparison-bounds/exposed_concentration_prices.json': '4cbde5374198bbf645157ef6bb7765e3b8fed57569cd2c99b85c25741f38fd25',
    'frontier/source-budgets/seven_pair_source_prices.py': '020dc470117d84f1a0646ad034ffc6bd2a10b1e18d17b20704f1bb99317c230f',
    'certificates/source_norms/source-budgets/seven_pair_source_prices.json': '052e3376ed1b3b4fb46bbb032e8bc5156c7f468a807e496e05fb312f452110f1',
    'frontier/comparison-bounds/wide_k_signed_tail_comparison.py': '248c4af165fc4e636c4f4a3c61947384afd9128cae6c652b07819e20a55da484',
    'certificates/source_norms/comparison-bounds/wide_k_signed_tail_comparison.json': '4fa3ff52514576814c380e21caaeb2cc9341180815cab34e5b64c8c6e896bade',
    'frontier/retained-transport/uniform_shallow_indicator_transport.py': 'c30be3b622143fbd629eed504642faede14664abbfc393c0d1a93246e087a765',
    'certificates/source_norms/retained-transport/uniform_shallow_indicator_transport.json': '07c1562ec4ef340c70dfa30c7b4e427d16d19e8e28190c09abb450f44c2ab0ee',
}
DELTA = F(1, 27)
SHELLS = ((F(0), F(1, 20000)), (F(1, 20000), F(1, 1000)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def guards(prices, par):
    d, r = par['delta'], par['rbar']
    require(0 <= d <= F(1, 27) and 0 <= par['rho'] <= F(1, 1000)
            and r == min(F(1, 520), 5*par['rho']), 'Explicit widened source domain')
    D = prices.norm_bounds(d)['availability_Linfinity']
    h1, eta = F(1, 3)-d/18, F(1, 9)-d/18
    gaps = (F(1, 10)-r, h1/5-r, eta/5-r,
            h1*(F(1, 10)-D)-2*r, (F(1, 6)-d/9)/5-r)
    minimum = min(gaps)
    require(minimum >= F(2513, 126360) > 0 and D <= F(1, 18),
            'All five actual91 gaps, including the closed r endpoint')
    require(par['gap'] > 0 and par['gap'] <= minimum, '134 wrong-slot simplex has a valid common gap')
    require(F(3, 5)-18*F(13, 1215) == F(11, 27) > 0,
            'All retained-deep marker coefficients are nonnegative')
    require(F(3, 4)+d/4 < F(4, 5) and F(1, 4)-3*d/4 > F(1, 20),
            'Actual first-label forcing and source-budget guards')
    require(6-49*d-70*d*d > 0 and 42+68*d-35*d*d > 0,
            'Whole shallow-indicator price comparisons')
    return {'availability_bound': D, 'five_gap_bounds': gaps, 'minimum_gap': minimum,
            'old_gap_floor': F(241, 22500), 'r_upper': r,
            'marker_coefficient_floor': F(11, 27)}


def heavy_bounds(study, prices, par, guard):
    """151 signed branch formula, with one156 norm price and the actual new gap."""
    d, rho, r = par['delta'], par['rho'], par['rbar']
    sig, hplus = study.heavy.SIGMA, F(1, 2)+d/18
    cap = d/90+par['v0']/6+par['v1']/3
    budget = sum(par['budget_increments'])+d/45+3*r
    nonH = 14*d/225+cap+budget+16*d*hplus/135
    H = 2*d/225+18*sig*r
    outputs = []
    for index, face in zip((0, 16), study.heavy_prior['radii'][0]['results']):
        spec, C = study.engine.specs[index], F(study.engine.thresholds[index]['constant'])
        zero = study.quadratic.raw35_lipschitz(study.source, spec['zero'])
        full = study.quadratic.raw_source_lipschitz(study.source, spec['tag'])
        names = ('mass_L1', 'pure_L1', 'availability_Linfinity')
        require(spec['zero'] == ('seven_block', (spec['tag'], 0))
                and all(full['finite_seven_blocks'][0][k] == zero[k] <= full[k] for k in names),
                'The exact common raw-zero block cancels once')
        remaining = {k: full[k]-zero[k] for k in names}
        branches = []
        for item in spec['layouts']:
            baseline = item['baseline']
            values = tuple(study.source.zero5_cost(spec['tag'], b) for b in baseline)
            derivative = tuple(study.source.zero5_cost(spec['tag'], b+1)-v for b, v in zip(baseline, values))
            vmax, kmax = max(derivative), max(C-v for v in values)
            require(min(derivative) >= 0 and all(0 <= C-v <= kmax for v in values),
                    'Every original branch has nonnegative derivatives and deficits')
            for c5 in study.source.BASES:
                cmax = max(x*y for x, y in zip(derivative, c5))
                Ln = remaining[names[0]]+max(map(abs, item['psi']))+2*kmax/5
                Le = (remaining[names[1]]+max(map(abs, item['correction']))
                      +zero['positive_five_pure_price']+2*cmax/25+3*kmax/20)
                Ld = remaining[names[2]]+zero[names[2]]+kmax/90+2*sig*(vmax+kmax)
                price_vector = prices.norm_prices(Ln, Le, Ld)
                norm = prices.price_record(price_vector, d)
                require(norm['upper'] == prices.joint_norm_upper(Ln, Le, Ld, d),
                        'One exposed support pays the three original source norms')
                intercept = norm['upper']+2*d*(kmax/4+cmax/10)/5+vmax*max(nonH, H)
                slope = max(vmax, hplus*vmax/(5*guard['minimum_gap']))
                branches.append({'baseline': baseline, 'positive_five_baseline': c5,
                                 'norm_coefficients': (Ln, Le, Ld), 'single_source_price': norm,
                                 'nonresidual_error': intercept, 'residual_coefficient': slope,
                                 'residual_error': slope*rho, 'G_error': intercept+slope*rho})
        require(len(branches) == 100, 'Every original branch of this heavy test')
        outputs.append({'index': index, 'weight': study.weights[index], 'barrier': C,
                        'face_upper': F(face['face_upper']), 'remaining_raw_prices': remaining,
                        'branches': branches, 'uniform_G_error': max(b['G_error'] for b in branches)})
    return {'costs': outputs, 'nonH_marker_intercept': nonH, 'H_marker_intercept': H,
            'weighted_G_error': sum(r['weight']*r['uniform_G_error'] for r in outputs),
            'weighted_barrier': sum(r['weight']*r['barrier'] for r in outputs)}


def shallow_H1(study, par):
    """Rebuild SI15--SI20 directly; do not call either narrower public wrapper."""
    shallow = study.get('uniform_shallow_indicator_transport')
    rows = [shallow.one_label_bound(label, L, par) for L in (2, 3, 4) for label in shallow.labels()]
    require(len(rows) == 141, 'All47 independent shallow labels at all three first-beta cells')
    bounded = []
    for m in (3, 9, 5, 15, 45):
        candidates = [r for r in rows if r['label'][0] == m]
        top = max(r['upper'] for r in candidates)
        bounded.append({'modulus': m, 'transported_upper': top, 'raw_haar_cap': F(1, m),
                        'upper': min(top, F(1, m)),
                        'maximizers': [{'first_beta': r['first_beta'], 'label': r['label']}
                                       for r in candidates if r['upper'] == top]})
    tails = []
    d, rho = par['delta'], par['rho']
    errors = (par['kbar']*rho, rho+d/240, rho, rho)
    for name, p, b, c, H, error in zip(('pure3', 'pure5', 'root5', 'cell5'),
                                      (3, 5, 5, 5), (3, 2, 2, 2), par['c'], par['H'], errors):
        row = study.denominator.complete_error_tail(p, b, H, error)
        row.update({'name': name, 'prime': p, 'start': b, 'reference_coefficient': c,
                    'envelope': H, 'error': error, 'upper': c*row['geometric_sum']+row['error_sum']})
        tails.append(row)
    positive7 = F(11, 72)+11*d/36
    upper = sum(r['upper'] for r in bounded)+sum(r['upper'] for r in tails)+F(1, 72)+positive7
    return {'upper': upper, 'face_upper': F(443, 900), 'excess': upper-F(443, 900),
            'bounded_labels': bounded, 'layout_rows': rows, 'complete_exponent_tails': tails,
            'deep_mixed_upper': F(1, 72), 'complete_positive7_upper': positive7}


def scan_heads(study, par, pair_bound, scanned, rescan=False):
    uniform, cost, finite, capacity, affine, mean, outer, portfolio = (study.get(n) for n in
        ('uniform_k_neighborhood_cost', 'complete_off_face_cost', 'finite_source_face_transport',
         'broad_weighted_identity_source', 'shared_budget_affine_tail', 'joint_deep_mean_transport',
         'uniform_factorial_neighborhood', 'uniform_mean_cost_portfolio'))
    face = cost.face_case(finite, study.source)
    point, increments = uniform.enlarged_point(face['point'], par)
    J = outer.UniformFactorialHead(study.factorial, study.tails, finite, face, par)
    Jrows = {layout: J.components(layout) for layout in mean.layouts()}
    pairtail = J.pairs['old_old_distinct']+pair_bound['pair_upper']
    require(pairtail <= J.pairs['tail_distinct_pairs'], '158 improves only the two complete seven-containing pair terms')
    base_rows = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, par)
    qvertices = finite.defect_vertices(par['gap'], par['gap'], par['rho'])
    errors = (par['kbar']*par['rho'], par['rho']+par['delta']/240, par['rho'], par['rho'])
    cut = tuple(uniform.crossing(p, b, H, e) for p, b, H, e in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], errors))
    cuts = sorted(set((cut, (10,)*4, (12,)*4)))
    require(scanned['parameters'] == uniform.encode(par), 'Exactly the already evaluated source box')
    cached = {r['index']: r for r in scanned['objective_rows']}
    require(len(cached) == len(scanned['objective_rows']) == 26, 'Independent original objective identities')

    def scan(index, coefficients, weight, theta=F(0)):
        record = finite.prepare(coefficients)
        a1 = record['coefficients'].get(1, F(0))
        rows = tuple((layout, a1*ref-theta*Jrows[layout]['head_total'], tuple(a1*p for p in prices))
                     for layout, ref, prices in base_rows)
        saved = cached[index]
        require(saved['coefficients'] == uniform.encode(record['coefficients'])
                and F(saved['factorial_tail_coefficient']) == theta and F(saved['weight']) == weight,
                'Unchanged coefficients of the recorded original objective')
        vertices = [{**v, 'q': tuple(map(F, v['q'])), 'residual': F(v['residual']),
                     'head_maxima': tuple(map(F, v['head_maxima']))} for v in saved['exhaustive_vertices']]
        require(tuple(v['q'] for v in vertices) == tuple(qvertices), 'All original common q vertices')
        for vertex in vertices:
            require(vertex['residual'] == par['rho']-par['gap']*sum(vertex['q'])
                    and vertex['original_head_evaluations'] == 125000 and vertex['rational_comparisons'] == 4
                    and len(vertex['head_maxima']) == len(vertex['witnesses']) == 7,
                    'Original scan inventory and its one common residual')
            for value, witness in zip(vertex['head_maxima'], vertex['witnesses']):
                require(value == F(witness['finite_upper'])+F(witness['reference_and_mean_price_shift']),
                        'Each stored maximum retains its exact original-head witness')
        if rescan:
            fresh = [uniform.exhaustive_vertex(cost, finite, capacity, record, face, point, par, rows, q)
                     for q in qvertices]
            require(uniform.encode(fresh) == uniform.encode(vertices), 'Recomputed every original head and digest')
        supports = [study.quadratic.constant_support(uniform, record, par,
                    uniform.fixed_tail(affine, record, par, c), vertices, theta*pairtail) for c in cuts]
        selected = min(supports, key=lambda r: r['upper'])
        require(uniform.encode(selected) == saved['selected_support'], 'Exact reconstruction of every complete tail support')
        print('rho<='+str(par['rho'])+' objective '+str(index)+': '+str(float(selected['upper'])), flush=True)
        return {'index': index, 'name': str(index), 'weight': weight, 'coefficients': record['coefficients'],
                'factorial_tail_coefficient': theta, 'exhaustive_vertices': vertices, 'selected_support': selected}

    denominator = [scan(r['name'], {int(k): F(v) for k, v in r['coefficients'].items()}, F(r['weight']))
                   for r in study.den_prior['cost_results']]
    H2 = scan('H2', {2: F(1)}, F(1))
    means = [scan(r['index'], {int(k): F(v) for k, v in r['coefficients'].items()}, study.weights[r['index']])
             for r in study.mean_prior['cost_results']]
    original = study.get('complete_off_face_quadratic_cost')
    targets = original.prepare_rows(study.source, study.get('whole_quadratic_same_head'), study.old, study.quadratic.INDICES)
    quadratics = [scan(r['index'], r['expansion']['hinge_coefficients'], study.weights[r['index']],
                      r['expansion']['factorial_tail_coefficient']) for r in targets if r['index'] != 47]
    jobs = denominator+[H2]+means+quadratics
    count = sum(v['original_head_evaluations'] for r in jobs for v in r['exhaustive_vertices'])
    checks = sum(v['rational_comparisons'] for r in jobs for v in r['exhaustive_vertices'])
    require(len(denominator) == 5 and len(means) == 11 and len(quadratics) == 9
            and count == 9750000 and checks == 312, 'All26 complete objectives, no old-rho head reuse')
    return {'uniform_caps': point['caps'], 'cap_increments': increments, 'uniform_budgets': point['budgets'],
            'denominator_costs': denominator, 'denominator_shared': portfolio.shared_maximum(denominator),
            'H2': H2, 'mean_costs': means, 'mean_shared': portfolio.shared_maximum(means),
            'quadratic_costs': quadratics, 'quadratic_shared': portfolio.shared_maximum(quadratics),
            'original_factorial_pairs': J.pairs, 'seven_pair_source_bound': pair_bound,
            'complete_pair_upper': pairtail, 'original_head_evaluations': count,
            'independent_rational_comparisons': checks}


def comparison(study, par, lower, heavy, H1, square, head):
    A, cE = F(53, 360), 1-F(1, 614922)
    cS, cQ, C0 = map(F, (study.old['signed_mass_coefficient'], study.old['complete_square_weight'], study.old['offset']))
    raw46 = study.square.retained_raw81(study.source, study.quadratic, study.old, study.read('k_face_complete_ratio'), par['delta'])
    raw47 = study.quadratic.retained_raw81_controller(study.source, study.old, par['delta'])
    simple = [{'index': r['index'], 'weight': F(r['weight']),
               'endpoint_upper': F(r['at_one'])*A+F(r['first_difference'])*H1['upper']
                                 +F(r['second_curvature'])*head['H2']['selected_support']['upper']}
              for r in study.simple_prior['radii'][0]['cost_results']]
    require(sum(F(r['weight'])*F(r['at_one']) for r in study.simple_prior['radii'][0]['cost_results'])
            == study.weights[40], 'Row40 supplies the only original single-hinge unit-mass coefficient')
    require(square['mass_upper'] == A+5*par['delta']/9+par['rho'], 'One original unit-mass term in the square')
    groups = {'mean11': head['mean_shared']['upper'],
              'single28_at_mass_floor': sum(r['weight']*r['endpoint_upper'] for r in simple),
              'quadratic9': head['quadratic_shared']['upper'],
              'raw81_first': raw46['outside_weight']*raw46['uniform_upper'],
              'raw81_second': raw47['weight']*raw47['uniform_upper'],
              'heavy2_at_both_mass_floors': sum(r['weight']*(r['face_upper']+r['uniform_G_error']) for r in heavy['costs']),
              'square_at_mass_floor': cQ*(A+square['full_square_upper']-square['mass_upper'])}
    N = cS*A+sum(groups.values())
    d = cE*A-head['denominator_shared']['upper']-H1['upper']/55902
    M = cS+heavy['weighted_barrier']+study.weights[40]+cQ
    require(d > 0 and N > 0 and 0 <= lower <= par['rho'], 'Positive endpoint and honest shell endpoints')
    target = C0+(N+M*lower)/(d+cE*lower)
    DS = (target-C0)*cE-M
    require(DS > 0 and heavy['weighted_barrier'] > 0
            and (target-C0)*d-N+DS*lower == 0, 'One actual residual lower bound in the signed comparison')
    indices = [r['index'] for r in head['mean_costs']+head['quadratic_costs']+simple]+[0, 16, 46, 47]
    require(sorted(indices) == list(range(52)), 'All52 original independent tests, each once')
    require(target <= 509, 'Complete comparison on this entire residual shell')
    ds509, margin = (509-C0)*cE-M, (509-C0)*d-N
    return {'residual_lower': lower, 'residual_upper': par['rho'], 'cost_groups': groups,
            'signed_endpoint': N, 'denominator_at_mass_floor': d, 'mass_coefficient': M,
            'offset': C0, 'comparison_upper': target, 'remaining_S_coefficient': DS,
            'raw_s_coefficient': heavy['weighted_barrier'], 'residual_coefficient_at509': ds509,
            'margin_at509_without_residual': margin, 'margin_at509_on_shell': margin+ds509*lower,
            'whole_rectangle_upper_without_shell': C0+N/d,
            'all_original_indices': sorted(indices), 'simple_rows': simple,
            'retained_raw81_first': raw46, 'retained_raw81_second': raw47}


def calculate(base, rescan=False):
    io = module('residual_shell_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    study = module('residual_shell_study', base/'frontier/endpoint-bounds/k_neighborhood_radius_study.py').Study(base)
    prior = study.read('seven_pair_source_prices')
    pins = {**study.pins, **prior['source_sha256'], **PINS}
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned complete source '+path)
    prices, pairs, wide = (study.get(n) for n in
        ('exposed_concentration_prices', 'seven_pair_source_prices', 'wide_k_signed_tail_comparison'))
    pair = pairs.bounds(prices, pairs.raw_coefficients(study.factorial), DELTA)
    scanned_heads = json.loads(io.read_artifact_bytes(base/HEAD_CERTIFICATE))
    require(all(pins.get(path) == pin for path, pin in scanned_heads['source_sha256'].items()),
            'Recorded original scans use this same pinned source closure')
    outputs = []
    for lower, upper in SHELLS:
        par = wide.parameters(study, DELTA, upper)
        par['positive7'] = pair['Z_upper']
        guard = guards(prices, par)
        heavy = heavy_bounds(study, prices, par, guard)
        H1 = shallow_H1(study, par)
        interface = SimpleNamespace(uniform_H1=lambda p: shallow_H1(study, p))
        square = study.square.uniform_square(par, interface, study.factorial, study.tails)
        saved = [r for r in scanned_heads['shells'] if F(r['rho']) == upper]
        require(len(saved) == 1, 'Exactly one previously complete scan at this residual radius')
        head = scan_heads(study, par, pair, saved[0], rescan)
        result = comparison(study, par, lower, heavy, H1, square, head)
        outputs.append({'parameters': par, 'guards': guard, 'heavy': heavy, 'H1': H1,
                        'square': square, 'complete_heads': head, 'comparison': result})
    require(SHELLS[0][0] == 0 and SHELLS[0][1] == SHELLS[1][0]
            and SHELLS[-1][1] == F(1, 1000), 'Two closed intervals cover every residual in the claimed domain')
    upper = max(r['comparison']['comparison_upper'] for r in outputs)
    return study.uniform.encode({'schema': 'erdos7-residual-shell-k-comparison-v1', 'source_sha256': pins,
                                  'source_radius': DELTA, 'residual_radius': F(1, 1000),
                                  'source_slot_loss_radius': F(1, 520), 'shells': outputs,
                                  'uniform_comparison_upper': upper,
                                  'original_head_evaluations': sum(r['complete_heads']['original_head_evaluations'] for r in outputs),
                                  'scope': 'Ordinary continuous actual-source inequalities and exact rational certificates. Both K orientations, all52 independent original tests and every original infinite tail. Two closed residual shells use the same actual rho as the global mass floor; no unrestricted/globalK or Lean theorem is claimed.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--rescan', action='store_true', help='Independently repeat all19.5 million recorded heads')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base, args.rescan)
    io = module('residual_shell_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete residual-shell certificate')
    print('PASS: rho<=1/1000, sigma<=1/27, r<=1/520, complete comparison<='+result['uniform_comparison_upper'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
