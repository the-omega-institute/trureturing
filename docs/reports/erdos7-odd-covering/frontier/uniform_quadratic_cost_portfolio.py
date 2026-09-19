#!/usr/bin/env python3
"""The ten positive quadratic rows retain their adopted face controllers."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
from time import perf_counter

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/uniform_quadratic_cost_portfolio.json'
INDICES = (41, 42, 43, 44, 45, 47, 48, 49, 50, 51)
JOINT_INDICES = tuple(i for i in INDICES if i != 47)
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/complete_off_face_quadratic_cost.py': '3832e1c9005d74c51d6eaec8da4f4f051c56ee7812e4103b76003f66e6d01288',
    'frontier/uniform_factorial_neighborhood.py': '76d35e7851e771cd9d94273fd2c178b1b93dbc48f04ab1c831020cd02b1546dc',
    'frontier/uniform_k_neighborhood_cost.py': '2868fc48d2b02e889402f7c2cbf89cd4236d28a3d575b53cf3cbdf48cd2dd781',
    'frontier/uniform_mean_cost_portfolio.py': '80a69842341990cf1eabf0e278c0cd79646440c4e449cd684db33a471c86c7e6',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def raw35_lipschitz(source, tag):
    """Prices for ||Delta n||1, ||Delta eta||1 and ||Delta d||infinity."""
    degree, a, b, cutoff = source.zero5_cost_metadata(tag)
    require(degree in (1, 2) and a > 0, 'Original convex linear/quadratic cost with complete polynomial tail')
    values = (1, 2, 3)
    N = max(abs(source.zero5_cost(tag, v)) for v in values)
    E = max(abs(source.zero5_centered_correction(tag, v)) for v in values)
    D = max(source.zero5_convex_pure_deep(tag, 1, v) for v in values)
    tails = tuple(4*z for z in source.geom(5, cutoff))
    constant = (sum(F(4, 5**n)*source.zero5_cost(tag, n) for n in range(2, cutoff))
                +a*tails[degree]+b*tails[0])
    require(constant >= 0 and tails[degree] >= tails[degree-1], 'Complete positive-five coefficients')
    positive = sum(F(4*(n-1), 5**n)*(source.zero5_cost(tag, 3*n)-source.zero5_cost(tag, n))/n
                   for n in range(2, cutoff))
    positive += a*(tails[degree]-tails[degree-1])*(3**degree-1)+constant
    require(min(N, E, D, positive) >= 0, 'Nonnegative complete Lipschitz prices')
    return {'tag': tag, 'mass_L1': N, 'pure_L1': E+positive, 'availability_Linfinity': D,
            'positive_five_pure_price': positive, 'polynomial_cutoff': cutoff}


def raw_source_lipschitz(source, tag, seven=True):
    """Complete raw operator prices; s=sum n is folded into mass_L1.

    For the pinned nonnegative increasing convex original costs of degree
    one or two: |Delta raw| <= mass_L1*||Delta n||1
       +pure_L1*||Delta eta||1+availability_Linfinity*||Delta d||infinity.
    This uses the complete running-increment maximum and polynomial tails;
    it does not assume monotonicity of a signed source formula.
    """
    if not seven:
        return raw35_lipschitz(source, tag)
    degree, a, b, cutoff = source.zero5_cost_metadata(tag)
    require(degree in (1, 2) and a > 0, 'Complete original raw357 linear/quadratic cost')
    tails = tuple(F(36, 5)*z for z in source.geom(7, cutoff))
    expectation = (sum(source.zero7_probability(n)*source.zero5_cost(tag, n) for n in range(1, cutoff))
                   +a*tails[degree]+b*tails[0])
    tail_coefficient = a*(tails[degree]-(cutoff-1)*tails[degree-1])
    require(tail_coefficient >= 0, 'Complete original seven-block tail coefficient')
    finite = [raw35_lipschitz(source, ('seven_block', (tag, e))) for e in range(cutoff-1)]
    monomial = raw35_lipschitz(source, (('h' if degree == 1 else 's'), F(0)))
    names = ('mass_L1', 'pure_L1', 'availability_Linfinity')
    prices = {k: sum(row[k] for row in finite)+tail_coefficient*monomial[k] for k in names}
    source_mass_price = abs(expectation-tail_coefficient)
    return {'tag': tag, **prices, 'mass_L1': prices['mass_L1']+source_mass_price,
            'separate_source_mass_price': source_mass_price,
            'finite_seven_blocks': finite, 'full_monomial_tail': {'coefficient': tail_coefficient, 'prices': monomial}}


def retained_raw81_controller(source, previous, delta):
    """Index47 keeps square357(81/4), including every Jensen count tail."""
    tag = ('s', F(81, 4))
    data = raw_source_lipschitz(source, tag)
    names = ('mass_L1', 'pure_L1', 'availability_Linfinity')
    prices = {k: data[k] for k in names}
    radius_price = prices[names[0]]/2+prices[names[1]]/9+5*prices[names[2]]/4
    require(radius_price == F(25207, 6480), 'Complete original raw81 n2 source-continuity price')
    parameters = list(source.vertices())
    face_values = [source.square357(F(81, 4), source.data(parameters[i]))
                   for i in (398, 410, 422, 616, 628, 640)]
    accepted = F(previous['improved_cost_bounds'][47])
    require(max(face_values) == accepted == F(1344356641, 405168750),
            'Retained convex source controller, not the looser113 quadratic-head candidate')
    return {'index': 47, 'controller': 'original square357(81/4)', 'face_vertices': face_values,
            'face_upper': accepted, 'delta_price': radius_price,
            'uniform_upper': accepted+delta*radius_price, 'source_prices': prices,
            'source_mass_price_included': data['separate_source_mass_price'],
            'finite_seven_blocks': data['finite_seven_blocks'], 'full_monomial_tail': data['full_monomial_tail'],
            'weight': F(previous['cost_weights'][47])}


def constant_support(uniform, record, par, tail, vertices, pair_payment):
    result = uniform.apply_support(record, par, tail, vertices)
    result['constant_factorial_pair_payment'] = pair_payment
    result['constant'] = result.get('constant', F(0))+pair_payment
    for vertex in result['vertices']:
        vertex['coordinate_values'] = tuple(x+pair_payment for x in vertex['coordinate_values'])
        vertex['upper'] = max(vertex['coordinate_values'])
    result['upper'] = max(v['upper'] for v in result['vertices'])
    return result


def radius_result(base, delta, rho, modules, previous, targets):
    uniform, cost, finite, capacity, affine, mean, source, factorial, tails, outer, portfolio = modules
    par = uniform.parameters(delta, rho)
    face = cost.face_case(finite, source)
    upper, increments = uniform.enlarged_point(face['point'], par)
    J = outer.UniformFactorialHead(factorial, tails, finite, face, par)
    Jrows = {layout: J.components(layout) for layout in mean.layouts()}
    raw_mean = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, par)
    qvertices = finite.defect_vertices(par['gap'], par['gap'], rho)
    face_tail = tails.complete_tails(face['dat'], face['pi'], face['defects'], face['parameter'][4])
    if rho:
        eps = (par['kbar']*rho, rho+delta/240, rho, rho)
        cuts = tuple(uniform.crossing(p, b, H, e) for p, b, H, e in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], eps))
        cut_candidates = sorted(set((cuts, (10,)*4, (12,)*4)))
    else:
        require(delta == 0, 'The exact face uses its exact zero-error tails')
        cut_candidates = [None]
    jobs = []
    for row in targets:
        if row['index'] == 47:
            continue
        started = perf_counter()
        expansion = row['expansion']
        require(expansion['at_one'] == 0, 'No face-mass substitution: every positive quadratic row has f(1)=0')
        record = finite.prepare(expansion['hinge_coefficients'])
        theta = expansion['factorial_tail_coefficient']
        a1 = record['coefficients'].get(1, F(0))
        same_head_rows = tuple((layout, a1*reference-theta*Jrows[layout]['head_total'],
                                tuple(a1*p for p in prices)) for layout, reference, prices in raw_mean)
        vertices = [uniform.exhaustive_vertex(cost, finite, capacity, record, face, upper, par, same_head_rows, q)
                    for q in qvertices]
        supports = []
        for cut in cut_candidates:
            if cut is None:
                constant = sum(a*(face_tail['old_remainders'][record['prefix'][t]]+face_tail['positive7'])
                               for t, a in record['coefficients'].items())
                tail = {'constant': constant, 'slopes': (F(0),)*4, 'cuts': None,
                        'supports': 'Exact complete zero-error face tails'}
            else:
                tail = uniform.fixed_tail(affine, record, par, cut)
            supports.append(constant_support(uniform, record, par, tail, vertices,
                                             theta*J.pairs['tail_distinct_pairs']))
        selected = min(supports, key=lambda x: x['upper'])
        require(row['face_joint_upper'] == row['face_accepted_upper'], 'This row adopted113 same-head controller')
        if not rho:
            require(selected['upper'] == row['face_accepted_upper'], 'Exact zero-radius recovery of adopted face cost')
        else:
            require(selected['upper'] >= row['face_accepted_upper'], 'Same adopted bound is the comparison baseline')
        jobs.append({'index': row['index'], 'weight': F(previous['cost_weights'][row['index']]),
                     'expansion': expansion, 'face_upper': row['face_accepted_upper'],
                     'exhaustive_vertices': vertices, 'support_candidates': supports,
                     'selected_support': selected, 'uniform_excess': selected['upper']-row['face_accepted_upper']})
        print('Quadratic '+str(row['index'])+' at radius '+str(delta)+': '+str(float(selected['upper']))
              +' ('+format(perf_counter()-started, '.3f')+' s)', flush=True)
    shared = portfolio.shared_maximum(jobs)
    raw = retained_raw81_controller(source, previous, delta)
    raw_weighted = raw['weight']*raw['uniform_upper']
    for vertex in shared['vertices']:
        vertex['coordinate_values'] = tuple(x+raw_weighted for x in vertex['coordinate_values'])
        vertex['upper'] += raw_weighted
    shared['upper'] += raw_weighted
    shared['separate_maxima_comparison'] += raw_weighted
    face_sum = sum(F(previous['cost_weights'][i])*F(previous['improved_cost_bounds'][i]) for i in INDICES)
    require(shared['upper'] >= face_sum, 'Portfolio retains precisely its ten adopted face baselines')
    if not rho:
        require(shared['upper'] == face_sum, 'Entire weighted portfolio exactly recovers accepted face')
    return {'delta': delta, 'rho_radius': rho, 'parameters': par, 'coordinates': uniform.COORDINATES,
            'uniform_factorial_pairs': J.pairs, 'uniform_factorial_heads_sha256': sha256(json.dumps(encode(list(Jrows.items())), separators=(',', ':')).encode()).hexdigest(),
            'joint_cost_results': jobs, 'retained_raw81_n2': raw, 'shared_portfolio': shared,
            'weighted_adopted_face_upper': face_sum, 'weighted_uniform_excess': shared['upper']-face_sum,
            'original_branch_evaluations': sum(v['original_head_evaluations'] for job in jobs for v in job['exhaustive_vertices']),
            'independent_rational_checks': sum(v['rational_comparisons'] for job in jobs for v in job['exhaustive_vertices'])}


def calculate(base):
    io = module('q140_io', base/'certificate_io.py')
    used = dict(PINS)
    prior = module('q140_prior', base/'frontier/complete_off_face_quadratic_cost.py')
    uniform = module('q140_uniform', base/'frontier/uniform_k_neighborhood_cost.py')
    used.update(prior.PINS); used.update(uniform.PINS)
    for path, pin in used.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    get = lambda filename: module('q140_'+filename, base/'frontier'/(filename+'.py'))
    cost, finite = get('complete_off_face_cost'), get('finite_source_face_transport')
    capacity, affine = get('broad_weighted_identity_source'), get('shared_budget_affine_tail')
    mean = get('joint_deep_mean_transport')
    source = module('q140_source', base/'verify_joint_frontier.py')
    factorial, tails = get('complete_off_face_factorial_tail'), get('complete_off_face_omitted_tails')
    outer, portfolio = get('uniform_factorial_neighborhood'), get('uniform_mean_cost_portfolio')
    expansion = get('whole_quadratic_same_head')
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/whole_quadratic_same_head.json'))
    targets = prior.prepare_rows(source, expansion, previous, INDICES)
    modules = (uniform, cost, finite, capacity, affine, mean, source, factorial, tails, outer, portfolio)
    results = [radius_result(base, d, r, modules, previous, targets)
               for d, r in ((F(0), F(0)), (F(1, 10000), F(1, 100000)))]
    require(tuple(x['original_branch_evaluations'] for x in results) == (1125000, 3375000),
            'All nine original heads at face and the three common polygon vertices')
    return encode({'schema': 'erdos7-uniform-quadratic-cost-portfolio-v1', 'source_sha256': used,
                   'indices': INDICES, 'same_head_indices': JOINT_INDICES, 'radius_results': results,
                   'scope': 'Continuous whole-K-source neighborhood for ten positive quadratic rows, preserving their exact adopted face controllers: nine same-head positive expansions plus original raw81 n2 controller. Independent original tests share one q polygon and shifted residual coordinate. All polynomial and geometric tails retained. All f(1)=0. Does not replace raw81 n1, square complement, remaining linear rows, full signed numerator or survival denominator; no new global K, Lean or unrestricted Erdos7 claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('q140_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Complete adopted quadratic portfolio')
    print('PASS: ten adopted quadratic rows, complete tails, common head and exact face recovery.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
