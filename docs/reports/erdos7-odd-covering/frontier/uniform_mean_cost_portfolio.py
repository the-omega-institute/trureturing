#!/usr/bin/env python3
"""One source-uniform polygon and defect coordinate for eleven original AP costs."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/uniform_mean_cost_portfolio.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/uniform_k_neighborhood_cost.py': '2868fc48d2b02e889402f7c2cbf89cd4236d28a3d575b53cf3cbdf48cd2dd781',
    'certificates/source_norms/uniform_k_neighborhood_cost.json': '69cf1b2ccfc8ac27bec748a0f3738092a6283646c69ce872c6b02543ee4162c4',
    'certificates/source_norms/whole_cost_mean_stop_loss.json': 'd535a2f69617536a06655c61a1166813bfd2ce3e17416fc329dcead0ba3201da',
}
INDICES = (1, 2, 7, 10, 17, 18, 23, 26, 32, 33, 36)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def shared_maximum(results):
    """No cost receives its own independent maximization over the shared coordinate."""
    first = results[0]['selected_support']['vertices']
    require(first, 'Nonempty common polygon')
    values = []
    for vertex_index, first_vertex in enumerate(first):
        require(all(row['selected_support']['vertices'][vertex_index]['q'] == first_vertex['q'] for row in results),
                'Exactly one common q for all costs')
        coordinates = tuple(sum(row['weight']*row['selected_support']['vertices'][vertex_index]['coordinate_values'][j]
                                for row in results) for j in range(7))
        values.append({'q': first_vertex['q'], 'coordinate_values': coordinates, 'upper': max(coordinates)})
    upper = max(v['upper'] for v in values)
    separate = sum(row['weight']*row['selected_support']['upper'] for row in results)
    require(upper <= separate, 'A common residual and q never worsens the independent maxima')
    return {'vertices': values, 'upper': upper, 'separate_maxima_comparison': separate,
            'sharing_gain': separate-upper,
            'maximizers': [{'vertex': i, 'coordinate': j} for i, v in enumerate(values)
                           for j, value in enumerate(v['coordinate_values']) if value == upper]}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('portfolio_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    uniform = module('portfolio_uniform', base/'frontier/uniform_k_neighborhood_cost.py')
    cost = module('portfolio_cost', base/'frontier/complete_off_face_cost.py')
    for path, pin in {**uniform.PINS, **cost.PINS}.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned uniform source '+path)
    finite = module('portfolio_finite', base/'frontier/finite_source_face_transport.py')
    affine = module('portfolio_affine', base/'frontier/shared_budget_affine_tail.py')
    mean = module('portfolio_mean', base/'frontier/joint_deep_mean_transport.py')
    source = module('portfolio_source', base/'verify_joint_frontier.py')
    capacity = module('portfolio_capacity', base/'frontier/broad_weighted_identity_source.py')
    old = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/whole_cost_mean_stop_loss.json'))
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/uniform_k_neighborhood_cost.json'))
    require(tuple(row['index'] for row in old['cost_results'] if row['status'] == 'enumerate') == INDICES,
            'Exactly the eleven adopted original mean-cost improvements')
    par = uniform.parameters(F(1, 10000), F(1, 100000))
    require(uniform.encode(par) == prior['parameters'], 'Exactly the established source-uniform rectangle')
    face = cost.face_case(finite, source)
    upper_point, du = uniform.enlarged_point(face['point'], par)
    qvertices = finite.defect_vertices(par['gap'], par['gap'], par['rho'])
    base_rows = uniform.mean_rows(mean, finite.prepare({1: F(1)}), face, par)
    eps = (par['kbar']*par['rho'], par['rho']+par['delta']/240, par['rho'], par['rho'])
    cuts = tuple(uniform.crossing(p, b, H, e) for p, b, H, e in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], eps))
    cut_candidates = sorted(set((cuts, (10,)*4, (12,)*4)))
    results = []
    for index in INDICES:
        original = old['cost_results'][index]
        require(original['index'] == index and F(original['constant_mass_term']) == 0,
                'Original test identity and zero f(1), with no face-mass substitution')
        face_upper = F(original['uniform_cost_upper'])
        require(face_upper == F(original['accepted_cost_upper']) == F(old['improved_cost_bounds'][index]),
                'Each target exactly matches the final adopted109 face consumer')
        record = finite.prepare({int(t): F(a) for t, a in original['objective']['coefficients'].items()})
        a1 = record['coefficients'].get(1, F(0))
        rows = tuple((layout, a1*reference, tuple(a1*p for p in prices)) for layout, reference, prices in base_rows)
        vertices = [uniform.exhaustive_vertex(cost, finite, capacity, record, face, upper_point, par, rows, q)
                    for q in qvertices]
        supports = [uniform.apply_support(record, par, uniform.fixed_tail(affine, record, par, cut), vertices)
                    for cut in cut_candidates]
        selected = min(supports, key=lambda support: support['upper'])
        require(selected['upper'] > face_upper, 'Positive rectangle exceeds its same original exact face bound')
        if index == 1:
            require(uniform.encode(selected) == prior['selected_support']
                    and uniform.encode(vertices) == prior['exhaustive_vertices'], 'Exact134 first-consumer regression')
        results.append({'index': index, 'name': original['name'], 'tuple': original['tuple'],
                        'weight': F(old['cost_weights'][index]), 'coefficients': record['coefficients'],
                        'at_one': F(0), 'face_upper': face_upper, 'exhaustive_vertices': vertices,
                        'cut_candidates': supports, 'selected_support': selected,
                        'individual_uniform_excess': selected['upper']-face_upper})
        print('Complete uniform cost '+str(index)+': '+str(float(selected['upper'])), flush=True)
    shared = shared_maximum(results)
    face_sum = sum(row['weight']*row['face_upper'] for row in results)
    excess = shared['upper']-face_sum
    require(excess > 0 and shared['upper'] < F(94, 10), 'The eleven-cost common-source portfolio is below9.4')
    require(sum(v['original_head_evaluations'] for r in results for v in r['exhaustive_vertices']) == 4125000,
            'All eleven original objectives and all three vertices exhaustively retained')
    require(sum(v['rational_comparisons'] for r in results for v in r['exhaustive_vertices']) == 132,
            'Independent rational and compiled LP comparisons in every objective')
    return uniform.encode({'schema': 'erdos7-uniform-mean-cost-portfolio-v1',
                           'source_sha256': {**PINS, **uniform.PINS, **cost.PINS},
                           'parameters': par, 'indices': INDICES, 'coordinates': uniform.COORDINATES,
                           'fixed_cut_candidates': cut_candidates, 'cost_results': results,
                           'shared_portfolio': shared, 'weighted_face_upper': face_sum,
                           'weighted_uniform_excess': excess,
                           'original_head_evaluations': 4125000, 'rational_comparisons': 132,
                           'unextended_numerator_indices': tuple(i for i in range(52) if i not in INDICES),
                           'scope': 'Uniform ordinary continuum consumer for exactly the eleven previously adopted109 mean-cost objectives, on134 complete actual K neighborhood. Each cost keeps its own original head, while all costs use one common q and one seven-coordinate residual simplex. Every original exponent tail is retained, and all constants f(1) are zero. Does not extend the other30 linear costs,11 quadratic costs, the signed mass and square complement, or the complete111 AP11/AP13 denominator. No full numerator, global K, Lean or unrestricted Erdos7 claim.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('portfolio_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact common-source eleven-cost certificate')
    print('PASS: eleven-cost common-source upper '+result['shared_portfolio']['upper'])
    print('Weighted uniform excess '+result['weighted_uniform_excess'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
