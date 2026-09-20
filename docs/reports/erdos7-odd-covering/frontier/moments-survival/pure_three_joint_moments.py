#!/usr/bin/env python3
"""Joint all-depth pure-three moments and their complete face consumer."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/pure_three_joint_moments.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/moments-survival/pure_five_joint_factorial_comparison.py': '6940c0405e968e3ca6ee864f32a51832286d39f03fbfb3c17f1ae6c9e0f71593', 'certificates/source_norms/moments-survival/pure_five_joint_factorial_comparison.json': 'bc8786df3001b76ff69bd5c3e3fc475ec2e4222a60abb70b64c501c9bd3e6ae7', 'frontier/cover-geometry/complete_off_face_omitted_tails.py': '33e8c164c64790483ba512c984e8090cf5c44b92bf6ca1cb08a17cb56a93201d', 'profile-notes/065-128/125-the-complete-off-face-omitted-tails-recover-every-face-constant.md': '5faf1c5ff5edf0881951c9337a431805e70edcbb8d81a8dce76cbc42d230f5b9', 'profile-notes/065-128/75-forced27-and-complete-pure3-deletion-on-the-k-faces.md': 'bf21f845032d56fb86f86dfdecd5426e58eceac63a1c4e44d6fe0a16d7070f33', 'frontier/cover-geometry/uniform_square_and_raw81_neighborhood.py': '3d47bd0d7ff5f5c4f8114d02538073de8bc87e455265817e9e9d80ca4bc5a62c'}
ROOT = (0, 0, 1, 1, 1)
FIRST = (F(7, 90), F(7, 90))
SECOND = (F(1, 40), F(1, 18), F(1, 30), F(1, 30), F(1, 30))
DENSITY = (F(7, 10), F(11, 20), F(3, 10), F(3, 10), F(3, 10))
RATIO, CROSS = F(1, 3), F(10, 3)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original input')
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


def envelope(lam):
    return max(F(77, 180)+F(59, 360)*lam, F(2, 5)+F(31, 180)*lam)


def potential(lam, counts, cell):
    return DENSITY[cell]*((2*counts[cell]+1+lam)/(1-RATIO)+2*RATIO/(1-RATIO)**2)


def candidate_lines():
    rows = []
    for root, second, deep in product(range(2), range(5), range(5)):
        count = int(ROOT[deep] == root)+int(deep == second)
        intercept = FIRST[root]+(1+2*int(ROOT[second] == root))*SECOND[second]+DENSITY[deep]*F(count+1, 9)
        slope = FIRST[root]+SECOND[second]+DENSITY[deep]/18
        require(intercept <= envelope(0) and intercept+slope*CROSS <= envelope(CROSS)
                and slope <= F(31, 180), 'This entire affine line is below the two-piece envelope')
        rows.append({'first_root': root, 'second_cell': second, 'deep_cell': deep,
                     'intercept': intercept, 'slope': slope})
    require(len(rows) == 50 and F(77, 180)+F(59, 360)*CROSS == F(2, 5)+F(31, 180)*CROSS,
            'All fifty candidates and the exact switch')
    for pair in ((F(77, 180), F(59, 360)), (F(2, 5), F(31, 180))):
        require(any((r['intercept'], r['slope']) == pair for r in rows),
                'Both envelope lines occur in the relaxed allocation problem')
    return rows


def finite_checks():
    rows = []
    for lam in (F(0), F(2), CROSS, F(10)):
        @lru_cache(None)
        def optimum(remaining, counts):
            if remaining == 0:
                return F(0)
            return max(DENSITY[j]*(2*counts[j]+1+lam)+RATIO*optimum(
                remaining-1, tuple(n+int(k == j) for k, n in enumerate(counts))) for j in range(5))
        for root, second in product(range(2), range(5)):
            counts = tuple(int(ROOT[j] == root)+int(j == second) for j in range(5))
            bound = max(potential(lam, counts, j) for j in range(5))
            for chosen in range(5):
                updated = tuple(n+int(j == chosen) for j, n in enumerate(counts))
                require(DENSITY[chosen]*(2*counts[chosen]+1+lam)
                        +RATIO*max(potential(lam, updated, j) for j in range(5)) <= bound,
                        'Independent first Bellman step for every shallow configuration')
            value = optimum(7, counts)
            complete = ((1+lam)*FIRST[root]
                        +(1+lam+2*int(ROOT[second] == root))*SECOND[second]+bound/27)
            require(value <= bound and complete <= envelope(lam), 'Seven arbitrary deep allocations and their full-tail bound')
            rows.append({'lambda': lam, 'first_root': root, 'second_cell': second,
                         'finite_discounted_maximum': value, 'infinite_discounted_upper': bound,
                         'complete_upper': complete})
    return rows


def calculate(base):
    require(PINS, 'Pin the complete inputs before consumption')
    io = module('three_joint_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    prior = read('certificates/source_norms/moments-survival/pure_five_joint_factorial_comparison.json')
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent inherited input '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    # OT3 on the saturated face, before its maximum over cells.
    attenuation = (F(1), F(4, 5), F(4, 5), F(4, 5), F(4, 5))
    source = (F(3, 4), F(3, 4), F(1, 2), F(1, 2), F(1, 2))
    require(DENSITY == tuple(a*d-F(1+r, 20) for a, d, r in zip(attenuation, source, ROOT)),
            'Cellwise OT3 caps, discarding only nonnegative beta source deletion')
    old_block = 3*F(7, 90)+5*F(1, 18)+F(7, 10)*F(4, 9)
    new_block, saving = envelope(F(2)), old_block-envelope(F(2))
    require((old_block, new_block, saving) == (F(37, 45), F(34, 45), F(1, 15)),
            'Exactly the old unit/pure-three and pure-three/pure-three block')
    D, L, oldQ = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, oldQ) == (F(53, 360), F(1151, 1800), F(2233, 450))
            and prior['rho'] == prior['r'] == '0', 'Both complete saturated faces')
    Q = oldQ-saving
    require(Q == F(2203, 450), 'The disjoint pure-five gain remains in the full square')
    load = lambda name: module('three_joint_'+name, io.named_artifact(base/'frontier', name+'.py'))
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(p) == h for p, h in engine.pins.items()), 'All original independent costs remain pinned')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    require(len(tags) == len(old_costs) == len(weights) == 52, 'Every one of the original52 costs')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda v, tag=t: engine.source.zero5_cost(tag, v) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, old_costs, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    require(square_weight > 0, 'Positive complete-square complement weight')
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*oldQ
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    propagation = sum(w*(a-b) for w, a, b in zip(weights, old_costs, costs))
    require(oldN == F(prior['numerator_upper']) and oldN-N == square_weight*saving+propagation
            and propagation >= 0 and N > 0, 'One full numerator with disjoint savings')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) == F(50511415637, 632754738000) > 0,
            'The full denominator and its complete count tail remain')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']), 'A strict complete-face improvement, still above403')
    return encode({'schema': 'erdos7-pure-three-joint-moments-v1', 'source_sha256': pins,
                   'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
                   'root_of_cell': ROOT, 'root_caps': FIRST, 'cell_caps': SECOND,
                   'deep_density_caps': DENSITY, 'candidate_lines': candidate_lines(),
                   'envelope_switch': CROSS, 'envelope_lines': ((F(77, 180), F(59, 360)), (F(2, 5), F(31, 180))),
                   'finite_allocation_checks': finite_checks(), 'old_pure_three_square_with_unit_cross': old_block,
                   'new_pure_three_square_with_unit_cross': new_block, 'complete_square_saving': saving,
                   'previous_complete_square_upper': oldQ, 'complete_square_upper': Q,
                   'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
                   'previous_cost_bounds': old_costs, 'improved_cost_bounds': costs, 'majorants': majorants,
                   'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
                   'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
                   'direct_numerator_improvement': square_weight*saving,
                   'majorant_propagation_improvement': propagation, 'numerator_upper': N,
                   'AP11_block_results': prior['AP11_block_results'], 'full_count_tail': prior['full_count_tail'],
                   'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
                   'uniform_denominator_lower': denominator, 'offset': offset,
                   'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
                   'comparison_improvement': F(prior['comparison_upper'])-comparison,
                   'scope': 'Ordinary all-depth moment bound and complete comparison on both actual saturated K faces. Independent pure-three labels may change cells at every depth. Retains168 factorial gains, all52 costs, every other LCM category and all infinite tails. No actual-family sharpness, off-face extension, global K, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('three_joint_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact pure-three moment/consumer certificate')
    print('PASS: all50 moment lines, arbitrary independent deep allocations, complete square<=2203/450.')
    print('Complete face comparison='+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
