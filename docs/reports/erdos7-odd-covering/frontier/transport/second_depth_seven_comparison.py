#!/usr/bin/env python3
"""Keep147/245 at the second seven depth in both complete heavy costs."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/second_depth_seven_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/transport/expanded_seven_survival_comparison.py': '8b7ec8a9781a8c0038795960d3e2326435de0281a76429cf552bf1325aae035a', 'certificates/source_norms/expanded_seven_survival_comparison.json': 'e3a1c9661b7c5159dd90d72e417f5c2b8bf2f107401816c1aae5c22541b2743f', 'frontier/transport/expanded_seven_pair_comparison.py': 'a651711988f8adf20dfc27cba9665f25d0d5863cb310c26e2f4b7fc16bab1c29', 'certificates/source_norms/expanded_seven_pair_comparison.json': '6d41632d57d45a3507abb8c95fdbbd09e12de08e635d261d583889a2872271ef', 'profile-notes/transport/201-two-more-seven-labels-and-selected-intersections-control-both-heavy-costs.md': '2e78cd791bbbfbbe3ffbcb2be6845e02fdbbe2bbd17e06b9e7151e3ddd23cb5d'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original source')
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


def seven_increment(threshold, value, first_extra, second_extra):
    """Delete the first q caps from two finite levels and the full unit tail."""
    q = max(threshold-value, 0)
    first, second = 1+first_extra, 1+second_extra
    return (F(6, 35)*max(first-q, 0)
            +F(6, 245)*max(second-max(q-first, 0), 0)
            +F(1, 5*7**(2+max(q-first-second, 0))))


class SecondDepthSevenHead:
    """Uniform upper for a nonnegative combination of the original hinges.

    Each branch takes the minimum of the valid201 two-projection bound,
    valid201 four-projection bound, and the new six-projection bound.
    The first two bounds allow whole families of deeper choices to be
    bounded before they are enumerated. No source branch is discarded.
    """
    def __init__(self, base):
        self.parent = module('second_depth_parent', base/'frontier/transport/expanded_seven_pair_comparison.py').CoupledSevenHead(base)
        self.bridge, self.common = self.parent.bridge, self.parent.common
        self.scale, self.total = self.parent.scale, self.parent.total
        self.tail_decrease = F(6, 245)*(F(5, 36)+F(1, 10))
        require(self.tail_decrease == F(43, 7350)
                and F(13, 360)-self.tail_decrease == F(2669, 88200),
                'Remove exactly the assigned147/245 caps from the complete201 tail')
        self.raw = {}
        for t, w, m, ell in product(range(1, 9), sorted(set(self.common.wi)), range(5), range(3)):
            values = [F(w, 5)*max(v-t, 0)+seven_increment(t, v, m, ell) for v in range(1, 12)]
            increments = [b-a for a, b in zip(values, values[1:])]
            require(min(increments) >= 0 and all(a <= b for a, b in zip(increments, increments[1:])),
                    'Every two-depth bridge is increasing and integer-convex')
            require(all(d == F(w, 5) for d in increments[t-1:]), 'The exact complete affine continuation')
            if ell == 0:
                require(all(seven_increment(t, v, m, 0) == self.bridge.seven_increment(t, v, m)
                            for v in range(1, 12)), 'Zero second-depth extras recover the original201 bridge')
            self.raw[t, w, (m, ell)] = [0]+[self.bridge.integer(self.scale*v) for v in values]
        self.pairs = list(product(range(5), range(3)))

    def prepare(self, coefficients):
        old = self.parent.prepare(coefficients)
        ints, cc = old['primitive_coefficients'], self.common
        weights = sorted(set(cc.wi))
        head = {(w, x): [0]+[sum(c*self.raw[t, w, x][v] for t, c in ints.items())
                                  for v in range(1, 7)] for w, x in product(weights, self.pairs)}
        arrays = {(i, k): {(w, x): [0]+[sum(c*(self.raw[t, w, x][v+k+1]-self.raw[t, w, x][v+k])
                                          for t, c in ints.items() if cc.prefix[t] >= i)
                                        for v in range(1, 7)] for w, x in product(weights, self.pairs)}
                  for i in range(1, old['highest_selected_label']+1) for k in range(i)}
        for i in range(1, old['highest_selected_label']+1):
            for w, x, v in product(weights, self.pairs, range(1, 7)):
                levels = [arrays[i, k][w, x][v] for k in range(i)]
                require(min(levels) >= 0 and all(a <= b for a, b in zip(levels, levels[1:])),
                        'Every selected-cylinder increment is nonnegative and ordered')
                if i == 4:
                    lo, mid, hi = levels[1:]
                    slope = max(2*(mid-lo), hi-lo)
                    require(slope >= 0 and 2*lo+slope >= 2*mid and lo+slope >= hi,
                            'The same two-count affine envelope controls both intersections')
        decrease = self.bridge.integer(self.total*sum(ints.values())*self.tail_decrease)
        require(0 < decrease < old['constant'], 'A strictly positive complete complementary tail remains')
        return old, {**old, 'head': head, 'raw_arrays': arrays, 'constant': old['constant']-decrease,
                     'second_depth_tail_decrease': decrease}

    def scan(self, coefficients):
        old, new = self.prepare(coefficients)
        p = self.parent
        best, witness, digest = -1, None, sha256()
        two_count = two_bounded = two_expanded = 0
        four_count = four_bounded = four_expanded = 0
        six_count = 0
        max_two_bounded = max_four_bounded = -1
        lp_start = p.lp_count
        correction = lambda layout: old['primitive_coefficients'].get(1, 0)*self.bridge.integer(
            self.total*p.mean.correction(layout))

        def expand_six(layout, B, cor, r, f, c63, r105, f105, first, two, four, seed):
            nonlocal best, witness, six_count
            for r147, f245, second in p.extras:
                value, detail = p.objective(new, B, list(zip(first, second)), cor, True)
                accepted = min(two, four, value)
                six_count += 1
                digest.update(json.dumps(['seed' if seed else 'six', layout, r, f, c63, r105, f105,
                                         r147, f245, two, four, value], separators=(',', ':')).encode())
                if accepted > best:
                    best = accepted
                    witness = {'layout': layout, 'seven21_root': r, 'seven35_slot': f,
                        'seven63_cell': c63, 'seven105_root': r105, 'seven105_slot': f105,
                        'seven147_root': r147, 'seven245_slot': f245,
                        'two_projection_upper': two, 'four_projection_upper': four,
                        'six_projection_upper': value, 'accepted_upper': accepted, 'components': detail}

        # The certified201 controller seeds a lower bound for this maximum.
        # Every seed candidate still uses all three complete valid bounds.
        seed = (1, 3, 2, 1, 2, 3, 2)
        B, cor = self.bridge.head_load(seed), correction(seed)
        for r, f, ex in p.extras:
            two, _ = p.objective(old, B, ex, cor, False)
            for c63, r105, f105, add in p.added:
                first = [a+b for a, b in zip(ex, add)]
                four, _ = p.objective(old, B, first, cor, True)
                expand_six(seed, B, cor, r, f, c63, r105, f105, first, two, four, True)
        for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
            B, cor = self.bridge.head_load(layout), correction(layout)
            for r, f, ex in p.extras:
                two, _ = p.objective(old, B, ex, cor, False)
                two_count += 1
                if two <= best:
                    two_bounded += 1
                    max_two_bounded = max(max_two_bounded, two)
                    digest.update(json.dumps(['two-bounded', layout, r, f, two], separators=(',', ':')).encode())
                    continue
                two_expanded += 1
                for c63, r105, f105, add in p.added:
                    first = [a+b for a, b in zip(ex, add)]
                    four, _ = p.objective(old, B, first, cor, True)
                    four_count += 1
                    inherited = min(two, four)
                    if inherited <= best:
                        four_bounded += 1
                        max_four_bounded = max(max_four_bounded, inherited)
                        digest.update(json.dumps(['four-bounded', layout, r, f, c63, r105, f105,
                                                  two, four], separators=(',', ':')).encode())
                        continue
                    four_expanded += 1
                    expand_six(layout, B, cor, r, f, c63, r105, f105, first, two, four, False)
        require(two_count == 125000 and two_bounded+two_expanded == two_count
                and four_count == 50*two_expanded and four_bounded+four_expanded == four_count
                and six_count == 5000+10*four_expanded,
                'All12500 heads and5000 independent six-projection choices per head are covered')
        require(500*two_bounded+10*four_bounded+(six_count-5000) == 62500000,
                'The complete62,500,000-branch inventory, without omissions or overlap')
        require(witness is not None and (two_bounded == 0 or 0 <= max_two_bounded <= best)
                and (four_bounded == 0 or 0 <= max_four_bounded <= best),
                'Every unexpanded branch has a complete valid upper below the maximum')
        actual_lp_count = p.lp_count-lp_start
        require(actual_lp_count == 10+500+two_count+four_count+six_count, 'Every exact source LP accounted for')
        scaled = lambda x: old['factor']*F(x, self.total)
        return {'coefficients': old['coefficients'], 'primitive_coefficients': old['primitive_coefficients'],
            'factor': old['factor'], 'common_scale': self.total, 'complete_hinge_upper': scaled(best),
            'original_head_projection_branches': two_count, 'two_projection_bounded': two_bounded,
            'two_projection_expanded': two_expanded, 'four_projection_evaluated': four_count,
            'four_projection_bounded': four_bounded, 'four_projection_expanded': four_expanded,
            'six_projection_evaluated_including_seed': six_count, 'covered_six_projection_branches': 62500000,
            'maximum_two_projection_bounded': scaled(max_two_bounded) if two_bounded else None,
            'maximum_four_projection_bounded': scaled(max_four_bounded) if four_bounded else None,
            'rational_lp_count': actual_lp_count, 'maximizing_witness': witness,
            'all_branch_decisions_sha256': digest.hexdigest(),
            'previous_complete_tail_constant': scaled(old['constant']),
            'new_complete_tail_constant': scaled(new['constant'])}


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned complete source and logical certificate reader')
    io = module('second_depth_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/expanded_seven_survival_comparison.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent inherited source '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('second_depth_'+name, base/'frontier'/(name+'.py'))
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in engine.pins.items()), 'Complete original52-cost inventory')
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800))
            and prior['r'] == prior['rho'] == '0', 'Same two complete actual saturated faces')
    problem = SecondDepthSevenHead(base)
    direct, records = list(old_costs), []
    for i in (0, 16):
        tag = engine.specs[i]['tag']
        f = lambda n: engine.source.zero5_cost(tag, n)
        coefficients = {1: f(2)-f(1)} | {t: f(t+1)-2*f(t)+f(t-1) for t in range(2, 9)}
        degree, leading, constant, cutoff = engine.source.zero5_cost_metadata(tag)
        require(degree == 1 and cutoff == 8 and min(coefficients.values()) >= 0 and f(1) == 0,
                'The exact original heavy-cost hinge expansion')
        expand = lambda n: f(1)+sum(c*max(n-t, 0) for t, c in coefficients.items())
        require(all(expand(n) == f(n) for n in range(1, 10)) and sum(coefficients.values()) == leading
                and f(1)-sum(t*c for t, c in coefficients.items()) == constant,
                'Every finite transition and the complete affine original tail')
        scan = problem.scan(coefficients)
        bound = scan['complete_hinge_upper']+f(1)*D
        require(0 < bound < old_costs[i], 'Strict complete heavy-cost improvement')
        direct[i] = bound
        records.append({'index': i, 'tag': tag, 'at_one': f(1), 'previous_cost_upper': old_costs[i],
                        'cost_upper': bound, 'scan': scan})
        print('Checked heavy'+str(i)+': '+str(float(bound))+', '+str(scan['rational_lp_count'])+' exact LPs.', flush=True)
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(encode(tags) == prior['original_cost_tags'] and len(tags) == len(old_costs) == len(weights) == 52
            and prior['all_original_indices'] == list(range(52)), 'Every complete203 original cost retained')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda n, tag=t: engine.source.zero5_cost(tag, n) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    require(oldN == F(prior['numerator_upper']) and all(0 <= b <= a for a, b in zip(old_costs, costs))
            and 0 < N < oldN, 'One complete numerator retains every203 improvement')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) == F(1420639249067, 17084377926000) > 0,
            'All improved203 AP11 blocks, separate AP13 loss and complete count tail retained')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper']) and 403 < comparison < F(prior['comparison_upper']),
            'A strict complete face improvement, still above403')
    return encode({'schema': 'erdos7-second-depth-seven-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'added_positive7_labels': [147, 245], 'removed_assigned_tail_caps': [F(1, 294), F(3, 1225)],
        'remaining_positive7_tail': F(2669, 88200), 'selected_labels': [25, 27, 75, 81],
        'heavy_results': records, 'all_original_indices': list(range(52)), 'original_cost_tags': tags,
        'cost_weights': weights, 'previous_cost_bounds': old_costs, 'direct_cost_bounds': direct,
        'improved_cost_bounds': costs, 'majorants': majorants,
        'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'numerator_upper': N, 'numerator_improvement': oldN-N, 'AP11_block_results': prior['AP11_block_results'],
        'AP13_result': prior['AP13_result'], 'uniform_hinge4_upper': prior['uniform_hinge4_upper'],
        'full_count_tail': prior['full_count_tail'], 'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'scope': 'Ordinary complete heavy-cost theorem on both whole actual saturated K faces. The arbitrary-residue bridge keeps all unit seven powers,21/35/63/105 at depth one and147/245 at depth two. Both prior complete bounds allow exact pruning, with all62,500,000 independent branches covered per cost. All original labels,52 costs,203 denominator and infinite tails remain. No actual attainment, off-face/global extension, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('second_depth_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact second-depth-seven certificate')
    print('PASS: complete second-depth seven bridge and both heavy costs; face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
