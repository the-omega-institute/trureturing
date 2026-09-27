#!/usr/bin/env python3
"""Keep63/105 in the seven bridge and selected old-label intersections."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/expanded_seven_pair_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/source-budgets/shared_six_head_square_comparison.py': 'dd0e7c561f2a32b264b655ee983e735d59fe0cce9d6c3509cde8a2ea0210a74a', 'certificates/source_norms/source-budgets/shared_six_head_square_comparison.json': '833ea6740c99c7cf5c7cf79f9bce63e2b9be253b504e5b8d3b5827abf4f2d871', 'frontier/comparison-bounds/whole_cost_mean_stop_loss.py': '3098c95dcd0c8ef6d27a5d78e4bfad13441d20dd2491e3ea21c76a6acc6c9b70', 'certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json': 'cb1decc204e827ab7ca7fd3f199364b44010e219cdc63f69d960a36520d66cf6', 'frontier/comparison-bounds/whole_cost_common_stop_loss.py': 'c220594349efc9a422b25e9bd434bb4508d4665b7ae80459e5cd14277d6df850', 'frontier/comparison-bounds/whole_face_stop_loss_generator.py': '8f02e3210c0e9477680a7f817fd3594db83fa1fb34221226b707f41e0a3f4784', 'certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json': 'e2456850d6db2ac5445e9ff927cdd75c104e3a1a25c8b22159d72c201fe3b924', 'profile-notes/065-128/98-a-complete-stop-loss-profile-strengthens-the-whole-face-comparison.md': '696bad2eb0aaf4642a05969e474224281d330ad8480e2a7d8a28bb5c36e0cb71', 'profile-notes/065-128/109-the-mean-and-all-hinges-share-one-original-test.md': '8bdfd8d0830de3b2ef5fd554b55308854118e74f0b89f511efdfdcf0297314d7', 'profile-notes/065-128/128-the-complete-factorial-tail-retains-its-head-off-the-face.md': '79ae5ce60d7121afdc3fe0eaa3a87abecf21709d15e7627c2425dd7bdb4926cc'}


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


class CoupledSevenHead:
    """A complete positive hinge combination, without a constant mass term.

    prepare(coefficients) constructs both valid versions of the same head.
    scan(coefficients) covers every original independent head and projection.
    The result is an upper on sum_t coefficients[t]*integral(A-t)_+.
    """
    def __init__(self, base):
        self.base = base
        load = lambda name: module('seven_pair_'+name, io.named_artifact(base/'frontier', name+'.py'))
        io = module('seven_pair_io', base/'certificate_io.py')
        profile = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json'))
        self.bridge = load('k_face_common_seven_hinges')
        self.mean_module = load('whole_cost_mean_stop_loss')
        common = load('whole_cost_common_stop_loss')
        self.mean = self.mean_module.MeanHead(self.bridge, profile, common)
        self.common, self.scale, self.total = self.mean.common, common.SCALE, common.TOTAL
        self.lp_count = 0
        self.deletion_gain = F(1, 70)+F(2, 175)
        require(self.deletion_gain == F(9, 350)
                and F(profile['stop_loss_profile']['complete_complementary_positive7_tail'])-self.deletion_gain == F(13, 360),
                'Remove exactly the original63 and105 cap terms from the complete positive-seven tail')
        require(F(6, 35)*F(1, 12) == F(1, 70) and F(6, 35)*F(1, 15) == F(2, 175),
                'The unchanged full raw63 and105 capacities')
        require(F(16200, 27*25) == 24 and F(16200, 81*25) == 8,
                'Same raw-source mixed-cylinder intersection scales')
        cc = self.common
        for t, w, m in product(range(1, 9), sorted(set(cc.wi)), range(5)):
            values = [F(w, 5)*max(v-t, 0)+self.bridge.seven_increment(t, v, m) for v in range(1, 12)]
            increments = [b-a for a, b in zip(values, values[1:])]
            require(min(increments) >= 0 and all(a <= b for a, b in zip(increments, increments[1:])),
                    'Every enlarged-seven bridge is increasing and integer-convex')
            require(all(d == F(w, 5) for d in increments[t-1:]), 'Exact affine bridge continuation')
            cc.raw_costs[t, w, m] = [0]+[self.bridge.integer(self.scale*v) for v in values]
        self.extras = [(r, f, cc.extra(r, f)) for r, f in product(range(2), range(5))]
        self.added = [(c63, r105, f105,
                       [int(c == c63)+int(self.bridge.ROOT[c] == r105 and s == f105)
                        for c, s in product(range(5), repeat=2)])
                      for c63, r105, f105 in product(range(5), range(2), range(5))]
        require(len(self.extras) == 10 and len(self.added) == 50, 'Every independent old projection of21/35/63/105')

    def prepare(self, coefficients):
        cc = self.common
        old = self.mean.prepare(coefficients)
        ints = old['primitive_coefficients']
        require(old['highest_selected_label'] <= 4, 'Exactly the original four selected labels')
        head = {(w, m): [0]+[sum(c*cc.raw_costs[t, w, m][v] for t, c in ints.items())
                                      for v in range(1, 7)]
                for w, m in product(sorted(set(cc.wi)), range(5))}
        raw = {}
        for i in range(1, old['highest_selected_label']+1):
            for k in range(i):
                raw[i, k] = {(w, m): [0]+[sum(c*(cc.raw_costs[t, w, m][v+k+1]-cc.raw_costs[t, w, m][v+k])
                                                   for t, c in ints.items() if cc.prefix[t] >= i)
                                          for v in range(1, 7)]
                             for w, m in product(sorted(set(cc.wi)), range(5))}
        # Each active threshold has every earlier selected label present
        # in its prefix. Check the coefficient order and the two-count
        # affine envelope once, before using them on any actual cylinder.
        for i in range(1, old['highest_selected_label']+1):
            for w, m, v in product(sorted(set(cc.wi)), range(5), range(1, 7)):
                levels = [raw[i, k][w, m][v] for k in range(i)]
                require(min(levels) >= 0 and all(a <= b for a, b in zip(levels, levels[1:])),
                        'All prefix-conditioned increment coefficients are nonnegative and ordered')
                if i == 4:
                    lo, mid, hi = levels[1:]
                    slope = max(2*(mid-lo), hi-lo)
                    require(slope >= 0 and 2*lo+slope >= 2*mid and lo+slope >= hi,
                            'One affine envelope controls both possible preceding-five counts')
        decrease = self.bridge.integer(self.total*sum(ints.values())*self.deletion_gain)
        require(0 <= decrease <= old['constant'], 'The full remaining cap tail remains nonnegative')
        return {'coefficients': old['coefficients'], 'primitive_coefficients': ints,
                'factor': old['factor'], 'highest_selected_label': old['highest_selected_label'],
                'head': head, 'raw_arrays': raw, 'old_constant': old['constant'],
                'constant': old['constant']-decrease, 'complete_tail_decrease': decrease}

    def objective(self, record, B, extra, correction, expanded):
        cc = self.common
        coefficients = [record['head'][w, m][v] for w, m, v in zip(cc.wi, extra, B)]
        head, dual = self.bridge.lp_bound(coefficients, cc.caps, cc.budgets)
        self.lp_count += 1
        require(head == sum(r['value'] for r in dual), 'Every source LP has a feasible primal and matching dual')
        selected = []
        for i, (a, b) in enumerate(self.bridge.ORDER[:record['highest_selected_label']], 1):
            def array(k):
                table = record['raw_arrays'][i, k]
                return [table[w, m][v] for w, m, v in zip(cc.wi, extra, B)]
            hi = array(i-1)
            upper = cc.tail(hi, a, b)
            if i in (2, 3):
                lo = array(i-2)
                upper = min(upper, cc.tail(lo, a, b)+24*max(x-y for x, y in zip(hi, lo)))
            if i == 4:
                lo, mid = array(1), array(2)
                upper = min(upper,
                    cc.tail(lo, a, b)+8*max(max(2*(m-l), h-l) for l, m, h in zip(lo, mid, hi)),
                    cc.tail(mid, a, b)+8*max(h-m for h, m in zip(hi, mid)))
            selected.append(upper)
        constant = record['constant'] if expanded else record['old_constant']
        value = constant+45*head-correction+sum(selected)
        require(value >= 0, 'Complete corrected same-head objective remains nonnegative')
        return value, {'head_source_lp': head, 'mean_head_deletion': correction,
                       'selected_increment_uppers': selected, 'complete_tail_constant': constant}

    def scan(self, coefficients):
        record = self.prepare(coefficients)
        correction = lambda layout: record['primitive_coefficients'].get(1, 0)*self.bridge.integer(
            self.total*self.mean.correction(layout))
        best, witness, digest = -1, None, sha256()
        original, expanded, pruned, checked = 0, 0, 0, 0
        max_pruned = -1
        lp_start = self.lp_count
        seed = (0, 1, 2, 0, 2, 1, 2)

        def consider(layout, B, cor, r, f, old_extra, old_value, seed_step):
            nonlocal best, witness, checked
            for c63, r105, f105, add in self.added:
                ex = [x+y for x, y in zip(old_extra, add)]
                new, detail = self.objective(record, B, ex, cor, True)
                value = min(old_value, new)
                checked += 1
                digest.update(json.dumps(['seed' if seed_step else 'expanded', layout, r, f, c63, r105, f105,
                                          old_value, new], separators=(',', ':')).encode())
                if value > best:
                    best = value
                    witness = {'layout': layout, 'seven21_root': r, 'seven35_slot': f,
                               'seven63_cell': c63, 'seven105_root': r105, 'seven105_slot': f105,
                               'old_two_projection_pair_upper': old_value,
                               'new_four_projection_pair_upper': new, 'components': detail}

        B, cor = self.bridge.head_load(seed), correction(seed)
        for r, f, ex in self.extras:
            old, _ = self.objective(record, B, ex, cor, False)
            consider(seed, B, cor, r, f, ex, old, True)
        for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
            B, cor = self.bridge.head_load(layout), correction(layout)
            for r, f, ex in self.extras:
                old, _ = self.objective(record, B, ex, cor, False)
                original += 1
                if old <= best:
                    pruned += 1
                    max_pruned = max(max_pruned, old)
                    digest.update(json.dumps(['bounded', layout, r, f, old], separators=(',', ':')).encode())
                else:
                    expanded += 1
                    consider(layout, B, cor, r, f, ex, old, False)
        require(original == 125000 and pruned+expanded == original and checked == 500+50*expanded,
                'Every original head and all6,250,000 independent four-projection choices are covered')
        require((pruned == 0 or 0 <= max_pruned <= best) and witness is not None,
                'Every unexpanded branch is bounded by the final maximum')
        upper = record['factor']*F(best, self.total)
        return {'coefficients': record['coefficients'], 'primitive_coefficients': record['primitive_coefficients'],
                'factor': record['factor'], 'common_scale': self.total,
                'complete_hinge_upper': upper, 'original_head_projection_branches': original,
                'bounded_without_extra_projections': pruned, 'expanded_branches': expanded,
                'expanded_objective_count_including_seed': checked, 'rational_lp_count': self.lp_count-lp_start,
                'maximum_unexpanded_upper': record['factor']*F(max_pruned, self.total) if pruned else None,
                'all_branch_decisions_sha256': digest.hexdigest(), 'maximizing_witness': witness,
                'old_complete_tail_constant': record['factor']*F(record['old_constant'], self.total),
                'new_complete_tail_constant': record['factor']*F(record['constant'], self.total)}


def calculate(base):
    require(PINS, 'Pin the source theorem and entire199 consumer')
    io = module('seven_pair_certificate_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior, mean_prior = read('shared_six_head_square_comparison'), read('whole_cost_mean_stop_loss')
    pins = dict(PINS)
    for data in (prior, mean_prior):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    load = lambda name: module('seven_pair_consumer_'+name, io.named_artifact(base/'frontier', name+'.py'))
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in engine.pins.items()), 'Complete original52-cost inventory')
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800)) and prior['r'] == prior['rho'] == '0',
            'Same saturated faces and complete199 square')
    problem = CoupledSevenHead(base)
    direct, records = list(old_costs), []
    targets = {0: F(1767382419284066416882094809, 299640136547155230246420000),
               16: F(1223584622012646577327283593201, 259563268283973218200961325000)}
    for i in (0, 16):
        tag = engine.specs[i]['tag']
        f = lambda n: engine.source.zero5_cost(tag, n)
        coefficients = {1: f(2)-f(1)} | {t: f(t+1)-2*f(t)+f(t-1) for t in range(2, 9)}
        degree, leading, constant, cutoff = engine.source.zero5_cost_metadata(tag)
        require(degree == 1 and cutoff == 8 and min(coefficients.values()) >= 0 and f(1) == 0,
                'The original heavy cost has a positive exact finite hinge expansion')
        expand = lambda n: f(1)+sum(c*max(n-t, 0) for t, c in coefficients.items())
        require(all(expand(n) == f(n) for n in range(1, 10))
                and sum(coefficients.values()) == leading
                and f(1)-sum(t*c for t, c in coefficients.items()) == constant,
                'All finite transitions and the entire original affine tail agree')
        row = problem.scan(coefficients)
        bound = row['complete_hinge_upper']+f(1)*D
        require(bound == targets[i] and bound < old_costs[i], 'Strict complete heavy bound over all original branches')
        direct[i] = bound
        records.append({'index': i, 'tag': tag, 'at_one': f(1), 'previous_cost_upper': old_costs[i],
                        'cost_upper': bound, 'scan': row})
        print('Checked heavy'+str(i)+': '+str(float(bound))+', '+str(row['rational_lp_count'])+' exact LPs.', flush=True)
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(len(tags) == len(old_costs) == len(weights) == 52 and prior['all_original_indices'] == list(range(52)),
            'All52 independent original costs retained')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda n, tag=t: engine.source.zero5_cost(tag, n) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    require(oldN == F(prior['numerator_upper']) and all(0 <= b <= a for a, b in zip(old_costs, costs)) and 0 < N < oldN,
            'Full signed numerator decreases with every199 improvement retained')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) == F(50511415637, 632754738000) > 0,
            'All AP11 blocks, AP13 loss and the complete count tail')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper']) and 403 < comparison < F(prior['comparison_upper']),
            'Strict complete-face improvement, without closing the terminal gap')
    return encode({'schema': 'erdos7-expanded-seven-pair-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'added_positive7_labels': [63, 105], 'removed_assigned_tail_caps': [F(1, 70), F(2, 175)],
        'remaining_positive7_tail': F(13, 360), 'selected_labels': [25, 27, 75, 81],
        'mixed_intersection_caps': {'27_with25_or75': F(1, 675), '81_with25_or75': F(1, 2025)},
        'heavy_results': records, 'all_original_indices': list(range(52)), 'original_cost_tags': tags,
        'cost_weights': weights, 'previous_cost_bounds': old_costs, 'direct_cost_bounds': direct,
        'improved_cost_bounds': costs, 'majorants': majorants,
        'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'numerator_upper': N, 'numerator_improvement': oldN-N, 'AP11_block_results': prior['AP11_block_results'],
        'full_count_tail': prior['full_count_tail'], 'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'scope': 'Ordinary complete heavy-cost and52-cost comparison on both saturated actual K faces. Retains63/105 in one arbitrary-residue seven bridge and bounds selected old-label increments through actual mixed intersections. Every source branch and infinite exponent tail remains covered; branch pruning uses a separate valid upper. No actual-family attainment, off-face/global extension, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('seven_pair_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact expanded-seven pair certificate')
    print('PASS: complete63/105 bridge, selected-pair constraints and both heavy costs; face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
