#!/usr/bin/env python3
"""Replay feasible rational raw-source duals for both complete heavy costs.

The canonical checker uses only the Python standard library. Numerical
proposal generation is separate in propose_joint_selected_duals.py.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/joint_selected_source_comparison.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/expanded_seven_quadratic_comparison.py': '6bd5cafc35b9eb0876ede720b610eade59f421207552d6be699c368ca2e0beb1',
    'certificates/source_norms/expanded_seven_quadratic_comparison.json': 'b1bdb455f13704423cbc340357ab54cbf88daffcd5b0624b08f6494a4e6942e0',
}


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
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


class RawSelectedLP:
    """One actual raw source split by all four selected event indicators.

    The independent original residue of each event selects a point mass
    in its own projection simplex. Relaxing the four simplexes to mixtures
    includes every original configuration. The variables are raw masses,
    never survivor masses or independently optimized summands.
    """
    def __init__(self, bridge):
        pre, raw, _, descendant = bridge.source_tables(2)
        cells = list(product(range(5), repeat=2))
        self.profiles = [
            [[descendant[c][s]/25 if s == a else F(0) for c, s in cells] for a in range(5)],
            [[pre[c][s]/27 if c == a else F(0) for c, s in cells] for a in range(5)],
            [[descendant[c][s]/25 if s == slot and bridge.ROOT[c] == root else F(0)
              for c, s in cells] for root, slot in product(range(2), range(5))],
            [[pre[c][s]/81 if c == a else F(0) for c, s in cells] for a in range(5)],
        ]
        self.nvars = 400+sum(map(len, self.profiles))
        self.rows, self.rhs, self.equalities = [], [], []
        def add(row, rhs):
            self.rows.append(row)
            self.rhs.append(rhs)
        for cell, (c, s) in enumerate(cells):
            add({16*cell+mask: F(1) for mask in range(16)}, raw[c][s])
        for group, mass in zip(bridge.GROUPS, bridge.GROUP_MASSES):
            add({16*cell+mask: F(1) for cell in group for mask in range(16)}, mass)
        start = 400
        self.lambda_groups = []
        for j, profiles in enumerate(self.profiles):
            columns = list(range(start, start+len(profiles)))
            self.lambda_groups.append(columns)
            self.equalities.append({column: F(1) for column in columns})
            for cell in range(25):
                row = {16*cell+mask: F(1) for mask in range(16) if mask >> j & 1}
                row.update({start+k: -v[cell] for k, v in enumerate(profiles) if v[cell]})
                add(row, F(0))
            start += len(profiles)
        self.intersections = [(0, 1, F(1, 675)), (1, 2, F(1, 675)),
                              (0, 3, F(1, 2025)), (2, 3, F(1, 2025))]
        for j, k, cap in self.intersections:
            add({16*cell+mask: F(1) for cell in range(25) for mask in range(16)
                 if mask >> j & 1 and mask >> k & 1}, cap)
        require(self.nvars == 425 and len(self.rows) == 132 and len(self.equalities) == 4,
                '400 raw masses,25 independent projection weights and all136 constraints')
        require(all(v >= 0 for row in self.profiles for profile in row for v in profile),
                'Every independent residue profile is a nonnegative raw cap')
        self.columns = [[] for _ in range(self.nvars)]
        for i, row in enumerate(self.rows):
            for j, a in row.items():
                self.columns[j].append((i, a))
        self.lambda_group_of = {column: j for j, columns in enumerate(self.lambda_groups) for column in columns}

    def check_dual(self, objective, record):
        require(len(objective) == self.nvars, 'Full raw objective, including the zero lambda columns')
        y = [F(0)]*len(self.rows)
        for key, value in record['nonzero_inequality_duals'].items():
            i = int(key)
            require(str(i) == str(key) and 0 <= i < len(y), 'Canonical dual row index')
            y[i] = F(value)
        z = list(map(F, record['equality_duals']))
        require(len(z) == 4 and min(y) >= 0, 'Nonnegative inequality duals and four free equality duals')
        margins = []
        for j, terms in enumerate(self.columns):
            lhs = sum((a*y[i] for i, a in terms), F(0))
            if j in self.lambda_group_of:
                lhs += z[self.lambda_group_of[j]]
            margins.append(lhs-objective[j])
        require(min(margins) >= 0, 'Every one of425 rational dual inequalities is feasible')
        bound = sum((a*v for a, v in zip(self.rhs, y)), F(0))+sum(z)
        require(bound == F(record['raw_objective_upper']), 'Exact feasible-dual value')
        return bound

    def specification(self):
        return encode({'variables': self.nvars, 'raw_mass_variables': 400, 'projection_mixture_variables': 25,
            'inequalities': len(self.rows), 'equality_normalizations': len(self.equalities),
            'selected_moduli': [25, 27, 75, 81], 'profiles': self.profiles,
            'mixed_intersection_caps': self.intersections,
            'rows_sha256': sha256(json.dumps(encode([self.rows, self.rhs, self.equalities]),
                                             sort_keys=True, separators=(',', ':')).encode()).hexdigest()})


class JointSelectedHead:
    def __init__(self, base, bank=None, proposer=None):
        self.depth = module('joint_selected_depth', base/'frontier/second_depth_seven_comparison.py').SecondDepthSevenHead(base)
        self.parent = self.depth.parent
        self.bridge, self.common = self.parent.bridge, self.parent.common
        self.lp = RawSelectedLP(self.bridge)
        self.bank = {} if bank is None else bank
        self.proposer = proposer
        self.used = set()
        self.verified = {}

    def dual_upper(self, integers, factor):
        key = sha256(json.dumps([str(factor), integers], separators=(',', ':')).encode()).hexdigest()
        if key in self.verified:
            self.used.add(key)
            return self.verified[key], key
        objective = [factor*x for x in integers]+[F(0)]*25
        if key not in self.bank:
            require(self.proposer is not None, 'Missing rational dual certificate '+key)
            self.bank[key] = self.proposer(self.lp, objective)
        upper = self.lp.check_dual(objective, self.bank[key])
        self.used.add(key)
        self.verified[key] = upper
        return upper, key

    def scan(self, coefficients):
        depth, p, cc, b = self.depth, self.parent, self.common, self.bridge
        old, new = depth.prepare(coefficients)
        ints = old['primitive_coefficients']
        scale = old['factor']/depth.total
        raw_scale = old['factor']/depth.scale
        lookup = {(w, m, ell, v): [sum(ct*depth.raw[t, w, (m, ell)][
            v+(mask & ((1 << cc.prefix[t])-1)).bit_count()] for t, ct in ints.items())
            for mask in range(16)]
            for w, m, ell, v in product(sorted(set(cc.wi)), range(5), range(3), range(1, 7))}
        best, witness, digest = F(-1), None, sha256()
        counts = {'two': 0, 'two_bounded': 0, 'four': 0, 'four_bounded': 0,
                  'six': 0, 'six_bounded': 0, 'joint': 0}
        maxima = {k: F(-1) for k in ('two', 'four', 'six')}
        lp_start, dual_start = p.lp_count, len(self.used)
        def record_decision(value):
            digest.update(json.dumps(encode(value), separators=(',', ':')).encode())
        def joint(layout, B, cor, projections, first, second, two, four, six, seed=False):
            nonlocal best, witness
            integers = [value for w, m, ell, v in zip(cc.wi, first, second, B)
                        for value in lookup[w, m, ell, v]]
            raw_upper, key = self.dual_upper(integers, raw_scale)
            upper = raw_upper+scale*(new['constant']-cor)
            accepted = min(scale*two, scale*four, scale*six, upper)
            counts['joint'] += 1
            record_decision(['seed' if seed else 'joint', layout, projections, two, four, six, key, upper])
            if accepted > best:
                best = accepted
                witness = {'layout': layout, 'projections21_35_63_105_147_245': projections,
                    'two_projection_upper': scale*two, 'four_projection_upper': scale*four,
                    'six_projection_upper': scale*six, 'joint_raw_upper': raw_upper,
                    'complete_tail_constant': scale*new['constant'], 'mean_credit': scale*cor,
                    'joint_complete_upper': upper, 'accepted_upper': accepted, 'dual_key': key}
        seed = (1, 3, 2, 1, 2, 3, 2)
        B = b.head_load(seed)
        correction = lambda layout: ints.get(1, 0)*b.integer(depth.total*p.mean.correction(layout))
        cor = correction(seed)
        rt, st, extra = next(v for v in p.extras if v[:2] == (1, 2))
        c63, r105, s105, added = next(v for v in p.added if v[:3] == (3, 1, 2))
        first = [a+d for a, d in zip(extra, added)]
        r147, s245, second = rt, st, extra
        two, _ = p.objective(old, B, extra, cor, False)
        four, _ = p.objective(old, B, first, cor, True)
        six, _ = p.objective(new, B, list(zip(first, second)), cor, True)
        joint(seed, B, cor, (rt, st, c63, r105, s105, r147, s245), first, second, two, four, six, True)
        for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
            B, cor = b.head_load(layout), correction(layout)
            for rt, st, extra in p.extras:
                two, _ = p.objective(old, B, extra, cor, False)
                counts['two'] += 1
                if scale*two <= best:
                    counts['two_bounded'] += 1
                    maxima['two'] = max(maxima['two'], scale*two)
                    record_decision(['two', layout, rt, st, two])
                    continue
                for c63, r105, s105, added in p.added:
                    first = [a+d for a, d in zip(extra, added)]
                    four, _ = p.objective(old, B, first, cor, True)
                    counts['four'] += 1
                    if scale*min(two, four) <= best:
                        counts['four_bounded'] += 1
                        maxima['four'] = max(maxima['four'], scale*min(two, four))
                        record_decision(['four', layout, rt, st, c63, r105, s105, two, four])
                        continue
                    for r147, s245, second in p.extras:
                        six, _ = p.objective(new, B, list(zip(first, second)), cor, True)
                        counts['six'] += 1
                        projections = (rt, st, c63, r105, s105, r147, s245)
                        if scale*min(two, four, six) <= best:
                            counts['six_bounded'] += 1
                            maxima['six'] = max(maxima['six'], scale*min(two, four, six))
                            record_decision(['six', layout, projections, two, four, six])
                            continue
                        joint(layout, B, cor, projections, first, second, two, four, six)
        require(counts['two'] == 125000
                and counts['four'] == 50*(counts['two']-counts['two_bounded'])
                and counts['six'] == 10*(counts['four']-counts['four_bounded'])
                and counts['joint']-1 == counts['six']-counts['six_bounded'],
                'Every containing branch is evaluated or has a complete certified upper')
        require(500*counts['two_bounded']+10*counts['four_bounded']
                +counts['six_bounded']+counts['joint']-1 == 62500000,
                'All62,500,000 original containing choices per independent cost')
        require(witness is not None and all(maxima[k] <= best for k in maxima),
                'Every pruned upper remains below the final maximum of accepted candidates')
        require(p.lp_count-lp_start == 3+counts['two']+counts['four']+counts['six'],
                'All old rational capacity LP evaluations accounted for')
        return {'coefficients': coefficients, 'complete_hinge_upper': best, 'counts': counts,
            'unique_dual_certificates': len(self.used)-dual_start, 'covered_containing_choices': 62500000,
            'source_capacity_lp_count': p.lp_count-lp_start, 'maximum_pruned_uppers': maxima,
            'maximizing_witness': witness, 'branch_decisions_sha256': digest.hexdigest()}


def calculate(base, bank=None, proposer=None):
    io = module('joint_selected_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/expanded_seven_quadratic_comparison.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent complete inherited source '+path)
        pins[path] = pin
    # The second-depth source is already inherited; require its actual presence.
    require('frontier/second_depth_seven_comparison.py' in pins, 'Pinned complete two-depth bridge')
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('joint_selected_'+name, base/'frontier'/(name+'.py'))
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in engine.pins.items()), 'All original independent52 costs')
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require(D == F(53, 360) and Q == F(8201, 1800) and prior['r'] == prior['rho'] == '0',
            'Same complete saturated actual faces and actual mass')
    problem = JointSelectedHead(base, bank, proposer)
    direct, records = list(old_costs), []
    for i in (0, 16):
        tag = engine.specs[i]['tag']
        f = lambda n: engine.source.zero5_cost(tag, n)
        co = {1: f(2)-f(1)} | {t: f(t+1)-2*f(t)+f(t-1) for t in range(2, 9)}
        degree, leading, constant, cutoff = engine.source.zero5_cost_metadata(tag)
        expand = lambda n: f(1)+sum(c*max(n-t, 0) for t, c in co.items())
        require(degree == 1 and cutoff == 8 and min(co.values()) >= 0
                and all(expand(n) == f(n) for n in range(1, 10))
                and sum(co.values()) == leading and f(1)-sum(t*c for t, c in co.items()) == constant,
                'Original heavy cost on every integer load, including its complete affine tail')
        scan = problem.scan(co)
        bound = scan['complete_hinge_upper']+f(1)*D
        require(0 < bound < old_costs[i], 'Strict complete original heavy-cost improvement')
        direct[i] = bound
        records.append({'index': i, 'tag': tag, 'at_one': f(1), 'previous_cost_upper': old_costs[i],
                        'cost_upper': bound, 'scan': scan})
        print('Checked heavy'+str(i)+': '+str(float(bound))+', '
              +str(scan['counts']['joint'])+' rational joint dual uses.', flush=True)
    require(set(problem.bank) == problem.used, 'Every stored dual is used; no unverified or unused proposal records')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(encode(tags) == prior['original_cost_tags'] and len(tags) == len(old_costs) == len(weights) == 52
            and prior['all_original_indices'] == list(range(52)), 'Every original207 test label retained')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda n, tag=t: engine.source.zero5_cost(tag, n) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    require(oldN == F(prior['numerator_upper']) and all(0 <= b <= a for a, b in zip(old_costs, costs))
            and 0 < N < oldN, 'Complete signed52-cost numerator retains every207 improvement')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) == F(1423627769987, 17084377926000) > 0,
            'All207 AP11/AP13 denominator terms and complete count tail retained')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']), 'Strict face improvement, still above403')
    return encode({'schema': 'erdos7-joint-selected-source-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'raw_lp': problem.lp.specification(), 'rational_dual_certificates': problem.bank,
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
        'scope': 'Ordinary complete heavy-cost theorem on both whole actual saturated K faces. One raw source couples all four original selected indicators, while each modulus keeps its independent residue projection. Every62,500,000 containing choices per cost is checked or safely bounded. Rational feasible duals suffice; numerical optimality and actual attainment are not claimed. All52 costs and infinite tails remain. No off-face/global, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = module('joint_selected_reader', args.base/'certificate_io.py')
    expected = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))
    result = calculate(args.base, expected['rational_dual_certificates'])
    require(result == expected, 'Exact canonical joint-source certificate')
    print('PASS: both complete heavy costs, all rational duals and52-cost face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
