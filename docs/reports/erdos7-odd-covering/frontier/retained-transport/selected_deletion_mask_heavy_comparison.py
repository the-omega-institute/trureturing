#!/usr/bin/env python3
"""Complete heavy costs with the actual deep-five deletion on selected masks."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/selected_deletion_mask_heavy_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
        'frontier/retained-transport/retained_deletion_heavy_comparison.py': '553c281d5de5a9bcd9098ea933f6cccf046b587132e6fa49ec4aa8b44b4ec86f',
        'frontier/retained-transport/retained_deletion_survival_comparison.py': 'bf265663d663f4e681e79efdca61af3607917cac3a47f9c8fbc1dd19f911abab',
        'certificates/source_norms/retained-transport/retained_deletion_survival_comparison.json': '646acfad14cbb6e3476c7d33a1fb2ce3ba068305dc02fa75635df8c8509fff87',
        'profile-notes/065-128/109-the-mean-and-all-hinges-share-one-original-test.md': '8bdfd8d0830de3b2ef5fd554b55308854118e74f0b89f511efdfdcf0297314d7'}
BRANCHES = ('nested', 'disjoint')
ETA = (F(1, 18), F(1, 9), F(1, 9), F(1, 9), F(1, 9))


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


class IntegerDualChecker:
    """Check every rational column after multiplying by positive denominators."""
    def __init__(self, lp):
        self.lp = lp
        values = [a for row in lp.rows+lp.equalities for a in row.values()]+lp.rhs+lp.erhs
        self.matrix_scale = lcm(*(a.denominator for a in values))
        integer = lambda a: a.numerator*(self.matrix_scale//a.denominator)
        self.columns = [[(i, integer(a)) for i, a in column] for column in lp.columns]
        self.eqcolumns = [[(i, integer(a)) for i, a in column] for column in lp.eqcolumns]
        self.rhs, self.erhs = map(lambda v: list(map(integer, v)), (lp.rhs, lp.erhs))
        require(self.matrix_scale > 0 and len(self.columns) == len(self.eqcolumns) == 1275
                and len(self.rhs) == 997 and len(self.erhs) == 54,
                'All1275 columns,997 inequalities and54 equalities')

    def check(self, objective, record):
        require(len(objective) == 1275, 'Complete raw/survivor/deletion objective')
        prices = [F(0)]*997
        for key, value in record['nonzero_inequality_duals'].items():
            i = int(key)
            require(str(i) == str(key) and 0 <= i < 997, 'Canonical dual inequality row')
            prices[i] = F(value)
        equalities = list(map(F, record['equality_duals']))
        require(len(equalities) == 54 and min(prices) >= 0,
                'All nonnegative inequality prices and unrestricted equality prices')
        scale = lcm(*{a.denominator for a in prices+equalities+objective})
        require(scale > 0, 'Positive exact objective and dual denominator')
        integer = lambda a: a.numerator*(scale//a.denominator)
        y, z, target = (list(map(integer, v)) for v in (prices, equalities, objective))
        for k in range(1275):
            lhs = sum(a*y[i] for i, a in self.columns[k])+sum(a*z[i] for i, a in self.eqcolumns[k])
            require(lhs >= self.matrix_scale*target[k], 'Exact selected-deletion dual column '+str(k))
        value = F(sum(a*v for a, v in zip(self.rhs, y))+sum(a*v for a, v in zip(self.erhs, z)),
                  self.matrix_scale*scale)
        require(value == F(record['raw_objective_upper']), 'Complete signed rational dual objective')
        return value


class MaskDeletionLP:
    """Extend216 with one actual deep-five measure, retaining every original label."""
    def __init__(self, original, wi, branch):
        require(branch in BRANCHES and original.nvars == 875, 'Original216 system and exhaustive branch')
        self.branch, self.nvars = branch, 1275
        self.rows, self.rhs = [dict(row) for row in original.rows], list(original.rhs)
        self.equalities, self.erhs = [dict(row) for row in original.equalities], list(original.erhs)
        self.lambda_groups = original.lambda_groups
        self.y_link, self.e3_zero = original.y_link, original.e3_zero
        self.selected_caps = original.selected_caps
        self.original_spec = original.specification()
        self.mask_links = []
        for c in range(5):
            self.equalities.append({16*(5*c+4)+mask: F(1) for mask in range(16)})
            self.erhs.append(ETA[c]/5)
            for slot in range(3):
                self.rows.append({850+5*c+slot: F(1)})
                self.rhs.append(F(0))
        for cell, w in enumerate(wi):
            self.equalities.append({850+cell: F(-1), **{875+16*cell+mask: F(1) for mask in range(16)}})
            self.erhs.append(F(0))
            for mask in range(16):
                self.mask_links.append(len(self.rows))
                self.rows.append({875+16*cell+mask: F(1), 425+16*cell+mask: F(1),
                                  16*cell+mask: -F(w, 5)})
                self.rhs.append(F(0))
        for c in range(1, 5):
            mass = ETA[c]*(1+int(c >= 2))/100
            for bit, group, ratio in ((1, 1, F(1, 3)), (3, 3, F(1, 9))):
                self.equalities.append({self.lambda_groups[group][c]: -mass*ratio,
                    **{875+16*(5*c+slot)+mask: F(1) for slot in range(5)
                       for mask in range(16) if mask & (1 << bit)}})
                self.erhs.append(F(0))
        bad = [mask for mask in range(16) if mask & 8
               and ((not mask & 2) if branch == 'nested' else bool(mask & 2))]
        self.rows.append({16*cell+mask: F(1) for cell in range(25) for mask in bad})
        self.rhs.append(F(0))
        self.columns, self.eqcolumns = ([[] for _ in range(self.nvars)] for _ in range(2))
        for i, row in enumerate(self.rows):
            for k, a in row.items():
                self.columns[k].append((i, a))
        for i, row in enumerate(self.equalities):
            for k, a in row.items():
                self.eqcolumns[k].append((i, a))
        self.checker = IntegerDualChecker(self)
        self.check_dual = self.checker.check

    def specification(self):
        return encode({'branch': self.branch, 'variables': self.nvars,
            'raw_mass_variables': 400, 'survivor_variables': 400,
            'projection_mixture_variables': 25, 'coarse_extra_deletion_variables': 50,
            'deep_five_mask_variables': 400, 'inequalities': len(self.rows),
            'equalities': len(self.equalities), 'original216_lp': self.original_spec,
            'fixed_H_equalities': 5, 'deep_five_QH_zero_rows': 15,
            'deep_five_mask_aggregation_equalities': 25, 'deep_five_mask_links': 400,
            'unthinned_ternary_marginal_equalities': 8,
            'rows_sha256': sha256(json.dumps(encode([self.rows, self.rhs, self.equalities, self.erhs]),
                sort_keys=True, separators=(',', ':')).encode()).hexdigest()})


def mask_head_class(base):
    parent = module('selected_mask_parent', base/'frontier/retained-transport/retained_deletion_heavy_comparison.py')
    whole = module('selected_mask_whole', base/'frontier/retained-transport/retained_deletion_survival_comparison.py')

    class MaskDeletionHead(parent.RetainedDeletionHead):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.branch_lps = {branch: MaskDeletionLP(self.lp, self.common.wi, branch) for branch in BRANCHES}
            self.objective_branches = {}

        def dual_upper(self, integers, factor):
            require(len(integers) == 875, 'Original complete216 objective retained')
            group = sha256(json.dumps([str(factor), integers], separators=(',', ':')).encode()).hexdigest()
            keys, values = {}, []
            objective = [factor*x for x in integers]+[F(0)]*400
            for branch, lp in self.branch_lps.items():
                key = sha256(json.dumps([group, branch], separators=(',', ':')).encode()).hexdigest()
                if key not in self.verified:
                    if key not in self.bank:
                        require(self.proposer is not None, 'Missing selected-deletion branch dual '+key)
                        self.bank[key] = self.proposer(lp, objective)
                    self.verified[key] = lp.check_dual(objective, self.bank[key])
                self.used.add(key)
                keys[branch] = key
                values.append(self.verified[key])
            self.objective_branches[group] = keys
            return max(values), group

        def scan(self, coefficients):
            result = whole.whole_hinge_scan(self, coefficients)
            witness = result['maximizing_witness']
            witness['nested_disjoint_dual_keys'] = self.objective_branches[witness['dual_key']]
            result['branch_rule'] = 'max(nested,disjoint), each a complete rational dual upper'
            return result

    return MaskDeletionHead


def calculate(base, bank=None, proposer=None):
    io = module('selected_mask_io', base/'certificate_io.py')
    prior = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/retained-transport/retained_deletion_survival_comparison.json'))
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent inherited source '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    load = lambda name: module('selected_mask_'+name, io.named_artifact(base/'frontier', name+'.py'))
    original = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in original.pins.items()), 'Complete original52 costs')
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800))
            and prior['r'] == prior['rho'] == '0', 'Same two whole actual saturated K faces')
    problem = mask_head_class(base)(base, bank, proposer)
    direct, records = list(old_costs), []
    for index in (0, 16):
        tag = original.specs[index]['tag']
        f = lambda n: original.source.zero5_cost(tag, n)
        coefficients = {1: f(2)-f(1)} | {t: f(t+1)-2*f(t)+f(t-1) for t in range(2, 9)}
        degree, leading, constant, cutoff = original.source.zero5_cost_metadata(tag)
        expansion = lambda n: f(1)+sum(a*max(n-t, 0) for t, a in coefficients.items())
        require(degree == 1 and cutoff == 8 and min(coefficients.values()) >= 0
                and all(expansion(n) == f(n) for n in range(1, 10))
                and sum(coefficients.values()) == leading
                and f(1)-sum(t*a for t, a in coefficients.items()) == constant,
                'Original heavy cost on every positive integer and its entire affine tail')
        print('Scanning complete heavy'+str(index)+' over62,500,000 original choices.', flush=True)
        scan = problem.scan(coefficients)
        bound = scan['complete_hinge_upper']+f(1)*D
        require(0 < bound < old_costs[index], 'Strict complete original heavy improvement')
        direct[index] = bound
        records.append({'index': index, 'tag': tag, 'at_one': f(1), 'previous_cost_upper': old_costs[index],
                        'cost_upper': bound, 'scan': scan})
        print('Checked complete heavy'+str(index)+': '+str(float(bound))+', '
              +str(scan['counts']['joint'])+' two-branch dual uses; '
              +str(scan['source_capacity_lp_count'])+' exact capacity LPs.', flush=True)
    if proposer is None:
        require(set(problem.bank) == problem.used, 'Every stored branch dual is used and checked')
    retained = {key: problem.bank[key] for key in sorted(problem.used)}
    tags = [s['tag'] for s in original.specs+original.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(encode(tags) == prior['original_cost_tags'] and len(tags) == len(old_costs) == len(weights) == 52
            and prior['all_original_indices'] == list(range(52)) and min(weights) > 0,
            'All218 original labels and positive weights retained')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda n, tag=tag: original.source.zero5_cost(tag, n) for tag in all_tags]
    metadata = [original.source.zero5_cost_metadata(tag) for tag in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    require(signed < 0 < square_weight and oldN == F(prior['numerator_upper']) > N > 0
            and all(0 <= b <= a for a, b in zip(old_costs, costs)), 'One complete stronger signed52-cost numerator')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(sum(F(r['joint_mean_upper'])
        for r in prior['AP11_block_results'])+F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) > 0
            and F(prior['uniform_hinge4_upper']) == 6*F(prior['standalone_hinge4_penalty'])
            == F(prior['AP13_result']['hinge_upper']), 'All218 independent survival terms and full count tail')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper'])
            and comparison < F(prior['comparison_upper']), 'Complete improved face comparison')
    return encode({'schema': 'erdos7-selected-deletion-mask-heavy-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'branch_lps': {branch: lp.specification() for branch, lp in problem.branch_lps.items()},
        'rational_dual_buckets': load('retained_deletion_heavy_comparison').bucket_duals(retained),
        'selected_policy': {1: [], **{t: [25, 27, 75, 81] for t in range(2, 9)}},
        'previous_prefix_duals_used': sorted(problem.prior_used), 'heavy_results': records,
        'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
        'previous_cost_bounds': old_costs, 'direct_cost_bounds': direct, 'improved_cost_bounds': costs,
        'majorants': majorants, 'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'previous_numerator_upper': oldN, 'numerator_upper': N, 'numerator_improvement': oldN-N,
        'AP11_block_results': prior['AP11_block_results'], 'AP13_result': prior['AP13_result'],
        'uniform_hinge4_upper': prior['uniform_hinge4_upper'], 'full_count_tail': prior['full_count_tail'],
        'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'scope': 'Both complete actual saturated K faces. The one deep-five deletion is split by the four independently selected test masks; eight unthinned-cell marginals retain its original ternary product structure. Nested and disjoint original27/81 residues are both bounded. Every62,500,000 original head/seven-projection choice is evaluated or bounded by a complete certified alternative per heavy cost. All1275 rational dual columns, all52 original costs, signed actual mass, complete square, independent218 survival tests and infinite tails remain. No common optimizer across independent tests, actual-family attainment, off-face/global extension, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = module('selected_mask_reader', args.base/'certificate_io.py')
    expected = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))
    parent = module('selected_mask_bank', args.base/'frontier/retained-transport/retained_deletion_heavy_comparison.py')
    result = calculate(args.base, parent.flatten_duals(expected['rational_dual_buckets']))
    require(result == expected, 'Exact complete selected-deletion-mask certificate')
    print('PASS: two complete heavy scans, all1275 dual columns and52-cost face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
