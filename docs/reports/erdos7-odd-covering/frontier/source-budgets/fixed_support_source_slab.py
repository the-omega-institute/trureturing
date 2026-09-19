#!/usr/bin/env python3
"""A concave fixed-support heavy margin on the complete broad source slab."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/fixed_support_source_slab.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/endpoint-bounds/vector_marked_source.py': 'e9917c725b8f910a0524ccae99dfffb5949f3af568980a70b5299e7fb1c71b39',
    'frontier/endpoint-bounds/broad_weighted_identity_source.py': 'ac969b33f833eb1cea191bdb74434ad6199077cfed1e551f0c5e0e7f286d3df1',
    'frontier/source-budgets/full_linear_carrier_frontier.py': '98cbec50d807ed9208504c8cd2384659a4300d6909d54414e5e2156285298888',
    'frontier/source-budgets/source_barrier_saturation.py': '6fe57e39274df1fa4a80ae4d4a22cab7b1d78d28c4f428b789071e3fb7776a64',
    'certificates/source_norms/moments-survival/whole_quadratic_same_head.json': 'ed24ce03bd65f29684a606ba601f88b06040562e7dd7a690d360cea5aa4a2852',
    'certificates/source_norms/comparison-bounds/residual_shell_k_comparison.json': '028c510517bb3e6cd5ff0261254c116a65d1879a3bb9dcf66ce9bfe659d94f68',
}
DELTA, PMAX, R_CUTOFF = F(1, 18), F(1, 20), F(1, 2500)
ROOT = (0, 0, 1, 1, 1)
INDICES = (0, 16)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original source')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def simplex(n, cap):
    return [(F(0),)*n]+[tuple(cap if i == j else F(0) for i in range(n)) for j in range(n)]


def joint_vertices():
    main = ((F(0), F(0), F(0)), (F(0), DELTA, F(0)), (F(0), F(0), DELTA),
            (PMAX, F(0), F(0)), (PMAX, DELTA-PMAX, F(0)), (PMAX, F(0), DELTA-PMAX))
    result = []
    for p, a, b in main:
        for alpha0 in sorted({F(0), a}):
            for beta0, beta1 in sorted({(F(0), F(0)), (b, F(0)), (F(0), b)}):
                for beta3, beta4 in ((F(0), F(0)), (PMAX, F(0)), (F(0), PMAX)):
                    alpha = (alpha0, F(1, 4)-a)
                    beta = (beta0, beta1, F(1, 4)-b-beta3-beta4, beta3, beta4)
                    require(min(alpha+beta) >= 0 and sum(alpha) <= F(1, 4) and sum(beta) <= F(1, 4)
                            and p+a+b <= DELTA and beta3+beta4 <= PMAX, 'The original joint source polytope')
                    result.append((alpha, beta, F(3, 4)+p))
    require(len(result) == len(set(result)) == 36, 'Exactly36 distinct joint-source generators')
    return result


class Slab:
    def __init__(self, base):
        self.base = base
        self.io = module('slab_io', base/'certificate_io.py')
        for path, pin in PINS.items():
            require(sha256(self.io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
        self.vector = module('slab_vector', base/'frontier/endpoint-bounds/vector_marked_source.py')
        self.broad = module('slab_broad', base/'frontier/endpoint-bounds/broad_weighted_identity_source.py')
        self.full = module('slab_full', base/'frontier/source-budgets/full_linear_carrier_frontier.py')
        self.engine = module('slab_engine', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
        self.source, self.sigma = self.engine.source, self.vector.SIGMA
        self.carriers = self.broad.CARRIERS
        self.a = tuple(tuple(1-F(int(ROOT[c] == r)+int(c == j), 5) for c in range(5)) for r, j in self.carriers)
        self.pins = {}
        for pins in (PINS, self.vector.PINS, self.engine.pins):
            for path, pin in pins.items():
                require(path not in self.pins or self.pins[path] == pin, 'Consistent inherited pin '+path)
                self.pins[path] = pin
        for path, pin in self.pins.items():
            require(sha256(self.io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Complete source closure '+path)
        self.original = json.loads(self.io.read_artifact_bytes(base/'certificates/source_norms/moments-survival/whole_quadratic_same_head.json'))
        weights = tuple(map(F, self.original['cost_weights']))
        require(len(weights) == 52 and weights[:41] == self.engine.weights, 'The unchanged complete52 normalization')
        self.weights = weights
        self.prepared = {i: self.prepare(i) for i in INDICES}

    def prepare(self, index):
        spec, source = self.engine.specs[index], self.source
        C, result = F(self.engine.thresholds[index]['constant']), []
        dstar = source.data(self.engine.parameters[398])[0]
        require(spec['zero'] == ('seven_block', (spec['tag'], 0)), 'Exact common zero-seven block cancellation')
        for item in spec['layouts']:
            b = item['baseline']
            costs = tuple(source.zero5_cost(spec['tag'], x) for x in b)
            derivative = tuple(source.zero5_cost(spec['tag'], x+1)-source.zero5_cost(spec['tag'], x) for x in b)
            k = tuple(C-x for x in costs)
            require(derivative == tuple(item['joint'][1]), 'Original branch derivatives')
            branches = []
            for positive5 in source.BASES:
                correction = tuple(x*y for x, y in zip(derivative, positive5))
                zstar = tuple(x*d-y/5 for x, d, y in zip(k, dstar, correction))
                support = max(range(5), key=lambda j: zstar[j])
                branches.append((positive5, correction, support))
            result.append((item, derivative, k, branches))
        require(len(result) == 10 and sum(len(row[3]) for row in result) == 100, 'Every original heavy branch')
        return spec, C, result

    def evaluate(self, parameter, index, check_original=False):
        source = self.source
        dat = source.data(parameter)
        d, n, eta, s, _ = dat
        spec, C, items = self.prepared[index]
        delta = parameter[4]-F(3, 4)+F(1, 4)-parameter[1][1]+F(1, 4)-sum(parameter[2][2:])
        require(0 <= delta <= DELTA and min(eta) >= F(1, 18) and min(d) >= F(1, 4), 'Containing source slab')
        pre = tuple(tuple(F(0) if slot == 0 or (slot == 1 and c >= 2) or (slot == 2 and c == 2)
                          else F(3, 20)+delta if slot == 3 and c < 2
                          else F(1, 10)+delta if slot == 3 else F(1, 5) for c in range(5)) for slot in range(4))
        common = source.zero7_raw(spec['tag'], dat)-source.zero5_raw(spec['zero'], dat)
        positive = self.engine.positive(index, eta)
        old, new, controllers = [None]*18, [None]*18, [None]*18
        for item, derivative, k, branches in items:
            vmax = max(derivative)
            H = sum(eta[c]*(1+int(c >= 2))*derivative[c] for c in range(5))/25
            H += self.sigma*min(derivative[c]/5+vmax*(d[0]-d[c]) for c in range(5))
            holes = [(tuple(eta[c]*derivative[c]*(F(1, 5)-p[c]) for c in range(5)),
                      self.sigma*min(derivative[c]*p[c]+vmax*(d[0]-d[c]) for c in range(5))) for p in pre]
            markers = [min(H, *(sum(x*y for x, y in zip(weights, aa))+extra for weights, extra in holes)) for aa in self.a]
            raw = common+sum(n[c]*item['psi'][c]+eta[c]*item['correction'][c] for c in range(5))
            raw += max(source.zero5_common_deep(spec['zero'], item['baseline'][c], d[c]) for c in range(5))
            for position, (positive5, correction, support) in enumerate(branches):
                U = raw+positive[position]
                A = tuple(k[c]*n[c]-correction[c]*eta[c]/5 for c in range(5))
                z = tuple(k[c]*d[c]-correction[c]/5 for c in range(5))
                width = tuple(9*eta[c]*k[c] for c in range(5))
                rest = F(13, 243)*max(z)+F(1, 486)*max(k[c]*d[c] for c in range(5))
                rest += (sum(width)+max(sum(width[:2]), sum(width[2:]))+max(width))/36+max(k)/72
                shift = self.sigma*(max(z[c]+derivative[c]/5 for c in range(5))-z[support])
                center = C*s-U-rest/5
                for j, (root, cell) in enumerate(self.carriers):
                    carrier = sum((A[c] for c in range(5) if ROOT[c] == root), F(0))+(A[cell] if cell >= 0 else F(0))
                    before = center-carrier/5
                    after = before+markers[j]-shift
                    old[j] = before if old[j] is None else min(old[j], before)
                    if new[j] is None or after < new[j]:
                        new[j], controllers[j] = after, (item['baseline'], positive5, support)
        if check_original:
            require(old == self.full.linear_direction(self.engine, dat, index)['conditional'], 'Independent reconstruction of every original old carrier margin')
        return {'old': old, 'new': new, 'gain': tuple(x-y for x, y in zip(new, old)), 'controllers': controllers}


def complete_inner_comparison(base, slab):
    """Aggregate the completed160 inner rectangle; do not repeat any head scan."""
    io = module('slab_consumer_io', base/'certificate_io.py')
    path = 'certificates/source_norms/comparison-bounds/residual_shell_k_comparison.json'
    require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == PINS[path], 'Complete160 source and head certificate')
    previous = json.loads(io.read_artifact_bytes(base/path))
    pins = {path: PINS[path], **previous['source_sha256']}
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin, 'Pinned complete inner input '+name)
    matching = [r for r in previous['shells'] if F(r['parameters']['rho']) == F(1, 20000)]
    require(len(matching) == 1, 'Exactly one existing complete inner rectangle')
    inner = matching[0]
    old, par = inner['comparison'], inner['parameters']
    require(F(par['delta']) == F(1, 27) and F(old['residual_lower']) == 0
            and F(par['rbar']) == F(1, 4000) < R_CUTOFF, 'Same source radius, zero lower residual and valid r range')
    require(F(1, 27)/(4*(1-F(1, 27))) == F(1, 104) < DELTA
            and F(3, 4)+F(1, 108) < F(4, 5), 'Both K orientations lie inside the new actual source slab')
    A, cE, rho = F(53, 360), 1-F(1, 614922), F(1, 20000)
    new_heavy, costs = F(0), []
    for row in slab['heavy_bounds']:
        index = row['index']
        native = next(r for r in inner['heavy']['costs'] if r['index'] == index)
        C, weight, margin, price = (F(row[k]) for k in ('barrier', 'weight', 'margin_lower', 'one_residual_price'))
        require(C == F(native['barrier']) and weight == F(native['weight']), 'Unchanged original barrier and cost weight')
        endpoint = C*A-margin+price*rho
        costs.append({'index': index, 'weight': str(weight), 'endpoint_upper': str(endpoint)})
        new_heavy += weight*endpoint
    weighted_C = sum(F(r['weight'])*F(r['barrier']) for r in slab['heavy_bounds'])
    require(weighted_C == F(inner['heavy']['weighted_barrier']), 'The heavy coefficient of actual S is unchanged')
    groups = {k: F(v) for k, v in old['cost_groups'].items()}
    old_heavy = groups.pop('heavy2_at_both_mass_floors')
    groups['heavy2_fixed_support'] = new_heavy
    endpoint = F(old['signed_endpoint'])-old_heavy+new_heavy
    denominator, coefficient, offset = (F(old[k]) for k in ('denominator_at_mass_floor', 'mass_coefficient', 'offset'))
    require(denominator > 0 and endpoint > 0, 'The existing complete actual denominator remains positive')
    target = offset+endpoint/denominator
    remaining = (target-offset)*cE-coefficient
    require(remaining > 0 and (target-offset)*denominator == endpoint and target < F(old['comparison_upper']) < 509,
            'Complete signed comparison with actual S and without the old favorable s term')
    require(old['all_original_indices'] == list(range(52)), 'Every original52 test retained exactly once')
    return {'source_sha256': pins, 'source_radius': '1/27', 'residual_radius': str(rho),
            'slot_loss_radius': par['rbar'], 'Delta_upper': '1/104', 'costs': costs,
            'cost_groups': {k: str(v) for k, v in groups.items()},
            'previous_heavy_endpoint': str(old_heavy), 'new_heavy_endpoint': str(new_heavy),
            'signed_endpoint': str(endpoint), 'denominator_at_mass_floor': str(denominator),
            'mass_coefficient': str(coefficient), 'raw_s_coefficient': '0', 'offset': str(offset),
            'comparison_upper': str(target), 'remaining_S_coefficient': str(remaining),
            'previous_comparison_upper': old['comparison_upper'], 'all_original_indices': old['all_original_indices'],
            'scope': 'Complete160 inner rectangle with only original heavy0/16 replaced by the proved source-slab bounds. All other50 costs, complete square, actualS coefficient, five denominator objectives and infinite tails are retained. The old favorable raw-s term is discarded. No new head scan or global comparison is asserted.'}


def calculate(base):
    study = Slab(base)
    joint = joint_vertices()
    minima, minimizing, negative_gains = {i: None for i in INDICES}, {i: [] for i in INDICES}, {i: 0 for i in INDICES}
    compact, digest, comparisons = [], sha256(), 0
    for number, (deficit, coordinate, late) in enumerate(product(simplex(5, F(1, 2)), joint, simplex(5, F(1, 72)))):
        alpha, beta, z = coordinate
        parameter = deficit, alpha, beta, late, z
        outputs = {}
        for index in INDICES:
            row = study.evaluate(parameter, index, check_original=(number % 216 == 0))
            comparisons += int(number % 216 == 0)*18
            for j, value in enumerate(row['new']):
                label = {'source': number, 'carrier': study.carriers[j], 'controller': row['controllers'][j]}
                if minima[index] is None or value < minima[index]:
                    minima[index], minimizing[index] = value, [label]
                elif value == minima[index]:
                    minimizing[index].append(label)
                negative_gains[index] += int(row['gain'][j] < 0)
                digest.update((str(number)+':'+str(index)+':'+str(j)+':'+str(value)+';').encode())
            value = min(row['new'])
            outputs[index] = {'minimum_over_carriers': value, 'carriers': [study.carriers[j] for j, x in enumerate(row['new']) if x == value]}
        compact.append({'source': number, 'heavy': outputs})
        if number % 216 == 215:
            print('Fixed-support slab sources: '+str(number+1)+'/1296', flush=True)
    require(number+1 == 1296 and comparisons == 216, 'Complete1296 new source generators and independent old-carrier checks')
    canonical, bounds = study.engine.parameters[398], []
    for index in INDICES:
        original = study.vector.cost_bound(study.engine, study.broad, study.full, canonical, study.broad.point_carrier(1, 1), index)
        require(minima[index] == original['new_layout_min'] > 0, 'The complete slab absolute minimum equals the original improved canonical face margin')
        _, C, items = study.prepared[index]
        vmax = max(max(row[1]) for row in items)
        P, D = F(2500, 241)*vmax, F(13, 9)*vmax
        require(18*study.sigma < F(13, 9) and 5*D < P, 'One actual residual pays both r transport and the old unresolved mass')
        bounds.append({'index': index, 'weight': study.weights[index], 'barrier': C, 'margin_lower': minima[index],
                       'max_derivative': vmax, 'slot_loss_price': D, 'one_residual_price': P,
                       'minimizers': minimizing[index],
                       'supports': [{'baseline': item['baseline'], 'positive5': pos, 'fixed_z_support': support}
                                    for item, _, _, branches in items for pos, _, support in branches]})
    require(F(1, 90)-R_CUTOFF == F(241, 22500)
            and F(1, 81)-2*R_CUTOFF > F(241, 22500), 'The complete original slab geometry retains its positive gap')
    untouched = tuple(i for i in range(52) if i not in INDICES)
    require(len(untouched) == 50 and sorted(untouched+INDICES) == list(range(52)), 'Exact complete52 replacement partition')
    weighted = {'barrier': sum(row['weight']*row['barrier'] for row in bounds),
                'margin_lower': sum(row['weight']*row['margin_lower'] for row in bounds),
                'one_residual_price': sum(row['weight']*row['one_residual_price'] for row in bounds)}
    result = study.vector.encode({'schema': 'erdos7-fixed-support-source-slab-v1', 'source_sha256': study.pins,
                                'delta_bound': DELTA, 'z_loss_bound': PMAX, 'slot_loss_strict_cutoff': R_CUTOFF,
                                'joint_source_generators': joint, 'source_factor_sizes': (6, 36, 6),
                                'source_points': 1296, 'carriers': study.carriers,
                                'branch_carrier_evaluations': 2*1296*100*18, 'old_carrier_reconstruction_checks': comparisons,
                                'all_new_margin_values_sha256': digest.hexdigest(), 'source_minima': compact,
                                'heavy_bounds': bounds, 'negative_gain_points': negative_gains,
                                'weighted_heavy_replacement': weighted, 'unchanged_original_indices': untouched,
                                'scope': 'Ordinary fixed-support continuum theorem on the original actual source slab and first-beta face, using a containing6x36x6 product and all18 carriers. Both heavy absolute margins attain their positive lower bounds at canonical398. The carrier mixture is actual and every original test/tail remains. The complete local160 inner comparison is strengthened; a full comparison on the entire new slab remains open. No positive gain relative to each old margin, actual-family attainment at slab generators, globalK improvement, Lean theorem or unrestricted Erdos7 conclusion.'})
    result['complete_inner_comparison'] = complete_inner_comparison(base, result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    modes.add_argument('--check-inner', action='store_true', help='Reconstruct only the complete local consumer from the stored slab certificate; do not replay the slab scan')
    args = parser.parse_args()
    io = module('slab_writer', args.base/'certificate_io.py')
    if args.check_inner:
        result = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))
        for path, pin in result['source_sha256'].items():
            require(sha256(io.read_artifact_bytes(args.base/path)).hexdigest() == pin, 'Pinned slab input '+path)
        require(result['complete_inner_comparison'] == complete_inner_comparison(args.base, result), 'Exact complete consumer from the previously verified slab scan')
        print('PASS: complete inner52 comparison reconstructed; the original slab scan was not replayed.')
        return
    result = calculate(args.base)
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact fixed-support source slab certificate')
    print('PASS: both heavy margins retain their face floor on the broad source slab; the complete inner52 comparison improves.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
