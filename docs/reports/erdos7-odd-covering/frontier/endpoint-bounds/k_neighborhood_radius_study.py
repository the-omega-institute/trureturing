#!/usr/bin/env python3
"""Expand the actual K rectangle using the global mass floor and coupled costs."""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/k_neighborhood_radius_study.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/comparison-bounds/uniform_complete_k_comparison.py': '75db40896f9a0fb1d7cd6ee17f6f8b7af5ef4c2bf074811b6df8ca3327809fd3',
    'certificates/source_norms/comparison-bounds/uniform_complete_k_comparison.json': '0df6d4d58c94097993ac4f424d6c11a4be3197f483f5a61ad6bf840abf2af4ad',
    'frontier/source-budgets/carrier_mass_residual_bound.py': 'b455566fe256dac370d3afb97c6e357d2c75296a2e36f483e6f189fda436141c',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def global_mass_floor(source, mass):
    """All five product-simplex factors and all18 full/partial carriers."""
    histogram, witnesses, digest = Counter(), [], sha256()
    count = 0
    for index, parameter in enumerate(source.vertices()):
        d, n, eta, s, _ = source.data(parameter)
        widths = tuple(9*v for v in eta)
        R = mass.nonshallow(d, widths)
        aa, bb = tuple(2*v for v in widths), tuple(4*v for v in d)
        ell = tuple(72*v for v in parameter[3])
        require(all(x.denominator == 1 for x in aa+bb+ell), 'Integer vertex coordinates')
        aa, bb, ell = tuple(map(int, aa)), tuple(map(int, bb)), tuple(map(int, ell))
        nn = tuple(a*b-l for a, b, l in zip(aa, bb, ell))
        rr = max(bb)+sum(aa)+max(sum(aa[:2]), sum(aa[2:]))+max(aa)+1
        require(tuple(F(v, 72) for v in nn) == n and F(rr, 72) == R,
                'Independent integer reconstruction of every full source term')
        for carrier in mass.CARRIERS:
            score = mass.weights(carrier)
            integer = 5*sum(nn)-sum(a*b for a, b in zip(score, nn))-rr
            direct = s-(sum(a*b for a, b in zip(score, n))+R)/5
            require(F(integer, 360) == direct >= F(53, 360), 'Every complete carrier mass is at least53/360')
            histogram[integer] += 1
            count += 1
            digest.update((str(index)+':'+str(carrier)+':'+str(integer)+';').encode())
            if integer == 53:
                witnesses.append({'vertex': index, 'carrier': carrier})
    require(index+1 == 1296 and count == 23328 and len(witnesses) == 20,
            'The complete five-factor product and all18 carriers')
    return {'source_factor_sizes': (6, 3, 6, 6, 2), 'source_vertices': 1296,
            'carriers': mass.CARRIERS, 'joint_entries': count, 'integer_scale': 360,
            'minimum_integer': min(histogram), 'minimum_S0': F(53, 360),
            'mass_histogram': dict(sorted(histogram.items())), 'minimizers': witnesses,
            'all_vertex_carrier_masses_sha256': digest.hexdigest(),
            'continuum_bridge': 'Dc is concave in each of the five factors separately and linear in the actual carrier mixture. Iterated Jensen on the containing product domain gives S0>=53/360; S=S0+rho. No joint concavity, product law for actual source randomness, vertex realizability or final AP-denominator floor is asserted.'}


class Study:
    def __init__(self, base):
        self.base, self.modules = base, {}
        self.io = module('radius_io', base/'certificate_io.py')
        require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
        self.pins = dict(PINS)
        prior = self.read('uniform_complete_k_comparison')
        self.pins.update(prior['source_sha256'])
        for path, pin in self.pins.items():
            require(sha256(self.io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
        self.old = self.read('whole_quadratic_same_head')
        self.mean_prior = self.read('uniform_mean_cost_portfolio')
        self.den_prior = self.read('uniform_ap_survival_denominator')
        self.simple_prior = self.read('uniform_single_hinge_cost_portfolio')
        self.heavy_prior = self.read('uniform_heavy_vector_neighborhood')
        self.engine = self.get('source_barrier_saturation').Experiment(base)
        self.source = self.engine.source
        self.uniform = self.get('uniform_k_neighborhood_cost')
        self.denominator = self.get('uniform_ap_survival_denominator')
        self.quadratic = self.get('uniform_quadratic_cost_portfolio')
        self.heavy = self.get('uniform_heavy_vector_neighborhood')
        self.square = self.get('uniform_square_and_raw81_neighborhood')
        self.factorial = self.get('complete_off_face_factorial_tail')
        self.tails = self.get('complete_off_face_omitted_tails')
        self.mass = self.get('carrier_mass_residual_bound')
        self.weights = tuple(map(F, self.old['cost_weights']))

    def read(self, name):
        return json.loads(self.io.read_artifact_bytes(self.io.named_artifact(self.base/'certificates/source_norms', name+'.json')))

    def get(self, name):
        if name not in self.modules:
            self.modules[name] = module('radius_'+name, self.io.named_artifact(self.base/'frontier', name+'.py'))
        return self.modules[name]

    def heavy_bounds(self, delta, rho):
        outputs = []
        for index, face in zip((0, 16), self.heavy_prior['radii'][0]['results']):
            row = self.heavy.branch_bounds(self.engine, self.quadratic, self.uniform, index, delta, rho)
            full, zero = row['raw_complete_prices'], row['raw_zero_prices']
            spec = self.engine.specs[index]
            require(spec['zero'] == ('seven_block', (spec['tag'], 0)), 'The same original e0 block cancels')
            first = full['finite_seven_blocks'][0]
            names = ('mass_L1', 'pure_L1', 'availability_Linfinity')
            require(all(first[k] == zero[k] and full[k] >= zero[k] for k in names),
                    'Exact common-block price cancellation with positive remaining prices')
            mass_save = 9*row['barrier']*delta/10
            common_save = 2*self.heavy.raw_price(zero, delta/2, delta/9, 3*delta/4)
            old_excess = row['barrier']*(5*delta/9+rho)+row['uniform_margin_error']
            new_excess = old_excess-mass_save-common_save
            require(new_excess >= 0, 'Retained source errors and one residual price remain nonnegative')
            outputs.append({'index': index, 'weight': self.weights[index], 'face_upper': F(face['face_upper']),
                            'old_excess': old_excess, 'coupled_mass_saving': mass_save,
                            'common_block_saving': common_save, 'uniform_excess': new_excess,
                            'uniform_upper': F(face['face_upper'])+new_excess,
                            'branch_transport': row,
                            'coupled_mass_source_price': F(7, 45),
                            'common_prices': {k: full[k]-zero[k] for k in names}})
        return {'costs': outputs, 'weighted_upper': sum(r['weight']*r['uniform_upper'] for r in outputs),
                'weighted_excess': sum(r['weight']*r['uniform_excess'] for r in outputs),
                'old_weighted_excess': sum(r['weight']*r['old_excess'] for r in outputs)}

    def scalar_result(self, delta, rho):
        par = self.uniform.parameters(delta, rho)
        H1 = self.denominator.uniform_H1(par)
        square = self.square.uniform_square(par, self.denominator, self.factorial, self.tails)
        heavy = self.heavy_bounds(delta, rho)
        one = self.simple_prior['radii'][0]['weighted_coefficients']
        H1_payment = F(one['H1'])*H1['excess']
        square_payment = F(self.old['complete_square_weight'])*square['square_excess']
        return {'delta': delta, 'rho': rho, 'H1_upper': H1['upper'], 'H1_single_portfolio_excess': H1_payment,
                'square_upper': square['full_square_upper'], 'square_payment_excess': square_payment,
                'old_mass_denominator_loss': (1-F(1, 614922))*101*delta/180,
                'heavy_weighted_excess_before_cancellation': heavy['old_weighted_excess'],
                'heavy_weighted_excess_after_cancellation': heavy['weighted_excess']}

    def complete_radius(self, delta, rho, denominator_only=False):
        u, co, fi, ca, af, me = (self.get(n) for n in ('uniform_k_neighborhood_cost', 'complete_off_face_cost',
                'finite_source_face_transport', 'broad_weighted_identity_source', 'shared_budget_affine_tail', 'joint_deep_mean_transport'))
        portfolio = self.get('uniform_mean_cost_portfolio')
        par = u.parameters(delta, rho)
        face = co.face_case(fi, self.source)
        point, _ = u.enlarged_point(face['point'], par)
        mean_rows = u.mean_rows(me, fi.prepare({1: F(1)}), face, par)
        qvertices = fi.defect_vertices(par['gap'], par['gap'], rho)
        eps = (par['kbar']*rho, rho+delta/240, rho, rho)
        cut = tuple(u.crossing(p, b, H, e) for p, b, H, e in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], eps))
        cuts = sorted(set((cut, (10,)*4, (12,)*4)))
        cache = {}

        def bound(coefficients):
            coeff = {int(k): F(v) for k, v in coefficients.items()}
            key = tuple(sorted(coeff.items()))
            if key not in cache:
                record = fi.prepare(coeff)
                a1 = coeff.get(1, F(0))
                rows = tuple((layout, a1*reference, tuple(a1*p for p in prices)) for layout, reference, prices in mean_rows)
                vertices = [u.exhaustive_vertex(co, fi, ca, record, face, point, par, rows, q) for q in qvertices]
                supports = [u.apply_support(record, par, u.fixed_tail(af, record, par, c), vertices) for c in cuts]
                cache[key] = {'coefficients': coeff, 'exhaustive_vertices': vertices,
                              'selected_support': min(supports, key=lambda s: s['upper'])}
                print('Radius '+str(delta)+' complete hinge '+str(len(cache))+': '+str(float(cache[key]['selected_support']['upper'])), flush=True)
            return cache[key]

        den_rows = [{**bound(r['coefficients']), 'weight': F(r['weight']), 'name': r['name']}
                    for r in self.den_prior['cost_results']]
        den_shared = portfolio.shared_maximum(den_rows)
        H1 = self.denominator.uniform_H1(par)
        d = (1-F(1, 614922))*F(53, 360)-den_shared['upper']-H1['upper']/F(55902)
        d_old = d-(1-F(1, 614922))*101*delta/180
        print('Radius '+str(delta)+' full denominator '+str(float(d))+'; prior mass version '+str(float(d_old)), flush=True)
        if denominator_only:
            require(d > 0, 'Positive denominator for the numerical-envelope obstruction')
            scalar = self.scalar_result(delta, rho)
            one = self.simple_prior['radii'][0]['weighted_coefficients']
            raw46_extra = self.weights[46]*F(7726415908741, 7564571872200)*delta
            raw47_extra = self.weights[47]*F(25207, 6480)*delta
            additions = {'heavy2': scalar['heavy_weighted_excess_after_cancellation'],
                         'H1_single': scalar['H1_single_portfolio_excess'],
                         'positive_mass_single': F(one['mass'])*(5*delta/9+rho),
                         'square': scalar['square_payment_excess'],
                         'raw81_first': raw46_extra, 'raw81_second': raw47_extra}
            Nfloor = F(self.old['numerator_upper'])+sum(additions.values())
            floor = F(self.old['offset'])+Nfloor/d
            return {'mode': 'fixed-envelope obstruction, not an actual-source lower bound',
                    'delta': delta, 'rho_radius': rho, 'parameters': par, 'mass_lower': F(53, 360),
                    'denominator_lower': d, 'denominator_shared_cost': den_shared, 'denominator_costs': den_rows,
                    'H1': H1, 'retained_numerator_excess': additions, 'optimistic_numerator': Nfloor,
                    'omitted_nonnegative_envelope_excesses': ('mean11', 'H2_single', 'joint_quadratic9'),
                    'fixed_envelope_comparison_lower': floor, 'target': F(509),
                    'proves_fixed_envelope_failure': floor > 509,
                    'original_head_evaluations': sum(v['original_head_evaluations'] for row in cache.values() for v in row['exhaustive_vertices'])}
        mean_jobs = [{**bound(r['coefficients']), 'weight': F(r['weight']), 'index': r['index']}
                     for r in self.mean_prior['cost_results']]
        mean_shared = portfolio.shared_maximum(mean_jobs)
        H2 = bound({2: F(1)})
        simple = self.simple_prior['radii'][0]
        S_upper = F(53, 360)+5*delta/9+rho
        simple_rows = [{'index': r['index'], 'weight': F(r['weight']),
                        'upper': F(r['at_one'])*S_upper+F(r['first_difference'])*H1['upper']
                                 +F(r['second_curvature'])*H2['selected_support']['upper']}
                       for r in simple['cost_results']]
        simple_upper = sum(r['weight']*r['upper'] for r in simple_rows)
        prior = self.get('complete_off_face_quadratic_cost')
        targets = prior.prepare_rows(self.source, self.get('whole_quadratic_same_head'), self.old, self.quadratic.INDICES)
        modules = (u, co, fi, ca, af, me, self.source, self.factorial, self.tails,
                   self.get('uniform_factorial_neighborhood'), portfolio)
        quad = self.quadratic.radius_result(self.base, delta, rho, modules, self.old, targets)
        heavy = self.heavy_bounds(delta, rho)
        square = self.square.uniform_square(par, self.denominator, self.factorial, self.tails)
        raw81 = self.square.retained_raw81(self.source, self.quadratic, self.old, self.read('k_face_complete_ratio'), delta)
        groups = {'mean11': mean_shared['upper'], 'single28': simple_upper,
                  'quadratic10': quad['shared_portfolio']['upper'], 'heavy2': heavy['weighted_upper'],
                  'raw81_first': raw81['outside_weight']*raw81['uniform_upper']}
        indices = [r['index'] for r in mean_jobs]+[r['index'] for r in simple_rows]
        indices += list(self.quadratic.INDICES)+[0, 16, 46]
        require(sorted(indices) == list(range(52)), 'Exactly the original52 independent cost labels')
        signed, square_weight, offset = map(F, (self.old['signed_mass_coefficient'], self.old['complete_square_weight'], self.old['offset']))
        require(signed < 0 < square_weight and d > 0, 'Correct actual-mass sign and positive division')
        N = signed*F(53, 360)+sum(groups.values())+square_weight*square['full_square_upper']
        require(N > 0, 'A positive complete numerator upper')
        upper = offset+N/d
        branch_count = sum(v['original_head_evaluations'] for row in cache.values() for v in row['exhaustive_vertices'])+quad['original_branch_evaluations']
        return {'delta': delta, 'rho_radius': rho, 'slot_bound': F(1, 520), 'parameters': par,
                'mass_lower': F(53, 360), 'mass_upper': S_upper, 'denominator_lower': d,
                'prior_mass_denominator_lower': d_old, 'denominator_shared_cost': den_shared,
                'denominator_costs': den_rows, 'H1': H1, 'H2': H2,
                'mean_costs': mean_jobs, 'mean_shared': mean_shared, 'simple_rows': simple_rows,
                'quadratic': quad, 'heavy': heavy, 'square': square, 'raw81_first': raw81,
                'cost_group_sums': groups, 'signed_mass_upper': signed*F(53, 360),
                'square_payment': square_weight*square['full_square_upper'], 'numerator_upper': N,
                'offset': offset, 'comparison_upper': upper, 'target': F(509),
                'target_margin': 509-upper, 'certifies_target': upper <= 509,
                'original_head_evaluations': branch_count,
                'independent_rational_comparisons': sum(v['rational_comparisons'] for row in cache.values() for v in row['exhaustive_vertices'])+quad['independent_rational_checks']}


def calculate(base, delta, denominator_only=False):
    study = Study(base)
    floor = global_mass_floor(study.source, study.mass)
    sensitivity = [study.scalar_result(F(d), F(1, 100000))
                   for d in ('1/10000', '1/1000', '1/200', '1/100', '1/50', '1/27')]
    full = study.complete_radius(delta, F(1, 100000), denominator_only)
    return study.uniform.encode({'schema': 'erdos7-k-neighborhood-radius-study-v1', 'source_sha256': study.pins,
                                  'global_mass_floor': floor, 'scalar_sensitivity': sensitivity,
                                  'complete_radius': full,
                                  'scope': 'Ordinary global lower bound for the complete actual carrier mass S0, plus exact cancellation of common source terms in142 and a source-uniform expanded K rectangle. All source factors,18 carriers,52 original costs and complete exponent/count tails retained. Actual packing is a subset of the source product relaxation; vertices need not be realizable. No joint-concavity assertion, new global K, Lean or unrestricted Erdos7 result.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--delta', type=F, default=F(1, 100))
    parser.add_argument('--denominator-only', action='store_true')
    parser.add_argument('--output', type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base, args.delta, args.denominator_only)
    io = module('radius_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.output or args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.output or args.base/CERTIFICATE)) == result, 'Exact expanded-radius certificate')
    row = result['complete_radius']
    if args.denominator_only:
        print('PASS: fixed-envelope comparison lower '+row['fixed_envelope_comparison_lower'])
        print('Fixed-envelope failure: '+str(row['proves_fixed_envelope_failure']))
    else:
        print('PASS: complete radius '+str(args.delta)+'; comparison '+row['comparison_upper'])
        print('Below509: '+str(row['certifies_target']))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
