#!/usr/bin/env python3
"""Use the actual six-loss budget and both source masses in one signed comparison."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/shared_loss_signed_k_comparison.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/k_neighborhood_radius_study.py': '41cbad92bacf1cd7b573afb48ecc0811fc0df05fe9a56cfa274d3f4fbb175682',
    'certificates/source_norms/k_neighborhood_radius_1_50.json': '2da786ff4bec608fadd903f038891fa813dd75e37e00e41f4316ff7c46cf27ff',
    'certificates/source_norms/k_neighborhood_radius_obstruction_1_27.json': '2bb8a9e3069f1393c1d0e03a639751570df9e6da743dc44182539a2db005024d',
    'frontier/joint_concentration_loss_budget.py': '41dd03ec2ced1cd33643f2e2955ded85dd2113b633f72f9d5954d6862c2e8fa2',
    'certificates/source_norms/joint_concentration_loss_budget.json': '1e8795d2380b186d40a9f4c866bbb5698db269c2055b9159a0d183584f05d725',
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


def norm_budget(delta, budget):
    require(0 <= delta < F(1, 2), 'The actual distinguished orientation exists')
    n_prices = budget.norm_prices(1, 0, 0)
    require(max(n_prices) == F(1, 6), 'The largest original source-norm coefficient')
    shared = budget.total_loss_upper(delta)
    return {'loss_order': budget.ORDER,
            'source_mass_prices': n_prices, 'shared_loss_upper': shared,
            **budget.norm_bounds(delta)}


def heavy_bounds(study, delta, rho):
    """Bound G in each original margin C*s+G; never charge C*s separately."""
    par = study.uniform.parameters(delta, rho)
    norms = norm_budget(delta, study.get('joint_concentration_loss_budget'))
    n, eta, availability = (norms[k] for k in ('mass_L1', 'pure_L1', 'availability_Linfinity'))
    require(par['rbar'] < F(1, 2500) and availability <= F(1, 18), 'Original91 source domain')
    sig = study.heavy.SIGMA
    hplus = F(1, 2)+delta/18
    cap_growth = delta/90+par['v0']/6+par['v1']/3
    budget_growth = sum(par['budget_increments'])+delta/45+3*par['rbar']
    marker_non_H = 14*delta/225+2*sig*availability+cap_growth+budget_growth+16*delta*hplus/135
    marker_H = 2*delta/225+sig*(18*par['rbar']+2*availability)
    outputs = []
    for index, face in zip((0, 16), study.heavy_prior['radii'][0]['results']):
        spec = study.engine.specs[index]
        C = F(study.engine.thresholds[index]['constant'])
        zero = study.quadratic.raw35_lipschitz(study.source, spec['zero'])
        full = study.quadratic.raw_source_lipschitz(study.source, spec['tag'])
        names = ('mass_L1', 'pure_L1', 'availability_Linfinity')
        require(spec['zero'] == ('seven_block', (spec['tag'], 0)) and
                all(full['finite_seven_blocks'][0][k] == zero[k] <= full[k] for k in names),
                'The complete identical zero-seven block cancels once')
        remaining = {k: full[k]-zero[k] for k in names}
        common = study.heavy.raw_price(remaining, n, eta, availability)
        branches = []
        for item in spec['layouts']:
            baseline = item['baseline']
            values = tuple(study.source.zero5_cost(spec['tag'], v) for v in baseline)
            derivative = tuple(study.source.zero5_cost(spec['tag'], v+1)-study.source.zero5_cost(spec['tag'], v)
                               for v in baseline)
            v, k = max(derivative), max(C-value for value in values)
            require(min(derivative) >= 0 and all(0 <= C-value <= k for value in values),
                    'Original nonnegative branch derivatives and deficits')
            for c5 in study.source.BASES:
                correction = max(a*b for a, b in zip(derivative, c5))
                score = 2*delta*(k/4+correction/10)+2*(k*n+correction*eta/5)
                rest = k*availability/18+3*k*eta/4
                old_G = (common+max(map(abs, item['psi']))*n
                         +max(map(abs, item['correction']))*eta
                         +zero['availability_Linfinity']*availability
                         +zero['positive_five_pure_price']*eta+(score+rest)/5)
                marker = v*max(marker_non_H, marker_H)
                deep = 2*sig*k*availability
                residual_coefficient = max(v, hplus*v/(5*F(241, 22500)))
                error = old_G+marker+deep+residual_coefficient*rho
                branches.append({'baseline': baseline, 'positive_five_baseline': c5,
                                 'old_G_error': old_G, 'marker_error': marker,
                                 'selected_deep_shift_error': deep,
                                 'residual_coefficient': residual_coefficient,
                                 'residual_error': residual_coefficient*rho, 'G_error': error})
        require(len(branches) == 100, 'All original100 branches of each heavy cost')
        upper = max(b['G_error'] for b in branches)
        outputs.append({'index': index, 'weight': study.weights[index], 'barrier': C,
                        'face_upper': F(face['face_upper']), 'remaining_raw_prices': remaining,
                        'branches': branches, 'uniform_G_error': upper})
    return {'norms': norms, 'costs': outputs,
            'weighted_G_error': sum(r['weight']*r['uniform_G_error'] for r in outputs),
            'weighted_barrier': sum(r['weight']*r['barrier'] for r in outputs)}


def comparison(study, prior, complete):
    delta, rho = F(prior['delta']), F(prior['rho_radius'])
    heavy = heavy_bounds(study, delta, rho)
    a, sstar, cE = F(53, 360), F(1, 4), 1-F(1, 614922)
    cS, cQ, offset = map(F, (study.old['signed_mass_coefficient'], study.old['complete_square_weight'], study.old['offset']))
    w40, CH = study.weights[40], heavy['weighted_barrier']
    row40 = [r for r in study.simple_prior['radii'][0]['cost_results'] if r['index'] == 40]
    require(len(row40) == 1 and tuple(F(row40[0][k]) for k in ('at_one', 'first_difference', 'second_curvature')) == (1, 1, 0),
            'Original row40 is exactly S+H1')
    one = study.simple_prior['radii'][0]['weighted_coefficients']
    require(F(one['mass']) == w40, 'No other single-hinge row has a unit-mass term')
    if complete:
        original = F(prior['numerator_upper'])
        old_excess = F(prior['heavy']['weighted_excess'])
        unit_mass = F(prior['mass_upper'])-a
        indices = [r['index'] for r in prior['mean_costs']]+[r['index'] for r in prior['simple_rows']]
        indices += list(study.quadratic.INDICES)+[0, 16, 46]
        require(sorted(indices) == list(range(52)), 'Exactly the unchanged original52 cost labels')
        square = prior['square']
        require(F(square['mass_upper']) == a+unit_mass and
                F(square['zero7_pair_upper']) == F(square['mass_upper'])
                +sum(F(r['weighted_upper']) for r in square['bounded_cylinders'])
                +sum(F(r['upper']) for r in square['complete_weighted_tails'])
                +F(square['complete_mixed_pair_sum']), 'The complete square has one exact actual unit-unit mass')
    else:
        original = F(prior['optimistic_numerator'])
        old_excess = F(prior['retained_numerator_excess']['heavy2'])
        unit_mass = 5*delta/9+rho
    # This endpoint is part of a signed target comparison. It is not an
    # unconditional upper bound on the actual original numerator.
    endpoint = original-old_excess+heavy['weighted_G_error']-(w40+cQ)*unit_mass
    d = F(prior['denominator_lower'])
    target = offset+endpoint/d
    coefficient = (target-offset)*cE-cS-CH-w40-cQ
    require(d > 0 and endpoint > 0 and CH > 0 and coefficient >= 0,
            'Positive denominator and both signed source-mass coefficients')
    require(((target-offset)*d-endpoint) == 0, 'Exact signed comparison at the stated endpoint')
    result = {'delta': delta, 'rho_radius': rho, 'complete': complete,
              'heavy': heavy, 'original_scalar_numerator': original,
              'old_heavy_excess': old_excess, 'replacement_G_error': heavy['weighted_G_error'],
              'unit_mass_saving': (w40+cQ)*unit_mass, 'signed_endpoint': endpoint,
              'denominator_lower': d, 'offset': offset, 'comparison_value': target,
              'remaining_S_coefficient': coefficient, 'raw_s_coefficient': CH,
              'mass_floor': a, 'raw_mass_floor': sstar, 'target': F(509),
              'below_target': target <= 509,
              'meaning': 'Complete source-uniform signed comparison' if complete else
                         'Optimistic incomplete envelope only; the named omitted positive increments remain unpaid'}
    if not complete:
        result['omitted_nonnegative_envelope_excesses'] = prior['omitted_nonnegative_envelope_excesses']
        result['still_proves_fixed_envelope_failure'] = target > 509
    return result


def actual_source_checks(study, comparison_row):
    delta, rho = comparison_row['delta'], comparison_row['rho_radius']
    heavy = comparison_row['heavy']
    norms = heavy['norms']
    vector, broad, full, finite, complete = (study.get(n) for n in
        ('vector_marked_source', 'broad_weighted_identity_source', 'full_linear_carrier_frontier',
         'finite_source_face_transport', 'complete_off_face_cost'))
    outputs = []
    for height in (12, 15):
        actual = complete.actual_398_case(finite, study.source, height)
        projected = study.heavy.project(actual['parameter'], 2)
        star = study.source.data(projected)
        n = sum(abs(a-b) for a, b in zip(actual['dat'][1], star[1]))
        eta = sum(abs(a-b) for a, b in zip(actual['dat'][2], star[2]))
        availability = max(abs(a-b) for a, b in zip(actual['dat'][0], star[0]))
        require(n <= norms['mass_L1'] and eta <= norms['pure_L1']
                and availability <= norms['availability_Linfinity'] and actual['defects']['rho'] <= rho,
                'Actual finite source satisfies the improved source-norm bounds')
        for row in heavy['costs']:
            index, C = row['index'], row['barrier']
            current = vector.cost_bound(study.engine, broad, full, actual['parameter'], actual['pi'], index,
                                        r=actual['point']['r'], partitions=('three_groups',), details=True)
            reference = vector.cost_bound(study.engine, broad, full, projected, broad.point_carrier(1, 1), index,
                                          partitions=('three_groups',), details=True)
            require('all_branches' in current and 'all_branches' in reference, 'Original91 actual source domain')
            slacks = []
            for a, b, price in zip(current['all_branches'], reference['all_branches'], row['branches']):
                require(a['b'] == b['b'] == price['baseline'] and
                        a['c5'] == b['c5'] == price['positive_five_baseline'], 'Same original branch labels')
                slack = (a['new_branch']-b['new_branch']-C*(actual['dat'][3]-star[3])
                         +price['G_error']-price['residual_error'])
                require(slack >= 0, 'The improved G transport bounds the complete actual original branch')
                slacks.append(slack)
            require(len(slacks) == 100, 'Every branch at each actual source')
            outputs.append({'height': height, 'index': index, 'delta': delta, 'rho_radius': rho,
                            'mass_L1': n, 'pure_L1': eta, 'availability_Linfinity': availability,
                            'branches': len(slacks), 'minimum_G_transport_slack': min(slacks)})
    return outputs


def calculate(base):
    io = module('shared_loss_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    old = module('shared_loss_radius', base/'frontier/k_neighborhood_radius_study.py')
    study = old.Study(base)
    budget = study.get('joint_concentration_loss_budget')
    budget_certificate = budget.calculate(base)
    require(budget_certificate == study.read('joint_concentration_loss_budget'), 'Exact153 common-loss certificate')
    pins = {**study.pins, **PINS}
    mass_floor = ((F(3, 4)*F(9, 2)-F(1, 4)*3-F(1, 4))/9-F(1, 72))
    require(mass_floor == F(1, 4), 'The direct global source-mass inequality')
    zero = heavy_bounds(study, F(0), F(0))
    require(zero['weighted_G_error'] == 0, 'Exact recovery of the adopted whole-face heavy bounds')
    outputs = []
    for name, complete in (('k_neighborhood_radius_1_50', True), ('k_neighborhood_radius_obstruction_1_27', False)):
        prior = study.read(name)
        require(prior['source_sha256'] == study.pins, 'Exactly the certified146 source closure')
        row = comparison(study, prior['complete_radius'], complete)
        row['input_certificate'] = 'certificates/source_norms/'+name+'.json'
        outputs.append(row)
    actual_checks = actual_source_checks(study, outputs[0])
    return study.uniform.encode({'schema': 'erdos7-shared-loss-signed-k-comparison-v1',
                                  'source_sha256': pins, 'global_raw_mass_floor': mass_floor,
                                  'zero_radius': zero, 'comparisons': outputs, 'actual_source_checks': actual_checks,
                                  'scope': 'Ordinary continuous-source proof with exact rational evaluation. The complete1/50 rectangle retains all52 original costs, all five denominator objectives and every original infinite tail. The1/27 calculation retains the explicit unpaid positive groups and gives no full comparison there. One actual residual budget is retained. No new global K, Lean theorem, or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('shared_loss_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact shared-loss signed certificate')
    for row in result['comparisons']:
        print('PASS: delta '+row['delta']+' complete='+str(row['complete'])+' comparison '+row['comparison_value'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
