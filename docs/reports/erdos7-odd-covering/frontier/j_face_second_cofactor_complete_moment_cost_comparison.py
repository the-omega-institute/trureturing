#!/usr/bin/env python3
"""Complete J comparison with the stronger second-depth cofactor survival hinge."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j_face_second_cofactor_complete_moment_cost_comparison.json'
PINS = {'frontier/j_face_pure_low_factorial_complete_moment_cost_comparison.py': '2af29e5b06f04ca067dc55308cccf181bf4e406c4fc5fa5fe7225f9d6a125242', 'certificates/source_norms/j_face_pure_low_factorial_complete_moment_cost_comparison.json': '9d528978ef1852d85efa83d65a0f9625bd5f240a34c6e4e619ce722cd13b9631', 'profile-notes/279-two-pure-factorial-observations-improve-the-complete-j-comparison.md': '78f43efacce63938b6e31ce62753e100934b0172bcb0634239c879b5ab6c0cfc', 'frontier/j_face_second_cofactor_survival_heads.py': '5afa46194762b28ea122034671e55c7abf49d0ddf67b6c2ed2a76a53c9933ed1', 'certificates/source_norms/j_face_second_cofactor_survival_heads.json': 'f87f6d83aec7ce23ad29fb4b48a0e24a8d606068465bfe2ffb11b5ddc94ee019', 'profile-notes/280-second-depth-cofactors-sharpen-the-complete-j-survival-hinge.md': '330935ce7557f355610b8c9ffa8fa6dce7d6066f95dbb85de2c76f5b83235571'}
MASS, TAIL_ENTRANCE = F(3, 20), 9


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable existing mathematical provider')
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


def inputs(base):
    require(PINS,'Final mathematical input pins')
    prior=module('second_cofactor_comparison279',base/'frontier/j_face_pure_low_factorial_complete_moment_cost_comparison.py')
    data=prior.inputs(base);previous,io=data['previous'],data['io']
    read=lambda name:json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                               object_pairs_hook=previous.unique)
    old=read('j_face_pure_low_factorial_complete_moment_cost_comparison')
    heads=read('j_face_second_cofactor_survival_heads')
    pins=dict(data['pins'])
    for source in(old,heads):
        require(source['geometry']==data['geometry'] and F(source['survivor_mass'])==MASS,
                'The same complete actual saturated J domain and survivor mass')
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent current source closure '+path);pins[path]=pin
    for path,pin in PINS.items():
        require(path not in pins or pins[path]==pin,'Consistent direct mathematical input '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical source '+path)
    names,functions,polynomials,bounds=(list(data[k])for k in('names','functions','polynomials','bounds'))
    require([r['name']for r in old['basis']]==names and [F(r['upper'])for r in old['basis']]==bounds
            and len(names)==28 and old['all_original_indices']==list(range(52)),
            'The exact final279 baseline retains all28 observations and all52 original costs')
    pos=names.index('hinge4');previous_bound=bounds[pos];upper=F(heads['complete_AP13_upper'])
    require(F(heads['source_mass'])==F(1,4)
            and heads['retained_positive7_labels']==[21,35,63,105,147,245,441,735]
            and heads['new_original_labels']==[441,735]
            and heads['removed_original_positive7_caps']=={'441':'1/490','735':'2/1225'}
            and F(heads['complete_positive7_tail'])==F(13,490)
            and F(13,490)+F(1,490)+F(2,1225)==F(37,1225)
            and F(heads['complete_zero7_affine_remainder'])==F(2471,81000)
            and F(heads['complete_zero7_joint_remainder'])==F(7951,405000)
            and F(heads['previous_complete_AP13_upper'])==previous_bound
            and F(heads['improvement_over_previous'])==previous_bound-upper>0,
            'Only assigned441/735 cap-series terms are replaced; all complete complementary tails remain')
    require(len(heads['results'])==1,'Only the original AP13 observation is strengthened')
    row=heads['results'][0];scan=row['scan'];c=scan['counts']
    require(row['name']=='AP13' and row['index']=='AP13' and row['coefficients']=={'4':'1'}
            and F(row['at_one'])==0 and F(row['complete_head_upper'])==F(row['adopted_upper'])==upper
            and F(row['previous_adopted_upper'])==previous_bound
            and F(row['improvement_over_previous'])==previous_bound-upper
            and polynomials[pos]==(F(-4),F(1),F(0))
            and all(functions[pos](n)==max(n-4,0)for n in range(1,TAIL_ENTRANCE)),
            'The same entire original positive-integer hinge H4, with its full linear continuation')
    two=sum(c[k]for k in('two_old_bounded','two_enhanced_bounded'))
    four=sum(c[k]for k in('four_old_bounded','four_enhanced_bounded'))
    six=sum(c[k]for k in('six_old_bounded','six_enhanced_bounded','six_known_dual_bounded'))
    covered=25000*two+500*four+50*six+10*c['seven_bounded']+c['eight_bounded']+c['seed_bounded']+c['lp_remaining']
    require(c['layouts']==12500 and c['two_seen']==125000
            and c['four_seen']==50*(c['two_seen']-two)
            and c['six_seen']==10*(c['four_seen']-four)
            and c['seven_seen']==5*(c['six_seen']-six)
            and c['eight_seen']==10*(c['seven_seen']-c['seven_bounded'])
            and c['lp_remaining']==0 and covered==3125000000
            and scan['covered_containing_choices']==heads['total_containing_choices']==covered
            and scan['original_choice_count']==62500000 and scan['new_independent_choices_per_original']==50
            and heads['rational_column_checks']==heads['seed_rational_column_checks']+heads['existing256_rational_column_checks'],
            'Every original choice retains fifty independent new-label completions and no unresolved branch')
    prior_bounds=list(bounds);bounds[pos]=upper
    require(sum(a!=b for a,b in zip(prior_bounds,bounds))==1 and len(names)==28,
            'Only the old hinge4 upper changes among all28 retained observations')
    data.update(pins=pins,names=names,functions=functions,polynomials=polynomials,bounds=bounds,old=old,
                changed_basis_bounds=[{'name':'hinge4','previous_upper':previous_bound,'updated_upper':upper,'source':'280'}],
                added_basis_bounds=[])
    return data


def calculate(base, proof_data):
    data = inputs(base)
    previous = data['previous']
    rational = previous.rational
    names, functions, polynomials, bounds, targets = (data[k] for k in ('names', 'functions', 'polynomials', 'bounds', 'targets'))
    require([row['name'] for row in proof_data] == [target[0] for target in targets], 'All59 original target functions in canonical order')
    old_targets = {row['name']: row for row in data['old']['results']}
    rows = []
    for proof, (name, target, target_polynomial) in zip(proof_data, targets):
        require(set(proof) == {'name', 'coefficients', 'finite_moment_witness'}
                and set(proof['coefficients']) <= set(names), 'Only declared original basis coefficients')
        coefficients = [rational(proof['coefficients'].get(k, '0')) for k in names]
        require(min(coefficients[1:]) >= 0, 'Only the coefficient of exact actual mass may be negative')
        low = [sum(v*f(n) for v, f in zip(coefficients, functions))-target(n) for n in range(1, TAIL_ENTRANCE)]
        tail = tuple(sum(v*p[k] for v, p in zip(coefficients, polynomials))-target_polynomial[k] for k in range(3))
        minimum, loads, values = previous.tail_minimum(tail)
        require(min(low) >= 0 and minimum >= 0, 'Whole-positive-integer envelope for '+name)
        upper = sum(v*b for v, b in zip(coefficients, bounds))
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete279 bound')
        witness = {}
        for key, value in proof['finite_moment_witness'].items():
            n, mass = int(key), rational(value)
            require(str(n) == key and n >= 1 and mass > 0, 'Positive canonical finite moment witness')
            witness[n] = mass
        require(witness and sum(witness.values()) == MASS, 'The independent witness has exact actual mass')
        measured = [sum(m*f(n) for n, m in witness.items()) for f in functions]
        require(measured[0] == bounds[0] and all(a <= b for a, b in zip(measured[1:], bounds[1:])),
                'Every updated moment inequality holds for the independent '+name+' witness')
        lower = sum(m*target(n) for n, m in witness.items())
        require(0 <= lower <= upper, 'Exact weak duality for each independent target')
        rows.append({'name': name, 'upper': upper, 'previous_upper': rational(old_targets[name]['upper']),
                     'independent_moment_lower': lower, 'duality_gap': upper-lower,
                     'low_load_gaps': low, 'tail_gap_polynomial': tail,
                     'tail_test_integers': loads, 'tail_test_values': values, 'tail_minimum': minimum,
                     'witness_moments': dict(zip(names, measured)),
                     'witness_moment_slacks': dict(zip(names, (b-a for a, b in zip(measured, bounds))))})
    by_name = {row['name']: row for row in rows}

    def comparison(field):
        get = lambda name: by_name[name][field]
        blocks = [get('AP11-'+str(i)) for i in range(4)]
        mean, square, hinge4 = (get(k) for k in ('mean', 'square', 'hinge4'))
        count = data['count']
        tail = count['remaining_hinge1_coefficient']*(mean-MASS)+count['whole_constant_coefficient']*MASS
        denominator = MASS-hinge4/6-(sum(blocks)+tail)/7
        payments = [w*get('cost-'+str(i)) for i, w in enumerate(data['weights'])]
        numerator = data['signed']*MASS+sum(payments)+data['outside_square']*square
        require(mean >= MASS and min(blocks) >= 0 and tail >= 0 and numerator > 0 and denominator > 0,
                'Complete numerator and denominator have the signs required by the ratio comparison')
        return {'comparison': data['offset']+numerator/denominator, 'numerator': numerator, 'denominator': denominator,
                'signed_mass_payment': data['signed']*MASS, 'outside_square_payment': data['outside_square']*square,
                'weighted_costs': payments, 'AP11_block_values': blocks, 'mean': mean, 'square': square,
                'hinge4': hinge4, 'complete_count_tail': tail,
                'target403_numerator_margin': (403-data['offset'])*denominator-numerator}

    upper, lower = comparison('upper'), comparison('independent_moment_lower')
    old_comparison = rational(data['old']['comparison_upper']['comparison'])
    gap = upper['comparison']-lower['comparison']
    require(0 <= gap < F(1, 10**10) and upper['comparison'] < old_comparison,
            'The new tight independent-moment bracket strictly improves the complete comparison')
    target403_position = ('below' if upper['comparison'] < 403 else
                          'above' if lower['comparison'] > 403 else 'straddles')
    result = {'schema': 'erdos7-j-face-second-cofactor-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
              'geometry': data['geometry'], 'survivor_mass': MASS, 'all_original_indices': list(range(52)),
              'original_cost_tags': data['tags'], 'cost_weights': data['weights'],
              'signed_mass_coefficient': data['signed'], 'complete_square_weight': data['outside_square'],
              'offset': data['offset'], 'count_law': data['count'], 'changed_basis_bounds': data['changed_basis_bounds'],
              'added_basis_bounds': data['added_basis_bounds'],
              'basis': [{'name': name, 'upper': bound, 'mass_is_exact': name == 'mass',
                         'low_load_values': [f(n) for n in range(1, TAIL_ENTRANCE)], 'tail_polynomial': polynomial}
                        for name, bound, f, polynomial in zip(names, bounds, functions, polynomials)],
              'proof_data': proof_data, 'results': rows, 'comparison_upper': upper,
              'previous_comparison_upper': old_comparison, 'complete_comparison_improvement': old_comparison-upper['comparison'],
              'independent_moment_method_lower': lower, 'method_bracket_width': gap,
              'target403_position': target403_position,
              'counts': {'basis_functions': len(names), 'updated_basis_bounds': len(data['changed_basis_bounds']),
                         'added_basis_bounds': len(data['added_basis_bounds']),
                         'targets': len(rows), 'cost_targets': len(data['weights']),
                         'low_load_inequalities': len(rows)*(TAIL_ENTRANCE-1), 'whole_tail_polynomials': len(rows),
                         'exact_witness_moment_checks': len(rows)*len(names),
                         'positive_witness_atoms': sum(len(p['finite_moment_witness']) for p in proof_data),
                         'nonzero_envelope_coefficients': sum(len(p['coefficients']) for p in proof_data)},
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All28 previous279 scalar observations remain, with only the original H4/AP13 upper strengthened by280. Its original independent441/735 labels retain all50 completions of every62500000 old choice, giving3125000000 containing choices and complete old/positive-seven exponent tails. Every original function retains independent test labels. All59 whole-positive-integer envelopes and59 fresh finite moment witnesses are checked against all28 updated constraints. Exact mass3/20, all52 positive cost weights, signed mass, outside square, all four AP11 blocks, the improved AP13 deduction and the complete count tail are recomputed. The lower witnesses delimit the updated independent scalar-moment method and need not be actual sources or mutually compatible. No earlier279 method bracket, actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
    return encode(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--proposal', type=Path, help='Rational proposal data, used only by the writer')
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(args.proposal is None or args.write, 'A proposal is consumed only when writing')
    require(not args.write or args.proposal is not None, 'The writer requires rational proposal data')
    previous = module('joint_j_envelope_reader', args.base/'frontier/j_face_complete_moment_cost_comparison.py')
    io = module('joint_j_envelope_io', args.base/'certificate_io.py')
    if args.write:
        proposed = json.loads(io.read_artifact_bytes(args.proposal), object_pairs_hook=previous.unique)
        proofs = encode(previous.normalize_proofs(proposed['results']))
    else:
        stored = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE), object_pairs_hook=previous.unique)
        proofs = stored['proof_data']
    result = calculate(args.base, proofs)
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == stored, 'Every new complete J envelope and comparison recomputes exactly')
    print('Complete J comparison <= '+str(float(F(result['comparison_upper']['comparison']))))
    print('Updated independent scalar-moment method >= '+str(float(F(result['independent_moment_method_lower']['comparison']))))
    print('PASS:52 original costs,59 exact whole-load envelopes,all updated moment witnesses and complete J survival.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
