#!/usr/bin/env python3
"""Complete J comparison with an exact retained factorial head and raw slope."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_exact_retained_factorial_complete_moment_cost_comparison.json'
PINS = {'frontier/j-geometry/j_face_triple_pair_complete_moment_cost_comparison.py': 'f1d72f8af5a02ffa9bb862d91246ae5ebc16f971499aa317c575428d866cb74b', 'certificates/source_norms/j-geometry/j_face_triple_pair_complete_moment_cost_comparison.json': 'b3892f71956473a5d5ab595a56b012845fc580adc0392ba1f468d54c44621fa0', 'profile-notes/257-320/283-seven-retained-old-labels-improve-the-complete-j-comparison.md': 'a3e30ec405f248277c3d7f3b588e4fdb1dbb899b3111d28dce919374548da9ae', 'frontier/j-geometry/j_face_exact_retained_factorial_head.py': 'ab2b13031f820bcebb3f5b4dd82a7b96df903230bf35fe68ba2a66c3c3c9fcbd', 'certificates/source_norms/j-geometry/j_face_exact_retained_factorial_head.json': '3e6c746bf968172975c122a7fecd0668ea0bee7da10733f40ebdfdcdecf34624', 'profile-notes/257-320/284-exact-retained-head-and-slope-sharpen-the-complete-j-factorial.md': 'f08c9622ab7cb81d36975dc2a0ad5346aa0e0f3032b130fd04bf1d7a33f43634'}
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
    require(PINS, 'Final mathematical input pins')
    prior=module('exact_retained_comparison283',base/'frontier/j-geometry/j_face_triple_pair_complete_moment_cost_comparison.py')
    data=prior.inputs(base);previous,io=data['previous'],data['io']
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),
                               object_pairs_hook=previous.unique)
    old=read('j_face_triple_pair_complete_moment_cost_comparison')
    heads=read('j_face_exact_retained_factorial_head')
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
            'The exact final283 baseline retains all28 observations and all52 original costs')
    pos=names.index('factorial5');previous_bound=bounds[pos];upper=F(heads['complete_factorial_upper'])
    original_bound=F(heads['previous_complete_factorial_upper'])
    expansion=heads['expansion'];scan=heads['scan'];counts=scan['counts']
    require(heads['name']=='factorial5' and heads['factorial_threshold']==expansion['factorial_threshold']==5
            and F(expansion['at_one'])==0 and expansion['hinge_coefficients']=={}
            and F(expansion['factorial_coefficient'])==1
            and polynomials[pos]==(F(10),F(-9,2),F(1,2))
            and all(functions[pos](n)==F(max(n-5,0)*max(n-4,0),2)for n in range(1,TAIL_ENTRANCE))
            and expansion['polynomial_tail']=={'entrance':5,'constant':'10','linear':'-9/2','leading':'1/2'},
            'The same whole-positive-integer Phi5 function including its complete quadratic tail')
    require(F(heads['source_mass'])==F(1,4) and 0<upper<previous_bound<=original_bound
            and F(heads['improvement_over_previous'])==original_bound-upper
            and F(scan['complete_cost_upper'])==upper,
            '284 strengthens current283 even though its source comparison baseline is276')
    require(heads['pair_partitions']['retained_old_labels']==[25,27,75,81,135,125]
            and F(heads['pair_partitions']['selected_POO_payment'])==F(8857,202500)
            and F(heads['pair_partitions']['selected_POZ_payment'])==F(5402,91875)
            and F(heads['pair_partitions']['original_complete_pair_tail'])==F(4879,7200),
            'The six-label exact-head source has its own unchanged complete tail partition')
    require(counts['layouts']==12500
            and counts['conditional_projections']==5000*(12500-counts['layout_bounded'])
            and counts['conditional_projections']==counts['conditional_bounded']+counts['joint_dual_branches']
            and 5000*counts['layout_bounded']+counts['conditional_bounded']+counts['joint_dual_branches']
                ==scan['covered_containing_choices']==62500000
            and heads['distinct_dual_count']==637 and heads['rational_column_checks']==3306*637,
            'Every independent original source choice has a complete verified bound')
    bounds[pos]=upper
    data.update(pins=pins,names=names,functions=functions,polynomials=polynomials,bounds=bounds,old=old,
                changed_basis_bounds=[{'name':'factorial5','previous_upper':previous_bound,'updated_upper':upper,'source':'284'}],
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete283 bound')
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
    result = {'schema': 'erdos7-j-face-exact-retained-factorial-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All28 previous283 scalar observations remain, with only Phi5 strengthened by284. Its exact six-label survivor head and nonnegative selected-positive-seven raw slope retain every complete complementary exponent tail and all62500000 independent choices. These source bounds concern the same actual measure and may be used together without identifying their relaxed optimizers. All59 whole-positive-integer envelopes and59 fresh finite moment witnesses are checked against all28 updated constraints. Exact mass3/20, all52 positive cost weights, signed mass, outside square, all four AP11 blocks, AP13 survival and the complete count tail are recomputed. The lower witnesses delimit only the updated independent scalar-moment method and need not be actual sources or mutually compatible. No actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
    return encode(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--proposal', type=Path, help='Rational proposal data, used only by the writer')
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(args.proposal is None or args.write, 'A proposal is consumed only when writing')
    require(not args.write or args.proposal is not None, 'The writer requires rational proposal data')
    previous = module('joint_j_envelope_reader', args.base/'frontier/j-geometry/j_face_complete_moment_cost_comparison.py')
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
