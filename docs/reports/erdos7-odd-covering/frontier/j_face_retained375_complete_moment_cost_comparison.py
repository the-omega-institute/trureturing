#!/usr/bin/env python3
"""Complete J comparison with375 retained in the full survival hinge."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j_face_retained375_complete_moment_cost_comparison.json'
PINS = {'frontier/j_face_four_pure_hinge_complete_moment_cost_comparison.py': '06341341c646c66e3aa41bd8721aa4c9d71b4b233313652bfd464d636a00d342', 'certificates/source_norms/j_face_four_pure_hinge_complete_moment_cost_comparison.json': '873827f28108da0f984bc963efc70ccbff80daf0c63fd2a0399f263774ab24c9', 'profile-notes/287-four-pure-hinges-improve-the-complete-j-comparison.md': 'e164e2eeeafba00daca60d1aeb39ce95adf1aaac5897eea4531dce72cfd35086', 'frontier/j_face_retained375_survival_heads.py': 'c5d2e171d97d3d21e1b95373e2731c13d067808537c856658e17129ff9ec5c2b', 'certificates/source_norms/j_face_retained375_survival_heads.json': 'f5e328aee9f52b8cfb57149766e9e95d73d3f865722b050bed594abeb826f224', 'profile-notes/288-retaining375-strengthens-the-complete-j-survival-hinge.md': '471e21713ee2ced6488fe0c3385450594f80fb1ba771e86ae1e8a7d723d9474f'}
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
    prior=module('retained375_comparison287',base/'frontier/j_face_four_pure_hinge_complete_moment_cost_comparison.py')
    data=prior.inputs(base);previous,io=data['previous'],data['io']
    read=lambda name:json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),object_pairs_hook=previous.unique)
    old=read('j_face_four_pure_hinge_complete_moment_cost_comparison')
    heads=read('j_face_retained375_survival_heads')
    pins=dict(data['pins'])
    for source in(old,heads):
        require(source['geometry']==data['geometry'] and F(source['survivor_mass'])==MASS,
                'The same complete actual saturated J domain and survivor measure')
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent current source closure '+path);pins[path]=pin
    for path,pin in PINS.items():
        require(path not in pins or pins[path]==pin,'Consistent direct mathematical input '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical source '+path)
    names,functions,polynomials,bounds=(list(data[k])for k in('names','functions','polynomials','bounds'))
    require([r['name']for r in old['basis']]==names and [F(r['upper'])for r in old['basis']]==bounds
            and len(names)==32 and old['all_original_indices']==list(range(52)),
            'The exact final287 baseline retains all32 observations and all52 original costs')
    pos=names.index('hinge4');prior_bound=bounds[pos];upper=F(heads['complete_AP13_upper'])
    require(heads['schema']=='erdos7-j-face-retained375-survival-heads-v1'
            and F(heads['source_mass'])==F(1,4)and heads['new_label']==375
            and F(heads['new_label_survivor_cap'])==F(1,375)
            and heads['model']['variables']==12941 and heads['model']['inequalities']==30454 and heads['model']['equalities']==20
            and heads['model']['preserved_original_rows']==11211 and heads['model']['preserved_original_equalities']==19,
            'The complete375 extension preserves every original264 actual-source constraint')
    require(heads['retained_old_labels']==[25,27,75,81,135,125,225,375]
            and heads['retained_positive7_labels']==[21,35,63,105,147,245,441,735]
            and F(heads['complete_old_tail_before375'])==F(6151,405000)
            and F(heads['complete_old_tail'])==F(5071,405000)
            and F(heads['complete_positive7_tail'])==F(13,490)
            and F(heads['complete_tail_constant'])==F(774979,19845000),
            'Only375 own1/375 cap is removed; every other complete exponent tail remains')
    ledger=heads['prefix_ledger'];c=ledger['counts']
    two=c['two_old_bounded']+c['two_enhanced_bounded'];four=c['four_old_bounded']+c['four_enhanced_bounded']
    six=c['six_old_bounded']+c['six_enhanced_bounded']+c['six_known_dual_bounded']
    require(c['layouts']==12500 and c['two_seen']==125000 and c['four_seen']==50*(125000-two)
            and c['six_seen']==10*(c['four_seen']-four)and c['seven_seen']==5*(c['six_seen']-six)
            and c['eight_seen']==10*(c['seven_seen']-c['seven_bounded'])
            and 25000*two+500*four+50*six+10*c['seven_bounded']+c['eight_bounded']+c['seed_bounded']+c['lp_remaining']
                ==ledger['covered_containing_choices']==heads['total_containing_choices']==3125000000,
            'Every original independent2/4/6/7/8 projection choice is covered')
    leaves=ledger['remaining_eight_projection_leaves'];rows=heads['residual_leaf_results'];fixed=F(heads['fixed_pruning_benchmark'])
    require(len(rows)==len(leaves)==c['lp_remaining']==heads['residual_leaf_count']
            and all(F(v)<=fixed for v in ledger['maximum_pruned_bounds'].values())
            and F(ledger['fixed_candidate_H4_benchmark'])==fixed,
            'Every bounded prefix meets the fixed threshold and every residual leaf is retained')
    for leaf,row in zip(leaves,rows):
        require(all(row[k]==leaf[k]for k in('layout','projection','projection441_735'))
                and F(row['complete_tail_constant'])==F(774979,19845000)
                and F(row['previous_available_upper'])==F(leaf['strongest_available_old_upper'])
                and F(row['adopted_upper'])==min(F(row['complete375_upper']),F(row['previous_available_upper'])),
                'Each residual leaf keeps the minimum of two complete valid source bounds')
    require(upper==max([fixed]+[F(r['adopted_upper'])for r in rows])
            and heads['rational_column_checks']==12941*heads['distinct_dual_count']
            and 0<upper<prior_bound==F(heads['previous_complete_AP13_upper'])
            and F(heads['improvement_over_previous'])==prior_bound-upper
            and polynomials[pos]==(F(-4),F(1),F(0))
            and all(functions[pos](n)==F(max(n-4,0))for n in range(1,TAIL_ENTRANCE)),
            'The same complete H4 function receives a strict uniform source improvement')
    bounds[pos]=upper
    data.update(pins=pins,names=names,functions=functions,polynomials=polynomials,bounds=bounds,old=old,
                changed_basis_bounds=[{'name':'hinge4','previous_upper':prior_bound,'updated_upper':upper,'source':'288'}],added_basis_bounds=[])
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete287 bound')
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
    result = {'schema': 'erdos7-j-face-retained375-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All32 previous287 scalar observations remain; only the complete H4 source bound is strengthened by288. Its same-source375 event refines all eight original marked states and their complements while preserving every264 row, independent original labels, common late parameter and every exponent/cofactor tail. The complete2/4/6/7/8 prefix ledger and all residual375 leaves cover every3.125 billion containing choice. All59 whole-positive-integer envelopes and59 fresh finite moment witnesses are checked against all32 updated constraints. Exact mass3/20, all52 positive cost weights, signed mass, outside square, all four AP11 blocks, the updated AP13 survival deduction and the complete count tail are recomputed. The lower witnesses delimit only this independent scalar-moment method and need not be actual sources or mutually compatible. No actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
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
