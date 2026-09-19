#!/usr/bin/env python3
"""Complete J comparison with the joint positive175/189 H4 source bound."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_joint_positive175189_complete_moment_cost_comparison.json'
PINS = {'frontier/j-geometry/j_face_exact_seven_factorial_complete_moment_cost_comparison.py': '241c166349792caa0f6cf9a136b6a2073d0f3b9620f043b13055ba56ade145f6', 'certificates/source_norms/j-geometry/j_face_exact_seven_factorial_complete_moment_cost_comparison.json': '9f80776771e97bc36cc15396a9ae0a5c6c14ee340fd0c48b580228e9146f50ed', 'profile-notes/257-320/295-the-exact-seven-factorial-head-improves-the-complete-j-comparison.md': 'c6276dc4c92a6236870ec26f1fee39801c67a8da694cf369c49b3fa17cce3212', 'frontier/j-geometry/j_face_joint_positive175189_survival_heads.py': 'e7558a78b034c5fd46d5deeadfe45ae8f3c5f55f9aa493fb3ecc960c284d8a48', 'certificates/source_norms/j-geometry/j_face_joint_positive175189_survival_heads.json': '91c7d1e277c7a40c5b81d7954dedcff755a62e9c5388a9d4019a6e0985612c71', 'profile-notes/257-320/296-joint-positive175189-strengthens-the-complete-j-survival-hinge.md': '533c267b6d02ee50b30c5e40b6e399b8dea6c61debe7fcf00ae53db72dfd6148'}
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
    require(PINS,'Final exact mathematical input pins')
    prior=module('joint_positive175189_comparison295',base/'frontier/j-geometry/j_face_exact_seven_factorial_complete_moment_cost_comparison.py')
    data=prior.inputs(base);previous,io=data['previous'],data['io']
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),object_pairs_hook=previous.unique)
    old=read('j_face_exact_seven_factorial_complete_moment_cost_comparison')
    heads=read('j_face_joint_positive175189_survival_heads');pins=dict(data['pins'])
    for item in(old,heads):
        require(item['geometry']==data['geometry']and F(item['survivor_mass'])==MASS,
                'Both entire actual saturated J faces on the same original survivor measure')
        for path,pin in item['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent mathematical source '+path);pins[path]=pin
    for path,pin in PINS.items():
        require(path not in pins or pins[path]==pin,'Consistent direct mathematical input '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical source '+path)
    names,functions,polynomials,bounds=(list(data[k])for k in('names','functions','polynomials','bounds'))
    require([r['name']for r in old['basis']]==names and [F(r['upper'])for r in old['basis']]==bounds
            and len(names)==34 and old['all_original_indices']==list(range(52)),
            'The exact complete295 baseline preserves all34 original observations and52 costs')
    pos=names.index('hinge4');prior_bound=bounds[pos];upper=F(heads['complete_AP13_upper'])
    require(heads['schema']=='erdos7-j-face-joint-positive175189-survival-heads-v1'
            and F(heads['source_mass'])==F(1,4)and heads['name']=='hinge4'and heads['threshold']==4
            and heads['retained_old_labels']==[25,27,75,81,135,125,225,375]
            and heads['previous_retained_positive7_labels']==[21,35,63,105,147,245,441,735]
            and heads['new_positive7_labels']==[175,189]and heads['fresh_old_cofactors']==[25,27]
            and heads['independent_profile_dimensions']==[5,5],
            'The same complete H4 with every old label and both independent fresh parent profiles')
    model=heads['model'];prior_model=heads['original288_model']
    require(model['variables']==32151 and model['inequalities']==56133 and model['equalities']==22
            and model['rows_sha256']=='4da5961945a50079d14a49fc0017409abeba79624086971f2c0747d63e8e494d'
            and prior_model['variables']==12941 and prior_model['inequalities']==30454 and prior_model['equalities']==20
            and prior_model['rows_sha256']=='e591c59f8891f6647f0e21f303cd3be9ca661f1d5b48ebd0625c2de85cfa32d0',
            'The complete joint raw refinement preserves the whole original375 actual-source model')
    require(list(map(F,heads['assigned_removed_tail_caps']))==[F(3,875),F(1,210)]
            and F(heads['complete_old_tail'])==F(5071,405000)
            and F(heads['complete_positive7_tail'])==F(337,18375)==F(13,490)-F(3,875)-F(1,210)
            and F(heads['complete_tail_constant'])==F(612439,19845000)==F(5071,405000)+F(337,18375)
            and F(heads['joint_raw_cap'])==F(1,675),
            'Only the two designated cap payments are removed once; every complete complementary tail remains')
    ledger=heads['prefix_ledger'];c=ledger['counts'];fixed=F(heads['fixed_pruning_benchmark'])
    two=c['two_old_bounded']+c['two_enhanced_bounded'];four=c['four_old_bounded']+c['four_enhanced_bounded']
    six=c['six_old_bounded']+c['six_enhanced_bounded']+c['six_known_dual_bounded']
    require(c['layouts']==12500 and c['two_seen']==125000 and c['four_seen']==50*(c['two_seen']-two)
            and c['six_seen']==10*(c['four_seen']-four)and c['seven_seen']==5*(c['six_seen']-six)
            and c['eight_seen']==10*(c['seven_seen']-c['seven_bounded']),
            'Every original independent two/four/six/seven/eight prefix choice')
    prefix=25000*two+500*four+50*six+10*c['seven_bounded']+c['eight_bounded']+c['seed_bounded']
    leaves=[r for batch in ledger['remaining_eight_projection_leaf_batches']for r in batch]
    reuse=heads['original375_reuse'];bounded=[r for batch in reuse['bounded_leaf_batches']for r in batch]
    remaining=[r for batch in reuse['remaining_leaf_batches']for r in batch]
    rows=[r for batch in heads['residual_leaf_batches']for r in batch]
    require(prefix==heads['prefix_bounded_original_choices']and len(leaves)==c['lp_remaining']==len(bounded)+len(remaining)
            and prefix+len(bounded)+len(rows)==ledger['covered_containing_choices']==heads['total_containing_choices']==3125000000
            and len(rows)==len(remaining)==heads['residual_leaf_count']and len(bounded)==reuse['bounded_leaf_count']
            and all(F(v)<=fixed for v in ledger['maximum_pruned_bounds'].values())
            and all(F(r['strongest_available_upper'])<=fixed for r in bounded),
            'The original prefix,own-branch375 reductions and all joint residuals cover the whole original domain')
    require(sorted(r['original_prefix_leaf_index']for r in bounded+remaining)==list(range(len(leaves))),
            'Each original unresolved prefix leaf occurs once in the375 reduction')
    for leaf in bounded+remaining:
        original=leaves[leaf['original_prefix_leaf_index']]
        require(all(leaf[k]==original[k]for k in('layout','projection','projection441_735'))
                and F(leaf['strongest_available_old_upper'])==F(original['strongest_available_old_upper']),
                'No original375 reduction changes the identity or old bound of its own source branch')
    for i,(leaf,row)in enumerate(zip(remaining,rows)):
        require(row['leaf_index']==i and all(row[k]==leaf[k]for k in('layout','projection','projection441_735'))
                and F(row['complete_tail_constant'])==F(612439,19845000)
                and F(row['previous_available_upper'])==F(leaf['strongest_available_upper'])
                and F(row['adopted_upper'])==min(F(row['complete_joint_upper']),F(row['previous_available_upper'])),
                'Every residual adopts its own complete new/old minimum with the same full tail')
    require(upper==max([fixed]+[F(r['adopted_upper'])for r in rows])
            and heads['rational_column_checks']==32151*heads['distinct_dual_count']
            and reuse['rational_column_checks']==12941*reuse['branch_reuse_count']
            and 0<upper<prior_bound==F(heads['previous_complete_AP13_upper'])
            and F(heads['improvement_over_previous'])==prior_bound-upper
            and polynomials[pos]==(F(-4),F(1),F(0))
            and all(functions[pos](n)==max(n-4,0)for n in range(1,TAIL_ENTRANCE)),
            'Exactly the same whole-positive-integer H4 receives the strict complete source improvement')
    bounds[pos]=upper
    data.update(pins=pins,names=names,functions=functions,polynomials=polynomials,bounds=bounds,old=old,
                changed_basis_bounds=[{'name':'hinge4','previous_upper':prior_bound,'updated_upper':upper,'source':'296'}],added_basis_bounds=[])
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete295 bound')
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
    result = {'schema': 'erdos7-j-face-joint-positive175189-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All34 observations from295 remain. Only the complete H4/AP13 source bound is strengthened by296 using the two fresh positive-seven labels175 and189. Every original3.125b projection choice is covered,and each branch includes both independent full new parent-profile simplexes. All original source constraints,actual measures,complete exponent/cofactor tails and the common late interval remain. All59 whole-positive-integer envelopes and fresh feasible moment witnesses are checked against all34 updated bounds; exact mass3/20 is an equality. All52 positive cost weights,signed mass,outside square,four AP11 blocks,AP13 survival and the complete count tail are recomputed. The method lower is restricted to independent scalar-envelope comparisons with positive survival denominator; its witnesses need not be actual sources or mutually compatible. No actual attainment,off-face/global extension,unrestricted Erdos7 result,or Lean verification is asserted.'}

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
