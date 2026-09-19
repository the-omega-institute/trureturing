#!/usr/bin/env python3
"""Complete J comparison with the exact seven-retained Phi5 source bound."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j_face_exact_seven_factorial_complete_moment_cost_comparison.json'
PINS = {'frontier/j_face_retained375_ap11_complete_moment_cost_comparison.py': '275112e167b65ba011123d023be53df226791d71de863e1fd097aa40413706b3', 'certificates/source_norms/j_face_retained375_ap11_complete_moment_cost_comparison.json': 'a695de09ee871b9a5b7c0aefe23bfa235178bf7bcce97aacee8aaa54fa0960a8', 'profile-notes/293-the-retained375-ap11-head-improves-the-complete-j-comparison.md': 'b2bf2aade496e4423ae0ce9fc4a53690dc1a66b4909b2bb73331978971ec5f59', 'frontier/j_face_exact_seven_retained_factorial_head.py': '0fba4dd51cf07c660ab4c520f5b7d2fc8c1ec820b4f5e77b0fbb0bc74f18c3ff', 'certificates/source_norms/j_face_exact_seven_retained_factorial_head.json': '8dc120b4fc1aeade34860dca5f41d9888557cfb0526cda7170fd3628a6423739', 'profile-notes/294-exact-seven-retained-head-and-slope-sharpen-the-complete-j-factorial.md': '8e16f2ca4f4a291f970344c9a999ff78a8e1f880068f5ee6722eae85cc447ca9'}
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
    prior=module('exact_seven_comparison293',base/'frontier/j_face_retained375_ap11_complete_moment_cost_comparison.py')
    data=prior.inputs(base);previous,io=data['previous'],data['io']
    read=lambda name:json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),object_pairs_hook=previous.unique)
    old=read('j_face_retained375_ap11_complete_moment_cost_comparison')
    heads=read('j_face_exact_seven_retained_factorial_head');pins=dict(data['pins'])
    for item in(old,heads):
        require(item['geometry']==data['geometry']and F(item['survivor_mass'])==MASS,
                'The same entire actual saturated J source and survivor measure')
        for path,pin in item['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent current mathematical source '+path);pins[path]=pin
    for path,pin in PINS.items():
        require(path not in pins or pins[path]==pin,'Consistent direct mathematical input '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical source '+path)
    names,functions,polynomials,bounds=(list(data[k])for k in('names','functions','polynomials','bounds'))
    require([r['name']for r in old['basis']]==names and [F(r['upper'])for r in old['basis']]==bounds
            and len(names)==34 and old['all_original_indices']==list(range(52)),
            'The complete293 baseline preserves all34 observations and52 original costs')
    pos=names.index('factorial5');prior_bound=bounds[pos];upper=F(heads['complete_factorial_upper'])
    require(heads['schema']=='erdos7-j-face-exact-seven-retained-factorial-head-v1'
            and F(heads['source_mass'])==F(1,4)and heads['name']=='factorial5'and heads['factorial_threshold']==5
            and heads['retained_old_labels']==[25,27,75,81,135,125,225]
            and heads['model']['variables']==6531 and heads['model']['inequalities']==11211 and heads['model']['equalities']==19
            and heads['model']['rows_sha256']=='9f571ed4977b916e2a0823e5e7262eb333717301ac85a30f6c96671ebc9465ce',
            'The unchanged complete seven-retained actual-source model and exact Phi5')
    expansion=heads['expansion']
    require(F(expansion['factorial_coefficient'])==1 and F(expansion['at_one'])==0 and expansion['hinge_coefficients']=={},
            'Exactly the pure complete Phi5 function, with no extra hinge or constant')
    payment=heads['pair_partitions']
    require(F(payment['selected_POO_payment'])==F(11537,202500)and F(payment['remaining_POO_upper'])==F(132479,1620000)
            and F(payment['selected_POZ_payment'])==F(17351,275625)and F(payment['remaining_POZ_upper'])==F(51501,490000)
            and F(payment['original_POO_upper'])==F(111,800)and F(payment['original_POZ_upper'])==F(121,720)
            and F(payment['original_PZZ_upper'])==F(89,240)and F(payment['original_complete_pair_tail'])==F(4879,7200)
            and len(payment['selected_POO_pairs'])==21 and len(payment['selected_POZ_blocks'])==49,
            'All complete original selected and complementary pair tails remain')
    ledger=heads['prefix_ledger'];c=ledger['counts'];fixed=F(heads['fixed_pruning_benchmark'])
    require(c['layouts']==12500 and c['projection_seen']==5000*(c['layouts']-c['layout_bounded'])
            and c['projection_seen']==c['conditional_bounded']+c['new_dual_bounded']+c['old_dual_bounded']+c['remaining']
            and 5000*c['layout_bounded']+c['projection_seen']==ledger['covered_containing_choices']==heads['total_containing_choices']==62500000
            and all(F(v)<=fixed for v in ledger['maxima'].values()),
            'Every original independent layout/projection choice is covered at the fixed threshold')
    seeds=heads['seed_rows'];leaves=[r for batch in ledger['leaf_batches']for r in batch]
    rows=[r for batch in heads['residual_leaf_batches']for r in batch]
    require(len(seeds)==ledger['seed_dual_count']==60 and len({r['key']for r in seeds})==60
            and fixed==max(F(r['upper'])for r in seeds)
            and len(rows)==len(leaves)==c['remaining']==heads['residual_leaf_count'],
            'Only the sixty original seed keys determine the fixed partition; every residual is retained')
    for leaf,row in zip(leaves,rows):
        require(all(leaf[k]==row[k]for k in('layout','projection','constant'))and leaf['objective_key']==row['dual_key']
                and F(row['previous_available_upper'])==F(leaf['strongest_available_upper'])
                and F(row['adopted_upper'])==min(F(row['complete_exact7_upper']),F(row['previous_available_upper'])),
                'Every residual adopts the minimum of two valid complete original-source bounds')
    phi=lambda n:F(max(n-5,0)*max(n-4,0),2)
    require(upper==max([fixed]+[F(r['adopted_upper'])for r in rows])
            and heads['rational_column_checks']==6531*heads['distinct_dual_count']
            and 0<upper<prior_bound==F(heads['previous_complete_factorial_upper'])
            and F(heads['improvement_over_previous'])==prior_bound-upper
            and polynomials[pos]==(F(10),F(-9,2),F(1,2))
            and all(functions[pos](n)==phi(n)for n in range(1,TAIL_ENTRANCE)),
            'The same whole-positive-integer Phi5 function receives a strict uniform source improvement')
    bounds[pos]=upper
    data.update(pins=pins,names=names,functions=functions,polynomials=polynomials,bounds=bounds,old=old,
                changed_basis_bounds=[{'name':'factorial5','previous_upper':prior_bound,'updated_upper':upper,'source':'294'}],added_basis_bounds=[])
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete293 bound')
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
    result = {'schema': 'erdos7-j-face-exact-seven-factorial-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All34 observations from293 remain, including the full retained375 H4 and AP11-0 bounds and full H7/H8 inequalities. Only the original complete Phi5 source bound is strengthened by294. Its unchanged6531-variable seven-retained model and exact fixed partition cover all62500000 independent containing choices, with the same sixty seeds and every residual leaf. Every original exponent/cofactor tail remains. All59 whole-positive-integer envelopes and fresh finite moment witnesses are checked against all34 updated observations; mass is an equality. Exact mass3/20, all52 positive cost weights, signed mass, outside square, all four AP11 blocks, AP13 survival and the complete count tail are recomputed. The method lower is restricted to independent scalar-envelope comparisons with positive survival denominator; its witnesses need not be actual sources or mutually compatible. No actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}

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
