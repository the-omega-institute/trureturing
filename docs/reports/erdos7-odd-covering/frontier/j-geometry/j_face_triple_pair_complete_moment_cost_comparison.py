#!/usr/bin/env python3
"""Complete J comparison with six seven-retained-label moment bounds."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_triple_pair_complete_moment_cost_comparison.json'
PINS = {'frontier/j-geometry/j_face_second_cofactor_complete_moment_cost_comparison.py': 'f20c85d69675aac8c9e18cac332d03359b043c2f1ee4edcb8e89dbe0ed39f662', 'certificates/source_norms/j-geometry/j_face_second_cofactor_complete_moment_cost_comparison.json': '46fa2fac5281708a2baf513b5ed2bbc5c5bdfff2c9de5be33250bec1da237a4d', 'profile-notes/257-320/281-second-depth-cofactors-improve-the-complete-j-comparison.md': 'c94fc9b6bb01d0de06a95ae28b26c6f0b80a2eb9ee177d63c745e380d53e6031', 'frontier/j-geometry/j_face_triple_pair_factorial_heads.py': 'bfcf19ee49df701d601a6a5963322d7526a15fc152443432861a85532c16d1c8', 'certificates/source_norms/j-geometry/j_face_triple_pair_factorial_heads.json': '61be6fc6001042ee0094089cfb8e4b30e9ab0aa349b40337eb480d05614de99a', 'profile-notes/257-320/282-seven-retained-old-labels-strengthen-the-complete-j-moments.md': '55b17f5415631d6d9ab6c7b3d428405ff65631e6b24a38dfd6b0885268dee8c8'}
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
    prior=module('triple_pair_comparison281',base/'frontier/j-geometry/j_face_second_cofactor_complete_moment_cost_comparison.py')
    data=prior.inputs(base);previous,io=data['previous'],data['io']
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),object_pairs_hook=previous.unique)
    old=read('j_face_second_cofactor_complete_moment_cost_comparison');heads=read('j_face_triple_pair_factorial_heads')
    pins=dict(data['pins'])
    for source in(old,heads):
        require(source['geometry']==data['geometry']and F(source['survivor_mass'])==MASS,'Same entire original actual saturated J domain')
        for path,pin in source['source_sha256'].items():
            require(path not in pins or pins[path]==pin,'Consistent inherited input '+path);pins[path]=pin
    for path,pin in PINS.items():
        require(path not in pins or pins[path]==pin,'Consistent direct input '+path);pins[path]=pin
    for path,pin in pins.items():require(sha256(io.read_artifact_bytes(base/path)).hexdigest()==pin,'Pinned mathematical source '+path)
    names,functions,polynomials,bounds=(list(data[k])for k in('names','functions','polynomials','bounds'))
    require([r['name']for r in old['basis']]==names and [F(r['upper'])for r in old['basis']]==bounds
            and len(names)==28 and old['all_original_indices']==list(range(52)),'Exact published281 baseline, all28 observations and52 costs')
    pay=heads['pair_partitions'];model=heads['model'];rows=heads['results']
    expected=('cost-48','cost-49','square','factorial5','factorial2','factorial3')
    require([r['name']for r in rows]==list(expected)and model['variables']==6531 and model['inequalities']==11211 and model['equalities']==19
            and model['marked_state_bit_labels']==[135,125,225]and model['marked_states']==list(range(1,8))
            and pay['retained_old_labels']==[25,27,75,81,135,125,225]
            and len(pay['selected_POO_pairs'])==21 and len(pay['selected_POZ_blocks'])==49
            and F(pay['selected_POO_payment'])==F(11537,202500)and F(pay['selected_POZ_payment'])==F(17351,275625)
            and F(pay['remaining_POO_upper'])==F(132479,1620000)and F(pay['remaining_POZ_upper'])==F(51501,490000)
            and F(pay['original_complete_pair_tail'])==F(4879,7200)and F(pay['original_PZZ_upper'])==F(89,240)
            and F(heads['complete_old_hinge_tail'])==F(6151,405000)and F(heads['complete_positive7_hinge_tail'])==F(37,1225),
            'Same actual seven-state source and exactly assigned complete pair/tail replacements')
    changed=[]
    for row in rows:
        target_name=row['name'];name=target_name.replace('cost-','cost');pos=names.index(name);upper=F(row['adopted_upper']);oldbound=bounds[pos];ex=row['expansion']
        k=ex['factorial_threshold'];at=F(ex['at_one']);fc=F(ex['factorial_coefficient']);co={int(t):F(v)for t,v in ex['hinge_coefficients'].items()}
        poly=(at-sum(t*v for t,v in co.items())+fc*F(k*(k-1),2),sum(co.values())+fc*F(1-2*k,2),fc/2)
        require(poly==polynomials[pos]and max([k]+list(co))<TAIL_ENTRANCE
                and all(at+sum(v*max(n-t,0)for t,v in co.items())+fc*F(max(n-k,0)*max(n-k+1,0),2)==functions[pos](n)for n in range(1,TAIL_ENTRANCE)),
                'Same original function at all finite transitions and entire quadratic tail')
        scan=row['scan'];c=scan['counts']
        if co:
            require(c['two_projection_branches']==125000 and c['four_projection_branches']==50*(125000-c['two_bounded'])
                    and c['six_projection_branches']==10*(c['four_projection_branches']-c['four_bounded'])
                    and c['joint_dual_branches']+c['six_affine_bounded']+c['conditional_affine_bounded']==c['six_projection_branches'],
                    'Every branch of the complete original conditional hinge/factorial scanner')
            covered=500*c['two_bounded']+10*c['four_bounded']+c['six_projection_branches']
        else:
            require(c['layouts']==12500 and c['conditional_projections']==5000*(12500-c['layout_bounded'])
                    and c['conditional_bounded']+c['joint_dual_branches']==c['conditional_projections'],
                    'Every branch of the complete original pure-factorial scanner')
            covered=5000*c['layout_bounded']+c['conditional_bounded']+c['joint_dual_branches']
        require(covered==scan['covered_containing_choices']==62500000 and F(scan['complete_cost_upper'])==F(row['complete_cost_upper'])==upper
                and F(row['previous_adopted_upper'])==oldbound and F(row['improvement_over_previous'])==oldbound-upper>0,
                'Strict whole-domain bound for this unchanged original observation')
        bounds[pos]=upper;changed.append({'name':name,'previous_upper':oldbound,'updated_upper':upper,'source':'282'})
    require(heads['total_containing_choices']==375000000 and heads['threshold_layout_record_count']==75000
            and heads['cross_endpoint_record_count']==150000 and heads['rational_column_checks']==6531*heads['distinct_dual_count']
            and len(changed)==6 and len(names)==28,'All six complete sources retain the same28-dimensional scalar basis')
    data.update(pins=pins,names=names,functions=functions,polynomials=polynomials,bounds=bounds,old=old,
                changed_basis_bounds=changed,added_basis_bounds=[])
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete281 bound')
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
    result = {'schema': 'erdos7-j-face-triple-pair-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All28 published281 observations remain, with the six source bounds cost48/cost49/square/Phi5/Phi2/Phi3 strengthened by282. Each source bound retains all62500000 original independent containing choices and every infinite old and positive-seven tail. The exact same264 seven-state raw/survivor model supplies the21 retained POO pairs and49 POZ blocks. All59 whole-positive-integer envelopes and59 fresh finite moment witnesses are checked against all28 updated constraints. Exact mass3/20, all52 positive costs, signed mass, outside square, four AP11 blocks, the unchanged280 H4/AP13 bound and complete count tail are retained. The lower witnesses delimit only this updated independent scalar-moment method and need not be actual sources or mutually compatible. No previous281 method bracket, actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
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
