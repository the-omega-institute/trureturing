#!/usr/bin/env python3
"""Complete J comparison with two higher pure-hinge observations."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_higher_pure_hinge_complete_moment_cost_comparison.json'
PINS = {'frontier/j-geometry/j_face_retained375_complete_moment_cost_comparison.py': '235c55da8126c815ce71753d72cebecbcbd47ceca89a71c35a0892fd03159c19', 'certificates/source_norms/j-geometry/j_face_retained375_complete_moment_cost_comparison.json': '4a09d876976db1fe9f83a20fc292c45cdf042e7086ac1f7005b46eb9fcb5e7d0', 'profile-notes/257-320/289-retaining375-improves-the-complete-j-comparison.md': '852588feb44c3beac7d38507e98f9034898c3086a932aa74804dd1065e005798', 'frontier/j-geometry/j_face_higher_pure_hinge_heads.py': '113ca5e3916dff90bf83db87613587392568c7203310f0ceaefe5cbd8193cd4a', 'certificates/source_norms/j-geometry/j_face_higher_pure_hinge_heads.json': '0596f3e436c0de3b58239f2a9377dbcadcf5a9304b6116433b9471c27a9c1e56', 'profile-notes/257-320/290-two-higher-pure-hinges-strengthen-the-complete-j-source.md': 'd429f9e12861fa4690e2169170628a003f326b1c39e412cd37d274c87c67e818'}
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
    prior=module('higher_hinge_comparison289',base/'frontier/j-geometry/j_face_retained375_complete_moment_cost_comparison.py')
    data=prior.inputs(base);previous,io=data['previous'],data['io']
    read=lambda name:json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),object_pairs_hook=previous.unique)
    old=read('j_face_retained375_complete_moment_cost_comparison')
    heads=read('j_face_higher_pure_hinge_heads')
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
            'The complete289 baseline retains all32 observations and all52 original costs')
    require(heads['schema']=='erdos7-j-face-higher-pure-hinge-heads-v1' and heads['thresholds']==[8,7]
            and heads['new_basis_names']==['hinge7','hinge8']
            and F(heads['source_mass'])==F(1,4) and heads['model']['variables']==6531
            and heads['model']['inequalities']==11211 and heads['model']['equalities']==19,
            'Both higher hinges use the unchanged264 actual-source model')
    require(heads['retained_old_labels']==[25,27,75,81,135,125,225]
            and heads['retained_positive7_labels']==[21,35,63,105,147,245]
            and F(heads['complete_zero7_joint_remainder'])==F(6151,405000)
            and F(heads['complete_positive7_tail'])==F(37,1225)
            and list(map(F,heads['removed_assigned_positive7_tail_caps']))==[F(3,980),F(3,1225)]
            and {int(k):F(v)for k,v in heads['complete_zero7_affine_remainders'].items()}=={7:F(2471,81000),8:F(2471,81000)},
            'The original joint and affine bounds retain their own full complementary tails')
    source_rows={r['threshold']:r for r in heads['results']}
    require(len(heads['results'])==2 and set(source_rows)=={7,8},'Exactly one complete source row per new observation')
    added=[]
    for t in (7,8):
        row=source_rows[t];name='hinge'+str(t);ex=row['expansion'];scan=row['scan'];c=scan['counts'];upper=F(row['complete_hinge_upper'])
        require(row['name']==name and F(ex['at_one'])==0 and ex['hinge_coefficients']=={str(t):'1'}
                and ex['zero_branch_last_integer']==t
                and ex['finite_transition_values']=={str(n):str(max(n-t,0))for n in range(1,t+2)}
                and ex['polynomial_tail']=={'entrance':t,'constant':str(-t),'linear':'1','leading':'0'}
                and scan['coefficients']=={str(t):'1'} and F(scan['complete_hinge_upper'])==upper and upper>0,
                'Exactly(n-t)_+ on the entire positive-integer domain, including its affine continuation')
        require(c['two_projection_branches']==125000
                and c['four_projection_branches']==50*(125000-c['two_bounded'])
                and c['six_projection_branches']==10*(c['four_projection_branches']-c['four_bounded']-c['prior251_bounded'])
                and c['joint_dual_branches']+c['six_affine_bounded']+c['prior256_bounded']==c['six_projection_branches']
                and 500*c['two_bounded']+10*(c['four_bounded']+c['prior251_bounded'])+c['six_projection_branches']
                    ==scan['covered_containing_choices']==62500000
                and F(scan['complete_tail_constant'])==F(900799,19845000),
                'Every original independent containing choice retains its full joint or affine tail')
        require(name not in names,'A new observation, without replacing an old scalar function')
        names.append(name);functions.append(lambda n,t=t:F(max(n-t,0)));polynomials.append((F(-t),F(1),F(0)));bounds.append(upper)
        added.append({'name':name,'threshold':t,'upper':upper,'source':'290'})
    require(len(names)==34 and heads['total_containing_choices']==125000000
            and heads['rational_column_checks']==6531*heads['distinct_dual_count'],
            'All34 actual-source observations and125 million complete original choices')
    data.update(pins=pins,names=names,functions=functions,polynomials=polynomials,bounds=bounds,old=old,
                changed_basis_bounds=[],added_basis_bounds=added)
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete289 bound')
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
    result = {'schema': 'erdos7-j-face-higher-pure-hinge-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All32 observations of289 remain, including the complete retained375 H4 bound, with complete pure hinges H7/H8 added by290. Each new hinge covers every62500000 independent original choice on the unchanged6531-variable model, one common late interval and all original exponent/cofactor tails. These uniform source inequalities apply together to the same actual measure without identifying relaxed optimizers. All59 whole-positive-integer envelopes and fresh finite moment witnesses are checked against all34 observations; mass is an equality. Exact mass3/20, all52 positive cost weights, signed mass, outside square, all four AP11 blocks, AP13 survival and the complete count tail are recomputed. The lower witnesses bound only the independent scalar-envelope comparison method with positive survival denominator; they need not be actual sources or mutually compatible. No actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}

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
