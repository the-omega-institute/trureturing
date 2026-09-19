#!/usr/bin/env python3
"""Complete J comparison with two additional pure shifted-factorial observations."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_face_pure_low_factorial_complete_moment_cost_comparison.json'
PINS = {'frontier/j-source/j_face_joint_pair_factorial_complete_moment_cost_comparison.py': 'fb833a2a2d19c9e97c407ac1f2a9a438de09f357e791f2e3cf353312b5a5e97d', 'certificates/source_norms/j-source/j_face_joint_pair_factorial_complete_moment_cost_comparison.json': 'a7b6639d73e6cc52d59857209233ba35b8a5592f6a2283de9c20d810afd99671', 'profile-notes/j-source/277-actual-retained-pairs-improve-the-complete-j-comparison.md': '2cd4609852b1f1018905fd84f02a833ed24d878648bb14712e60d2f693b8003e', 'frontier/j-source/j_face_pure_low_factorial_heads.py': 'ddee35c8f61e626eae68e116788eb2c7958a90f831a72d2ecc7ac5cffd60c15b', 'certificates/source_norms/j-source/j_face_pure_low_factorial_heads.json': 'dc38003f46c3d5323fecb935267593078a18873db226dc5f358bd14bc71bc384', 'profile-notes/j-source/278-two-pure-factorial-observations-strengthen-the-j-source.md': 'c311bcb6e191e3e6119beac57423dfec0a7afbbde0b2080a7bbd9a16d1b04947'}
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
    prior_module = module('pure_low_j_previous', base/'frontier/j-source/j_face_joint_pair_factorial_complete_moment_cost_comparison.py')
    data = prior_module.inputs(base)
    previous, io = data['previous'], data['io']
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=previous.unique)
    old = read('j-source/j_face_joint_pair_factorial_complete_moment_cost_comparison')
    heads = read('j-source/j_face_pure_low_factorial_heads')
    published_pairs = read('j-source/j_face_joint_pair_factorial_heads')
    pins = dict(data['pins'])
    for source in (old, heads):
        require(source['geometry'] == data['geometry'] and F(source['survivor_mass']) == MASS,
                'Every input uses the same two entire saturated actual J faces and exact mass')
        for path, pin in source['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent full J source closure '+path)
            pins[path] = pin
    for path, pin in PINS.items():
        require(path not in pins or pins[path] == pin, 'Consistent direct mathematical input '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical source '+path)
    names, functions, polynomials, bounds = (list(data[k]) for k in ('names', 'functions', 'polynomials', 'bounds'))
    require([row['name'] for row in old['basis']] == names
            and [F(row['upper']) for row in old['basis']] == bounds
            and len(names) == 26 and old['all_original_indices'] == list(range(52)),
            'The exact complete277 baseline and all26 current moment constraints')
    require(heads['new_basis_names'] == ['factorial2','factorial3']
            and heads['factorial_thresholds'] == [2,3]
            and [r['name'] for r in heads['results']] == ['factorial2','factorial3']
            and heads['total_containing_choices'] == 125000000
            and heads['threshold_layout_record_count'] == 25000 and heads['cross_endpoint_record_count'] == 50000
            and heads['rational_column_checks'] == 3306*heads['distinct_dual_count']
            and F(heads['original_affine_pruning_pair_tail']) == F(4879,7200)
            and heads['model'] == published_pairs['model']
            and all(heads[k] == published_pairs[k] for k in ('pair_partitions','cross_partitions','conditional_positive7')),
            'Two complete pure-factorial observations retain the original source and all full published pair/cross tails')
    prior_bounds = list(bounds); prior_names = list(names); added = []
    old_proofs = {r['name']:r for r in old['proof_data']}
    for row in heads['results']:
        name, threshold = row['name'], row['factorial_threshold']
        require(name not in names and (name,threshold) in (('factorial2',2),('factorial3',3)),
                'Exactly two new scalar functions, without replacing an earlier observation')
        fn = lambda n,k=threshold: F(max(n-k,0)*max(n-k+1,0),2)
        polynomial = (F(threshold*(threshold-1),2),F(1-2*threshold,2),F(1,2))
        ex = row['expansion']; tail = ex['polynomial_tail']
        require(ex['factorial_threshold'] == threshold and F(ex['at_one']) == 0
                and F(ex['factorial_coefficient']) == 1 and ex['hinge_coefficients'] == {}
                and ex['zero_branch_last_integer'] == threshold
                and all(fn(n) == F(value) for n,value in ((int(n),v) for n,v in ex['finite_transition_values'].items()))
                and all(fn(n) == 0 for n in range(1,threshold+1))
                and tail['entrance'] == threshold
                and tuple(F(tail[k]) for k in ('constant','linear','leading')) == polynomial,
                'The exact pure positive-integer factorial function and its entire quadratic continuation')
        upper = F(row['complete_factorial_upper']); scan = row['scan']; c = scan['counts']
        require(upper == F(scan['complete_cost_upper']) > 0 and scan['coefficients'] == {}
                and scan['scanner_kind'] == 'pure-factorial-complete-conditional'
                and scan['covered_containing_choices'] == 62500000 and c['layouts'] == 12500
                and c['conditional_projections'] == 5000*(12500-c['layout_bounded'])
                and c['conditional_bounded']+c['joint_dual_branches'] == c['conditional_projections']
                and 5000*c['layout_bounded']+c['conditional_bounded']+c['joint_dual_branches'] == 62500000,
                'The empty-hinge scanner covers every original head/projection choice with all tails')
        separation = row['old_moment_separation']; proof = old_proofs[separation['published277_target']]
        witness = {int(n):F(v) for n,v in proof['finite_moment_witness'].items()}
        measured = [sum(v*f(n) for n,v in witness.items()) for f in functions[:26]]
        violation = sum(v*fn(n) for n,v in witness.items())-upper
        require(encode(witness) == separation['finite_moment_witness']
                and separation['old_basis_names'] == prior_names
                and min(witness.values()) > 0 and sum(witness.values()) == MASS
                and measured[0] == prior_bounds[0]
                and all(a <= b for a,b in zip(measured[1:],prior_bounds[1:]))
                and encode(measured) == separation['old_witness_moments']
                and encode([b-a for a,b in zip(measured,prior_bounds)]) == separation['old_witness_slacks']
                and F(separation['new_source_upper']) == upper
                and F(separation['new_factorial_moment']) == upper+violation
                and F(separation['strict_violation']) == violation > 0,
                'The new inequality removes a checked feasible measure from the prior26-observation moment model')
        names.append(name);functions.append(fn);polynomials.append(polynomial);bounds.append(upper)
        added.append({'name':name,'upper':upper,'source':'278','strict_old_moment_violation':violation})
    require(names[:26] == prior_names and bounds[:26] == prior_bounds
            and [r['name'] for r in added] == ['factorial2','factorial3']
            and len(names) == len(functions) == len(polynomials) == len(bounds) == 28,
            'Every previous scalar constraint remains unchanged, with exactly two additional observations')
    data.update(pins=pins,names=names,functions=functions,polynomials=polynomials,
                bounds=bounds,old=old,changed_basis_bounds=[],added_basis_bounds=added)
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete277 bound')
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
    result = {'schema': 'erdos7-j-face-pure-low-factorial-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All26 previous277 scalar observations remain unchanged; complete purePhi2/Phi3 from278 add two observations, giving28. Each addition excludes an explicitly checked feasible old26-moment measure and retains all62500000 original source choices, complete pair and exponent tails, and an empty hinge sum. All59 whole-positive-integer envelopes and59 fresh independent finite moment witnesses are checked against all28 constraints. Exact mass3/20, all52 positive cost weights, signed mass, outside square, all four AP11 blocks, AP13 and the entire count tail are recomputed. The independent witnesses delimit this updated scalar-moment method; they need not be actual sources or coexist on one actual family. No earlier277 method bracket, actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
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
    previous = module('joint_j_envelope_reader', args.base/'frontier/j-source/j_face_complete_moment_cost_comparison.py')
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
