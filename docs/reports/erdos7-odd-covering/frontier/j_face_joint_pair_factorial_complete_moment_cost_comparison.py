#!/usr/bin/env python3
"""Complete J comparison with actual retained pairs strengthening square, Phi5 and costs48/49."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j_face_joint_pair_factorial_complete_moment_cost_comparison.json'
PINS = {'frontier/j_face_generalized_factorial_complete_moment_cost_comparison.py': '95a08a05d6a8619bedc56dbfaef422134001bd4ac2f1d698a712cf87c4b79e0c', 'certificates/source_norms/j_face_generalized_factorial_complete_moment_cost_comparison.json': '31f6ee08f263b7cfe5d3a50c8cabb0ed0e629ca86ea7d72b34a25db7e453f717', 'profile-notes/275-generalized-factorial-observations-improve-the-complete-j-comparison.md': '745490a332d3f21d5be02d459a3bef0172e5c3845a19a5874cbc61835f98725c', 'frontier/j_face_joint_pair_factorial_heads.py': '0ec9429da53290028977f7c985df3938e3798a76accd348ce2aec362cb7b30d0', 'certificates/source_norms/j_face_joint_pair_factorial_heads.json': 'debba12ad306a8623c2420ead390af4714ae149738b16aa33adca875606893c9', 'profile-notes/276-actual-retained-tail-pairs-strengthen-original-j-costs-and-square.md': 'b447c335f033501aa00b198d22cf2c5573c7d88843df1e4028ac475f014d21b8'}
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
    prior_module = module('joint_pair_factorial_j_envelope_previous', base/'frontier/j_face_generalized_factorial_complete_moment_cost_comparison.py')
    data = prior_module.inputs(base)
    previous, io = data['previous'], data['io']
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=previous.unique)
    old = read('j_face_generalized_factorial_complete_moment_cost_comparison')
    heads = read('j_face_joint_pair_factorial_heads')
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
            'The exact complete275 baseline with all26 moment constraints')
    require(heads['original_cost_indices'] == [48, 49] and heads['outside_targets'] == ['square','factorial5']
            and [row['name'] for row in heads['results']] == ['cost-48', 'cost-49', 'square', 'factorial5']
            and [row['original_cost_index'] for row in heads['results']] == [48, 49, None, None]
            and heads['factorial_thresholds'] == [3, 2, 1, 5]
            and F(heads['original_affine_pruning_pair_tail']) == F(4879, 7200)
            and F(heads['complete_positive7_hinge_tail']) == F(37, 1225)
            and heads['total_containing_choices'] == 250000000
            and heads['rational_column_checks'] == 3306*heads['distinct_dual_count'],
            'The complete276 original costs and square use their own thresholds and every original source choice')
    pairs = heads['pair_partitions']; conditional = heads['conditional_positive7']
    require(pairs['retained_old_labels'] == [25, 27, 75, 81, 135, 125]
            and len(pairs['selected_POO_pairs']) == 15 and len(pairs['selected_POZ_blocks']) == 42
            and F(pairs['selected_POO_payment']) == F(8857, 202500)
            and F(pairs['selected_POZ_payment']) == F(5402, 91875)
            and F(pairs['remaining_POO_upper']) == F(pairs['original_POO_upper'])-F(pairs['selected_POO_payment']) > 0
            and F(pairs['remaining_POZ_upper']) == F(pairs['original_POZ_upper'])-F(pairs['selected_POZ_payment']) > 0
            and F(pairs['original_POO_upper'])+F(pairs['original_POZ_upper'])+F(89, 240) == F(4879, 7200)
            and F(pairs['original_PZZ_upper']) == F(89, 240),
            'Only the assigned retained pair payments are replaced; their complete disjoint complements remain')
    require(conditional['original_raw_head_count'] == 12500 and conditional['raw_endpoint_record_count'] == 25000
            and len(conditional['first_projection_rows']) == 500 and len(conditional['second_projection_rows']) == 10
            and conditional['first_completion_count'] == 25 and conditional['second_completion_count'] == 1250
            and conditional['complete_projection_count'] == 5000 and conditional['conditional_endpoint_count'] == 10000
            and tuple(map(F, conditional['first_depth_weights'])) == (F(6,35), F(1,70))
            and tuple(map(F, conditional['second_depth_weights'])) == (F(6,245), F(1,70))
            and tuple(map(F, conditional['later_depth_weights'])) == (F(1,245), F(1,210))
            and F(conditional['complete_later_depth_constant']) == F(31,1470),
            'Both independently completed raw heads and every later positive-seven depth remain')
    partition = heads['cross_partitions']
    require(tuple(map(F, partition['old_zero7_weights'])) == (F(1,18), F(1,20), F(1,20), F(1,20), F(1,72))
            and tuple(map(F, partition['selected_zero7_weights'])) == (F(4,81), F(6,125), F(1,25), F(0), F(1,135))
            and tuple(map(F, partition['remaining_zero7_weights'])) == (F(1,162), F(1,500), F(1,100), F(1,20), F(7,1080))
            and tuple(F(a)-F(b) for a,b in zip(partition['old_zero7_weights'], partition['selected_zero7_weights']))
                == tuple(map(F, partition['remaining_zero7_weights']))
            and F(partition['positive7_first_depth_weight']) == F(6,35)
            and F(partition['positive7_second_depth_weight']) == F(6,245)
            and F(partition['complete_positive7_weight']) == F(1,5)
            and tuple(map(F, partition['raw_mask_residual_weights'])) == (F(1,245), F(1,35), F(1,245), F(1,35), F(1,5)),
            'Every selected raw/survivor cross replaces its own assigned term with the complete remaining tail')
    original_targets = {name: (fn, poly) for name, fn, poly in data['targets']}
    factorial_position = names.index('factorial5')
    original_targets['factorial5'] = functions[factorial_position], polynomials[factorial_position]
    old_targets = {row['name']: F(row['upper']) for row in old['results']}
    old_targets['factorial5'] = bounds[factorial_position]
    changed, added = [], []
    prior_bounds = list(bounds)
    for row in heads['results']:
        index = row['original_cost_index']; target_name = row['name']
        name = target_name if index is None else 'cost'+str(index)
        fn, poly = original_targets[target_name]
        expansion = row['expansion']; at_one = F(expansion['at_one'])
        co = {int(t): F(v) for t, v in expansion['hinge_coefficients'].items()}
        fc = F(expansion['factorial_coefficient'])
        threshold = row['factorial_threshold']
        phi = lambda n: F(max(n-threshold, 0)*max(n-threshold+1, 0), 2)
        require(row['tag'] == ({'kind': target_name} if index is None else encode(data['tags'][index])) and expansion['factorial_threshold'] == threshold
                and threshold == {'cost-48':3,'cost-49':2,'square':1,'factorial5':5}[target_name]
                and ((not co and name == 'factorial5' and at_one == 0 and fc == 1)
                     or (co and min(co.values()) > 0 and min(co) >= 1 and max(co) < TAIL_ENTRANCE))
                and at_one >= 0 and fc > 0,
                'The same original target has a positive shifted-factorial expansion')
        polynomial = (at_one-sum(t*v for t, v in co.items())+fc*F(threshold*(threshold-1), 2),
                      sum(co.values())+fc*F(1-2*threshold, 2), fc/2)
        require(polynomial == poly and all(at_one+sum(v*max(n-t, 0) for t, v in co.items())+fc*phi(n) == fn(n)
                                           for n in range(1, TAIL_ENTRANCE)),
                'Every finite transition and entire polynomial continuation of the unchanged original function')
        complete, upper, prior = (F(row[k]) for k in ('complete_cost_upper', 'adopted_upper', 'previous_adopted_upper'))
        scan = row['scan']; counts = scan['counts']
        require(complete == F(scan['complete_cost_upper']) and upper == min(complete, prior)
                and prior == old_targets[target_name] and 0 < upper < prior
                and F(row['improvement_over_previous']) == prior-upper
                and scan['covered_containing_choices'] == 62500000,
                'The complete276 source bound improves its own original275 target and retains every containing choice')
        if name == 'factorial5':
            require(scan['scanner_kind'] == 'pure-factorial-complete-conditional'
                    and counts['layouts'] == 12500
                    and counts['conditional_projections'] == 5000*(12500-counts['layout_bounded'])
                    and counts['conditional_bounded']+counts['joint_dual_branches'] == counts['conditional_projections']
                    and 5000*counts['layout_bounded']+counts['conditional_bounded']+counts['joint_dual_branches'] == 62500000,
                    'The separate empty-hinge Phi5 scanner covers all original labels with complete conditional pruning')
        else:
            require(scan['scanner_kind'] == 'complete-conditional-two-four-six'
                    and 500*counts['two_bounded']+10*counts['four_bounded']+counts['six_projection_branches'] == 62500000
                    and counts['two_projection_branches'] == 125000
                    and counts['four_projection_branches'] == 50*(125000-counts['two_bounded'])
                    and counts['six_projection_branches'] == 10*(counts['four_projection_branches']-counts['four_bounded'])
                    and counts['six_affine_bounded']+counts['conditional_affine_bounded']+counts['joint_dual_branches'] == counts['six_projection_branches'],
                    'The original complete two/four/six scanner and complete conditional refinement retain all independent labels')
        require(name in names, 'Every new target already belongs to the complete26-observation basis')
        position = names.index(name)
        require(functions[position] == fn and polynomials[position] == poly
                and prior <= bounds[position] and upper < bounds[position],
                'The same original basis function improves; target envelope and basis bound keep their own roles')
        changed.append({'name': name, 'previous_upper': bounds[position], 'updated_upper': upper, 'source': '276'})
        bounds[position] = upper
    require([row['name'] for row in changed] == ['cost48', 'cost49', 'square', 'factorial5'] and not added
            and sum(a != b for a, b in zip(bounds, prior_bounds)) == 4
            and len(names) == len(functions) == len(polynomials) == len(bounds) == 26,
            'All26 prior observations remain, with stronger original cost48/cost49, square and factorial5')
    data.update(pins=pins, names=names, functions=functions, polynomials=polynomials,
                bounds=bounds, old=old, changed_basis_bounds=changed, added_basis_bounds=added)
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete275 bound')
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
    result = {'schema': 'erdos7-j-face-joint-pair-factorial-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All26 previous scalar observations remain, with strictly stronger original cost48/cost49, square and factorial5 bounds from276 actual retained POO/POZ pairs and full conditional positive-seven pairs. Each source target retains its own original labels, full62500000 choices and threshold3/2/1/5; purePhi5 has a separate complete empty-hinge scanner. All59 whole-positive-integer envelopes and59 fresh independent finite moment witnesses are checked against all26 current constraints. Exact mass3/20, all52 positive cost weights, signed mass, outside square, all four AP11 blocks, AP13 and the entire count tail are recomputed. The independent witnesses constrain this updated scalar-moment method and need not be actual sources or coexist on one actual family. No old275 method bracket, actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
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
