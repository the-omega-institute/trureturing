#!/usr/bin/env python3
"""Complete J comparison with generalized factorial thresholds on original costs48/49."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_face_generalized_factorial_complete_moment_cost_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j-source/j_face_joint_factorial_cross_complete_moment_cost_comparison.py': 'acb6844a1be1f260f9f9c42ae93f2bb457bcc892ebe84af8462f6c3831fb077b', 'certificates/source_norms/j-source/j_face_joint_factorial_cross_complete_moment_cost_comparison.json': 'c4bf89095799c9658d37f978acdff0e57cc2b57a67987eddf71b9e02ba860f4e', 'profile-notes/j-source/273-joint-factorial-crosses-improve-the-complete-j-comparison.md': '0de38a8be85d0dcbc0f12db543afaf0172c4b5f148d0a54f81e6f2cfb80444a9', 'frontier/j-source/j_face_generalized_factorial_heads.py': '2f72e4846ec7755585602ec801400289302503211d87d1c2a0506d447a7429ee', 'certificates/source_norms/j-source/j_face_generalized_factorial_heads.json': '95df26743561df015c6a50023521261aafdcdabc25b4ffe2101c5cbf6e054623', 'profile-notes/j-source/274-generalized-factorial-thresholds-strengthen-two-original-j-costs.md': '6c60b8ddff1c1d978636cb6bd183cabbbbc23fdb6769db84791aaf71b508674d'}
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
    prior_module = module('generalized_factorial_j_envelope_previous', base/'frontier/j-source/j_face_joint_factorial_cross_complete_moment_cost_comparison.py')
    data = prior_module.inputs(base)
    previous, io = data['previous'], data['io']
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=previous.unique)
    old = read('j-source/j_face_joint_factorial_cross_complete_moment_cost_comparison')
    heads = read('j-source/j_face_generalized_factorial_heads')
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
            and len(names) == 25 and old['all_original_indices'] == list(range(52)),
            'The exact complete273 baseline with all25 moment constraints')
    require(heads['original_cost_indices'] == [48, 49]
            and [row['index'] for row in heads['results']] == [48, 49]
            and heads['factorial_thresholds'] == [3, 2]
            and F(heads['complete_pair_tail']) == F(4879, 7200)
            and F(heads['complete_positive7_hinge_tail']) == F(37, 1225)
            and heads['total_containing_choices'] == 125000000
            and heads['rational_column_checks'] == 3306*heads['distinct_dual_count']
            and heads['positive7_cross_cost_indices'] == [48, 49]
            and heads['zero7_cross_cost_indices'] == [48, 49]
            and [row['retained_zero7_cross'] for row in heads['results']] == [True, True],
            'The complete274 original costs at their own thresholds, all source columns and all tails')
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
    old_targets = {row['name']: F(row['upper']) for row in old['results']}
    changed, added = [], []
    prior_bounds = list(bounds)
    for row in heads['results']:
        index = row['index']; name = 'cost'+str(index)
        fn, poly = original_targets['cost-'+str(index)]
        expansion = row['expansion']; at_one = F(expansion['at_one'])
        co = {int(t): F(v) for t, v in expansion['hinge_coefficients'].items()}
        fc = F(expansion['factorial_coefficient'])
        threshold = row['factorial_threshold']
        phi = lambda n: F(max(n-threshold, 0)*max(n-threshold+1, 0), 2)
        require(row['tag'] == encode(data['tags'][index]) and expansion['factorial_threshold'] == threshold
                and threshold == {48: 3, 49: 2}[index]
                and co and min(co.values()) > 0 and min(co) >= 1 and max(co) < TAIL_ENTRANCE
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
                and prior == old_targets['cost-'+str(index)] and 0 < upper < prior
                and F(row['improvement_over_previous']) == prior-upper
                and scan['covered_containing_choices'] == 62500000
                and 500*counts['two_bounded']+10*counts['four_bounded']+counts['six_projection_branches'] == 62500000
                and counts['prior251_bounded'] == 0,
                'The complete274 source bound improves its own original273 target and retains every containing choice')
        if name in names:
            position = names.index(name)
            require(index == 48 and functions[position] == fn and polynomials[position] == poly
                    and prior <= bounds[position] and upper < bounds[position],
                    'The same original cost48 improves within the previous complete basis')
            changed.append({'name': name, 'previous_upper': bounds[position], 'updated_upper': upper, 'source': '274'})
            bounds[position] = upper
        else:
            require(index == 49, 'Only original cost49 is a new scalar observation')
            names.append(name); functions.append(fn); polynomials.append(poly); bounds.append(upper)
            added.append({'name': name, 'upper': upper, 'source': '274', 'original_cost_index': index})
    require(len(changed) == 1 and changed[0]['name'] == 'cost48'
            and len(added) == 1 and added[0]['name'] == 'cost49'
            and sum(a != b for a, b in zip(bounds, prior_bounds)) == 1
            and len(names) == len(functions) == len(polynomials) == len(bounds) == 26,
            'All25 prior observations remain, with stronger cost48 and original cost49 as the26th observation')
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete273 bound')
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
    require(lower['comparison'] > 403 and 0 <= gap < F(1, 10**10)
            and upper['comparison'] < old_comparison,
            'The new tight independent-moment bracket remains above403 and strictly improves the complete comparison')
    result = {'schema': 'erdos7-j-face-generalized-factorial-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'counts': {'basis_functions': len(names), 'updated_basis_bounds': len(data['changed_basis_bounds']),
                         'added_basis_bounds': len(data['added_basis_bounds']),
                         'targets': len(rows), 'cost_targets': len(data['weights']),
                         'low_load_inequalities': len(rows)*(TAIL_ENTRANCE-1), 'whole_tail_polynomials': len(rows),
                         'exact_witness_moment_checks': len(rows)*len(names),
                         'positive_witness_atoms': sum(len(p['finite_moment_witness']) for p in proof_data),
                         'nonzero_envelope_coefficients': sum(len(p['coefficients']) for p in proof_data)},
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All25 previous scalar observations remain; original cost48 improves via itsPhi3 expansion and original cost49 is the26th scalar observation via itsPhi2 expansion. Both complete source bounds use274 actual common raw and survivor factorial crosses, distinct threshold-specific caches and unchanged complete pair tail4879/7200. Every original function retains independently chosen original test labels. All59 whole-positive-integer envelopes and59 fresh independent finite moment witnesses are checked against all26 current constraints. Exact mass3/20, all signed payments, all four AP11 blocks, AP13 and the entire count tail are recomputed. The witnesses constrain only this updated independent scalar-moment method and need not be actual sources or coexist on one actual family. The old273 method bracket is not reused. No actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
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
