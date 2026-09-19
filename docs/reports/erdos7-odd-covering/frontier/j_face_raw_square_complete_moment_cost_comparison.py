#!/usr/bin/env python3
"""Complete J costs with a stronger complete raw-square pair tail."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j_face_raw_square_complete_moment_cost_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j_face_retained_pair_complete_moment_cost_comparison.py': '1777b9b0d7f91b0c561a171e2e4995316068b9db4837bff6690460f88ce7df68', 'certificates/source_norms/j_face_retained_pair_complete_moment_cost_comparison.json': '988ebe739b00cbd88fada0ecde846b5d7af01b8eec3254698d368a50b4a7c38b', 'profile-notes/254-retained-original-heads-and-prime-path-square-improve-the-complete-j-comparison.md': 'e07a45e77f8c4117d6921264b7efd10d6d6e166f1e07229c63271e31998a251b', 'frontier/j_face_coherent_positive7_pairs.py': 'd643cc68b0c0d076a29246e78c75d1f6d6778617a852fa0bb738a18d2554619c', 'certificates/source_norms/j_face_coherent_positive7_pairs.json': '1840efa1ced6f86beb990cb03ee4cce3be8c3e04d1508268c598c7f0a5076845', 'profile-notes/258-independent-positive-seven-depths-share-one-complete-raw-source.md': '2d2ebe6ca7762c9b7da6b8900c2412667f2df303303fe4a3ae5b5d60951c5090'}
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
    prior_module = module('raw_square_j_envelope_previous', base/'frontier/j_face_retained_pair_complete_moment_cost_comparison.py')
    data = prior_module.inputs(base)
    previous, io = data['previous'], data['io']
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=previous.unique)
    old = read('j_face_retained_pair_complete_moment_cost_comparison')
    source = read('j_face_coherent_positive7_pairs')
    pins = dict(data['pins'])
    for certificate in (old, source):
        require(certificate['geometry'] == data['geometry'] and F(certificate['survivor_mass']) == MASS,
                'Every input uses the same two entire saturated actual J faces and exact mass')
        for path, pin in certificate['source_sha256'].items():
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
            and len(names) == 24 and old['all_original_indices'] == list(range(52)),
            'The exact complete254 baseline with all24 moment constraints')
    prior_bounds = list(bounds)
    changed = []
    def replace(name, bound):
        k = names.index(name)
        require(0 < bound < bounds[k], 'Strict same-domain bound improvement for '+name)
        changed.append({'name': name, 'previous_upper': bounds[k], 'updated_upper': bound, 'source': '258'})
        bounds[k] = bound
    gain = F(source['complete_pair_improvement'])
    old_tail = source['original_complete_tail_partition']
    old_pairs, new_pairs = F(old_tail['distinct_tail_pairs']), F(source['complete_tail_distinct_pairs'])
    require(gain == F(29, 1080) and F(old_tail['positive7_positive7_distinct']) == F(2, 5)
            and F(source['complete_PZZ_upper']) == F(403, 1080) == F(2, 5)-gain
            and old_pairs == F(5089, 7200) and new_pairs == old_pairs-gain
            and new_pairs == F(old_tail['old_old_distinct'])+F(old_tail['old_positive7'])+F(source['complete_PZZ_upper'])
            and F(source['complete_ordered_tail_square']) == F(old_tail['complete_ordered_tail_square'])-2*gain
            and F(source['complete_mean_upper']) == bounds[names.index('mean')],
            'The complete258 positive-seven pair replacement preserves every other pair, both diagonals and mean')
    for name, stem, coefficient, expected in (('square', 'square', F(2), F(49001, 10800)),
                                             ('factorial5', 'factorial', F(1), F(18359, 21600))):
        prior, upper = F(source['previous_complete_'+stem+'_upper']), F(source['complete_'+stem+'_upper'])
        require(prior == bounds[names.index(name)] and upper == expected == prior-coefficient*gain
                and F(source['complete_'+stem+'_improvement']) == coefficient*gain,
                'The complete258 '+stem+' replaces only its assigned full pair block')
        replace(name, upper)
    require(source['original_cost_indices'] == [47, 48]
            and [row['index'] for row in source['quadratic_results']] == [47, 48],
            'Exactly the two independently labelled original quadratic costs')
    for row in source['quadratic_results']:
        index = row['index']; name = 'cost'+str(index)
        prior, upper = F(row['previous_cost_upper']), F(row['cost_upper'])
        head = F(row['unchanged_joint_head_upper'])
        old_charge, new_charge = F(row['old_complete_pair_charge']), F(row['new_complete_pair_charge'])
        require(row['tag'] == encode(data['tags'][index]) and prior == bounds[names.index(name)]
                and old_charge == 2*old_pairs and new_charge == 2*new_pairs
                and prior == head+old_charge and upper == head+new_charge == prior-2*gain
                and F(row['cost_improvement']) == 2*gain,
                'The exact original quadratic function retains its complete head and substitutes the same complete pair tail')
        replace(name, upper)
    require(sum(a != b for a, b in zip(bounds, prior_bounds)) == 4
            and len(names) == len(functions) == len(polynomials) == len(bounds) == 24,
            'Exactly four source bounds improve while all24 basis functions remain')
    data.update(pins=pins, names=names, functions=functions, polynomials=polynomials,
                bounds=bounds, old=old, changed_basis_bounds=changed, added_basis_bounds=[])
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete254 bound')
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
    result = {'schema': 'erdos7-j-face-raw-square-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All24 previous scalar basis functions retain independently chosen original test labels. Only258 square, factorial5 and original cost47/cost48 bounds change. Every one of59 exact integer envelopes and59 independent finite moment witnesses is verified against all24 updated constraints. Exact mass3/20, every signed payment, all four AP11 blocks, AP13 and the complete count tail are recomputed. The witnesses constrain only this updated scalar-moment method; they need not be actual source configurations or coexist on one actual family. The old254 method bracket is not reused. No actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
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
        proposed = json.loads(args.proposal.read_text(), object_pairs_hook=previous.unique)
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
