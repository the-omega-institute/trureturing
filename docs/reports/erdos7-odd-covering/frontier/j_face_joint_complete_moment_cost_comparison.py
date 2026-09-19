#!/usr/bin/env python3
"""Complete independent J cost envelopes with244 heads and245 square."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j_face_joint_complete_moment_cost_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j_face_complete_moment_cost_comparison.py': '3ee3a0c5fafb61a918db124f32a81ed272d4ebed29a2dc99c40a656f2a2dbc01', 'certificates/source_norms/j_face_complete_moment_cost_comparison.json': '89e5a1101aaa20051cccaab47318ea4ac222d1e158bb8273d15d56bbe3efb8b1', 'frontier/j_face_joint_selected_heads.py': '01033d19b43910a667954005342d2a03fe57dd6f621bf319398cfdb77ec821ec', 'certificates/source_norms/j_face_joint_selected_heads.json': '87038435aecbfee3d5a3845c29fe9ece863652a79a35312af00f1096b952fed6', 'frontier/j_face_joint_retained_square.py': '7f4bcecb86c0cdb53b06f4b338366324d61a6acd13a1c566645ccfc0cf34f7f0', 'certificates/source_norms/j_face_joint_retained_square.json': '7d32a00575385a0af956ada8f89f4c2cf92fe723855ff5695262ebf29be15504', 'profile-notes/243-all-original-j-costs-have-exact-moment-envelopes-and-a-method-boundary.md': '8182e4c87846ef722e9bdfe3ef318351e169532a4c1d1e26f9362c2ff916f14e', 'profile-notes/245-the-actual-j-survivor-mass-and-h-column-sharpen-the-complete-square.md': '9d1888a68947501b2dfb0de0c8245167de09038f64925db3850b33e232cd1146'}
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
    previous = module('joint_j_envelope_previous', base/'frontier/j_face_complete_moment_cost_comparison.py')
    (io, pins, geometry, names, functions, polynomials, bounds, targets,
     tags, weights, signed, outside_square, offset, count) = previous.inputs(base)
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=previous.unique)
    old = read('j_face_complete_moment_cost_comparison')
    heads, square = read('j_face_joint_selected_heads'), read('j_face_joint_retained_square')
    original_heads = read('j_face_coupled_seven_heads')
    for source in (old, heads, square):
        for path, pin in source['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent full J source closure '+path)
            pins[path] = pin
    for path, pin in PINS.items():
        require(path not in pins or pins[path] == pin, 'Consistent direct mathematical input '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical source '+path)
    require(geometry == old['geometry'] == heads['geometry'] == square['geometry']
            and F(square['survivor_mass']) == MASS
            and F(square['complete_mean_upper']) == bounds[names.index('mean')]
            and F(square['complete_factorial_upper']) == bounds[names.index('factorial5')],
            'One entire actual J domain, exact mass, unchanged mean/factorial and common late split')
    prior_bounds = list(bounds)
    bounds = list(bounds)
    changed = []
    source_square = F(square['complete_square_upper'])
    require(source_square == F(5539, 1200) < bounds[names.index('square')], 'Complete245 square on the same actual source')
    changed.append({'name': 'square', 'previous_upper': bounds[names.index('square')],
                    'updated_upper': source_square, 'source': '245'})
    bounds[names.index('square')] = source_square
    original = {str(row['index']): row for row in original_heads['results']}
    improved = {str(row['index']): row for row in heads['results']}
    require(set(original) == set(improved) == {'AP13', '0', '16'}, 'All three original complete J head objectives')
    for index, name in (('AP13', 'hinge4'), ('0', 'cost0'), ('16', 'cost16')):
        row, prior = improved[index], original[index]
        require(row['scan']['coefficients'] == prior['scan']['coefficients']
                and F(row['at_one']) == F(prior['at_one']), 'The same complete original function for '+name)
        coefficients = {int(t): F(v) for t, v in row['scan']['coefficients'].items()}
        require(coefficients and min(coefficients.values()) > 0, 'Positive original J hinge combination')
        at_one = F(row['at_one'])
        raw = at_one*MASS+F(row['scan']['complete_hinge_upper'])
        mean = at_one*MASS+sum(coefficients.values())*(bounds[names.index('mean')]-MASS)
        adopted = F(row['adopted_upper'])
        k = names.index(name)
        require(F(row['complete_head_upper']) == raw
                and adopted == min(raw, F(prior['adopted_upper']), mean)
                and 0 < adopted < bounds[k], 'Exact complete244 adoption and strict same-source improvement for '+name)
        changed.append({'name': name, 'previous_upper': bounds[k], 'updated_upper': adopted, 'source': '244'})
        bounds[k] = adopted
    require(len(names) == len(bounds) == 22 and sum(a != b for a, b in zip(prior_bounds, bounds)) == 4
            and all(0 < a <= b for a, b in zip(bounds, prior_bounds)), 'Exactly four stronger bounds with all22 original basis functions retained')
    require([row['name'] for row in old['basis']] == names
            and [F(row['upper']) for row in old['basis']] == prior_bounds
            and old['all_original_indices'] == list(range(52)), 'The complete243 baseline and exact basis order')
    return {'previous': previous, 'io': io, 'pins': pins, 'geometry': geometry, 'names': names,
            'functions': functions, 'polynomials': polynomials, 'bounds': bounds, 'targets': targets,
            'tags': tags, 'weights': weights, 'signed': signed, 'outside_square': outside_square,
            'offset': offset, 'count': count, 'old': old, 'changed_basis_bounds': changed}


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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete243 bound')
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
    result = {'schema': 'erdos7-j-face-joint-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
              'geometry': data['geometry'], 'survivor_mass': MASS, 'all_original_indices': list(range(52)),
              'original_cost_tags': data['tags'], 'cost_weights': data['weights'],
              'signed_mass_coefficient': data['signed'], 'complete_square_weight': data['outside_square'],
              'offset': data['offset'], 'count_law': data['count'], 'changed_basis_bounds': data['changed_basis_bounds'],
              'basis': [{'name': name, 'upper': bound, 'mass_is_exact': name == 'mass',
                         'low_load_values': [f(n) for n in range(1, TAIL_ENTRANCE)], 'tail_polynomial': polynomial}
                        for name, bound, f, polynomial in zip(names, bounds, functions, polynomials)],
              'proof_data': proof_data, 'results': rows, 'comparison_upper': upper,
              'previous_comparison_upper': old_comparison, 'complete_comparison_improvement': old_comparison-upper['comparison'],
              'independent_moment_method_lower': lower, 'method_bracket_width': gap,
              'counts': {'basis_functions': len(names), 'updated_basis_bounds': len(data['changed_basis_bounds']),
                         'targets': len(rows), 'cost_targets': len(data['weights']),
                         'low_load_inequalities': len(rows)*(TAIL_ENTRANCE-1), 'whole_tail_polynomials': len(rows),
                         'exact_witness_moment_checks': len(rows)*len(names),
                         'positive_witness_atoms': sum(len(p['finite_moment_witness']) for p in proof_data),
                         'nonzero_envelope_coefficients': sum(len(p['coefficients']) for p in proof_data)},
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. The original22 scalar basis functions retain independently chosen test labels; only244 hinge4/heavy0/heavy16 and245 square bounds change. Exact mass3/20, every signed payment, all four AP11 blocks and the complete count tail are recomputed. The independent rational witnesses bound only this updated scalar-moment relaxation; they need not be actual source configurations or coexist on one actual family. The old243 method bracket is not reused. No off-face/global join, actual attainment, unrestricted Erdos7 result or Lean verification is asserted.'}
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
