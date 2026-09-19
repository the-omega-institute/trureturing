#!/usr/bin/env python3
"""Complete J costs with two stronger second-depth survival blocks."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_second_depth_survival_complete_moment_cost_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/j-geometry/j_face_second_depth_complete_moment_cost_comparison.py': '95c581a71c7b8ce57ab92b66e1a2fceb267573f6ca3c88fc20b97e7636de0204', 'certificates/source_norms/j-geometry/j_face_second_depth_complete_moment_cost_comparison.json': '4124976e43b9e7a82ef7df35fff3c488743169f8e2e1db98a9186c9c136e8e56', 'profile-notes/257-320/262-a-second-seven-depth-improves-the-full-j-comparison.md': 'fbd6e95fb32c5769d25324eb4b339ce6adb468685905ef3cd6ea6f46fce2ff6f', 'frontier/j-geometry/j_face_second_depth_survival_heads.py': 'b4cccdc886a094bbda8967343af8b28726ed6c1a004f5f7e43c46fdcd6c7a4c7', 'certificates/source_norms/j-geometry/j_face_second_depth_survival_heads.json': '2d3f18c0325b2518a8c56207341a092c9b79a4d9df0ad5fbd92734545bdb8a6b', 'profile-notes/257-320/266-two-original-ap11-blocks-use-the-complete-second-depth-interface.md': 'c4552881dbe56109092b7a721e512ef642dc68853cbc25456db176b3f853e00a'}
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
    prior_module = module('second_depth_survival_j_envelope_previous', base/'frontier/j-geometry/j_face_second_depth_complete_moment_cost_comparison.py')
    data = prior_module.inputs(base)
    previous, io = data['previous'], data['io']
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),
                                   object_pairs_hook=previous.unique)
    old = read('j_face_second_depth_complete_moment_cost_comparison')
    heads = read('j_face_second_depth_survival_heads')
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
            and len(names) == 24 and old['all_original_indices'] == list(range(52)),
            'The exact complete262 baseline with all24 moment constraints')
    prior_bounds = list(bounds)
    changed = []
    require(heads['count_law'] == old['count_law']
            and F(heads['complete_mean_upper']) == bounds[names.index('mean')]
            and F(heads['complete_AP13_upper']) == bounds[names.index('hinge4')]
            and [row['name'] for row in heads['results']] == ['AP11-0', 'AP11-1']
            and heads['retained_positive7_labels'] == [21, 35, 63, 105, 147, 245]
            and F(heads['complete_positive7_tail']) == F(37, 1225),
            'Exactly two original complete266 blocks, the same AP13, mean and infinite count law')
    for row in heads['results']:
        name = row['name']; k = names.index(name)
        co = {int(t): F(v) for t, v in row['coefficients'].items()}
        require(co and min(co.values()) > 0 and min(co) >= 1
                and max(co) < TAIL_ENTRANCE and F(row['at_one']) == 0
                and row['scan']['coefficients'] == row['coefficients'],
                'The original positive complete AP11 hinge expansion')
        continuation = (-sum(t*v for t, v in co.items()), sum(co.values()), F(0))
        require(continuation == polynomials[k]
                and all(sum(v*max(n-t, 0) for t, v in co.items()) == functions[k](n)
                        for n in range(1, TAIL_ENTRANCE)),
                'The same original AP11 block function on every positive integer')
        raw = F(row['scan']['complete_hinge_upper'])
        mean = sum(co.values())*(bounds[names.index('mean')]-MASS)
        upper, prior = F(row['adopted_upper']), F(row['previous_adopted_upper'])
        require(prior == bounds[k] and F(row['complete_head_upper']) == raw
                and F(row['complete_mean_only_upper']) == mean
                and upper == min(raw, prior, mean) and 0 < upper < prior,
                'The complete266 block includes every exponent tail and strictly improves the identical basis bound')
        changed.append({'name': name, 'previous_upper': prior, 'updated_upper': upper, 'source': '266'})
        bounds[k] = upper
    require([row['name'] for row in heads['unchanged_AP11_bounds']] == ['AP11-2', 'AP11-3']
            and all(F(row['adopted_upper']) == bounds[names.index(row['name'])]
                    for row in heads['unchanged_AP11_bounds']),
            'Both remaining original AP11 input bounds are retained completely')
    count = data['count']
    tail = count['remaining_hinge1_coefficient']*(bounds[names.index('mean')]-MASS)+count['whole_constant_coefficient']*MASS
    old_sum = sum(prior_bounds[names.index('AP11-'+str(i))] for i in range(4))
    new_sum = sum(bounds[names.index('AP11-'+str(i))] for i in range(4))
    before = MASS-bounds[names.index('hinge4')]/6-(old_sum+tail)/7
    after = MASS-bounds[names.index('hinge4')]/6-(new_sum+tail)/7
    require(F(heads['complete_count_tail_upper']) == tail == F(277, 4392300)
            and F(heads['previous_AP11_sum']) == old_sum and F(heads['complete_AP11_sum']) == new_sum
            and F(heads['previous_survival_denominator']) == before
            and F(heads['complete_survival_denominator']) == after
            and F(heads['survival_denominator_improvement']) == after-before == (old_sum-new_sum)/7 > 0,
            'The direct266 source denominator contains all four original blocks, AP13 and every count-tail term')
    require(sum(a != b for a, b in zip(bounds, prior_bounds)) == 2
            and len(names) == len(functions) == len(polynomials) == len(bounds) == 24,
            'Exactly two source bounds improve while all24 basis functions remain')
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete262 bound')
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
    result = {'schema': 'erdos7-j-face-second-depth-survival-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All24 previous scalar basis functions retain independently chosen original test labels. Only266 original AP11-0/AP11-1 bounds change. Every one of59 exact integer envelopes and59 independent finite moment witnesses is verified against all24 updated constraints. Exact mass3/20, every signed payment, all four AP11 blocks, AP13 and the complete count tail are recomputed. The witnesses constrain only this updated scalar-moment method; they need not be actual source configurations or coexist on one actual family. The old262 method bracket is not reused. No actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
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
