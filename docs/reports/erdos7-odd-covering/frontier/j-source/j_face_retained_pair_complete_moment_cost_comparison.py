#!/usr/bin/env python3
"""Complete J costs with retained135/125 heads and prime-path square blocks."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_face_retained_pair_complete_moment_cost_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j-source/j_face_combined_complete_moment_cost_comparison.py': '77544d1b14deb1da658f19564331b9fe38955f63500615b25b37c03b4f18126a', 'certificates/source_norms/j-source/j_face_combined_complete_moment_cost_comparison.json': 'a6b4239551739fddd6555f298a81ad4031219576b325e41de42f8da7d1ca6a78', 'profile-notes/j-source/250-joint-quadratic-factorial-and-survival-bounds-improve-the-complete-j-comparison.md': 'da61e5cf555c4190a055c4bedd0a99832f0d9b766aac1be67cb588db6b60e60c', 'frontier/j-source/j_face_retained135125_heads.py': '9af138e632fc8d9ec4f8be253e01fbbedd004ba378b1b89212bf2def557ea2f8', 'certificates/source_norms/j-source/j_face_retained135125_heads.json': '4a8eb666d29a6d56c8e33100d283e192d52dba526ecae4e5c631ce83e88bdd86', 'profile-notes/j-source/251-two-retained-original-tests-sharpen-the-complete-j-heads.md': '7d5cfb5b75f9c577aa52c9845f7f304808b9dd7c66e7069f6b7a05497572c555', 'frontier/j-source/j_face_pure_path_square.py': 'f128a419ee8dd12fc16b98cc11d0bd77a4d51da5af61c20b5c004487822bb3ba', 'certificates/source_norms/j-source/j_face_pure_path_square.json': 'd6e279c7a28222d321fffb4fd492c92d3e0efb942b3f35cb7d1ae3f38e81fc4e', 'profile-notes/j-source/253-two-complete-prime-path-blocks-sharpen-the-j-square.md': 'f23d3e22ad39eb40f81882ba3f15a24e0f9de41b290aa5e41c7150b6c886125e'}
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
    prior_module = module('retained_pair_j_envelope_previous', base/'frontier/j-source/j_face_combined_complete_moment_cost_comparison.py')
    data = prior_module.inputs(base)
    previous, io = data['previous'], data['io']
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=previous.unique)
    old = read('j-source/j_face_combined_complete_moment_cost_comparison')
    heads, square = read('j-source/j_face_retained135125_heads'), read('j-source/j_face_pure_path_square')
    pins = dict(data['pins'])
    for source in (old, heads, square):
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
            'The exact complete250 baseline with all24 moment constraints')
    prior_bounds = list(bounds)
    changed = []
    def replace(name, bound, source):
        k = names.index(name)
        require(0 < bound < bounds[k], 'Strict same-domain bound improvement for '+name)
        changed.append({'name': name, 'previous_upper': bounds[k], 'updated_upper': bound, 'source': source})
        bounds[k] = bound
    require(F(square['previous_complete_square_upper']) == bounds[names.index('square')]
            and F(square['complete_square_upper']) == F(5509, 1200)
            and F(square['complete_factorial_upper']) == bounds[names.index('factorial5')]
            and F(square['complete_mean_upper']) == bounds[names.index('mean')],
            'The complete253 square replaces its previous bound with unchanged mean and factorial')
    replace('square', F(square['complete_square_upper']), '253')
    require(F(heads['complete_mean_upper']) == bounds[names.index('mean')]
            and [str(row['index']) for row in heads['results']] == ['AP13', '0', '16'],
            'Exactly the three original complete independent251 head functions')
    for row, name in zip(heads['results'], ('hinge4', 'cost0', 'cost16')):
        k = names.index(name)
        co = {int(t): F(v) for t, v in row['scan']['coefficients'].items()}
        at_one = F(row['at_one'])
        require(co and min(co.values()) > 0 and min(co) >= 1
                and max(co) < TAIL_ENTRANCE and at_one >= 0,
                'Positive original complete affine head expansion')
        continuation = (at_one-sum(t*v for t, v in co.items()), sum(co.values()), F(0))
        require(continuation == polynomials[k]
                and all(at_one+sum(v*max(n-t, 0) for t, v in co.items()) == functions[k](n)
                        for n in range(1, TAIL_ENTRANCE)),
                'The same original head function on every positive integer')
        raw = at_one*MASS+F(row['scan']['complete_hinge_upper'])
        mean = at_one*MASS+sum(co.values())*(bounds[names.index('mean')]-MASS)
        upper, prior = F(row['adopted_upper']), F(row['previous_adopted_upper'])
        require(prior == bounds[k] and F(row['complete_head_upper']) == raw
                and F(row['complete_mean_only_upper']) == mean
                and upper == min(raw, prior, mean),
                'The complete251 retained135/125 head with every original tail and exact adoption')
        replace(name, upper, '251')
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete250 bound')
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
    result = {'schema': 'erdos7-j-face-retained-pair-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All24 previous scalar basis functions retain independently chosen original test labels. Only251 hinge4/heavy0/heavy16 and253 square bounds change. Every one of59 exact integer envelopes and59 independent finite moment witnesses is verified against all24 updated constraints. Exact mass3/20, every signed payment, all four AP11 blocks, AP13 and the complete count tail are recomputed. The witnesses constrain only this updated scalar-moment method; they need not be actual source configurations or coexist on one actual family. The old250 method bracket is not reused. No actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
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
