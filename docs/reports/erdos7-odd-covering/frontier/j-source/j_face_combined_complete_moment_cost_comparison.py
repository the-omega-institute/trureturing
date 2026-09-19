#!/usr/bin/env python3
"""Complete J cost envelopes with joint quadratic, factorial and AP11 bounds."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_face_combined_complete_moment_cost_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j-source/j_face_joint_complete_moment_cost_comparison.py': '1813e5a88ddbfa1e63250d8b6da5e99cbf26d0ad768a3eec5fbd5b8e174e593b', 'certificates/source_norms/j-source/j_face_joint_complete_moment_cost_comparison.json': '0d541ec224303be93fc997910b81f407b839931af9a62bc5bb3c191712563f7a', 'profile-notes/j-source/246-the-joint-j-heads-and-square-improve-the-complete-cost-comparison.md': '307cfc05d509d0410dc051831c8e5be372c36feaaf1e84ef569d60f3dab35891', 'frontier/j-source/j_face_joint_quadratic_heads.py': '43186a9df119b1f09059a349b0a3c9a8cc6a66e5d9745cfb847688e7dc367c3a', 'certificates/source_norms/j-source/j_face_joint_quadratic_heads.json': 'f01396b853d869c86fb3e615e88bf348d4c21a21c2cda07ac31793d3ba1f9345', 'profile-notes/j-source/247-two-original-j-quadratic-costs-share-hinges-and-factorial-head.md': '54d25458fa8d5fb4a5f36894b72917e5a6104c8c79196ac51ea535727e69aaa8', 'frontier/j-source/j_face_pure_path_factorial.py': 'b0888d8b5094782439a113b9a04d936dfcf6df4ce1190e8a0e9e6aa254631930', 'certificates/source_norms/j-source/j_face_pure_path_factorial.json': '119ea1549bd3edff0ecad0f74859660dff68ee64cd995c3d49583ceb2a70dd59', 'profile-notes/j-source/248-the-complete-j-factorial-tail-retains-both-prime-paths.md': '295efbd2439d70186636cf8943f0c6253bc02f0fcf506a2296163b62614252ef', 'frontier/j-source/j_face_joint_survival_heads.py': 'ef29e4e8b7136e31551f5cc7ab85ee25febe188068db532d15fcb55c6cd08526', 'certificates/source_norms/j-source/j_face_joint_survival_heads.json': 'f92cd5001e5fdbd3d8ede07e5ad7221790f7d393253aa9c6f455454ff9942bbc', 'profile-notes/j-source/249-all-four-complete-j-ap11-blocks-retain-the-same-marked-source.md': '6aad5ff9cfa441f8265541d8528f7f689793f9a2440468672209383d77258862'}
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
    prior_module = module('combined_j_envelope_previous', base/'frontier/j-source/j_face_joint_complete_moment_cost_comparison.py')
    data = prior_module.inputs(base)
    previous, io = data['previous'], data['io']
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=previous.unique)
    old = read('j-source/j_face_joint_complete_moment_cost_comparison')
    quadratic = read('j-source/j_face_joint_quadratic_heads')
    factorial = read('j-source/j_face_pure_path_factorial')
    survival = read('j-source/j_face_joint_survival_heads')
    pins = dict(data['pins'])
    for source in (old, quadratic, factorial, survival):
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
            and len(names) == 22 and old['all_original_indices'] == list(range(52)),
            'The exact complete246 baseline with all22 moment constraints')
    prior_bounds = list(bounds)
    changed = []
    def replace(name, bound, source):
        k = names.index(name)
        require(0 < bound < bounds[k], 'Strict same-domain bound improvement for '+name)
        changed.append({'name': name, 'previous_upper': bounds[k], 'updated_upper': bound, 'source': source})
        bounds[k] = bound
    require(F(factorial['old_complete_factorial_upper']) == bounds[names.index('factorial5')]
            and F(factorial['complete_factorial_upper']) == F(6313, 7200)
            and F(factorial['complete_mean_upper']) == bounds[names.index('mean')],
            'The complete248 factorial replaces its previous bound on the identical source')
    replace('factorial5', F(factorial['complete_factorial_upper']), '248')
    require(survival['count_law'] == old['count_law']
            and F(survival['inherited_AP13_upper']) == bounds[names.index('hinge4')]
            and F(survival['complete_mean_upper']) == bounds[names.index('mean')]
            and [row['name'] for row in survival['results']] == ['AP11-'+str(i) for i in range(4)],
            'All four original AP11 blocks, unchanged AP13, mean and complete count law')
    for row in survival['results']:
        name = row['name']; k = names.index(name)
        coefficients = {int(t): F(v) for t, v in row['coefficients'].items()}
        require(coefficients and min(coefficients.values()) > 0 and min(coefficients) >= 1
                and max(coefficients) < TAIL_ENTRANCE and F(row['at_one']) == 0,
                'Positive original all-load AP11 hinge combination')
        continuation = (-sum(t*v for t, v in coefficients.items()), sum(coefficients.values()), F(0))
        require(continuation == polynomials[k]
                and all(sum(v*max(n-t, 0) for t, v in coefficients.items()) == functions[k](n)
                        for n in range(1, TAIL_ENTRANCE)), 'The identical original AP11 function on every positive integer')
        upper, prior = F(row['adopted_upper']), F(row['previous_adopted_upper'])
        mean = sum(coefficients.values())*(bounds[names.index('mean')]-MASS)
        require(prior == bounds[k] and row['scan']['coefficients'] == row['coefficients']
                and F(row['complete_head_upper']) == F(row['scan']['complete_hinge_upper'])
                and F(row['complete_mean_only_upper']) == mean
                and upper == min(F(row['complete_head_upper']), prior, mean),
                'Complete249 same-function head adoption with every tail retained')
        replace(name, upper, '249')
    require(sum(a != b for a, b in zip(bounds, prior_bounds)) == 5,
            'Exactly the factorial and four AP11 inequalities change among the original basis')
    target_map = {name: (function, polynomial) for name, function, polynomial in data['targets']}
    old_results = {row['name']: F(row['upper']) for row in old['results']}
    require(quadratic['original_cost_indices'] == [47, 48]
            and [row['index'] for row in quadratic['quadratic_results']] == [47, 48],
            'Exactly both new original quadratic cost inequalities')
    added = []
    for row in quadratic['quadratic_results']:
        index = row['index']; name = 'cost'+str(index)
        target, polynomial = target_map['cost-'+str(index)]
        expansion = row['expansion']
        co = {int(t): F(v) for t, v in expansion['hinge_coefficients'].items() if F(v)}
        fc, at_one = F(expansion['factorial_tail_coefficient']), F(expansion['at_one'])
        phi = functions[names.index('factorial5')]
        continuation = (at_one-sum(t*v for t, v in co.items())+10*fc,
                        sum(co.values())-F(9,2)*fc, fc/2)
        require(row['tag'] == encode(data['tags'][index]) and fc == 2 and at_one >= 0
                and co and min(co.values()) > 0 and max(co) < TAIL_ENTRANCE
                and continuation == polynomial
                and all(at_one+sum(v*max(n-t,0) for t,v in co.items())+fc*phi(n) == target(n)
                        for n in range(1, TAIL_ENTRANCE)),
                'The exact original quadratic function and its entire polynomial continuation')
        pair = F(quadratic['complete_tail_distinct_pairs'])
        outside = at_one*MASS+fc*pair
        upper = F(row['cost_upper'])
        require(pair == F(5089,7200) and F(row['scan']['factorial_coefficient']) == fc
                and row['scan']['hinge_coefficients'] == encode(co)
                and F(row['scan']['complete_pair_tail_charge']) == fc*pair
                and F(row['constant_mass_and_complete_pair_tail']) == outside
                and upper == F(row['scan']['joint_head_upper'])+outside
                and 0 < upper < F(row['previous_cost_upper']) == old_results['cost-'+str(index)],
                'The complete247 same-source quadratic bound with mass and every distinct tail pair')
        names.append(name); functions.append(target); polynomials.append(polynomial); bounds.append(upper)
        added.append({'name': name, 'upper': upper, 'source': '247', 'original_index': index})
    require(len(names) == len(functions) == len(polynomials) == len(bounds) == 24,
            'All22 original basis functions and both additional original cost inequalities')
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete246 bound')
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
    result = {'schema': 'erdos7-j-face-combined-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
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
              'scope': 'Complete original52-cost comparison on both entire actual saturated J faces. All22 original scalar basis functions retain independent test labels; the complete248 factorial and249 four AP11 bounds improve five inequalities, and247 adds two complete original quadratic cost inequalities. All59 envelopes cover every positive integer, and each independent finite moment witness satisfies all24 updated constraints. Exact mass3/20, every signed payment, all AP11 blocks, AP13 and the whole count tail are recomputed. Lower witnesses bound only this updated independent scalar-moment method and need not be actual source configurations or coexist on one actual family. The old246 method bracket is not reused. No actual attainment, off-face/global join, unrestricted Erdos7 result or Lean verification is asserted.'}
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
