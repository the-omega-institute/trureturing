#!/usr/bin/env python3
"""Complete saturated-J comparison below403 with the retained375 heavy bound."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_face_heavy_positive175189_complete_moment_cost_comparison.json'
PINS = {'frontier/j-source/j_face_joint_positive175189_complete_moment_cost_comparison.py': 'd4906f9d851c097dd1339fdb0e27f1a05d8c99bfea994da9bf6a028fd1656df6', 'certificates/source_norms/j-source/j_face_joint_positive175189_complete_moment_cost_comparison.json': 'efd69ea3cac1e32b3419dc5bb7b21f19efc61f9f634d37d9f39d339ea9673b0c', 'profile-notes/j-source/297-joint-positive175189-improves-the-complete-j-comparison.md': 'bdfa9f91e074bcc7191c3d5733703728518b4deacb3cea81a6932a47ae244c46', 'frontier/j-source/j_face_retained375_heavy_heads.py': 'fde2ab1ef212cf69f97ec94eaa4d6764fa0f5205d10d9304c2e78a600e0dae31', 'certificates/source_norms/j-source/j_face_retained375_heavy_heads.json': '066de548c01bc9809e8c528f2f2eb9fdeac44412b8ba9842d2ce2f804c69f766', 'profile-notes/j-source/298-retaining375-certifies-the-complete-heavy-cost.md': '8b12202c80972a5d331676209413122f05dfb8ce69f5ca13352c8abd645435f5'}
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
    require(PINS, 'Final exact mathematical input pins')
    prior = module('heavy_positive_comparison297', base/'frontier/j-source/j_face_joint_positive175189_complete_moment_cost_comparison.py')
    data = prior.inputs(base)
    previous, io = data['previous'], data['io']
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=previous.unique)
    old = read('j-source/j_face_joint_positive175189_complete_moment_cost_comparison')
    heavy = read('j-source/j_face_retained375_heavy_heads')
    pins = dict(data['pins'])
    for item in (old, heavy):
        require(item['geometry'] == data['geometry'] and F(item['survivor_mass']) == MASS,
                'Both entire actual saturated J faces on the same original survivor measure')
        for path, pin in item['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent mathematical source '+path)
            pins[path] = pin
    for path, pin in PINS.items():
        require(path not in pins or pins[path] == pin, 'Consistent direct mathematical input '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical source '+path)
    names, functions, polynomials, bounds = (list(data[k]) for k in ('names', 'functions', 'polynomials', 'bounds'))
    require([r['name'] for r in old['basis']] == names and [F(r['upper']) for r in old['basis']] == bounds
            and len(names) == 34 and old['all_original_indices'] == list(range(52)),
            'The complete297 baseline preserves all34 observations and52 distinct original cost functions')
    require(heavy['schema'] == 'erdos7-j-face-retained375-heavy-heads-v1'
            and F(heavy['source_mass']) == F(1, 4) and heavy['index'] == 0 and heavy['name'] == 'cost0'
            and heavy['retained_old_labels'] == [25,27,75,81,135,125,225,375]
            and heavy['retained_positive7_labels'] == [21,35,63,105,147,245,441,735]
            and heavy['model']['rows_sha256'] == 'e591c59f8891f6647f0e21f303cd3be9ca661f1d5b48ebd0625c2de85cfa32d0'
            and heavy['model']['variables'] == 12941 and heavy['model']['inequalities'] == 30454
            and heavy['model']['equalities'] == 20,
            'The complete unchanged original375 source model, with every original independent projection')
    require(F(heavy['complete_old_tail']) == F(5071,405000)
            and F(heavy['complete_positive7_tail']) == F(13,490)
            and F(heavy['complete_late_slope']) == F(403,8)
            and F(heavy['complete_tail_constant']) == F(403,8)*(F(5071,405000)+F(13,490)) == F(312316537,158760000)
            and heavy['total_containing_choices'] == heavy['prefix_ledger']['covered_containing_choices'] == 3125000000
            and heavy['own_bound_closed_leaves'] == 2768
            and heavy['covering_leaf_counts'] == {'prior70':305,'stage1':13569,'stage2':3611,'stage3':161,'final':15}
            and heavy['own_bound_closed_leaves']+sum(heavy['covering_leaf_counts'].values())
                == heavy['original_residual_leaf_count'] == 20429
            and heavy['target_closed'] and F(heavy['complete_upper']) == F(543,100),
            'The completed full prefix and exact rational residual cover retain every infinite tail')
    positions = [names.index(k) for k in ('cost0','cost16')]
    p0, p16 = positions
    co = {int(k): F(v) for k,v in heavy['original_coefficients'].items()}
    require(set(co) == set(range(1,9)) and min(co.values()) > 0 and F(heavy['at_one']) == functions[p0](1) == 0
            and all(functions[p0](n) == sum(a*max(n-t,0) for t,a in co.items()) for n in range(1,9))
            and polynomials[p0] == (-sum(t*a for t,a in co.items()),sum(co.values()),F(0)),
            'The complete source bound is for the exact original cost0 on every positive integer')
    scale = F(4,5)
    low = [scale*functions[p0](n)-functions[p16](n) for n in range(1,TAIL_ENTRANCE)]
    tail = tuple(scale*polynomials[p0][k]-polynomials[p16][k] for k in range(3))
    minimum, loads, values = previous.tail_minimum(tail)
    require(min(low) >= 0 and minimum >= 0,
            'On every positive integer load, the original cost16 is at most4/5 of original cost0')
    transfer = {'source_function':'cost0','target_function':'cost16','scale':scale,
                'domain':'Every positive integer load of the target test itself; distinct tests are not identified.',
                'low_load_gaps':low,'whole_tail_gap_polynomial':tail,
                'tail_test_integers':loads,'tail_test_values':values,'tail_minimum':minimum}
    updates = []
    for pos, upper in ((p0,F(543,100)),(p16,F(543,125))):
        require(0 < upper < bounds[pos], 'Each complete heavy source update is a strict improvement')
        updates.append({'name':names[pos],'previous_upper':bounds[pos],'updated_upper':upper,'source':'298'})
        bounds[pos] = upper
    data.update(pins=pins,names=names,functions=functions,polynomials=polynomials,bounds=bounds,old=old,
                changed_basis_bounds=updates,added_basis_bounds=[],whole_integer_transfer=transfer)
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
        require(upper <= rational(old_targets[name]['upper']), 'Each new envelope is no worse than its complete297 bound')
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
    require(upper['comparison'] < 403 and upper['target403_numerator_margin'] > 0,
            'The complete comparison on both saturated J faces is strictly below403')
    target403_position = ('below' if upper['comparison'] < 403 else
                          'above' if lower['comparison'] > 403 else 'straddles')
    result = {'schema': 'erdos7-j-face-heavy-positive175189-complete-moment-cost-comparison-v1', 'source_sha256': data['pins'],
              'geometry': data['geometry'], 'survivor_mass': MASS, 'all_original_indices': list(range(52)),
              'original_cost_tags': data['tags'], 'cost_weights': data['weights'],
              'signed_mass_coefficient': data['signed'], 'complete_square_weight': data['outside_square'],
              'offset': data['offset'], 'count_law': data['count'], 'changed_basis_bounds': data['changed_basis_bounds'],
              'added_basis_bounds': data['added_basis_bounds'],
              'whole_integer_transfer': data['whole_integer_transfer'],
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
              'scope': 'Complete original52-cost comparison below403 on both entire actual saturated J faces. All34 observations from297 remain, including the completed joint positive175/189 H4 bound from296. Only cost0 and cost16 source upper bounds improve through the complete retained375 heavy bound298 and a checked whole-positive-integer pointwise transfer, applied on each target test own load. All original source constraints, actual measures, complete exponent/cofactor tails and common late interval remain. All59 whole-positive-integer envelopes and fresh feasible moment witnesses are checked against all34 updated bounds; mass3/20 is exact. All52 positive cost weights, signed mass, outside square, four AP11 blocks, AP13 survival and complete count tail are recomputed. The method lower is restricted to independent scalar-envelope comparisons with positive survival denominator; witnesses need not be actual sources or mutually compatible. No actual attainment, off-face/global extension, later-prime continuation, unrestricted Erdos7 result or Lean verification is asserted.'}

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
