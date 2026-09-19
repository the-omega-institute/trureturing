#!/usr/bin/env python3
"""Exact complete J cost envelopes and their independent-moment limitation.

Rational proposal coefficients and finite supported moment witnesses are data,
not an optimization oracle. The checker uses only the Python standard library;
it proves each envelope for every positive integer load, retains all52 original
independent tests, and consumes only219/241/242 numerical J bounds.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_complete_moment_cost_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'verify_joint_frontier.py': '85341d7f8fa2d0b109697bc17b005a7e75f7f6ec412fd2eb3d26383cf9fce24f', 'frontier/source-budgets/source_barrier_saturation.py': '6fe57e39274df1fa4a80ae4d4a22cab7b1d78d28c4f428b789071e3fb7776a64', 'certificates/source_norms/retained-transport/retained135125_survival_comparison.json': '2b3a347050126d9b40697b78d3f02cfb727c8bffc321fbbbdd1a18eec6590da1', 'frontier/j-geometry/j_face_coupled_seven_heads.py': '375b207dad898b55ea0780277d47a94a4ebadd151dff798d86953d9f102c205a', 'certificates/source_norms/j-geometry/j_face_coupled_seven_heads.json': 'dde1cb32e4ff46643ecef36004ebf2603ab0310ab6f3c83a398f08060dd6b04b', 'frontier/j-geometry/j_face_shared_square_factorial.py': 'a36157d88e4bab3b11fc31b0921513f9b61508a4a3be2854461344c17cf6bdd1', 'certificates/source_norms/j-geometry/j_face_shared_square_factorial.json': '215e92dc7d6f8dae2bdd3a23edc16a12ffb473e9200d11fae98c0497e1e8baf1', 'frontier/j-geometry/j_face_complete_survival_linear_heads.py': '525113d7986c06958412c576f669c85b0d48574c194755df1aac8d5e6489d59e', 'certificates/source_norms/j-geometry/j_face_complete_survival_linear_heads.json': '0c1d6ce72ed9e3d30f513c0a9a9b07b515e09902e86ace47586f4547930b1f9e', 'profile-notes/193-256/219-one-late-source-split-controls-complete-saturated-j-heads.md': 'd0f78950c8ca3040b2a90c5b5d470655cd53e68f39b54d531f793915490ff73d', 'profile-notes/193-256/241-one-original-j-head-controls-complete-square-and-factorial-moments.md': 'a6900d40ccc370e3565d4784c653c213667f736088082cf1ac622153fe807d06', 'profile-notes/193-256/242-the-complete-j-survival-and-linear-heads-retain-one-late-split.md': '24564c3ee7efc83307f50e67a55d56ea25a1eefa5b0eca93c54e37e3192afd5f'}
SOURCES = ('j_face_coupled_seven_heads', 'j_face_shared_square_factorial',
           'j_face_complete_survival_linear_heads')
MASS = F(3, 20)
TAIL_ENTRANCE = 9
EXTERNAL_TARGETS = ('AP11-0', 'AP11-1', 'AP11-2', 'AP11-3', 'hinge4', 'mean', 'square')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable exact input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Unique JSON key: '+key)
        result[key] = value
    return result


def rational(value):
    require(type(value) in (str, int), 'Rational data has no binary floating-point input')
    return F(value)


def polynomial_value(polynomial, n):
    c, b, a = polynomial
    return c+b*n+a*n*n


def tail_minimum(polynomial):
    """Global minimum of a quadratic on integer n>=9, with exact witnesses."""
    c, b, a = polynomial
    require(a >= 0, 'Nonnegative eventual quadratic coefficient')
    if a == 0:
        require(b >= 0, 'A linear tail cannot decrease without bound')
        loads = [TAIL_ENTRANCE]
    else:
        vertex = -b/(2*a)
        floor = vertex.numerator//vertex.denominator
        loads = sorted({TAIL_ENTRANCE, max(TAIL_ENTRANCE, floor), max(TAIL_ENTRANCE, floor+1)})
    values = [polynomial_value(polynomial, n) for n in loads]
    return min(values), loads, values


def cost_polynomial(source, tag):
    degree, leading, constant, entrance = source.zero5_cost_metadata(tag)
    require(degree in (1, 2) and 1 <= entrance <= TAIL_ENTRANCE,
            'Original metadata supplies the whole affine or quadratic continuation')
    polynomial = (constant, leading if degree == 1 else F(0), leading if degree == 2 else F(0))
    require(all(source.zero5_cost(tag, n) == polynomial_value(polynomial, n)
                for n in range(TAIL_ENTRANCE, TAIL_ENTRANCE+3)), 'The original tail identity matches its metadata')
    return polynomial


def affine_identity(source, tag, coefficients, at_one):
    co = {int(t): rational(v) for t, v in coefficients.items()}
    require(co and min(co) >= 1 and max(co) < TAIL_ENTRANCE and min(co.values()) > 0,
            'Positive original finite hinge vector')
    at_one = rational(at_one)
    expansion = lambda n: at_one+sum(v*max(n-t, 0) for t, v in co.items())
    polynomial = (at_one-sum(t*v for t, v in co.items()), sum(co.values()), F(0))
    require(at_one >= 0 and polynomial == cost_polynomial(source, tag)
            and all(expansion(n) == source.zero5_cost(tag, n) for n in range(1, TAIL_ENTRANCE)),
            'Original cost agrees at every transition and throughout the infinite tail')


def inputs(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned canonical certificate reader')
    io = module('j_moment_cost_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path), object_pairs_hook=unique)
    docs = {name: read(io.named_artifact(base/'certificates/source_norms', name + '.json').relative_to(base).as_posix()) for name in SOURCES}
    pins = dict(PINS)
    for name, doc in docs.items():
        for path, pin in doc['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent J source identity '+name+': '+path)
            pins[path] = pin
    engine = module('j_moment_cost_inventory', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    for path, pin in engine.pins.items():
        require(path not in pins or pins[path] == pin, 'Consistent original function inventory '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical input '+path)
    j, moments, heads = (docs[n] for n in SOURCES)
    geometry = j['geometry']
    require(geometry == moments['geometry'] == heads['geometry']
            and rational(geometry['source_mass']) == F(1, 4)
            and rational(geometry['survivor_mass']) == MASS
            and list(map(rational, geometry['late_split_interval'])) == [F(1, 135), F(1, 90)]
            and rational(moments['survivor_mass']) == rational(heads['mass']) == MASS,
            'Every bound uses both entire original saturated J faces and one common late split')
    mean = rational(j['complete_mean_upper'])
    square, factorial = (rational(moments[k]) for k in ('complete_square_upper', 'complete_factorial_upper'))
    require(mean == rational(moments['complete_mean_upper']) == rational(heads['complete_mean_upper']) == F(16, 25)
            and rational(j['hinge1_upper']) == rational(heads['hinge1_upper']) == mean-MASS
            and (square, factorial) == (F(371, 80), F(6353, 7200)), 'The complete219/241/242 J moments')
    old = {str(row['index']): row for row in j['results']}
    require(set(old) == {'AP13', '0', '16'} and old['AP13']['scan']['coefficients'] == {'4': '1'}
            and rational(old['AP13']['at_one']) == 0, 'The three inherited219 independent heads')
    hinge4 = rational(old['AP13']['adopted_upper'])
    require(hinge4 == rational(heads['inherited_AP13_upper']) == F(29483, 147000), 'Complete independent AP13')
    # This older K certificate supplies only the unchanged original function
    # labels, positive weights and signed comparison formula, never K bounds.
    original = read('certificates/source_norms/retained-transport/retained135125_survival_comparison.json')
    tags = [row['tag'] for row in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    weights = list(map(rational, original['cost_weights']))
    require(len(tags) == len(weights) == 52 and min(weights) > 0
            and original['all_original_indices'] == list(range(52))
            and encode(tags) == original['original_cost_tags'], 'All52 unchanged independently labelled positive-weight functions')
    signed, outside_square, offset = (rational(original[k]) for k in
                                     ('signed_mass_coefficient', 'complete_square_weight', 'offset'))
    require(signed < 0 and outside_square > 0 and offset == engine.source.WHOLE_CONST > 0,
            'The original negative actual-mass coefficient and positive complete-square weight')
    source = engine.source
    functions = [lambda n: F(1), lambda n: F(n), lambda n: F(n*n),
                 lambda n: F(max(n-5, 0)*(n-4), 2), lambda n: F(max(n-4, 0))]
    polynomials = [(F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1)),
                   (F(10), F(-9, 2), F(1, 2)), (F(-4), F(1), F(0))]
    bounds = [MASS, mean, square, factorial, hinge4]
    names = ['mass', 'mean', 'square', 'factorial5', 'hinge4']
    for index in (0, 16):
        row = old[str(index)]
        affine_identity(source, tags[index], row['scan']['coefficients'], row['at_one'])
        bound = rational(row['adopted_upper'])
        require(bound == min(rational(row['at_one'])*MASS+rational(row['scan']['complete_hinge_upper']),
                             rational(row['at_one'])*MASS+sum(map(rational, row['scan']['coefficients'].values()))*(mean-MASS))
                == rational(heads['inherited_heavy_costs'][str(index)]), 'Exact original heavy-cost interface')
        functions.append(lambda n, tag=tags[index]: source.zero5_cost(tag, n))
        polynomials.append(cost_polynomial(source, tags[index]))
        names.append('cost'+str(index)); bounds.append(bound)
    provider = module('j_moment_cost_heads', base/'frontier/j-geometry/j_face_complete_survival_linear_heads.py')
    jobs, count = provider.prepare_jobs(source, engine)
    require(encode(count) == heads['count_law'] and len(jobs) == len(heads['results']) == 15,
            'Complete original count distribution and all15 J head objectives')
    for job, row in zip(jobs, heads['results']):
        require(all(encode(v) == row[k] for k, v in job.items())
                and row['covered_containing_choices'] == 6250000 and rational(row['at_one']) == 0,
                'The same original all-choice AP or affine-cost objective')
        co = {int(t): rational(v) for t, v in row['coefficients'].items()}
        require(min(co) >= 1 and max(co) < TAIL_ENTRANCE and min(co.values()) > 0, 'Positive finite hinge basis')
        if row['kind'] == 'cost':
            affine_identity(source, tags[row['index']], row['coefficients'], row['at_one'])
        functions.append(lambda n, co=co: sum(v*max(n-t, 0) for t, v in co.items()))
        polynomials.append((-sum(t*v for t, v in co.items()), sum(co.values()), F(0)))
        names.append(row['name']); bounds.append(rational(row['adopted_upper']))
    require(len(names) == len(set(names)) == 22 and min(bounds) > 0
            and count['remaining_hinge1_coefficient'] == F(1, 7986)
            and count['whole_constant_coefficient'] == F(1, 87846), 'Exactly22 common J moment constraints and complete count-tail coefficients')
    targets = [('cost-'+str(i), lambda n, tag=tag: source.zero5_cost(tag, n), cost_polynomial(source, tag))
               for i, tag in enumerate(tags)]
    targets += [(name, functions[names.index(name)], polynomials[names.index(name)]) for name in EXTERNAL_TARGETS]
    return io, pins, geometry, names, functions, polynomials, bounds, targets, tags, weights, signed, outside_square, offset, count


def normalize_proofs(rows):
    """Retain only mathematical coefficients and witnesses from a proposal."""
    return [{'name': row['name'],
             'coefficients': {k: rational(v) for k, v in row['coefficients'].items() if rational(v)},
             'finite_moment_witness': {k: rational(v) for k, v in row['finite_moment_witness'].items() if rational(v)}}
            for row in rows]


def calculate(base, proof_data):
    (io, pins, geometry, names, functions, polynomials, bounds, targets,
     tags, weights, signed, outside_square, offset, count) = inputs(base)
    require([row['name'] for row in proof_data] == [target[0] for target in targets], 'All59 distinct original targets in their canonical order')
    rows = []
    for proof, (name, target, target_polynomial) in zip(proof_data, targets):
        require(set(proof) == {'name', 'coefficients', 'finite_moment_witness'}
                and set(proof['coefficients']) <= set(names), 'Only declared rational basis coefficients')
        coefficients = [rational(proof['coefficients'].get(name, '0')) for name in names]
        require(min(coefficients[1:]) >= 0, 'Only the exact-mass coefficient may be negative')
        low = [sum(v*f(n) for v, f in zip(coefficients, functions))-target(n) for n in range(1, TAIL_ENTRANCE)]
        tail = tuple(sum(v*p[k] for v, p in zip(coefficients, polynomials))-target_polynomial[k] for k in range(3))
        minimum, loads, values = tail_minimum(tail)
        require(min(low) >= 0 and minimum >= 0, 'The entire exact envelope for '+name)
        upper = sum(v*b for v, b in zip(coefficients, bounds))
        witness = {}
        for key, value in proof['finite_moment_witness'].items():
            n, mass = int(key), rational(value)
            require(str(n) == key and n >= 1 and mass > 0, 'Positive canonical finite supported moment witness')
            witness[n] = mass
        require(witness and sum(witness.values()) == MASS, 'The witness has exact J survivor mass')
        measured = [sum(m*f(n) for n, m in witness.items()) for f in functions]
        require(measured[0] == bounds[0] and all(a <= b for a, b in zip(measured[1:], bounds[1:])),
                'All22 moment constraints hold exactly for the independent '+name+' witness')
        lower = sum(m*target(n) for n, m in witness.items())
        require(0 <= lower <= upper, 'Exact weak dual ordering for '+name)
        rows.append({'name': name, 'upper': upper, 'independent_moment_lower': lower,
                     'duality_gap': upper-lower, 'low_load_gaps': low, 'tail_gap_polynomial': tail,
                     'tail_test_integers': loads, 'tail_test_values': values, 'tail_minimum': minimum,
                     'witness_moments': dict(zip(names, measured)),
                     'witness_moment_slacks': dict(zip(names, (b-a for a, b in zip(measured, bounds))))})
    by_name = {row['name']: row for row in rows}

    def comparison(field):
        get = lambda name: by_name[name][field]
        blocks = [get('AP11-'+str(i)) for i in range(4)]
        mean, square, hinge4 = (get(name) for name in ('mean', 'square', 'hinge4'))
        tail = count['remaining_hinge1_coefficient']*(mean-MASS)+count['whole_constant_coefficient']*MASS
        denominator = MASS-hinge4/6-(sum(blocks)+tail)/7
        weighted = [w*get('cost-'+str(i)) for i, w in enumerate(weights)]
        numerator = signed*MASS+sum(weighted)+outside_square*square
        require(mean >= MASS and min(blocks) >= 0 and tail >= 0 and numerator > 0 and denominator > 0,
                'Correct monotonic direction of the complete positive comparison')
        return {'comparison': offset+numerator/denominator, 'numerator': numerator, 'denominator': denominator,
                'signed_mass_payment': signed*MASS, 'outside_square_payment': outside_square*square,
                'weighted_costs': weighted, 'AP11_block_values': blocks, 'mean': mean, 'square': square,
                'hinge4': hinge4, 'complete_count_tail': tail,
                'target403_numerator_margin': (403-offset)*denominator-numerator}

    upper = comparison('upper')
    lower = comparison('independent_moment_lower')
    gap = upper['comparison']-lower['comparison']
    require(lower['comparison'] > F(4475579782099, 10**10) > 403
            and upper['comparison'] < F(4475579782100, 10**10) and 0 <= gap < F(1, 10**10),
            'Certified tight bracket for this independent scalar-moment method, strictly above403')
    require(upper['denominator'] == F(67792212611, 813541806000)
            and upper['complete_count_tail'] == F(277, 4392300), 'The complete adopted J denominator and infinite count tail')
    result = {'schema': 'erdos7-j-face-complete-moment-cost-comparison-v1', 'source_sha256': pins,
              'geometry': geometry, 'survivor_mass': MASS, 'all_original_indices': list(range(52)),
              'original_cost_tags': tags, 'cost_weights': weights, 'signed_mass_coefficient': signed,
              'complete_square_weight': outside_square, 'offset': offset, 'count_law': count,
              'basis': [{'name': name, 'upper': bound, 'mass_is_exact': name == 'mass',
                         'low_load_values': [f(n) for n in range(1, TAIL_ENTRANCE)], 'tail_polynomial': polynomial}
                        for name, bound, f, polynomial in zip(names, bounds, functions, polynomials)],
              'proof_data': proof_data, 'results': rows, 'comparison_upper': upper,
              'independent_moment_method_lower': lower, 'method_bracket_width': gap,
              'counts': {'basis_functions': len(names), 'targets': len(rows), 'cost_targets': len(weights),
                         'low_load_inequalities': len(rows)*(TAIL_ENTRANCE-1), 'whole_tail_polynomials': len(rows),
                         'exact_witness_moment_checks': len(rows)*len(names),
                         'positive_witness_atoms': sum(len(p['finite_moment_witness']) for p in proof_data),
                         'nonzero_envelope_coefficients': sum(len(p['coefficients']) for p in proof_data)},
              'scope': 'Complete original52-cost comparison on both entire saturated actual J faces, using219/241/242 numerical J inputs only, exact survivor mass3/20, all independent test labels and complete exponent/count tails. The separate finite moment witnesses bound only the independent scalar-envelope method with these22 constraints; they need not arise from any actual source or coexist on one actual family. Independent tests are never identified with one common load random variable. The method lower bound does not constrain a stronger joint source method. No threshold403 crossing, off-face extension, unrestricted Erdos7 result, actual attainment or Lean verification is asserted.'}
    return encode(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--proposal', type=Path, help='External rational proposal JSON, only when writing')
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true'); modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(args.proposal is None or args.write, 'A proposal is consumed only by the exact writer')
    require(not args.write or args.proposal is not None, 'Writing requires explicit rational proposal data')
    require(sha256((args.base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned certificate IO')
    io = module('j_moment_cost_output', args.base/'certificate_io.py')
    if args.write:
        proposed = json.loads(args.proposal.read_text(), object_pairs_hook=unique)
        proofs = encode(normalize_proofs(proposed['results']))
    else:
        stored = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE), object_pairs_hook=unique)
        proofs = stored['proof_data']
    result = calculate(args.base, proofs)
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == stored, 'Every rational certificate result recomputes exactly')
    print('Complete J comparison <= '+str(float(F(result['comparison_upper']['comparison']))))
    print('Independent scalar-moment method >= '+str(float(F(result['independent_moment_method_lower']['comparison']))))
    print('PASS:52 original costs,59 whole-load envelopes,59 independent exact moment witnesses and the complete J denominator.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
