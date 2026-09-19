#!/usr/bin/env python3
"""Retain one original head across the expanded-seven hinges and full factorial tail."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util
import json
from math import lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/expanded_seven_quadratic_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/moments-survival/second_depth_seven_survival_comparison.py': 'c7a9d5ce28f2b278a57e8ad3f595a2bbb61823f1f22be4de6ef1ad5c05357322', 'certificates/source_norms/moments-survival/second_depth_seven_survival_comparison.json': '1a7523018db9212c2a6f9001b2b52db6aaad011bdbdf6817f18d1be3a5c0f436', 'frontier/comparison-bounds/expanded_seven_pair_comparison.py': 'a87399cd2b88dafa12ecaeb84fa2ea240537ded21815cb198f13c3e7a3083784', 'certificates/source_norms/comparison-bounds/expanded_seven_pair_comparison.json': '89cdaf8085de7b8d35489e7352cc8ad1907c56a989f2504229947a7c3c99e1fa', 'frontier/moments-survival/pure_three_joint_factorial_comparison.py': '135c77770cfb09752ff9ab82508ddd1e377f49b5ec783d8e85d2d7638cb0cef8', 'certificates/source_norms/moments-survival/pure_three_joint_factorial_comparison.json': 'cd6f257de24931fc8aa0ecc2bf95e87ad4327cc72b77c401a325572dca22f3c6', 'frontier/moments-survival/pure_five_joint_factorial_comparison.py': '5a1448675aea32e0a7d6103e1b29af3c965896bdd4d62027b40f357b77846042', 'certificates/source_norms/moments-survival/pure_five_joint_factorial_comparison.json': '683b75b5706681b5081d4384401615882119cea7d069632bca3647cf1c1bdbac', 'frontier/moments-survival/whole_factorial_same_head.py': '02b5af74e00afc26b940d8c6b485fbea654a4d2f9dd52d986875c303a79faacd', 'frontier/moments-survival/whole_quadratic_same_head.py': 'ba2de9c8850b1936ebac15ab9e4cc546a052de6139289343e0de5d2dec560938', 'frontier/comparison-bounds/load_two_cost_remainders.py': '46573a7effb28fac5eb6036991523f2fd34e5df54822b3ed09cca538e7d13d69', 'certificates/source_norms/comparison-bounds/load_two_cost_remainders.json': 'ec6674b8507503f64616098d80047a0600f46fa513420020667516e61c89ce95'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable complete original input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


class JointQuadraticHead:
    """Combine201's finite-hinge bound and174's whole factorial head explicitly.

    The same theta*J(layout) is inside both valid projection bounds.
    The complete theta*pair_tail and constant mass terms are outside.
    """
    def __init__(self, base, factorial_certificate, five_certificate):
        load = lambda name: module('joint_quad207_'+name, module('named_artifact_io', base/'certificate_io.py').named_artifact(base/'frontier', name+'.py'))
        self.parent = load('expanded_seven_pair_comparison').CoupledSevenHead(base)
        self.bridge = self.parent.bridge
        old = load('whole_factorial_same_head').FactorialHead(self.bridge)
        five = load('pure_five_joint_factorial_comparison').JointFiveHead(
            self.bridge, old, tuple(map(F, five_certificate['deep_density_caps'])))
        self.factorial = load('pure_three_joint_factorial_comparison').JointThreeHead(
            old, tuple(map(F, factorial_certificate['deep_density_caps'])), five)
        self.heads, digest, largest = {}, sha256(), F(-1)
        for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
            B = self.bridge.head_load(layout)
            parts = self.factorial.components(layout, B)
            J = parts['head_upper']
            self.bridge.integer(21600*J)
            self.heads[layout] = (B, J)
            largest = max(largest, J)
            digest.update(json.dumps(encode([layout, parts]), separators=(',', ':')).encode())
        self.digest = digest.hexdigest()
        self.pair_tail = F(factorial_certificate['complete_tail_distinct_pairs'])
        self.factorial_upper = largest+self.pair_tail
        require(len(self.heads) == 12500 and self.digest == factorial_certificate['head_components_sha256']
                and largest == F(factorial_certificate['head_operator_maximum']) == F(319, 2160)
                and self.pair_tail == F(2539, 3600)
                and self.factorial_upper == F(factorial_certificate['second_factorial_tail_upper']) == F(2303, 2700),
                'Every complete174 head component and its entire pair complement reconstructed')

    def scan(self, coefficients, theta):
        require(theta > 0, 'Positive complete factorial coefficient')
        p = self.parent
        record = p.prepare(coefficients)
        total = lcm(p.total*record['factor'].denominator, 21600*theta.denominator)
        mean_scale = self.bridge.integer(total*record['factor']/p.total)
        correction = lambda layout: record['primitive_coefficients'].get(1, 0)*self.bridge.integer(
            p.total*p.mean.correction(layout))
        best, witness, digest = None, None, sha256()
        original = bounded = expanded = checked = 0
        max_bounded = None
        lp_start = p.lp_count

        def consider(layout, B, J, cor, r, f, extra, old_raw, seed):
            nonlocal best, witness, checked
            charge = self.bridge.integer(total*theta*J)
            old_value = mean_scale*old_raw+charge
            for c63, r105, f105, add in p.added:
                first = [a+b for a, b in zip(extra, add)]
                raw, details = p.objective(record, B, first, cor, True)
                new_value = mean_scale*raw+charge
                value = min(old_value, new_value)
                checked += 1
                digest.update(json.dumps(['seed' if seed else 'expanded', layout, r, f, c63, r105, f105,
                                          old_value, new_value, charge], separators=(',', ':')).encode())
                if best is None or value > best:
                    best = value
                    witness = {'layout': layout, 'seven21_root': r, 'seven35_slot': f,
                        'seven63_cell': c63, 'seven105_root': r105, 'seven105_slot': f105,
                        'two_projection_joint_upper': old_value, 'four_projection_joint_upper': new_value,
                        'factorial_head_upper': J, 'scaled_factorial_head_charge': charge,
                        'hinge_mean_scale': mean_scale, 'hinge_components': details}

        seed = (0, 1, 2, 0, 2, 1, 2)
        B, J = self.heads[seed]
        cor = correction(seed)
        for r, f, extra in p.extras:
            old_raw, _ = p.objective(record, B, extra, cor, False)
            consider(seed, B, J, cor, r, f, extra, old_raw, True)
        for layout, (B, J) in self.heads.items():
            cor = correction(layout)
            charge = self.bridge.integer(total*theta*J)
            for r, f, extra in p.extras:
                old_raw, _ = p.objective(record, B, extra, cor, False)
                old_value = mean_scale*old_raw+charge
                original += 1
                if old_value <= best:
                    bounded += 1
                    max_bounded = old_value if max_bounded is None else max(max_bounded, old_value)
                    digest.update(json.dumps(['bounded', layout, r, f, old_value, charge], separators=(',', ':')).encode())
                    continue
                expanded += 1
                consider(layout, B, J, cor, r, f, extra, old_raw, False)
        require(original == 125000 and bounded+expanded == original and checked == 500+50*expanded
                and 50*bounded+checked-500 == 6250000,
                'All original heads and all6,250,000 independent projection choices covered')
        require(best is not None and witness is not None
                and (max_bounded is None or max_bounded <= best),
                'Every bounded branch retains its complete same-layout factorial charge')
        require(p.lp_count-lp_start == 10+125000+checked, 'Every exact primal/dual LP accounted for')
        return {'hinge_coefficients': record['coefficients'], 'factorial_coefficient': theta,
            'common_scale': total, 'hinge_mean_scale': mean_scale, 'joint_head_upper': F(best, total),
            'original_head_projection_branches': original, 'bounded_branches': bounded,
            'expanded_branches': expanded, 'four_projection_evaluated_including_seed': checked,
            'maximum_bounded_joint_upper': F(max_bounded, total) if max_bounded is not None else None,
            'rational_lp_count': p.lp_count-lp_start, 'maximizing_witness': witness,
            'all_branch_decisions_sha256': digest.hexdigest(), 'factorial_head_components_sha256': self.digest}


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical reader and complete206 input')
    io = module('quadratic207_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior = read('second_depth_seven_survival_comparison')
    fact_cert = read('pure_three_joint_factorial_comparison')
    five_cert = read('pure_five_joint_factorial_comparison')
    identities_cert = read('load_two_cost_remainders')
    pins = dict(PINS)
    for data in (prior, fact_cert, five_cert, identities_cert):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent inherited source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('quadratic207_'+name, io.named_artifact(base/'frontier', name+'.py'))
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in engine.pins.items()), 'All original52 cost functions')
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800))
            and all(data['faces'] == prior['faces'] and data['r'] == data['rho'] == '0'
                    and F(data['mass']) == D and F(data['linear_upper']) == L
                    for data in (prior, fact_cert, five_cert, identities_cert)),
            'The same actual source and complete saturated faces for every uniform input')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    costs_old, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    require(encode(tags) == prior['original_cost_tags'] and prior['all_original_indices'] == list(range(52))
            and len(tags) == len(costs_old) == len(weights) == 52 and min(weights) > 0,
            'Every original206 cost and positive weight retained')
    problem = JointQuadraticHead(base, fact_cert, five_cert)
    quadratic = load('whole_quadratic_same_head')
    direct, scans = list(costs_old), []
    targets = {47: F(125420431, 38896200), 48: F(17859883, 4630500)}
    for i in (47, 48):
        expansion = quadratic.quadratic_expansion(engine.source, tags[i])
        require(not expansion['negative_hinge_coefficients']
                and expansion['factorial_tail_coefficient'] == 2,
                'The exact original raw81 cost has a positive complete quadratic expansion')
        scan = problem.scan(expansion['hinge_coefficients'], expansion['factorial_tail_coefficient'])
        outside = expansion['at_one']*D+expansion['factorial_tail_coefficient']*problem.pair_tail
        bound = outside+scan['joint_head_upper']
        require(0 < bound == targets[i] < costs_old[i], 'Strict uniform complete original quadratic bound')
        direct[i] = bound
        scans.append({'index': i, 'tag': tags[i], 'expansion': expansion, 'scan': scan,
                      'outside_constant_mass_and_complete_pair_tail': outside,
                      'previous_cost_upper': costs_old[i], 'cost_upper': bound})
        print('Checked complete quadratic'+str(i)+': '+str(float(bound))+', '+str(scan['rational_lp_count'])+' exact LPs.', flush=True)
    require(tags[48] == ('s', F(9)), 'The new complete cost48 is exactly the uniform raw-square9 function')
    U9, U4, T5 = direct[48], F(prior['uniform_hinge4_upper']), problem.factorial_upper
    require(U4 == 6*F(prior['standalone_hinge4_penalty']) == F(295741, 1543500)
            and T5 == F(2303, 2700) < F(identities_cert['second_factorial_tail_upper']) == F(619, 720),
            'The complete separate uniform hinge and factorial bounds used by every identity')
    remainders = load('load_two_cost_remainders')
    feedback = []
    for row in remainders.SUPPORTS:
        i = row[0]
        identity = remainders.verify_identity(engine.source, tags[i], row)
        saved = [r for r in identities_cert['exact_integer_identities'] if r['index'] == i]
        require(len(saved) == 1 and all(saved[0][k] == encode(v) for k, v in identity.items()),
                'The unchanged original202 identity, on every positive integer load')
        bound = (identity['square_minus_mass']*(Q-D)+identity['raw_square9']*U9
                 +identity['hinge4']*U4+identity['factorial5']*T5)
        before = direct[i]
        direct[i] = min(before, bound)
        feedback.append({**identity, 'previous_cost_upper': before, 'source_bound': bound,
                         'accepted_cost_upper': direct[i], 'weighted_gain': weights[i]*(before-direct[i])})
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda n, tag=t: engine.source.zero5_cost(tag, n) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, costs_old, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    require(signed < 0 < square_weight and all(0 <= b <= a for a, b in zip(costs_old, costs)),
            'Every signed mass, square and preceding cost bound retained')
    oldN = signed*D+sum(w*c for w, c in zip(weights, costs_old))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) == F(1423627769987, 17084377926000) > 0,
            'The full206 AP11/AP13 denominator and every infinite count tail remain')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(oldN == F(prior['numerator_upper']) > N > 0
            and offset+oldN/denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']),
            'One complete new52-cost numerator, with no separate numeric gain added')
    return encode({'schema': 'erdos7-expanded-seven-quadratic-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
        'complete_square_upper': Q, 'factorial_head_components_sha256': problem.digest,
        'complete_tail_distinct_pairs': problem.pair_tail, 'second_factorial_tail_upper': T5,
        'uniform_raw_square9_upper': U9, 'uniform_hinge4_upper': U4,
        'quadratic_results': scans, 'integer_identity_feedback': feedback,
        'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
        'previous_cost_bounds': costs_old, 'direct_cost_bounds': direct, 'improved_cost_bounds': costs,
        'majorants': majorants, 'improved_cost_indices': [i for i, (a, b) in enumerate(zip(costs_old, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'previous_numerator_upper': oldN, 'numerator_upper': N, 'numerator_improvement': oldN-N,
        'AP11_block_results': prior['AP11_block_results'], 'AP13_result': prior['AP13_result'],
        'full_count_tail': prior['full_count_tail'], 'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
        'uniform_denominator_lower': denominator, 'offset': offset,
        'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'rational_lp_count': sum(r['scan']['rational_lp_count'] for r in scans),
        'scope': 'Each of the two original raw81 functions separately retains one head across201 finite hinges and174 complete factorial term. The identical factorial charge is inside both branch bounds; its complete pair complement remains outside. The new uniform raw-square9 bound, old complete hinge4 bound and174 uniform factorial bound separately feed202 exact original-cost identities. All206 costs, signed terms and full denominator remain on both entire actual saturated K faces. No shared optimizer across tests, actual attainment, off-face/global extension, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('quadratic207_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete quadratic certificate')
    print('PASS: complete shared-head quadratic bounds and original identity feedback; face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
