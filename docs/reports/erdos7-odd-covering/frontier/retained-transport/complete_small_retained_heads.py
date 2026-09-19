#!/usr/bin/env python3
"""Close all original candidate channels for four heads on a positive source box.

The legacy raw-prefix certificates are transported explicitly before the
minima of candidates are joined. This is not a complete52-cost comparison.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/complete_small_retained_heads.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/retained-transport/uniform_pruning_candidate_transport.py': '3275032d3f9512336606d393b1783e256a5780c281e44a2e85c1eec5bf19e738', 'frontier/retained-transport/retained_small_domain_all_bank_transport.py': 'f07c441ac5475d27e09d7c84ab49e463ccf1e7a1581c121a0d77e87db273846c', 'frontier/source-budgets/joint_selected_source_comparison.py': '27e01b28ef759fea1a3e8cb7ac336f71211fdd4fa9fd589c6270443ad9ec9355', 'frontier/endpoint-bounds/k_face_common_seven_hinges.py': '3128cab9f43ad9c89a5f129b7c7d0115a6f73684f613111a07a56f0bd71ddcdd', 'frontier/comparison-bounds/second_depth_seven_comparison.py': 'b49a13dde9aa26ce8b1a132c11f3a9bc125d995b9497567c7bff26eb2f4bb239', 'certificates/source_norms/retained-transport/uniform_pruning_candidate_transport.json': '767d31ccf9316bc0e790479cf2f81c891cce79b64f9629ecc324935d408cbdc9', 'certificates/source_norms/retained-transport/retained_small_domain_all_bank_transport.json': '1965686a03fc6a93f8c89bef5359d42e405b4af0a91fa9a37666e47fa7e97570', 'certificates/source_norms/retained-transport/retained135125_heavy_comparison.json': 'a885a6b1153e17a7005278cf89755ef60d4064eb95f8758ef2226ed7031b24b0', 'certificates/source_norms/retained-transport/retained135125_survival_comparison.json': '2b3a347050126d9b40697b78d3f02cfb727c8bffc321fbbbdd1a18eec6590da1', 'certificates/source_norms/source-budgets/joint_selected_source_comparison.json': '245e6e5902c7b30cd246d3910c4e773f5f2fef99aff1d3dc939f60550dd11696'}
PRIMITIVES = ('E5', 'E15', 'E27', 'Ege4', 'E5d', 'E15d', 'omega')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original input')
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


def prefix_record(dual, par, caps, budgets, bridge, components):
    """Price a132-row raw-prefix dual with its own complete objective movement."""
    prices = {int(k): F(v) for k, v in dual['nonzero_inequality_duals'].items()}
    require(all(str(int(k)) == k for k in dual['nonzero_inequality_duals'])
            and all(0 <= i < 132 and v >= 0 for i, v in prices.items())
            and len(dual['equality_duals']) == 4, 'Original raw dual dimensions and signs')
    get = lambda i: prices.get(i, F(0))
    d, R, G = (F(par[k]) for k in ('delta', 'rho', 'gap'))
    require(0 < d <= F(1, 12) and 0 < R and 0 < G, 'A guarded positive source box')
    face = [v for row in bridge.source_tables(2)[1] for v in row]
    subtraction = sum(get(i)*face[i] for i in range(25))
    subtraction += sum(get(25+j)*v for j, v in enumerate(bridge.GROUP_MASSES))
    crt_constant = (get(128)+get(129))/675+(get(130)+get(131))/2025
    require(subtraction+crt_constant+sum(map(F, dual['equality_duals'])) == F(dual['raw_objective_upper']),
            'The original signed raw dual RHS; no unrelated objective RHS is used')
    profiles = [d/450*max(get(start+s) for s in range(1, 5)) for start in (28, 78)]
    profiles += [max(par['v0' if c < 2 else 'v1']*get(start+5*c+3) for c in range(5))/den
                 for start, den in ((53, 27), (103, 81))]
    base_prices = [get(i)+get(25+(0 if i < 5 else 1 if i < 10 else 2)) for i in range(25)]
    H, MH = F(components['H6']), F(components['maximum_selected_old_hinge'])
    primitive = {k: F(v) for k, v in components['shifted_primitive_prices'].items()}
    require(set(primitive) == set(PRIMITIVES) and min(primitive.values()) >= 0,
            'The seven common nonnegative prices, including one old-hinge W price')
    wrong_prices = list(map(F, components['tail_wrong_slot_coefficients']))
    require(len(wrong_prices) == 2 and min(wrong_prices) >= 0, 'Only the tail adds wrong-slot terms')
    source = sum(profiles)+F(components['combined_source_upper'])
    vertices = []
    for q5, q15 in ((F(0), F(0)), (R/G, F(0)), (F(0), R/G)):
        coefficient = [base_prices[i]+MH*(d/5*int(i//5 != 0)+q5*int(i % 5 == 4)
                       +q15*int(i//5 >= 2 and i % 5 == 4)) for i in range(25)]
        raw, witnesses = bridge.lp_bound(coefficient, caps, budgets)
        remaining = R-G*(q5+q15)
        wrong = G*sum(a*q for a, q in zip(wrong_prices, (q5, q15)))
        value = source+raw-subtraction+wrong+remaining*max(primitive.values())
        require(remaining >= 0, 'One remaining actual residual')
        vertices.append({'q': [q5, q15], 'raw_coefficients': coefficient,
                         'signed_raw_support': raw-subtraction, 'raw_primal_dual_witnesses': witnesses,
                         'tail_wrong_slot_upper': wrong, 'remaining_residual': remaining,
                         'prefix_transport_error_upper': value})
    return {'old_profile_source_uppers_25_75_27_81': profiles, 'raw_base_prices': base_prices,
            'raw_face_subtraction': subtraction, 'source_upper': source,
            'primitive_prices': primitive, 'H6': H, 'maximum_selected_old_hinge': MH,
            'triangle_vertices': vertices,
            'transport_error_upper': max(v['prefix_transport_error_upper'] for v in vertices)}


def calculate(base):
    require(PINS, 'Final source and logical-certificate pins')
    io = module('small_heads_io', base/'certificate_io.py')
    read = lambda n: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', n+'.json')))
    heavy, survival, raw_source, pruning, joint = [read(n) for n in (
        'retained135125_heavy_comparison', 'retained135125_survival_comparison',
        'joint_selected_source_comparison', 'uniform_pruning_candidate_transport',
        'retained_small_domain_all_bank_transport')]
    pins = dict(PINS)
    for doc in (heavy, survival, raw_source, pruning, joint):
        for path, pin in doc['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    load = lambda n: module('small_heads_'+n, io.named_artifact(base/'frontier', n+'.py'))
    small, bridge, prune, depth = [load(n) for n in ('retained_small_domain_all_bank_transport',
        'k_face_common_seven_hinges', 'uniform_pruning_candidate_transport', 'second_depth_seven_comparison')]
    domain = small.parameters(F(1, 10**8), F(1, 10**11), F(1, 60))
    require(encode(domain) == joint['domain'], 'The same complete source box and raw polytope')
    par, caps, budgets = domain['parameters'], domain['raw_caps'], domain['raw_budgets']
    raw = load('joint_selected_source_comparison').RawSelectedLP(bridge)
    require(raw.specification() == raw_source['raw_lp'], 'The132-row raw-prefix certificate matrix')
    used = heavy['previous_prefix_duals_used']
    bank = raw_source['rational_dual_certificates']
    require(len(used) == len(set(used)) == 12 and set(used) == set(bank)
            and survival['previous_prefix_duals_used'] == [], 'Every original used prefix dual, including both heavy costs')
    small_pruning = [v for v in pruning['domains'] if v['domain'] == 'small_1e8']
    require(len(small_pruning) == 1 and all(F(small_pruning[0][k]) == par[k] for k in ('delta', 'rho', 'gap')),
            'The same pruning rectangle')
    scans = prune.original_scans(heavy, survival)
    names = {'heavy0': 'heavy-0', 'heavy16': 'heavy-16', 'AP13': 'AP13', 'AP11-B0': 'AP11-block0'}
    original = {r['objective']: r for r in pruning['original_scans']}
    records = []
    for scan in scans:
        name = scan['objective'];target = joint['tests'][names[name]]
        require(encode(scan) == original[name] and encode(scan['coefficients']) == target['hinge_coefficients']
                and F(scan['face_maximum']) == F(target['face_complete_hinge_upper']), 'One source-bound original test')
        finite = prune.finite_coefficients(scan['coefficients'], 6, bridge, depth)
        components = prune.evaluate_with_finite(scan['coefficients'], 6, finite, par['delta'], par['rho'], par['gap'], 17)
        candidates = small_pruning[0]['objectives'][name]['candidate_errors']
        require(encode(components) == candidates['6'], 'The exact full-deletion and complete-tail components')
        tail_components = prune.deletion_tail_data(scan['coefficients'], 6, par['delta'], par['rho'], 17)
        require(all(components[k] == tail_components[k] for k in ('H6', 'maximum_selected_old_hinge', 'source_whole_hinge_deletion', 'source_complete_tails')), 'Same233 complete deletion and tail')
        prefix = {key: prefix_record(bank[key], par, caps, budgets, bridge, tail_components) for key in used} if name.startswith('heavy') else {}
        e_prefix = max([F(0)]+[r['transport_error_upper'] for r in prefix.values()])
        e_joint = max(F(0), F(target['transport_error_upper']))
        errors = {j: F(candidates[j]['error_upper']) for j in ('2', '4', '6')}
        errors.update({'joint': e_joint, 'prefix': e_prefix})
        allowance = max(errors.values())
        require(allowance >= 0, 'The maximum of all five valid transport allowances')
        M = F(scan['face_maximum'])
        pruned = {}
        for label, js in (('two', ('2',)), ('four', ('2', '4')), ('six', ('2', '4', '6'))):
            pruned[label] = F(scan['classes'][label]['face_upper'])+max(errors[j] for j in js)
            require(pruned[label] <= M+allowance, 'Every accepted minimum retains every candidate error')
        final = max(M+allowance, *pruned.values())
        records.append({'objective': name, 'hinge_coefficients': scan['coefficients'], 'face_ceiling': M,
                        'original_containing_choices': 62500000, 'original_joint_leaves': scan['joint_original_leaves'],
                        'candidate_error_uppers': errors, 'uniform_transport_allowance': allowance,
                        'transported_pruned_class_uppers': pruned, 'complete_hinge_upper': final,
                        'prefix_records': prefix, 'prefix_maximizers': [k for k, r in prefix.items() if r['transport_error_upper'] == e_prefix],
                        'original_branch_decisions_sha256': scan['branch_decisions_sha256']})
    return encode({'schema': 'erdos7-complete-small-retained-heads-v1', 'source_sha256': pins,
                   'domain': domain, 'original_raw_prefix_duals': len(used), 'complete_tests': records,
                   'scope': 'Complete225/226 heavy0,heavy16,AP13 and AP11-block0 bounds on delta<=10^-8,rho<=10^-11. Every original two/four/six,joint and raw-prefix candidate is transported before taking their minimum; all independent labels and infinite tails remain. No complete52-cost K comparison, global complement, Lean or unrestricted Erdos7 resolution.'})


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = p.add_mutually_exclusive_group();modes.add_argument('--write', action='store_true');modes.add_argument('--check', action='store_true')
    args = p.parse_args();result = calculate(args.base)
    io = module('small_heads_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact complete four-head certificate')
    for r in result['complete_tests']:
        print(r['objective']+': complete hinge='+str(float(F(r['complete_hinge_upper'])))+', allowance='+str(float(F(r['uniform_transport_allowance']))))
    print('PASS: four complete heads on a positive source box; all52-cost/global comparison remains separate.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
