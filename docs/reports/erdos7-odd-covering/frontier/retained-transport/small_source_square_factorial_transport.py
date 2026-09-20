#!/usr/bin/env python3
"""Uniform199 square transport and the existing138 complete factorial bound."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/small_source_square_factorial_transport.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765', 'frontier/retained-transport/retained_small_domain_all_bank_transport.py': '3cfb8cf69e578f527a5f6cbf008bbffeddff5f7f461809ddf2c71f5124452c84', 'frontier/comparison-bounds/uniform_k_neighborhood_cost.py': '365265347aca1ee5a179df991be2316219f0cb4dbe7a5606a020664c3a56723b', 'frontier/moments-survival/complete_off_face_factorial_tail.py': '6f09199dd8379336bbc84e4245c3ea95a0499939cf72a2c41b9ef7b658049498', 'frontier/moments-survival/uniform_factorial_neighborhood.py': 'f88deae1854a1fc5af0a40a0a3bbf5918c813959145c5d45dcb8cd91a5c31d3c', 'frontier/cover-geometry/complete_off_face_omitted_tails.py': '33e8c164c64790483ba512c984e8090cf5c44b92bf6ca1cb08a17cb56a93201d', 'frontier/retained-transport/finite_source_face_transport.py': '04c99f1a0c6e1781734531923705863fbc9843c610f6d4933a81c89429aa5291', 'frontier/comparison-bounds/complete_off_face_cost.py': '0d53ac6dc99eac6db322525d94375c498e61cb1c5cacd8776327c70d311306c8', 'frontier/source-budgets/shared_six_head_square_comparison.py': 'dd0e7c561f2a32b264b655ee983e735d59fe0cce9d6c3509cde8a2ea0210a74a', 'certificates/source_norms/source-budgets/shared_six_head_square_comparison.json': '833ea6740c99c7cf5c7cf79f9bce63e2b9be253b504e5b8d3b5827abf4f2d871', 'certificates/source_norms/moments-survival/uniform_factorial_neighborhood.json': 'c64376b9d5e355257566bb2336a28dc0d9ef6fc2a22c0fae05c5fa220bb3602e', 'profile-notes/193-256/199-one-six-label-head-controls-the-square-and-both-complete-crosses.md': '8088d1d4709a746b9bdf6f558bdc4ef3bf54a816220556019b241447764ccccf', 'profile-notes/129-192/138-the-complete-factorial-tail-is-uniform-on-a-source-neighborhood.md': '7d7eabc5183be81090967c221a6c3611544cc6841829e7d40c7517fb5b5d10f5', 'profile-notes/065-128/128-the-complete-factorial-tail-retains-its-head-off-the-face.md': '79ae5ce60d7121afdc3fe0eaa3a87abecf21709d15e7627c2425dd7bdb4926cc', 'profile-notes/193-256/234-every-retained-dual-transports-on-a-generated-small-source-domain.md': '0f36d0aa09744103b3a1ae1d8d8729e6897f896ae283543dce46491d7e4db014', 'frontier/source-budgets/shared_budget_affine_tail.py': 'bdf09dc45ec3f38d7791853c974d1fc637ce3da30cc78c155e643c9d66c60ebd', 'frontier/source-budgets/actual_five_slot_source_modulus.py': '4dd89f4919d2150fa27ba405e586f6bfe74f76b6037b934441ca7ff5357afa86', 'frontier/moments-survival/whole_factorial_same_head.py': '845768cfb7c67a9683c92e4ecaacee40dfc22d6b7f6c8791b5169917650e5c24', 'frontier/endpoint-bounds/k_face_common_seven_hinges.py': 'c382bed2ef52cc22c624c33f8aa2b1313df3a43935916f985c9c11060433c1e3', 'frontier/source-budgets/source_cost_endpoint_attainment.py': '9c22b67d249f21e86e0292189c7808db023fd9c45090911f7c58bffa6b6d1ea2', 'frontier/endpoint-bounds/broad_weighted_identity_source.py': 'bfc5f98109c02b318ee3e92c0951d1d33ded45971d6718623d4c60629dc2e6e6', 'frontier/retained-transport/joint_deep_mean_transport.py': 'efbb0825f227e5cc97a0fc24b71acf3e16a35f6b3db662f0e4b392afb8e3d0d0', 'certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json': 'cb1decc204e827ab7ca7fd3f199364b44010e219cdc63f69d960a36520d66cf6', 'frontier/source-budgets/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original source')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def ordered_tail_square(problem, par, factorial):
    """Restore the tail diagonal to the existing distinct-pair cap series."""
    d, R = par['delta'], par['rho']
    eps = (par['kbar']*R, R+d/240, R, R)
    old = sum(par['c'][j]*factorial.geometric(p, start)
              +factorial.clipped_line(eps[j], par['H'][j], p, start)
              for j, (p, start) in enumerate(((3, 3), (5, 2), (5, 2), (5, 2))))+F(1, 72)
    a0, b1 = factorial.geometric(3, 3), factorial.geometric(5, 1)
    raw = problem.pairs['raw_coefficient_upper']
    weights = (F(1), F(1), F(1), a0, b1, b1, b1, a0*b1)
    raw_linear = sum(x*y for x, y in zip(raw, weights))
    positive = raw_linear/5
    pairs = problem.pairs['tail_distinct_pairs']
    result = 2*pairs+old+positive
    require(min(old, positive, pairs) > 0, 'All nonnegative complete tail classes')
    if d == R == 0:
        require((pairs, old, positive, result) == (F(2539, 3600), F(163, 1800), F(11, 72), F(2977, 1800)),
                'Exact199 ordered tail-square recovery including all diagonals')
    return {'old_tail_diagonal': old, 'positive7_tail_diagonal': positive,
            'raw_old_linear_cap': raw_linear, 'raw_linear_weights': weights,
            'distinct_tail_pairs': pairs, 'complete_ordered_tail_square': result,
            'complete_ordered_tail_square_excess': result-F(2977, 1800)}


def calculate(base):
    require(PINS, 'Final source and logical predecessor pins')
    io = module('small_moment_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical input '+path)
    load = lambda name: module('small_moment_'+name, io.named_artifact(base/'frontier', name+'.py'))
    small, uniform = load('retained_small_domain_all_bank_transport'), load('uniform_k_neighborhood_cost')
    factorial, existing = load('complete_off_face_factorial_tail'), load('uniform_factorial_neighborhood')
    tails, finite, cost = load('complete_off_face_omitted_tails'), load('finite_source_face_transport'), load('complete_off_face_cost')
    source = module('small_moment_source', base/'verify_joint_frontier.py')
    square_face = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/shared_six_head_square_comparison.json'))
    require(F(square_face['complete_square_upper']) == F(8201, 1800)
            and square_face['r'] == square_face['rho'] == '0', 'The original complete199 square theorem')
    d, R, G = F(1, 10**8), F(1, 10**11), F(1, 60)
    domain = small.parameters(d, R, G)
    par, zero = uniform.parameters(d, R), uniform.parameters(F(0), F(0))
    require(par['rbar'] == 5*R and par['gap'] >= G
            and min(par['v0'], par['v1']) > 0, 'The same actual source with valid138 outer tables')
    face = cost.face_case(finite, source)
    problem = existing.UniformFactorialHead(factorial, tails, finite, face, par)
    reference = existing.UniformFactorialHead(factorial, tails, finite, face, zero)
    require(all(sum(problem.pre[5*c+s] for s in range(5)) <= 1 for c in range(5))
            and sum(problem.eta_upper) <= 1 and max(problem.descendant) <= 1,
            'All current raw old-tail operator mass bounds are at most one')
    best, face_best, count = F(-1), F(-1), 0
    witnesses, digest = [], sha256()
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        parts, before = problem.components(layout), reference.components(layout)
        require(all(parts[k] >= before[k] for k in ('head', 'old_cross_baseline', 'old_cross_error', 'positive7_cross', 'head_total')),
                'Every original138 head component has a containing neighborhood bound')
        value = parts['head_total']
        face_best = max(face_best, before['head_total'])
        count += 1
        digest.update(json.dumps(encode([layout, parts]), separators=(',', ':')).encode())
        if value > best:
            best, witnesses = value, [{'layout': layout, 'components': parts}]
        elif value == best:
            witnesses.append({'layout': layout, 'components': parts})
    T5 = best+problem.pairs['tail_distinct_pairs']
    require(count == 12500 and face_best == F(139, 900)
            and face_best+reference.pairs['tail_distinct_pairs'] == F(619, 720), 'The complete original138 factorial face specialization')
    require(F(619, 720) < T5 < F(619, 720)+F(1, 100000), 'Actual uniform factorial bound, without importing174 face value')
    ordered_zero = ordered_tail_square(reference, zero, factorial)
    ordered = ordered_tail_square(problem, par, factorial)
    require(ordered['complete_ordered_tail_square_excess'] >= 0, 'Nonnegative complete tail-square transport')
    delta_cap = sum(domain['cap_increments'])
    delta_budget = sum(domain['parameters']['budget_increments'])
    delta_raw = delta_cap+delta_budget
    dw, v = d/5+R/G, max(par['v0'], par['v1'])
    operator = F(1, 18)+F(3, 20)+F(1, 72)
    profile = 6*v/18+d/20
    clipped = {'pure3': factorial.clipped_line(R, F(1), 3, 3),
               'each_five_family': factorial.clipped_line(R, F(1), 5, 2),
               'mixed': factorial.clipped_product(R, F(1))}
    excess = 6*(clipped['pure3']+3*clipped['each_five_family']+clipped['mixed'])
    q_loss, e27 = d/2+10*R, d/360+par['Cbar']*R
    credit = 36*(q_loss/135+5*e27)
    head = 36*delta_raw+36*dw*F(97, 360)+credit+36*R
    old_cross = 2*(profile+6*dw*operator+excess)
    seven_cross = F(2, 5)*(36*delta_raw+profile)
    epsilon = head+old_cross+seven_cross+ordered['complete_ordered_tail_square_excess']
    Q = F(8201, 1800)+epsilon
    require(min(delta_raw, dw, profile, credit, head, old_cross, seven_cross) > 0
            and 0 < epsilon < F(1, 100000), 'Explicit complete all-layout square modulus')
    face_caps, face_budgets = small.face_geometry()
    require(sum(face_caps) == F(97, 360) and sum(face_budgets) == F(1, 4), 'Exact old25-node geometry')
    pins = dict(PINS)
    for path, pin in square_face['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent original199 source closure')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned original199 dependency '+path)
        pins[path] = pin
    return encode({'schema': 'erdos7-small-source-square-factorial-transport-v1', 'source_sha256': pins,
                   'domain': domain, 'factorial_parameters': par,
                   'factorial': {'complete_factorial_upper': T5, 'face_upper': F(619, 720),
                                 'excess': T5-F(619, 720), 'head_maximum': best,
                                 'pair_partition': problem.pairs, 'original_layout_count': count,
                                 'all_layout_components_sha256': digest.hexdigest(), 'maximizing_witnesses': witnesses},
                   'square': {'face_square_upper': F(8201, 1800), 'complete_square_upper': Q,
                              'complete_error_upper': epsilon, 'raw_cap_increment_sum': delta_cap,
                              'raw_budget_increment_sum': delta_budget, 'density_increment': dw,
                              'old_tail_operator_weight': operator, 'old_tail_profile_increment': profile,
                              'positive_excess_clipped_series': clipped, 'old_tail_positive_excess_upper': excess,
                              'pure5_slot_credit_loss': q_loss, 'forced27_defect_upper': e27,
                              'forced27_square_credit_loss': credit, 'head_square_error': head,
                              'twice_old_cross_error': old_cross, 'twice_positive7_cross_error': seven_cross,
                              'complete_ordered_tail': ordered, 'zero_radius_ordered_tail': ordered_zero},
                   'scope': 'Whole-source199 square transport on delta<=10^-8,rho<=10^-11, both actual K orientations and all original independent test labels; existing138 factorial evaluated on the same domain. Every cross and complete geometric/pair tail is retained. No174 face factorial substitution,52-cost K conclusion,global join,Lean or unrestricted Erdos7 result.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('small_moment_output', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)), 'Exact complete small-domain square/factorial certificate')
    print('Complete square <= '+str(float(F(result['square']['complete_square_upper'])))
          +'; square error='+str(float(F(result['square']['complete_error_upper']))))
    print('Complete factorial <= '+str(float(F(result['factorial']['complete_factorial_upper']))))
    print('PASS: all12500 existing factorial heads and full199 square transport; complete52-cost consumer remains separate.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
