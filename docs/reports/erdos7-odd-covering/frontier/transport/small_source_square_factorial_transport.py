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
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe', 'frontier/transport/retained_small_domain_all_bank_transport.py': '593507898cf7773907422a6f1795098c7d7cc91db7c9e27e190485f7d4d889fc', 'frontier/uniform_k_neighborhood_cost.py': '2868fc48d2b02e889402f7c2cbf89cd4236d28a3d575b53cf3cbdf48cd2dd781', 'frontier/complete_off_face_factorial_tail.py': '8447e1cd50d6452a881413067858188344d22631c7b73b74734b3006a244d047', 'frontier/uniform_factorial_neighborhood.py': '76d35e7851e771cd9d94273fd2c178b1b93dbc48f04ab1c831020cd02b1546dc', 'frontier/complete_off_face_omitted_tails.py': '0dc92761c65f6729dfe45770b02dae327d5ddfa1d4b0a79dcc45fb9deb8b81f8', 'frontier/finite_source_face_transport.py': 'aa4099317ddf1b7cca16df4916166b1399d0b6e44cbe6459dde081075db8d332', 'frontier/complete_off_face_cost.py': '6ab17509f6946409cef6b431cdfb316cc35c9055d21de93eb2906c723d93e234', 'frontier/transport/shared_six_head_square_comparison.py': '6143fda13d510610a8a0b46c428e5f94837d43e53f37e956c79c8bb0b310b84d', 'certificates/source_norms/shared_six_head_square_comparison.json': 'a828450b582d41939ae8144da63513e43210b4204ee50f6abdb3f23c36f9fd76', 'certificates/source_norms/uniform_factorial_neighborhood.json': '6f139762ccb6f3aef9e33be770aecf38674ec8e80f6f00e4af5e140052b973ed', 'profile-notes/transport/199-one-six-label-head-controls-the-square-and-both-complete-crosses.md': '1ff5cca5dc8b15a13571b5f7ec91e4f1964c595bf7039a3abed9ba3f6fd6638d', 'profile-notes/138-the-complete-factorial-tail-is-uniform-on-a-source-neighborhood.md': 'd16fd00b71f4c1b0daf0a83df419358294c7322cf8a68d3e6148f13d27466850', 'profile-notes/128-the-complete-factorial-tail-retains-its-head-off-the-face.md': '9c070de9ab953772260c316b96846a874c5799449d0fa4baf72d90d6b33df4e3', 'profile-notes/transport/234-every-retained-dual-transports-on-a-generated-small-source-domain.md': '398289f4b189bf8c8897c818814f6c54e736903ba390c9b72845604d7021637c', 'frontier/shared_budget_affine_tail.py': '0b0a509626dda7f44ecccf56825c2a3027fce2e4269c64a0419e65da3bce1136', 'frontier/actual_five_slot_source_modulus.py': 'dab8cbce31dd85d8a6476c1b13a8146159ff748fa6ce94d78775febf4f3832c0', 'frontier/whole_factorial_same_head.py': '65def5c326c9da6dde7de1bfd91c241347aed825e37af8eeda17883dc091c205', 'frontier/k_face_common_seven_hinges.py': '8cc4600c9b3f2f65a11820fcb2d0d6663c765c20765bbaf1ae0de6e883cefc97', 'frontier/source_cost_endpoint_attainment.py': 'b7daf5ab9c8656d922681e298b030c199c5f9bcc36af7a43e84a5bef156fb68f', 'frontier/broad_weighted_identity_source.py': 'e0a89669a6b8b6ff732391b4c27dddd21bf5517f8a37928120e75955349dd98f', 'frontier/joint_deep_mean_transport.py': 'a63225e637c6e926e80b04822ab8c83b79f8b99d3069b283375838df69ea4534', 'certificates/source_norms/whole_cost_mean_stop_loss.json': 'd535a2f69617536a06655c61a1166813bfd2ce3e17416fc329dcead0ba3201da', 'frontier/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645'}


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
    load = lambda name: module('small_moment_'+name, base/'frontier'/(name+'.py'))
    small, uniform = load('transport/retained_small_domain_all_bank_transport'), load('uniform_k_neighborhood_cost')
    factorial, existing = load('complete_off_face_factorial_tail'), load('uniform_factorial_neighborhood')
    tails, finite, cost = load('complete_off_face_omitted_tails'), load('finite_source_face_transport'), load('complete_off_face_cost')
    source = module('small_moment_source', base/'verify_joint_frontier.py')
    square_face = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/shared_six_head_square_comparison.json'))
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
