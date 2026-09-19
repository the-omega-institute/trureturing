#!/usr/bin/env python3
"""Complete second-factorial load tail on both actual saturated K faces.

Repartition the nonnegative LCM cap series itself and combine the result
with the surviving six-head/old-tail operator. The quadratic consumer
compares against the current complete104 rows, not an earlier endpoint.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/whole_face_second_factorial_tail.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/comparison-bounds/whole_cost_common_stop_loss.py': 'a43c2d8ec4228d1a58e8d8511db17f91c8f47470c0114460656be59ccfce2327',
    'certificates/source_norms/comparison-bounds/whole_cost_common_stop_loss.json': '8d2770aa7147105fe03c4428293b588feae64b140afe80585583c786146bbbc5',
    'frontier/endpoint-bounds/k_face_complete_ratio.py': 'e94a6532ff6951d464a224f1a56415aaea90251c520c7b06fc9afe4e6a82c5db',
    'frontier/endpoint-bounds/k_face_common_seven_hinges.py': '3128cab9f43ad9c89a5f129b7c7d0115a6f73684f613111a07a56f0bd71ddcdd',
}
HEAD = ((0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
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


def geometric(p, start):
    return F(1, p**start)/(1-F(1, p))


def cap_row(square, head, surviving):
    """Complete old-coordinate LCM row, split into four disjoint exponent regions."""
    ah, bh = head
    cap = square.cylinder_cap
    require(head in HEAD, 'One of the six original zero-seven head labels')
    coef3 = F(7, 10) if surviving else F(3, 4)
    coef5 = (F(2, 5), F(4, 15), F(4, 45)) if surviving else (F(1, 2), F(1, 3), F(1, 9))
    core = sum(cap(max(a, ah), max(b, bh), surviving) for a, b in product(range(3), range(2)))
    a_tail = geometric(3, 3)*sum(coef3 if max(b, bh) == 0 else F(1, 5**max(b, bh)) for b in range(2))
    b_tail = geometric(5, 2)*sum(coef5[max(a, ah)] for a in range(3))
    mixed = geometric(3, 3)*geometric(5, 2)
    total = core+a_tail+b_tail+mixed
    reconstructions = []
    for cut in (3, 7):
        prefix = sum(cap(max(a, ah), max(b, bh), surviving)
                     for a, b in product(range(cut+1), repeat=2))
        a_complement = geometric(3, cut+1)*(
            (coef3+geometric(5, 1)) if bh == 0 else (F(2, 5)+geometric(5, 2)))
        b_complement = geometric(5, cut+1)*(sum(coef5[max(a, ah)] for a in range(3))
                                           +sum(F(1, 3**a) for a in range(3, cut+1)))
        require(prefix+a_complement+b_complement == total, 'Independent finite row plus its entire complement')
        reconstructions.append({'cut': cut, 'prefix': prefix, 'complete_tail': a_complement+b_complement})
    return {'core': core, 'a_tail': a_tail, 'b_tail': b_tail, 'mixed_tail': mixed,
            'total': total, 'prefix_reconstructions': reconstructions}


def pair_partition(square):
    sums = square.square_sums()
    rows = []
    for head in HEAD:
        live, raw = cap_row(square, head, True), cap_row(square, head, False)
        rows.append({'head_exponents': head, 'surviving_old_row': live, 'raw_old_row': raw,
                     'complete_row': live['total']+raw['total']/5})
    Q, zero_Q, raw_Q = (F(sums[k]) for k in ('full_square_upper', 'zero7_pair_sum', 'raw35_pair_sum'))
    require((Q, zero_Q, raw_Q) == (F(374, 75), F(4651, 1800), F(173, 48)), 'K-face complete square cap series')
    H_all = sum(row['complete_row'] for row in rows)
    H_zero = sum(row['surviving_old_row']['total'] for row in rows)
    H_raw = sum(row['raw_old_row']['total'] for row in rows)
    HH = sum(square.cylinder_cap(max(a, aa), max(b, bb), True) for a, b in HEAD for aa, bb in HEAD)
    H_diag = sum(square.cylinder_cap(a, b, True) for a, b in HEAD)
    L_zero, L_raw = rows[0]['surviving_old_row']['total'], rows[0]['raw_old_row']['total']
    L_all = L_zero+L_raw/5
    TT_ordered = Q-2*H_all+HH
    TT_diag = L_all-H_diag
    PTT = (TT_ordered-TT_diag)/2
    positive7_pair_factor = F(6, 5)*(square.weighted_tail(7, 1)-2*geometric(7, 1))
    OO = zero_Q-2*H_zero+HH
    OP = (raw_Q-H_raw)/5
    PP = positive7_pair_factor*raw_Q
    O_diag, P_diag = L_zero-H_diag, L_raw/5
    require(positive7_pair_factor == F(4, 15) and min(OO-O_diag, OP, PP-P_diag) >= 0,
            'Complete positive cap subseries for old-old, old-seven and seven-seven tail pairs')
    require(OO+2*OP+PP == TT_ordered and (OO-O_diag)/2+OP+(PP-P_diag)/2 == PTT,
            'Independent disjoint-tail reconstruction avoids subtracting unknown moments')
    require((H_all, HH, H_diag, L_all, TT_ordered, TT_diag, PTT)
            == (F(536, 225), F(859, 600), F(713, 1800), F(1151, 1800),
                F(2977, 1800), F(73, 300), F(2539, 3600)), 'Exact complete tail-tail cap partition')
    raw45 = rows[-1]['raw_old_row']['total']
    require(raw45 == F(7, 40), 'Complete raw45 row for both head/seven cross indicators')
    return {'complete_square_sums': sums, 'head_rows': rows, 'head_all_rows': H_all,
            'head_head_ordered': HH, 'head_diagonal': H_diag, 'complete_linear_cap': L_all,
            'tail_tail_ordered': TT_ordered, 'tail_diagonal': TT_diag, 'tail_distinct_pairs': PTT,
            'independent_tail_partition': {'old_old_ordered': OO, 'old_positive7': OP,
                'positive7_positive7_ordered': PP, 'old_diagonal': O_diag, 'positive7_diagonal': P_diag,
                'positive7_positive7_factor': positive7_pair_factor},
            'head_positive7_cross': F(2, 5)*raw45}


def old_tail_operator(bridge):
    pre, raw, w, descendant = bridge.source_tables(2)
    for first in (2, 3, 4):
        moved = bridge.source_tables(first)
        perm = list(range(5)); perm[2], perm[first] = perm[first], perm[2]
        require(all(canonical[c] == other[perm[c]] for canonical, other in zip((pre, raw, w, descendant), moved)
                    for c in range(5)) and tuple(bridge.ROOT[c] for c in perm) == bridge.ROOT,
                'Every complete source and tail table transports by the original first-beta swap')
    p = [[bridge.integer(20*x) for x in row] for row in pre]
    d = [[bridge.integer(18*x) for x in row] for row in descendant]
    wi = [bridge.integer(5*x) for row in w for x in row]
    best, witness, ties, count = -1, None, 0, 0
    digest = sha256()
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        B = bridge.head_load(layout)
        require(min(B) >= 1 and max(B) <= 6, 'The complete independently labelled six-head load')
        z = [weight*max(value-4, 0) for weight, value in zip(wi, B)]
        terms = (max(sum(p[c][s]*z[5*c+s] for s in range(5)) for c in range(5)),
                 max(sum(d[c][s]*z[5*c+s] for c in range(5)) for s in range(5)),
                 max(sum(d[c][s]*z[5*c+s] for c in range(5) if bridge.ROOT[c] == r)
                     for r, s in product(range(2), range(5))),
                 max(d[c][s]*z[5*c+s] for c, s in product(range(5), repeat=2)),
                 5*max(z))
        value = sum(terms)
        digest.update(json.dumps([layout, value], separators=(',', ':')).encode())
        count += 1
        if value > best:
            best, ties = value, 1
            witness = {'layout': layout, 'five_contributions': [F(x, 1800) for x in terms]}
        elif value == best:
            ties += 1
    require(count == 12500 and F(best, 1800) == F(1, 15), 'Exact maximum of the complete old-tail operator')
    return {'source_pre_table': pre, 'source_upper_table': raw, 'retained_density': w,
            'descendant5_coefficients': descendant, 'geometric_coefficients': [F(1, 18), F(1, 20), F(1, 20), F(1, 20), F(1, 72)],
            'layout_count': count, 'all_layout_values_sha256': digest.hexdigest(),
            'maximum': F(best, 1800), 'maximizing_witness': witness, 'maximizer_count': ties}


def quadratic_expansion(source, tag, D, U, T5):
    degree, leading, constant, cutoff = source.zero5_cost_metadata(tag)
    require(degree == 2 and cutoff <= 4 and leading > 0, 'The complete quadratic polynomial is valid from level4')
    values = [source.zero5_cost(tag, n) for n in range(1, 9)]
    first, d1 = values[0], values[1]-values[0]
    curvature = {j: values[j]-2*values[j-1]+values[j-2] for j in (2, 3, 4)}
    theta = 2*leading
    require(first >= 0 and d1 >= 0 and min(curvature.values()) >= 0, 'Nonnegative exact stop-loss coefficients')
    phi = lambda n: F(max(n-5, 0)*(n-4), 2)
    expand = lambda n: first+d1*(n-1)+sum(c*max(n-j, 0) for j, c in curvature.items())+theta*phi(n)
    require(all(expand(n) == values[n-1] for n in range(1, 9)), 'Every low-load transition is reconstructed')
    require(d1+sum(curvature.values())-F(9, 2)*theta == 0
            and first-d1-sum(j*c for j, c in curvature.items())+10*theta == constant,
            'The entire infinite quadratic tail has the identical polynomial coefficients')
    require(all(values[n-1] == leading*n*n+constant for n in range(max(cutoff, 1), 9)), 'Pinned complete polynomial tail')
    bound = first*D+d1*U[1]+sum(c*U[j] for j, c in curvature.items())+theta*T5
    return {'at_one': first, 'first_difference': d1, 'curvatures': curvature, 'factorial_tail_coefficient': theta,
            'polynomial_tail': {'leading': leading, 'constant': constant, 'entrance': cutoff}, 'cost_upper': bound}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('factorial_tail_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/comparison-bounds/whole_cost_common_stop_loss.json'))
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited pin')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
        used[path] = pin
    square = module('factorial_tail_square', base/'frontier/endpoint-bounds/k_face_complete_ratio.py')
    bridge = module('factorial_tail_head', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
    partition, old_tail = pair_partition(square), old_tail_operator(bridge)
    head = square.cylinder_cap(2, 1, True)
    T5 = head+old_tail['maximum']+partition['head_positive7_cross']+partition['tail_distinct_pairs']
    require((head, old_tail['maximum'], partition['head_positive7_cross'], T5)
            == (F(4, 225), F(1, 15), F(7, 100), F(619, 720)), 'Complete factorial-tail theorem')
    require(previous['faces'] == [{'vertices': [398, 410, 422], 'carrier': [1, 1]},
                                  {'vertices': [616, 628, 640], 'carrier': [1, 0]}]
            and previous['r'] == previous['rho'] == '0', 'Exactly both complete actual saturated K faces')
    D, L, Q = map(F, (previous['mass'], previous['linear_upper'], previous['complete_square_upper']))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(374, 75)), 'Same actual mass and complete moments')
    source = module('factorial_tail_cost_source', base/'verify_joint_frontier.py')
    schedule = module('factorial_tail_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('factorial_tail_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    schedule_data = json.loads(io.read_artifact_bytes(base/'certificates/ap_schedule_norms.json'))
    specs, _, _ = schedule.inventory(source, fixed, schedule_data)
    require(len(specs) == 46 and [row['tuple'] for row in specs[41:]] == [[0, 0], [0, 1], [0, 2], [1, 0], [2, 0]], 'All five original quadratic costs')
    U = {int(t): F(value) for t, value in previous['uniform_hinge_uppers'].items()}
    old_costs, weights = list(map(F, previous['improved_cost_bounds'])), list(map(F, previous['cost_weights']))
    require(all(weights[i] == F(2371, 2880) for i in range(41, 46)), 'Original complete quadratic comparison weights')
    direct, updates = list(old_costs), []
    for index in range(41, 46):
        spec = specs[index]
        expansion = quadratic_expansion(source, spec['tag'], D, U, T5)
        bound = expansion['cost_upper']
        direct[index] = min(old_costs[index], bound)
        updates.append({'index': index, 'name': spec['name'], 'tuple': spec['tuple'],
                        'weight': weights[index], 'expansion': expansion,
                        'previous104_bound': old_costs[index], 'accepted_bound': direct[index],
                        'candidate_gain': old_costs[index]-bound,
                        'weighted_direct_improvement': weights[index]*(old_costs[index]-direct[index])})
    require([row['index'] for row in updates if row['candidate_gain'] > 0] == [42, 43, 44, 45]
            and direct[41] == old_costs[41], 'Current104 quadratic00 stays; exactly the other four rows improve')
    consumer = module('factorial_tail_consumer', base/'frontier/endpoint-bounds/vector_face_complete_ratio.py')
    majorant = module('factorial_tail_majorant', base/'frontier/endpoint-bounds/endpoint_numerator_common_costs.py')
    tags = [('h', F(0)), ('s', F(0))]+[spec['tag'] for spec in specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    functions = [lambda n, tag=tag: source.zero5_cost(tag, n) for tag in tags]
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    costs, proofs = consumer.propagate(majorant, functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = F(previous['signed_mass_coefficient']), F(previous['complete_square_weight'])
    require(len(costs) == len(weights) == 52 and min(weights) > 0 and signed < 0 < square_weight,
            'All52 costs, negative mass term and complete positive square complement')
    old_N = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    direct_gain = sum(w*(a-b) for w, a, b in zip(weights, old_costs, direct))
    propagation = sum(w*(a-b) for w, a, b in zip(weights, direct, costs))
    require(old_N == F(previous['numerator_upper']) and old_N-N == direct_gain+propagation
            and direct_gain > 0 and propagation >= 0 and N > 0, 'The entire numerator improvement balances once')
    coefficients = {key: F(value) for key, value in previous['denominator_coefficients'].items()}
    denominator = coefficients['mass']*D-coefficients['linear']*L-sum(coefficients['hinge'+str(t)]*U[t] for t in range(2, 6))
    require(denominator == F(previous['uniform_denominator_lower']) == F(1358432973299, 17084377926000) > 0,
            'Unchanged complete101 AP11 denominator')
    offset = F(previous['offset'])
    comparison = offset+N/denominator
    require(offset+old_N/denominator == F(previous['comparison_upper']) and 403 < comparison < F(previous['comparison_upper']),
            'Strict full-face improvement with the same complete denominator, still above403')
    return {'schema': 'erdos7-whole-face-second-factorial-tail-v1', 'source_sha256': used,
            'faces': previous['faces'], 'mass': D, 'r': F(0), 'rho': F(0), 'linear_upper': L,
            'head_exponents': HEAD, 'head_factorial_bound': head, 'old_tail_operator': old_tail,
            'complete_pair_partition': partition, 'second_factorial_tail_upper': T5,
            'quadratic_updates': updates, 'cost_weights': weights, 'direct_cost_upper_bounds': direct,
            'majorants': proofs, 'improved_cost_bounds': costs, 'signed_mass_coefficient': signed,
            'complete_square_weight': square_weight, 'complete_square_upper': Q,
            'direct_numerator_improvement': direct_gain, 'majorant_propagation_improvement': propagation,
            'total_numerator_improvement': old_N-N, 'previous_numerator': old_N, 'numerator_upper': N,
            'uniform_hinge_uppers': U, 'denominator_coefficients': coefficients,
            'full_AP11_tail': previous['full_AP11_tail'], 'uniform_denominator_lower': denominator,
            'offset': offset, 'previous_comparison': F(previous['comparison_upper']),
            'comparison_upper': comparison, 'comparison_improvement': F(previous['comparison_upper'])-comparison,
            'scope': 'Ordinary complete second-factorial-tail theorem on both full actual saturated K faces, with arbitrary independent original labels and all exponent tails. Repartitions explicit nonnegative LCM-cap subseries, not unknown moments. Uses current104 row minima and retains all52 costs and the full101 denominator. No off-face extension, new global K, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('factorial_tail_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete factorial-tail and current-row certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:12500 independent head layouts, complete cap-series partition, factorial tail619/720, four current quadratic gains and all52 costs.')
    print('Complete face comparison '+str(float(F(result['comparison_upper'])))+'; no global K claim.')


if __name__ == '__main__':
    main()
