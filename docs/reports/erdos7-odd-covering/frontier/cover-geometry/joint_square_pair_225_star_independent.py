#!/usr/bin/env python3
"""Independent coefficients for one joint head release and its whole network.

Reuses the pinned published independent geometric-atom routines, not the new
producer. Rebuilds all induced responses, rational-threshold full-height hinges,
seventh moments, exact Euler products and both infinite-tail coefficients.
Universal source and gluing arguments are ordinary mathematics in the report.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import comb, factorial, isqrt, prod
from pathlib import Path
import json
import runpy


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    candidate_path = args.candidate or args.directory / 'joint_square_pair_225_star_certificate.json'
    blob = candidate_path.read_bytes()
    data = json.loads(blob)
    helper = args.directory / 'five_parent_seventy_one_halfrow_independent.py'
    helper_bytes = helper.read_bytes()
    if sha256(helper_bytes).hexdigest() != '1567153cf05d74bf95646f688cc5a27c5fd8f49f0fdd374b22649b721d56d9da':
        raise RuntimeError('independent helper hash mismatch')
    lib = runpy.run_path(str(helper), run_name='joint_release_independent_library')
    check = lib['check']
    checks = lib['CHECKS']
    check('candidate_pin', sha256(blob).hexdigest() == 'cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5')
    check('candidate_metadata', data['schema'] == 'joint-square-pair-225-star-v1' and data['status'] == 'PASS' and data['new_lean_verification'] is False)
    sources = {}
    for number, filename, pin in (
        (651, 'unqueried_head_four_parent_certificate.json', '8bf5da7b70697b67e5f3df8b2787cbcac087841342423d028372ba4ebe903d2f'),
        (657, 'ordinary_domain_five_parent_certificate.json', 'e46183469f280d262da37a9c33005e724690fc20b0106202c42c9913ed8d8ec0'),
    ):
        raw = (args.directory / filename).read_bytes()
        check('source_pin', sha256(raw).hexdigest() == data[f'source{number}_sha256'] == pin)
        sources[number] = json.loads(raw)
        check('source_status', sources[number]['status'] == 'PASS')
    source = sources[657]
    gamma = F(203129722400814193208791597, 20692505911553620784640000000)
    alpha = F(2673, 110656)
    g = 1 - F(1084133, 201247200)
    check('common_old_gate', F(data['head_gate_before_release']) == F(source['head_gate']) == F(sources[651]['head_gate']) == gamma)
    check('unit_inclusive_coefficient', F(data['g']) == g)
    check('common_projection', F(data['projection_alpha']) == F(source['projection_alpha']) == alpha)
    check('incidence_scope', data['head_root_incidence_counts'] == {'linear_stars': 35, 'pairs': 20})
    qset = (7, 11, 13, 17, 19)
    ds = {q: F(5, 6) if q == 7 else F(q - 2, q - 1) - F(2, q * (q - 2)) for q in qset}
    rs = {q: F(1, q - 1) for q in qset}
    aa = {q: F(1, q * (q - 2)) for q in qset}
    beta = {(q, s): aa[q] * rs[s] + rs[q] * aa[s] for q, s in combinations(qset, 2)}

    def response(u):
        return prod(ds[q] for q in u) - sum(beta[q, s] * prod(ds[z] for z in u if z not in (q, s)) for q, s in combinations(u, 2))

    lower_mass = dict(ds)
    lower_mass[7] = F(157, 210)
    floor = 1 - sum(value / (lower_mass[q] * lower_mass[s]) for (q, s), value in beta.items())
    check('induced_uniform_retention', floor == F(data['uniform_induced_retention_lower']) == F(328686693796069, 337134711943765) > 0)
    responses = {}
    for mask in range(32):
        u = tuple(q for i, q in enumerate(qset) if not (mask & (1 << i)))
        value = response(u)
        check('induced_response', value == F(data['induced_response_upper'][str(mask)]) > 0)
        check('induced_retention_floor', value >= floor * prod(ds[q] for q in u))
        responses[str(mask)] = str(value)
    check('coordinate_mass_caps', {str(q): str(ds[q]) for q in qset} == data['coordinate_mass_upper'])
    debit = F(0)
    released = []
    check('release_inventory', [row['modulus'] for row in data['released225_originals']] == [225 * q for q in qset])
    for q, row in zip(qset, data['released225_originals']):
        central = F(2, 9) * F(4, 75)
        induced = response(tuple(p for p in qset if p != q))
        mass = central * rs[q] * induced
        cost = g * mass
        check('original_label_identity', row['owner'] == q and row['modulus'] == 3**2 * 5**2 * q)
        check('release_central_cap', F(row['central_leaf_cap']) == central)
        check('release_root_cap', F(row['outside_root_cap']) == rs[q])
        check('release_induced_response', F(row['induced_response']) == induced)
        check('release_actual_mass_upper', F(row['actual_event_mass_upper']) == mass)
        check('release_unit_gate_debit', F(row['gate_debit_upper']) == cost)
        debit += cost
        released.append({'modulus': 225 * q, 'event_upper': str(mass), 'gate_debit': str(cost)})
    joint_gate = gamma - debit
    check('joint_debit', debit == F(data['complete_release_gate_debit']) == F(775917695419823486527, 216739001084649120000000))
    check('joint_head_gate', joint_gate == F(data['head_gate']) == F(129051308183692805303085853, 20692505911553620784640000000))

    scale = 2**384
    specs = [(3, F(2, 3), F(2)), (5, F(4, 15), F(4, 3)), (7, F(1, 6), F(7, 5))]
    factor = prod(ds[q] for q in qset if q != 7)
    thresholds = [F(row['t']) for row in data['finite_rows']]
    max_t = max((t.numerator + t.denominator - 1) // t.denominator for t in thresholds)
    ec, hinges = lib['complete_hinges'](specs, max_t, scale)
    check('three_parent_branch', data['branch_parameters'] == {'parents': [3, 5, 7], 'factor': str(factor), 'exact_EC': str(ec)} and ec == F(11, 5))
    check('unchanged_policy_rules', data['finite_row_parameters_reoptimized'] is False and data['finite_row_rule'] == 'inherited657 actual-domain full-Haar cap calibration' and data['tail_row_rule'] == source['tail_row_rule'])
    check('finite_threshold_range', data['threshold_max'] == max_t == 1079 and data['finite_endpoint'] == 1253)
    primes = [p for p in range(3, 2188, 2) if all(p % divisor for divisor in range(2, isqrt(p) + 1))]
    finite_primes = [p for p in primes if 37 <= p < 1253]
    rows = data['finite_rows']
    check('row_prime_census', [row['owner'] for row in rows] == finite_primes and len(rows) == 193)
    caps = {}
    lo_sum = hi_sum = reported_lo = reported_hi = F(0)
    independent_rows = []
    for row, old in zip(rows, source['finite_rows']):
        p, h = row['owner'], row['h']
        domain = F(p - 2) - F(1, 65536)
        t = domain - h
        n = t.numerator // t.denominator
        u = t - n
        check('inherited_actual_row', all(row[key] == old[key] for key in ('owner', 'h', 'D', 't', 'N', 'cap')))
        check('row_scope_and_capacity', row['r'] == 3 and row['N'] == 0 and F(row['D']) == domain and F(row['t']) == t and 10 <= h < domain)
        cap = F(p - 1, h)
        check('row_conditional_cap', F(row['cap']) == cap and cap < F(p, 10))
        check('rational_threshold', u == F(65535, 65536) and 0 <= n and n + 1 <= max_t)
        lo, hi = [factor * ((1 - u) * hinges[n][j] + u * hinges[n + 1][j]) / h for j in (0, 1)]
        check('independent_fee_enclosed', F(row['fee_lower']) <= lo <= hi <= F(row['fee_upper']))
        lo_sum += lo
        hi_sum += hi
        reported_lo += F(row['fee_lower'])
        reported_hi += F(row['fee_upper'])
        caps[p] = cap
        independent_rows.append({'owner': p, 'h': h, 't': str(t), 'fee_lower': str(lo), 'fee_upper': str(hi)})
    check('complete_finite_fee', reported_lo == F(data['finite_fee_lower']) <= lo_sum <= hi_sum <= reported_hi == F(data['finite_fee_upper']))
    generic = specs + [(11, F(1, 10), F(11, 9)), (13, F(1, 10), F(13, 10))]
    moments = [[lib['power_moment'](spec, j) for j in range(8)] for spec in generic]
    for i in range(5):
        for j in range(8):
            check('geometric_power_moment', moments[i][j] == F(data['coordinate_moments'][i][j]))
    moment = sum((-1)**(7 - j) * comb(7, j) * prod(moments[i][j] for i in range(5)) for j in range(8))
    constant = F(2**7 * 6**6, 7**7)
    tail = constant * moment / (6 * 1249**6)
    check('complete_moment7', moment == F(data['complete_generic_five_role_moment7']) == F(source['complete_fifth_role_count_moment7']))
    check('sharp_halfrow_constant', F(data['sharp_halfrow_constant7']) == constant)
    check('complete_halfrow_tail', tail == F(data['complete_five_parent_tail']) == F(source['complete_five_parent_tail']))
    heads = dict(zip((3, 5, 7, 11, 13, 17, 19, 23, 29, 31), map(F, ('2', '4/3', '7/5', '11/9', '13/11', '17/15', '19/17', '5/3', '20/11', '2'))))
    exact_m0 = exact_podd = F(1)
    counts = {'head': 0, 'finite': 0, 'half': 0}
    for p in reversed(primes):
        if p in heads:
            c = heads[p]
            counts['head'] += 1
        elif p in caps:
            c = caps[p]
            counts['finite'] += 1
        else:
            c = F(2 * (p - 1), p - 3)
            counts['half'] += 1
        exact_m0 *= 1 + c * (F(3, p - 1) + F(2, (p - 1)**2))
        exact_podd *= F(p, p - 1)
    check('full_Euler_census', counts == data['Euler_counts'] == {'head': 10, 'finite': 193, 'half': 123})
    check('exact_Euler_enclosed', F(data['M0_lower']) <= exact_m0 <= F(data['M0_upper']))
    check('exact_prime_product_enclosed', F(data['Podd_lower']) <= exact_podd <= F(data['Podd_upper']))
    for key in ('M0_lower', 'M0_upper', 'Podd_lower', 'Podd_upper', 'Euler_endpoint', 'Ctail'):
        check('identical_inherited_Euler_bounds', data[key] == source[key])
    type_i = F(1, 65536)
    check('ordinary_typeI_fee', F(data['ordinary_typeI_fee']) == type_i)
    base_fee = reported_hi + tail + type_i
    check('pre_arbitrary_fee', F(data['fee_before_arbitrary']) == base_fee)
    mhi, plo = F(data['M0_upper']), F(data['Podd_lower'])
    ctail = F(2187, 2186)
    check('complete_tail_correction', F(data['Ctail']) == ctail and data['Euler_endpoint'] == 2187)
    check('policy_census', [(p['kind'], p['K']) for p in data['policies']] == [('RS', 46), ('elementary', 68)])
    policies = []
    for policy in data['policies']:
        k = policy['K']
        v = 2**k
        check('policy_scope', policy['arbitrary_threshold'] == v and policy['max_parents_below_switch'] == 3 and policy['density_denominator'] == 10000)
        if policy['kind'] == 'RS':
            polynomial = sum(F(factorial(6), factorial(6 - j)) * F(7 * k, 10)**(6 - j) for j in range(7))
            fee = mhi * ctail * F(99, 97)**6 * F(v, v - 3)**2 * polynomial / (2 * (v - 1) * F(1841, 240)**6)
            source_policy = source['RS_policy']
        else:
            ratio = F(1, 2) * F(k + 3, k + 2)**6
            check('elementary_tail_ratio', ratio < 1)
            fee = 2 * mhi * ctail / plo**6 * (4 * (k + 2))**6 / F(2**k) / (1 - ratio)
            source_policy = source['elementary_policy']
        check('same_cap_arbitrary_parent_tail', fee == F(policy['fee']) == F(source_policy['fee']))
        raw_margin = joint_gate - base_fee - fee
        projected = alpha * raw_margin
        check('positive_common_budget', F(policy['raw_margin']) == raw_margin > 0)
        check('claimed_density', F(policy['projected_margin']) == projected > F(1, 10000))
        policies.append({'kind': policy['kind'], 'K': k, 'fee': str(fee), 'raw_margin': str(raw_margin), 'projected_margin': str(projected)})
    check('candidate_unchanged', candidate_path.read_bytes() == blob)
    out = {'schema': 'joint-square-pair-225-star-independent-v1', 'status': 'PASS', 'new_lean_verification': False,
           'scope': 'Independent coefficients for the fixed55-incidence head and two complete three-parent networks, not unrestricted noncoverage or a proof of the ordinary source arguments',
           'candidate_sha256': sha256(blob).hexdigest(), 'helper_sha256': sha256(helper_bytes).hexdigest(), 'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
           'source651_sha256': data['source651_sha256'], 'source657_sha256': data['source657_sha256'], 'producer_source_read': False,
           'interval_scale': str(scale), 'induced_responses': responses, 'released_originals': released, 'release_debit': str(debit), 'head_gate': str(joint_gate),
           'finite_rows': independent_rows, 'finite_fee_lower': str(lo_sum), 'finite_fee_upper': str(hi_sum), 'complete_moment7': str(moment),
           'complete_halfrow_tail': str(tail), 'Euler_counts': counts, 'policies': policies, 'checks': dict(checks), 'check_count': sum(checks.values())}
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'check_count': out['check_count'], 'candidate_sha256': out['candidate_sha256'], 'output': str(args.output)}))


if __name__ == '__main__':
    main()
