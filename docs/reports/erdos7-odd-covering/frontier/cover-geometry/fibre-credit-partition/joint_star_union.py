"""Exact same-source union certificate for the fixed FC36 root-1 inventory.

Ordinary mathematical/finite evidence, not Lean verification. The union
bound is a relaxation over one common source. It excludes this fixed
mixed inventory as a covering realization under the stated height and
star metadata; it is not a bound uniform over every candidate inventory.

Run with explicit --input and --output paths. No third-party dependency.
"""

import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from math import factorial, prod
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', required=True)
    ap.add_argument('--output', required=True)
    args = ap.parse_args()
    raw = Path(args.input).read_bytes()
    data = json.loads(raw)
    checks = 0

    def need(condition, message):
        nonlocal checks
        checks += 1
        if not condition:
            raise ValueError(message)

    primes = data['primes']
    heights = dict(zip(primes, data['heights']))
    stars = {(q, e): t for q, e, t in data['star_roots']}
    selected = dict(data['selected_witness'])
    need(primes == [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41],
         'Specified finite FC36 support')
    need(data['heights'] == [5, 5, 4, 4, 4, 4, 4, 3, 3, 3, 3],
         'Specified original height profile')
    need(len(selected) == len(data['selected_witness']) == 2138,
         'Distinct fixed mixed inventory')
    need(len(stars) == len(data['star_roots']) == sum(heights.values()),
         'Complete distinct star metadata')
    for q in primes:
        for e in range(1, heights[q] + 1):
            need(stars[q, e] == (1 if q == 5 else 2),
                 'Every star keeps the prescribed actual root')

    c = {q: 1 / (1 - sum((F(1, q**e)
                          for e in range(1, heights[q] + 1)), F(0)))
         for q in primes}
    b = {q: c[q] - 1 for q in primes}
    B = {q: b[q] if q == 5 else F(0) for q in primes}
    carrier = prod(1 - B[q] for q in primes)
    singles = sum((b[q] * prod(1 - B[r] for r in primes if r != q)
                   for q in primes), F(0))
    # Product expansion: every support, minus the empty and singleton ones.
    free_charge = prod(1 - B[q] + b[q] for q in primes) - carrier - singles
    selected_charge = F(0)
    root1_count = 0
    root1_palette = []
    for d, t in selected.items():
        need(t in (1, 2), 'Actual retained ternary root')
        need(d > 1, 'Positive nonunit mixed cofactor')
        rest = d
        support = []
        for q in primes:
            e = 0
            while rest % q == 0:
                e += 1
                rest //= q
            if e:
                support.append(q)
                need(e <= heights[q], 'Original exponent stays within profile')
        need(rest == 1 and len(support) >= 2, 'Original mixed cofactor factors')
        if t == 1:
            root1_count += 1
            root1_palette.append(d)
            selected_charge += prod(c[q] if q in support else 1 - B[q]
                                    for q in primes) / d
    need(root1_count == 187, 'Original root-1 mixed count')
    old_lower = carrier - free_charge - selected_charge
    need(old_lower == F(-65412811398963818975709603474259586033354459743,
                       2333849532135992506177716822537480405847422046272),
         'Independent reconstruction of FC36 L1')

    records = []
    totals = []
    group_free = F(0)
    group_selected = F(0)
    group_free_count = 0
    group_selected_count = 0
    for q in primes:
        if q == 5:
            continue
        exponents = [e for e in range(1, heights[q] + 1)
                     if selected.get(5 * q**e) == 1]
        free_q = c[q] * sum((F(1, q**e)
                            for e in range(1, heights[q] + 1)), F(0))
        selected_q = c[q] * sum((F(1, q**e) for e in exponents), F(0))
        total = free_q + selected_q
        need(0 <= total < 1, 'One q-block simplex mass is below one')
        group_free += c[5] / 5 * free_q
        group_selected += c[5] / 5 * selected_q
        group_free_count += heights[q]
        group_selected_count += len(exponents)
        records.append({'prime': q, 'free_exponents': list(range(1, heights[q] + 1)),
                        'root1_selected_exponents': exponents,
                        'free_q_budget': str(free_q),
                        'selected_q_budget': str(selected_q), 'T': str(total)})
        totals.append(total)
    old_group_charge = group_free + group_selected
    need(group_free_count == 37 and group_selected_count == 28,
         'One disjoint 37-free/28-selected grouping of the original charges')
    need(group_free <= free_charge and group_selected <= selected_charge,
         'Group charges are subcharges of the very same old comparison')
    need(old_group_charge == c[5] / 5 * sum(totals, F(0)),
         'Complete same-group independent charge')

    S = 5 * (1 - B[5]) / c[5]
    rho = S - 2
    gamma = F(53, 100)
    P = prod(1 - t for t in totals)
    need(rho == F(313, 625) and 0 <= rho < 1, 'Capped-simplex fractional row')
    need(rho < gamma, 'Rational lower square-root bound exceeds fractional row')
    need(gamma**2 <= P, 'Exact rational square-root certificate')
    need(P >= rho**2, 'Union theorem threshold')
    upper = c[5] / 5 * (2 - 2 * gamma)
    gain = old_group_charge - upper
    corrected = carrier - (free_charge - group_free) - (selected_charge - group_selected) - upper
    need(corrected == old_lower + gain, 'No omitted or repeated group charge')
    need(gain > 0 and corrected > 0, 'Strict positive fixed-inventory survivor certificate')
    need(corrected > F(4, 125), 'Simple rational positive root-1 margin')
    density_cap = 3 * prod(c.values())
    need(density_cap < 8, 'Normalized root-1/pure-survivor law has density cap below eight')
    haar_lower = corrected / density_cap
    need(haar_lower > F(1, 250), 'Full normalized-Haar survivor density certificate')

    # Existing Chapter33 SH6/SH11--SH13 consumer. This rational check
    # retains the analytic prime-product premise; it does not prove it.
    head_primes = [3] + primes
    head_moment = prod(F(p * (p + 1), (p - 1)**2) for p in head_primes)
    cutoff, level = 100000, 10
    need(cutoff >= 286 and level >= 4 and 3**level <= cutoff,
         'Inherited SH11 analytic-product applicability')
    product_constant = F(2 * level**2 + 1, 2 * level**2 - 1)
    polynomial = sum((F(factorial(7), factorial(7 - j) * level**j)
                      for j in range(8)), F(0))
    tau7 = product_constant**7 / cutoff * F(cutoff, cutoff - 3)**2 * polynomial
    tail_loss = head_moment * tau7
    tail_reserve = F(1, 250) - tail_loss
    need(head_moment == F(17517439415203, 525533184000), 'Twelve-prime joint Haar moment')
    need(tail_reserve == F(964282896927551623215869645389,
                           308475661132619977601166622720000),
         'Exact inherited complete-tail reserve')
    need(tail_reserve > F(1, 320), 'Positive mass after every finite large-prime tail')
    tail = {
        'head_primes': head_primes, 'cutoff': cutoff, 'level': level,
        'head_mass_floor': '1/250', 'head_joint_haar_cap': '1',
        'head_second_moment': str(head_moment),
        'analytic_product_constant': str(product_constant),
        'integral_polynomial': str(polynomial), 'tau7': str(tau7),
        'complete_tail_loss_upper': str(tail_loss),
        'distorted_survivor_mass_lower': str(tail_reserve),
        'distorted_survivor_mass_lower_decimal': float(tail_reserve),
        'simple_strict_lower': '1/320',
        'surplus_over_1_over_320': str(tail_reserve - F(1, 320)),
        'source': 'Unnormalized actual Haar restriction to the head-only survivor, '
                  'uniformly lifted to full-family head query heights.',
        'contract': 'Head-only originals satisfy the fixed finite profile and '
                    '187-label palette contract. Every actual support prime '
                    'outside the twelve-prime head exceeds 100000. Originals '
                    'touching those primes may have arbitrary finite head and '
                    'tail exponents, including higher ternary depth. All phases '
                    'remain globally fixed and numerical moduli distinct.',
        'analytic_dependency': 'Chapter33 SH6 and SH11--SH13 with its existing '
                               'Rosser--Schoenfeld/source attribution; not proved '
                               'by this finite rational computation.',
        'boundary': 'Final reserve is distorted-measure mass, not a natural-density '
                    'lower bound for the full family. This does not include '
                    'arbitrary head-only palettes or additional small primes.'
    }

    # Complete vertex assignments in SMALL models. No 5**10 fixture scan.
    # The extra choice -1 is the zero vertex of each <=T simplex.
    models = [
        (F(0), [], F(1)),
        (F(1, 2), [F(1, 2), F(1, 2)], F(1, 2)),
        (F(1, 3), [F(1, 3)], F(4, 5)),
        (F(1, 2), [F(1, 5), F(1, 4), F(1, 6)], F(7, 10)),
        (F(1, 4), [F(1, 7), F(1, 6), F(1, 5), F(1, 4)], F(3, 5)),
        (F(0), [F(2, 3), F(1, 3), F(1, 4), F(1, 5)], F(1, 3)),
        (F(3, 4), [F(1, 10)] * 4, F(4, 5)),
        (F(1, 2), [F(3, 4), F(0)], F(1, 2)),
    ]
    model_records = []
    assignment_count = 0
    source_checks = 0
    for model_rho, model_T, model_gamma in models:
        model_P = prod((1 - t for t in model_T), start=F(1))
        need(model_rho <= model_gamma and model_gamma**2 <= model_P,
             'Finite model satisfies the theorem hypotheses')
        R = [F(1), F(1), model_rho, F(0), F(0)]
        shifted = R[2:] + R[:2]
        mixed = [(2 * a + 3 * d) / 5 for a, d in zip(R, shifted)]
        vectors = [R, shifted, mixed]
        maximum = F(0)
        for assignment in product(range(-1, 5), repeat=len(model_T)):
            row_products = [F(1)] * 5
            for t, row in zip(model_T, assignment):
                if row >= 0:
                    row_products[row] *= 1 - t
            assignment_count += 1
            for vector in vectors:
                value = sum((r * (1 - z) for r, z in zip(vector, row_products)), F(0))
                need(value <= 2 - 2 * model_gamma, 'Small exact joint union bound')
                maximum = max(maximum, value)
                source_checks += 1
        model_records.append({'rho': str(model_rho), 'T': list(map(str, model_T)),
                              'gamma': str(model_gamma), 'P': str(model_P),
                              'max_over_checked_sources_and_assignments': str(maximum)})

    # A hypothesis-sensitive countermodel to the unconditional bound.
    bad_rho = F(1, 2)
    bad_T = [F(3, 4)] * 3
    bad_P = prod(1 - t for t in bad_T)
    bad_union = bad_T[0] + bad_T[1] + bad_rho * bad_T[2]
    bad_sqrt = F(1, 8)
    need(bad_sqrt**2 == bad_P < bad_rho**2,
         'Negative control violates the threshold, not the arithmetic')
    need(bad_union > 2 - 2 * bad_sqrt,
         'Dropping the P>=rho squared condition can invalidate the claimed bound')

    # A small fixture diagnostic, restricted to its two full rows. This is
    # an attaining lower witness for the relaxation, not a claimed optimizer.
    best_two_rows = F(0)
    best_partition = None
    for assignment in product(range(2), repeat=len(totals)):
        row_products = [F(1), F(1)]
        for t, row in zip(totals, assignment):
            row_products[row] *= 1 - t
        value = 2 - sum(row_products)
        need(value <= 2 - 2 * gamma, 'Fixture two-row assignment respects rational upper bound')
        if value > best_two_rows:
            best_two_rows = value
            best_partition = assignment

    result = {
        'contract': 'One fixed FC36 height profile and complete star/root metadata; '
                    'the selected 2138 mixed inventory and the full bounded 3-free debit. '
                    'Same-source FC34 enlarged root-1 carrier. Positive lower mass '
                    'excludes a cover with this fixed mixed inventory; not uniform over '
                    'all numerical inventories and not unrestricted Erdos #7.',
        'input': args.input, 'input_sha256': sha256(raw).hexdigest(),
        'primes': primes, 'heights': data['heights'], 'root1_mixed_count': root1_count,
        'root1_allowable_palette': sorted(root1_palette),
        'group_free_label_count': group_free_count,
        'group_selected_label_count': group_selected_count,
        'q_groups': records, 'c5_over_5': str(c[5] / 5), 'row_sum': str(S),
        'rho': str(rho), 'gamma': str(gamma), 'rho_squared': str(rho**2),
        'gamma_squared': str(gamma**2), 'P': str(P),
        'P_minus_gamma_squared': str(P - gamma**2), 'gamma_minus_rho': str(gamma - rho),
        'sum_T': str(sum(totals, F(0))), 'carrier': str(carrier),
        'full_free_charge': str(free_charge), 'selected_root1_charge': str(selected_charge),
        'group_free_charge': str(group_free), 'group_selected_charge': str(group_selected),
        'old_group_charge': str(old_group_charge), 'old_L1': str(old_lower),
        'union_upper_rational': str(upper), 'gain_rational': str(gain),
        'corrected_L1_rational': str(corrected),
        'corrected_L1_simple_strict_lower': '4/125',
        'source_to_full_haar_density_cap': str(density_cap),
        'full_haar_survivor_lower': str(haar_lower),
        'full_haar_survivor_simple_strict_lower': '1/250',
        'haar_bridge': 'Choose normalized Haar on retained ternary root1 and the '
                       'actual pure-survivor coordinate laws. Their product density '
                       'relative to full normalized Haar is at most 3*product(c_q). '
                       'The FC34 enlarged carrier does not change that probability law.',
        'decimals': {k: float(v) for k, v in [('P', P), ('sum_T', sum(totals, F(0))),
                    ('old_group_charge', old_group_charge), ('union_upper', upper),
                    ('gain', gain), ('old_L1', old_lower), ('corrected_L1', corrected),
                    ('source_density_cap', density_cap), ('full_haar_lower', haar_lower)]},
        'large_prime_tail': tail,
        'small_model_count': len(models), 'small_assignment_count': assignment_count,
        'small_source_assignment_checks': source_checks, 'small_models': model_records,
        'negative_control': {'rho': str(bad_rho), 'T': list(map(str, bad_T)),
                             'P': str(bad_P), 'actual_union': str(bad_union),
                             'invalid_unconditional_upper': str(2 - 2 * bad_sqrt)},
        'fixture_two_row_assignments': 2**len(totals),
        'fixture_best_checked_two_row_union': str(best_two_rows),
        'fixture_best_checked_partition': list(best_partition),
        'fixture_two_row_scope': 'Lower witness in the relaxed model, not a global maximum.',
        'checks': checks,
    }
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: result[k] for k in ['checks', 'small_assignment_count',
          'small_source_assignment_checks', 'gain_rational', 'corrected_L1_rational', 'decimals']},
          sort_keys=True))


if __name__ == '__main__':
    main()
