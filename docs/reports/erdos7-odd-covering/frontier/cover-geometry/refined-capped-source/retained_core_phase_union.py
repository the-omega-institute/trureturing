#!/usr/bin/env python3
"""Exact retained-core intersection certificate for finite shallow phase contracts.

Ordinary rational verification: not Lean and not unrestricted Erdos #7.
Only standard-library imports and explicit adjacent inputs are used.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial, prod
from pathlib import Path
import argparse
import json

PRIMES = (5, 7, 11, 13, 17, 19, 23)
CHECKS = 0


def need(ok, label):
    global CHECKS
    CHECKS += 1
    if not ok:
        raise ValueError(label)


def factor_support(n):
    mask = 0
    for i, p in enumerate(PRIMES):
        if n % p == 0:
            mask |= 1 << i
            while n % p == 0:
                n //= p
    return mask if n == 1 else None


def core_responses(t, removed):
    # Independent Bernoulli count recurrence for zero or one non5 hit.
    zero, one = F(1), F(0)
    for i in range(1, 7):
        if removed >> i & 1:
            continue
        zero, one = zero * (1 - t[i]), one * (1 - t[i]) + zero * t[i]
    non5 = F(1) if removed & 1 else 1 - t[0]
    A, B = non5 * (zero + one), zero
    need(0 <= A <= 1 and 0 <= B <= 1, 'positive core response probabilities')
    return A, B


def a4(p):
    return F(p * (p ** 3 + 11 * p ** 2 + 11 * p + 1), (p - 1) ** 4) - 1


def continuation_data(a, b, caps, cutoff, ell, delta, growth):
    r, v = max(2 * a, 3 * b), max(a, b)
    axes = (3,) + PRIMES

    def tail(p, exponent):
        if exponent == 0:
            return F(1)
        if p == 3:
            return r if exponent == 1 else v / 3 ** (exponent - 2)
        return caps[PRIMES.index(p)] / p ** exponent

    @lru_cache(None)
    def pmf(k, n):
        if k == 0:
            return F(int(n == 1))
        p = axes[k - 1]
        return sum(((tail(p, d - 1) - tail(p, d)) * pmf(k - 1, n // d)
                    for d in range(1, n + 1) if n % d == 0), F(0))

    mean = (1 + r + 3 * v / 2) * prod(caps)
    atoms = {n: pmf(8, n) for n in range(1, 28)}
    hinges = {h: mean - h + sum(((h - n) * p for n, p in atoms.items() if n < h), F(0))
              for h in range(28)}
    need(all(h > 0 for h in hinges.values()), 'positive all-height query hinges')
    K0 = (1 + 15 * r + 216 * v) * prod(1 + c * a4(q) for c, q in zip(caps, PRIMES))
    K29 = K0 * (1 + F(28, 27) * a4(29))
    need(cutoff >= 286 and ell >= 4 and 3 ** ell <= cutoff and 4 * ell >= growth,
         'Report734 complete prime-tail range')
    coefficients = (F(1),) + tuple(F(x) / (1 - delta) for x in (15, 50, 60, 24))
    need(all(x <= comb(growth, i) for i, x in enumerate(coefficients)), 'quartic growth polynomial')
    series = sum((F(factorial(growth), factorial(growth - j) * (3 * ell) ** j)
                  for j in range(growth + 1)), F(0))
    tau = (F(27, 256) / (3 * delta ** 3 * (1 - delta))
           * F(2 * ell ** 2 + 1, 2 * ell ** 2 - 1) ** growth
           * F(cutoff, (cutoff - 1) ** 4) * series)
    critical = min((hinges[h] + 27 * K29 * tau) / (28 - h) for h in hinges)
    return hinges, K0, K29, tau, critical


def calculate(cert):
    global CHECKS
    CHECKS = 0
    need(cert['schema'] == 'retained-core-phase-union-v1', 'certificate schema')
    need(tuple(cert['primes']) == PRIMES, 'fixed seven nonternary primes')
    need(isinstance(cert['cases'], list) and 1 <= len(cert['cases']) <= 5,
         'nonempty bounded set of fixed-law certificates')
    need(len({case['name'] for case in cert['cases']}) == len(cert['cases']),
         'distinct fixed-law case names')
    limit = cert['enumeration_limit']
    need(type(limit) is int and 1000 <= limit <= 20000, 'explicit finite enumeration range')
    cutoff, ell, growth = cert['cutoff'], cert['ell'], cert['growth']
    delta = F(cert['delta'])
    need((cutoff, ell, growth, delta) == (3000, 7, 21, F(2, 7)), 'stated fixed tail parameters')
    caps = tuple(F(q - 1, q - 2) for q in PRIMES)
    bD = tuple(prod(F(1, q - 2) for i, q in enumerate(PRIMES) if s >> i & 1) for s in range(128))
    def bit_core(bits, root):
        return (bits & 1 == 0 and bits.bit_count() <= 1) if root == 0 else bits & 126 == 0
    for bits in range(128):
        for removed in range(128):
            for root in range(2):
                need(bit_core(bits, root) <= bit_core(bits & ~removed, root),
                     'forcing every queried hit to zero only enlarges the core')
    records = {}
    for n in range(2, limit + 1):
        s = factor_support(n)
        if s is None:
            continue
        cap = prod(caps[i] for i in range(7) if s >> i & 1) / n
        for height in range(3):
            if height == 0 and s.bit_count() == 1:
                continue
            m = 3 ** height * n
            need(m not in records, 'unique original numerical label')
            records[m] = (height, s, cap, n)
    vertices = []
    for mask in range(128):
        t = tuple(caps[i] / q if mask >> i & 1 else F(0) for i, q in enumerate(PRIMES))
        responses = tuple(core_responses(t, s) for s in range(128))
        vertices.append(responses)
    result_cases = []
    for case in cert['cases']:
        weights = tuple(map(F, case['weights']))
        need(len(weights) == 5 and weights[0] == weights[1] and len(set(weights[2:])) == 1,
             'one symmetric five-leaf law')
        a, b = weights[0], weights[2]
        need(a > 0 and b > 0 and sum(weights) == 1, 'positive normalized fixed weights')
        selected = case['selected_labels']
        need(type(case['minimum_claim']) is bool and F(case['tail_floor']) > 0,
             'explicit minimality flag and positive stated tail floor')
        need(len(selected) == len(set(selected)) and all(type(m) is int and m in records for m in selected),
             'distinct selected shallow mixed labels')
        remain = [[bD[s] if (s > 0 and (h > 0 or s.bit_count() > 1)) else F(0)
                   for s in range(128)] for h in range(3)]
        for m in selected:
            h, s, cap, n = records[m]
            remain[h][s] -= cap
        need(all(x >= 0 for row in remain for x in row), 'nonnegative residual support inventories')

        def multiplier(h, A, B):
            return (2 * a * A + 3 * b * B, max(2 * a * A, 3 * b * B), max(a * A, b * B))[h]

        def credit(m, response):
            h, s, cap, n = records[m]
            return cap * multiplier(h, *response[s])

        rows = []
        bases = []
        for mask, response in enumerate(vertices):
            mass = multiplier(0, *response[0])
            high = sum((bD[s] * max(a * A, b * B) / 2 for s, (A, B) in enumerate(response)), F(0))
            shallow = sum((remain[h][s] * multiplier(h, A, B)
                           for s, (A, B) in enumerate(response) for h in range(3)), F(0))
            value = mass - high - shallow
            full_shallow = sum((bD[s] * multiplier(h, A, B)
                                for s, (A, B) in enumerate(response) if s > 0
                                for h in range(3) if h > 0 or s.bit_count() > 1), F(0))
            base = mass - high - full_shallow
            need(value == base + sum((credit(m, response) for m in selected), F(0)),
                 'same-source debit and selected-credit identity')
            rows.append(dict(mask=mask, core=str(mass), high_loss=str(high),
                             shallow_loss=str(shallow), lower_bound=str(value)))
            bases.append(base)
        # Exact midpoint controls for the coordinatewise-concavity derivation.
        def actual_parameter_bound(t):
            response = tuple(core_responses(t, s) for s in range(128))
            mass = multiplier(0, *response[0])
            high = sum((bD[s] * max(a * A, b * B) / 2 for s, (A, B) in enumerate(response)), F(0))
            low = sum((remain[h][s] * multiplier(h, A, B)
                       for s, (A, B) in enumerate(response) for h in range(3)), F(0))
            return mass - high - low
        center = [caps[i] / (2 * q) for i, q in enumerate(PRIMES)]
        midpoint = actual_parameter_bound(center)
        for i, q in enumerate(PRIMES):
            lower, upper = center.copy(), center.copy()
            lower[i], upper[i] = F(0), caps[i] / q
            need(2 * midpoint >= actual_parameter_bound(lower) + actual_parameter_bound(upper),
                 'exact coordinatewise concavity midpoint control')
        worst = min(range(128), key=lambda k: F(rows[k]['lower_bound']))
        alpha = F(rows[worst]['lower_bound'])
        hinges, K0, K29, tau, critical = continuation_data(a, b, caps, cutoff, ell, delta, growth)
        need(alpha > critical, 'all128 source vertices cross the complete-tail gate')
        h = min(hinges, key=lambda j: j + hinges[j] / alpha)
        query = h + hinges[h] / alpha
        post29 = (28 - query) / 27
        final = post29 - K29 * tau / alpha
        need(final > F(case['tail_floor']), 'strict stated distorted mass floor')
        ordered = sorted(records, key=lambda m: (-credit(m, vertices[127]), m))
        need(selected == ordered[:len(selected)], 'selected labels are globally ordered at all-upper vertex')
        last = credit(selected[-1], vertices[127])
        unseen = prod(caps) / (limit + 1)
        need(unseen < last, 'every unenumerated label has smaller all-upper credit')
        previous = bases[127] + sum((credit(m, vertices[127]) for m in ordered[:len(selected) - 1]), F(0))
        if case['minimum_claim']:
            need(previous <= critical, 'one fewer label cannot certify positivity in this fixed box bound')
        result_cases.append(dict(name=case['name'], weights=list(map(str, weights)),
                                 count=len(selected), selected_labels=selected, all_vertices=rows,
                                 worst_vertex=worst, alpha=str(alpha), alpha_decimal=float(alpha),
                                 critical=str(critical), critical_decimal=float(critical),
                                 previous_best_at_all_upper=str(previous), unseen_credit_upper=str(unseen),
                                 last_selected_credit=str(last), minimum_claim=case['minimum_claim'],
                                 threshold=h, query_upper=str(query), query_upper_decimal=float(query),
                                 post29_mass=str(post29), fourth_product_before29=str(K0),
                                 fourth_product_with29=str(K29), tau3000=str(tau),
                                 full_tail_reserve=str(final), full_tail_reserve_decimal=float(final),
                                 full_hinges={str(k): str(v) for k, v in hinges.items()}))
    return dict(schema='retained-core-phase-union-result-v1', check_count=CHECKS,
                scope='Conditional ordinary finite-source proof and exact rational controls. Selected actual classes must be null on one common reference core. All other phases/heights are charged. No Lean or unrestricted Erdos7 conclusion; minimality is only for each fixed weight/core/fullbox/hinge/tail certificate.',
                cases=result_cases)


def main():
    stem = Path(__file__)
    parser = argparse.ArgumentParser()
    parser.add_argument('--certificate', type=Path, default=stem.with_name(stem.stem + '_certificate.json'))
    parser.add_argument('--result', type=Path, default=stem.with_suffix('.json'))
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    result = calculate(json.loads(args.certificate.read_text()))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, indent=2) + '\n')
    else:
        need(json.loads(args.result.read_text()) == result, 'retained result exact replay')
    print(json.dumps(dict(check_count=result['check_count'],
                         cases=[{k: row[k] for k in ('name', 'count', 'alpha_decimal', 'worst_vertex',
                                                    'query_upper_decimal', 'full_tail_reserve_decimal')}
                                for row in result['cases']]), indent=2))


if __name__ == '__main__':
    main()
