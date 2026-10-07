#!/usr/bin/env python3
"""Exact clique-polynomial constants for the mixed ternary inventory contract.

The deletion recurrence is Report563 PF9. Its independent check expands the
same disjoint-block polynomial in elementary symmetric functions. This finite
consumer neither searches families nor proves the ordinary source reduction.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import comb, prod
from pathlib import Path
import argparse
import hashlib
import json

P = (3, 5, 7, 11, 13, 17, 19, 23)
CHECKS = Counter()


def check(group, label, condition):
    if not condition:
        raise RuntimeError(f'{group}: {label}')
    CHECKS[group] += 1


def subset_products(weights):
    return tuple(prod((w for i, w in enumerate(weights) if mask >> i & 1),
                      start=F(1)) for mask in range(1 << len(weights)))


def support_polynomials(name, weights, positive):
    """PF9 with zero singleton weights; compare a separate partition expansion."""
    products = subset_products(weights)

    @lru_cache(None)
    def rho(mask):
        if mask == 0:
            return F(1)
        first = mask & -mask
        rest = mask ^ first
        value = rho(rest)
        other = rest
        while other:
            block = other | first
            value -= products[block] * rho(mask ^ block)
            other = (other - 1) & rest
        return value

    # c_n is the signed count of set partitions with no singleton block.
    coefficients = [1, 0]
    for n in range(2, len(weights) + 1):
        coefficients.append(-sum(comb(n - 1, k - 1) * coefficients[n - k]
                                 for k in range(2, n + 1)))
    values = tuple(rho(mask) for mask in range(len(products)))
    for mask, value in enumerate(values):
        alternative = F(0)
        sub = mask
        while True:
            alternative += coefficients[sub.bit_count()] * products[sub]
            if sub == 0:
                break
            sub = (sub - 1) & mask
        check('independent_polynomial_equalities', f'{name}/{mask}',
              value == alternative)
        if positive:
            check('positive_coordinate_subsets', f'{name}/{mask}', value > 0)
    return values, products, coefficients


def query_numerator(polynomials, query_weights):
    full = len(polynomials) - 1
    products = subset_products(query_weights)
    return sum(polynomials[full ^ mask] * weight
               for mask, weight in enumerate(products))


def query_cap(d, polynomials):
    remaining, support, weight = d, 0, F(1)
    for i, p in enumerate(P):
        e = 0
        while remaining % p == 0:
            remaining //= p
            e += 1
        if e:
            support |= 1 << i
            weight *= ((F(1, 2) if e == 1 else F(1, 3 ** (e - 1)))
                       if p == 3 else F(p - 1, (p - 2) * p ** e))
    check('query_contract', str(d), remaining == 1)
    full = len(polynomials) - 1
    return weight * polynomials[full ^ support] / polynomials[full]


def compute():
    CHECKS.clear()
    root_mass = F(1, 3) - F(1, 9) / (1 - F(1, 3))
    row_without_shallow = F(1, 3) / (1 - F(1, 3))
    high_tail = F(1, 81) / (1 - F(1, 3))
    row_cap = F(1, 2) + high_tail
    ternary_query_sum = F(1, 2) + row_without_shallow
    check('source_arithmetic', 'root survival', root_mass == F(1, 6))
    check('source_arithmetic', 'root normalization density', F(1, 2)/root_mass == 3)
    check('source_arithmetic', 'no shallow label', row_without_shallow == F(1, 2))
    check('source_arithmetic', 'height five tail', high_tail == F(1, 54))
    check('source_arithmetic', 'actual row cap', row_cap == F(14, 27))
    check('source_arithmetic', 'all query heights', ternary_query_sum == 1)
    nonternary = tuple(F(1, p - 2) for p in P[1:])
    for p, total in zip(P[1:], nonternary):
        check('source_arithmetic', f'query sum {p}',
              F(p - 1, p - 2) * F(1, p)/(1 - F(1, p)) == total)
    event_weights = (row_cap,) + nonternary
    query_weights = (ternary_query_sum,) + nonternary
    rho, _, coefficients = support_polynomials('mixed_tower', event_weights, True)
    check('claimed_constants', 'full minimum', min(rho) == rho[-1])
    check('claimed_constants', 'full polynomial', rho[-1] == F(1235933, 14313915))
    numerator = query_numerator(rho, query_weights)
    check('claimed_constants', 'query numerator', numerator == F(166489454, 71569575))
    bound = numerator/rho[-1]
    check('claimed_constants', 'query bound', bound == F(166489454, 6179665) < 27)
    caps = {str(d): query_cap(d, rho) for d in (3, 5, 9, 15)}
    for d, cap in caps.items():
        check('probability_corrections', d, cap > 1)
    capped_bound = bound - sum(cap - 1 for cap in caps.values())
    check('claimed_constants', 'four corrected queries',
          capped_bound == F(4061891809, 185389950) < 22)

    rho_q, _, _ = support_polynomials('nonternary', nonternary, True)
    q_numerator = query_numerator(rho_q, nonternary)
    q_bound = q_numerator/rho_q[-1]
    check('claimed_constants', 'Q polynomial', rho_q[-1] == F(5049311, 7952175))
    check('claimed_constants', 'Q restriction', rho_q[-1] == rho[len(rho) - 2])
    check('claimed_constants', 'Q complete query bound', q_bound == F(13463054, 5049311))
    unrestricted, _, _ = support_polynomials('unrestricted_majorant', (F(1),) + nonternary, False)
    check('claimed_constants', 'unrestricted majorant fails',
          unrestricted[-1] == F(-3364432, 7952175) < 0)
    return {
        'scope': 'Exact rational constants; the actual-source and all-height argument is Report563 section8.',
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'primes': P,
        'contract': 'For each Q-smooth n>1, presence of 3n excludes 9n,27n,81n; other labels unrestricted.',
        'row_supplier': {'root_mass_lower': root_mass,
                         'without_3n_upper': row_without_shallow,
                         'height_at_least_five_tail': high_tail,
                         'with_3n_upper': row_cap,
                         'full_ternary_query_sum': ternary_query_sum},
        'signed_partition_coefficients': coefficients,
        'mixed_tower': {'event_weights': event_weights, 'query_weights': query_weights,
                        'polynomials_by_mask': rho, 'query_numerator': numerator,
                        'uncorrected_bound': bound, 'four_query_caps': caps,
                        'probability_corrected_bound': capped_bound},
        'nonternary_companion': {'polynomials_by_mask': rho_q,
                                'query_numerator': q_numerator, 'query_bound': q_bound},
        'unrestricted_majorant': {'polynomials_by_mask': unrestricted,
                                 'meaning': 'Negative upper-activity polynomial; no all-law obstruction.'},
        'checks': dict(CHECKS), 'passed_checks': sum(CHECKS.values()),
        'claim_limit': 'No unrestricted eight-prime query theorem, optimizer, or Lean verification.'}


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write exact results; default verifies the saved result.')
    args = parser.parse_args()
    result = compute()
    rendered = json.dumps(result, indent=2, default=encode) + '\n'
    if args.output:
        args.output.write_text(rendered)
    else:
        saved = Path(__file__).with_suffix('.json')
        if json.loads(saved.read_text()) != json.loads(rendered):
            raise RuntimeError(f'stale or inconsistent exact result: {saved}')
    print(json.dumps({'passed_checks': result['passed_checks'],
                      'mixed_tower_bound': result['mixed_tower']['probability_corrected_bound'],
                      'nonternary_bound': result['nonternary_companion']['query_bound']},
                     default=encode))


if __name__ == '__main__':
    main()
