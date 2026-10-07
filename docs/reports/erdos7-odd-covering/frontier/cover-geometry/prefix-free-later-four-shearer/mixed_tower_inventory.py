#!/usr/bin/env python3
"""Exact clique-polynomial constants for the mixed ternary inventory contract.

The deletion recurrence is Report563 PF9. Its independent check expands the
same disjoint-block polynomial in elementary symmetric functions. This finite
consumer neither searches families nor proves the ordinary source reduction.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import comb, gcd, prod
from pathlib import Path
import argparse
import hashlib
import importlib.util
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



def phase_union_budget(rho, event_weights, query_weights):
    """Actual first-phase union budget: exact shared-root activity perturbations."""
    full = len(rho) - 1
    products = subset_products(event_weights)
    corrections = ((1, F(1, 2)), (2, F(4, 15)),
                   (1, F(1, 3)), (3, F(2, 15)))

    def numerator(table):
        return query_numerator(table, query_weights) - sum(
            cap * table[full ^ support] - table[full]
            for support, cap in corrections)

    def perturbed(epsilon):
        @lru_cache(None)
        def value(mask):
            if not mask:
                return F(1)
            first = mask & -mask
            rest = mask ^ first
            result, sub = value(rest), rest
            while sub:
                block = first | sub
                result -= (products[block] + epsilon.get(block, F(0))) * value(mask ^ block)
                sub = (sub - 1) & rest
            return result
        return tuple(value(mask) for mask in range(full + 1))

    n0 = numerator(rho)
    gap0 = 28 * rho[-1] - n0
    expected = (F(1129026791, 10906481736), F(7903187537, 45977658372),
                F(12419294701, 38927263500), F(14677348283, 37248983352),
                F(19193455447, 35211078432), F(21451509029, 34547909724),
                F(25967616193, 33598694052))
    rows, simultaneous = [], {}
    for i, q in enumerate(P[1:], 1):
        pair = 1 | (1 << i)
        derivative = tuple(-rho[mask ^ pair] if mask & pair == pair else F(0)
                           for mask in range(full + 1))
        cap = F(q - 1, q * (q - 2))
        gap_derivative = 28 * derivative[-1] - numerator(derivative)
        tau = -gap0 / (cap * gap_derivative)
        check('phase_union_thresholds', str(q), tau == expected[i - 1] > 0)
        check('phase_union_thresholds', f'positivity/{q}', cap * tau < F(1, 28))
        table = perturbed({pair: cap / 2})
        for mask, value in enumerate(table):
            check('phase_union_polynomial', f'{q}/{mask}',
                  value == rho[mask] + cap * derivative[mask] / 2)
        check('phase_union_thresholds', f'gap/{q}',
              28 * table[-1] - numerator(table) == gap0 * (1 - F(1, 2) / tau))
        row = {'prime': q, 'tau': tau, 'activity_at_threshold': cap * tau,
               'gap_activity_derivative': gap_derivative}
        if q >= 17:
            for mask, value in enumerate(table):
                check('phase_union_positive_corollaries', f'{q}/{mask}', value > 0)
            row['eta_half_query_bound'] = numerator(table) / table[-1]
            check('phase_union_positive_corollaries', f'query/{q}',
                  row['eta_half_query_bound'] < 28)
        rows.append(row)
        simultaneous[pair] = cap * tau / 8
    mixed = perturbed(simultaneous)
    for mask, value in enumerate(mixed):
        linear = rho[mask] - sum(eps * rho[mask ^ pair]
            for pair, eps in simultaneous.items() if mask & pair == pair)
        check('phase_union_simultaneous', str(mask), value == linear > 0)
    check('phase_union_simultaneous', 'gap',
          28 * mixed[-1] - numerator(mixed) == gap0 / 8)
    check('phase_union_constants', 'three common-prime bounds',
          [row['eta_half_query_bound'] for row in rows[-3:]] ==
          [F(64168877249, 2348456910), F(72359284393, 2733458520),
           F(88703129633, 3495407100)])
    check('phase_union_constants', 'positivity margin',
          rho[-1] - F(1, 28) == F(2898887, 57255660) > 0)
    check('phase_union_constants', 'base extrema', min(rho) == rho[-1] and max(rho) == 1)
    check('phase_union_constants', 'outside reciprocal inventory',
          F(53, 918) - F(7, 216) == F(31, 1224) > 0)
    failure_ratio = F(13, 54) / expected[0]
    check('phase_union_constants', 'five-prime budget failure',
          failure_ratio == F(2625634492, 1129026791) > 1)
    free_root_bound = F(5, 2) * prod(F(q, q - 1) for q in P[1:])
    check('phase_union_constants', 'alternative supported law',
          free_root_bound == F(3380195, 663552) < 28)
    families = {'new_scope': ((2, 3), (1, 51), (136, 153), (274, 459), (904, 1377)),
                'budget_failure': ((2, 3), (1, 15), (10, 45), (112, 135), (13, 405))}
    for name, family in families.items():
        check('phase_union_actual_examples', f'{name}/labels',
              len({m for _, m in family}) == len(family))
        for j, (a, m) in enumerate(family):
            check('phase_union_actual_examples', f'{name}/odd/{m}', m > 1 and m % 2 == 1)
            for b, n in family[:j]:
                check('phase_union_actual_examples', f'{name}/{m}/{n}', (a - b) % gcd(m, n) != 0)
        q = 17 if name == 'new_scope' else 5
        for (a, m), j, root in zip(family[2:], (2, 3, 4), (1, 4, 13)):
            check('phase_union_actual_examples', f'{name}/prefix/{m}',
                  m == q * 3 ** j and a % 3 ** j == root)
    return {'thresholds': rows, 'base_gap': gap0,
            'meaning': 'Sufficient sum eta_q/tau_q<1 under one fixed pure reference; not universal.',
            'five_prime_failure_ratio': failure_ratio,
            'failure_family_alternative_bound': free_root_bound,
            'actual_families': families}


def prime_tail_budget(mass):
    """Reuse Report734's quartic continuation on the MT1 unnormalized source."""
    supplier = (Path(__file__).resolve().parent.parent /
                'fibre-credit-depth-two-obstruction' /
                'fibre_credit_depth_two_quartic_prime_tail.py')
    spec = importlib.util.spec_from_file_location('mt1_quartic_tail', supplier)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'cannot load quartic tail supplier: {supplier}')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    density = 3 * prod(F(p - 1, p - 2) for p in P[1:])
    check('prime_tail_application', 'joint density', density == F(4096, 595))
    result = module.evaluate(P, mass, density, 4, F(1, 4), 20, 729, 6, F(1, 80))
    check('prime_tail_application', 'absolute fourth moment',
          F(result['absolute_moment_potential']) == F(27529207808375, 46574352))
    check('prime_tail_application', 'remaining absolute mass',
          F(result['remaining_absolute_mass_lower']) > F(1, 80))
    check('prime_tail_application', 'Haar conversion',
          F(result['Haar_lower_prefactor']) == F(119, 65536))
    bridge_path = (supplier.parent.parent / 'refined-capped-source' /
                   'retained_core_prime_bridge.py')
    bridge_spec = importlib.util.spec_from_file_location('mt1_finite_prime_bridge', bridge_path)
    if bridge_spec is None or bridge_spec.loader is None:
        raise RuntimeError(f'cannot load finite prime bridge: {bridge_path}')
    bridge = importlib.util.module_from_spec(bridge_spec)
    bridge_spec.loader.exec_module(bridge)
    tail = module.evaluate(P, mass, density, 4, F(1, 4), 20, 3000, 7, F(1, 80))
    primes = bridge.complete_primes(500, 3000)
    check('prime_tail_application', 'complete finite prime interval',
          len(primes) == 335 and primes[0] == 503 and primes[-1] == 2999)
    allowance, exact, rows = bridge.continuation(
        primes, F(tail['tail_coefficient']), F(1, 4), F(9), 10**30)
    forward, growth_product = F(0), F(1)
    for p in primes:
        forward += growth_product * F(9, (p - 1)**4)
        growth_product *= 1 + bridge.a4(p) / F(3, 4)
    forward += growth_product * F(tail['tail_coefficient'])
    check('prime_tail_application', 'forward and backward exact allowance', forward == exact)
    check('prime_tail_application', 'rounded finite bridge allowance',
          allowance == F(70027231661987264313567, 5 * 10**29))
    remaining = mass - F(tail['absolute_moment_potential']) * allowance
    check('prime_tail_application', 'finite bridge positive mass',
          remaining == F(78952939940002286208867333912015109,
                         22169391552000000000000000000000000000) > F(1, 300))
    result['finite_prime_bridge'] = {
        'cutoff_exclusive': 500, 'analytic_tail': tail, 'primes': primes,
        'prime_count': len(primes), 'rounding_scale': 10**30,
        'rounded_loss_coefficient': allowance,
        'rounding_error_upper': F(1, 10**26),
        'remaining_absolute_mass_lower': remaining, 'strict_simple_lower': F(1, 300),
        'Haar_lower_prefactor': F(1, 300) / density,
        'Haar_tail_factor_per_actual_prime': F(3, 4), 'rows': rows}
    return result


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
    phase_union = phase_union_budget(rho, event_weights, query_weights)
    prime_tail = prime_tail_budget(rho[-1])
    return {
        'scope': 'Exact rational constants; actual-source and all-height arguments are in Report563 sections8 and9.',
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
        'phase_union_budget': phase_union,
        'prime_tail_budget': prime_tail,
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
