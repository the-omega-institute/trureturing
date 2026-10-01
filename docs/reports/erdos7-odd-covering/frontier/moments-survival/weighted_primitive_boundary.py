#!/usr/bin/env python3
"""Exact, bounded checks for the periodic weighted-Fourier boundary.

Uses integer cyclotomic remainders, not numerical complex arithmetic or
the divisibility criterion, to decide whether each actual fibre cancels.
Only the four explicitly declared small original families are checked.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
import json
from math import gcd, lcm
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def divisors(n):
    return [j for j in range(1, n + 1) if n % j == 0]


def trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def divrem(a, b):
    a = trim(list(a))
    quotient = [0] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and any(a):
        require(b[-1] == 1, "divisor must be monic")
        offset = len(a) - len(b)
        coefficient = a[-1]
        quotient[offset] = coefficient
        for i, value in enumerate(b):
            a[offset + i] -= coefficient * value
        trim(a)
    return trim(quotient), trim(a)


@lru_cache(None)
def cyclotomic(d):
    polynomial = [-1] + [0] * (d - 1) + [1]
    for c in divisors(d)[:-1]:
        polynomial, remainder = divrem(polynomial, cyclotomic(c))
        require(not any(remainder), "nonexact cyclotomic division")
    return tuple(polynomial)


def character_remainder(d, terms):
    polynomial = [0] * d
    for exponent, coefficient in terms:
        polynomial[exponent % d] += coefficient
    return divrem(polynomial, cyclotomic(d))[1]


@lru_cache(None)
def ramanujan(d, t):
    units = [k for k in range(d) if gcd(k, d) == 1]
    remainder = character_remainder(d, ((k * t, 1) for k in units))
    require(len(remainder) == 1, "Ramanujan sum not rational")
    return Fraction(remainder[0], len(units))


def valuation(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def prime_support(n):
    return [p for p in divisors(n)[1:]
            if all(p % j for j in range(2, p))]


def moments(family, q, residue):
    period = lcm(*(d for _, d in family), q)
    a, d = family[0]
    beta = h = s = xsum = identity = Fraction(0)
    for x in range(residue, period, q):
        hits = [x % m == b % m for b, m in family]
        load = sum(hits)
        beta += hits[0]
        h += load - 1
        s += load == 0
        xsum += hits[0] * (load - 1)
        identity += (load - 1) * ramanujan(d, (x - a) % d)
    return {key: value / period for key, value in
            (('beta', beta), ('H', h), ('S', s), ('X', xsum),
             ('identity', identity))}


def run():
    fixtures = [
        ('one_label', [(0, 3)]),
        ('two_incomparable', [(0, 15), (0, 21)]),
        ('one_cut_retains_other_axes', [(11, 45), (2, 21), (17, 35)]),
        ('both_selected_axes_required', [(0, 45), (0, 9), (0, 15), (0, 35)]),
    ]
    counts = dict(families=0, periods=0, termwise_iff=0,
                  safe_fibres=0, residual_kernel_values=0)
    boundaries = []
    for name, family in fixtures:
        period = lcm(*(d for _, d in family))
        a, d = family[0]
        primes = prime_support(d)
        require(all(m % d for _, m in family[1:]), 'selected not maximal')
        deficits = [{p for p in primes if valuation(m, p) < valuation(d, p)}
                    for _, m in family[1:]]
        admissible = []
        for q in divisors(period):
            counts['periods'] += 1
            all_termwise = True
            for index in range(-1, len(family)):
                if index == 0:
                    continue
                terms_zero = []
                for r in range(q):
                    points = [x for x in range(r, period, q)
                              if index == -1 or x % family[index][1]
                              == family[index][0] % family[index][1]]
                    terms_zero.append(not any(character_remainder(
                        d, ((x - a, 1) for x in points))))
                predicted = (q if index == -1 else lcm(q, family[index][1])) % d != 0
                require(all(terms_zero) == predicted, f'termwise iff: {name,q,index}')
                counts['termwise_iff'] += 1
                all_termwise = all_termwise and all(terms_zero)
            cut = {p for p in primes if valuation(q, p) < valuation(d, p)}
            require(all_termwise == (bool(cut) and all(cut & z for z in deficits)),
                    f'hitting criterion: {name,q}')
            e = d // gcd(d, q)
            require(all_termwise == (e > 1 and all(
                (m // gcd(m, q)) % e for _, m in family[1:])),
                f'residual criterion: {name,q}')
            if all_termwise:
                admissible.append(q)
            if q % d == 0:
                continue
            dangerous = [(b, m) for b, m in family[1:] if lcm(q, m) % d == 0]
            for r in range(q):
                safe = all((r - b) % gcd(q, m) for b, m in dangerous)
                actual_safe = all(not any(character_remainder(d, (
                    (x - a, 1) for x in range(r, period, q) if x % m == b % m)))
                                  for b, m in family[1:])
                require(safe == actual_safe, f'actual safe-fibre iff: {name,q,r}')
                if safe:
                    counts['safe_fibres'] += 1
                    terms = []
                    beta_count = 0
                    for x in range(r, period, q):
                        load = sum(x % m == b % m for b, m in family)
                        terms.append((x - a, load - 1))
                        beta_count += x % d == a % d
                    terms.append((0, -beta_count))
                    require(not any(character_remainder(d, terms)),
                            f'masked weighted identity: {name,q,r}')
                g = gcd(d, q)
                if (r - a) % g == 0:
                    for x in range(r, period, q):
                        require(ramanujan(d, (x - a) % d)
                                == ramanujan(e, ((x - a) // g) % e),
                                f'residual kernel: {name,q,r,x}')
                        counts['residual_kernel_values'] += 1
        maximal = [q for q in admissible if not any(t != q and t % q == 0
                                                    for t in admissible)]
        minimal_hits = []
        for length in range(1, len(primes) + 1):
            for values in combinations(primes, length):
                chosen = set(values)
                if all(chosen & z for z in deficits) and not any(
                        old <= chosen for old in minimal_hits):
                    minimal_hits.append(chosen)
        predicted_maximal = []
        for chosen in minimal_hits:
            q = period
            for p in chosen:
                q //= p ** (valuation(period, p) - valuation(d, p) + 1)
            predicted_maximal.append(q)
        require(sorted(maximal) == sorted(predicted_maximal), f'maximal periods: {name}')
        boundaries.append(dict(name=name, period=period, maximal_periods=sorted(maximal)))
        counts['families'] += 1
    bad = moments(fixtures[1][1], 5, 0)
    require(bad['identity'] == Fraction(8, 105) and bad['beta'] == Fraction(7, 105),
            'sharp offending-label identity failure')
    constant_bad = moments(fixtures[0][1], 3, 0)
    require(constant_bad['identity'] == 0 and constant_bad['beta'] == Fraction(1, 3),
            'sharp constant-term identity failure')
    good = moments(fixtures[1][1], 21, 3)
    require(good == dict(beta=Fraction(1,105), H=Fraction(-4,105),
                         S=Fraction(4,105), X=Fraction(0), identity=Fraction(1,105)),
            'actual positive residual fixture')
    full_bound = (good['beta'] - Fraction(1,8)*good['H']) / Fraction(5,8)
    residual_bound = 4 * good['beta']
    require(full_bound == Fraction(4,175) < residual_bound == good['S'],
            'strict residual improvement')
    bucket = moments(fixtures[1][1], 21, 0)
    require(bucket == dict(beta=Fraction(1,105), H=Fraction(1,105),
                           S=Fraction(0), X=Fraction(1,105), identity=Fraction(1,105)),
            'actual partner-bucket fixture')
    debit = (bucket['beta'] - Fraction(1,8)*bucket['H']) / Fraction(7,8)
    partner_residue, partner_modulus = fixtures[1][1][1]
    bucket_period = lcm(*(m for _, m in fixtures[1][1]), 21)
    actual_deleted_hinge = Fraction(sum(
        x % 21 == 0 and x % partner_modulus == partner_residue % partner_modulus
        for x in range(bucket_period)), bucket_period)
    require(actual_deleted_hinge == Fraction(1,21), 'actual deleted-hinge mass')
    require(debit == Fraction(1,105) <= actual_deleted_hinge, 'positive actual bucket debit')
    return dict(scope='Four declared finite families; no all-family computational claim',
                arithmetic='Exact integers, cyclotomic remainders, rational probabilities',
                counts=counts, boundaries=boundaries,
                sharp_failure={k: str(v) for k,v in bad.items()},
                residual_fixture={k: str(v) for k,v in good.items()},
                bucket_fixture={k: str(v) for k,v in bucket.items()},
                bucket_debit=str(debit), actual_deleted_hinge=str(actual_deleted_hinge),
                full_conductor_bound=str(full_bound), residual_bound=str(residual_bound))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    encoded = json.dumps(run(), indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(encoded, encoding='utf-8')
    else:
        print(encoded, end='')
