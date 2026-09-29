#!/usr/bin/env python3
"""Exact reference-centre profiles and a noncovering prime-pair family.

The global minimum uses the exchange proof in report 420. Finite controls
check literal CRT fibres, the arithmetic, and joint survivor counts; they
do not enumerate the large period or replace the general proof. Standard
library only; importing or running this file writes no files.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt, lcm, prod
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, lower, name):
    need(type(value) is int and value >= lower,
         name + ' must be a literal integer >= ' + str(lower))
    return value


def prime(value):
    return (type(value) is int and value >= 2
            and all(value % d for d in range(2, isqrt(value) + 1)))


def primes(values):
    need(type(values) in (list, tuple) and values, 'nonempty prime sequence required')
    need(all(prime(p) and p % 2 for p in values), 'odd primes required')
    need(len(set(values)) == len(values), 'distinct primes required')
    return tuple(sorted(values))


def odd_primes_through(limit):
    integer(limit, 3, 'limit')
    return tuple(p for p in range(3, limit + 1, 2) if prime(p))


def family(classes):
    need(type(classes) in (list, tuple) and classes, 'nonempty original family required')
    result = []
    for item in classes:
        need(type(item) in (list, tuple) and len(item) == 2,
             'each original class must be (modulus, residue)')
        modulus, residue = item
        integer(modulus, 3, 'modulus')
        need(modulus % 2 == 1, 'odd modulus required')
        need(type(residue) is int and 0 <= residue < modulus,
             'canonical literal residue required')
        result.append((modulus, residue))
    need(len({m for m, _ in result}) == len(result), 'distinct original moduli required')
    return tuple(result)


def totient(value):
    integer(value, 1, 'totient input')
    answer, remaining, divisor = value, value, 2
    while divisor * divisor <= remaining:
        if remaining % divisor == 0:
            answer -= answer // divisor
            while remaining % divisor == 0:
                remaining //= divisor
        divisor += 1
    if remaining > 1:
        answer -= answer // remaining
    return answer


def center_profile(classes, center):
    classes = family(classes)
    need(type(center) is int, 'literal integer centre required')
    return sum((F(1, totient(m)) for m, a in classes if gcd(a - center, m) == 1), F())


def prime_pair_family(prime_values):
    ps = primes(prime_values)
    return family([(p, 0) for p in ps]
                  + [(p * q, 1) for p, q in combinations(ps, 2)])


def prefix_minimum(prime_values, squarefree=False):
    """Exact all-centre minimum, by the two exchange arguments in report 420."""
    ps = primes(prime_values)
    need(type(squarefree) is bool, 'literal squarefree selector required')
    weights = [F(1, p - 1) for p in ps]
    total = sum(weights, F())
    prefix_sum, pair_sum, prefix_product = F(), F(), F(1)
    candidates = []
    for count in range(len(ps) + 1):
        value = (total + prefix_product - 1 - 2 * prefix_sum if squarefree
                 else total - prefix_sum + pair_sum)
        candidates.append((value, count))
        if count < len(ps):
            weight = weights[count]
            pair_sum += weight * prefix_sum
            prefix_sum += weight
            prefix_product *= 1 + weight
    value, count = min(candidates)
    return value, ps[:count]


def attaining_center(prime_values, zero_primes):
    ps = primes(prime_values)
    need(type(zero_primes) in (list, tuple, set, frozenset)
         and all(type(p) is int for p in zero_primes)
         and len(set(zero_primes)) == len(zero_primes)
         and set(zero_primes) <= set(ps), 'distinct zero-prime subset required')
    zero_part = prod(zero_primes)
    one_part = prod(p for p in ps if p not in zero_primes)
    center = 0 if one_part == 1 else zero_part * pow(zero_part, -1, one_part)
    need(all(center % p == (0 if p in zero_primes else 1) for p in ps),
         'CRT centre mismatch')
    return center


def survivor_formula(prime_values):
    ps = primes(prime_values)
    period = prod(ps)
    no_one = prod(p - 2 for p in ps)
    survivors = no_one + sum(no_one // (p - 2) for p in ps)
    unit_count = prod(p - 1 for p in ps)
    unit_survival = prod((F(p - 2, p - 1) for p in ps), start=F(1)) * (
        1 + sum((F(1, p - 2) for p in ps), F()))
    need(unit_survival == F(survivors, unit_count), 'joint survivor identity')
    return {'period': period, 'survivors': survivors,
            'haar_survival': F(survivors, period), 'unit_survival': unit_survival}


def literal_fibre_control(classes):
    classes = family(classes)
    period = lcm(*(m for m, _ in classes))
    need(period <= 2000, 'literal control period exceeds its stated finite bound')
    units = [u for u in range(period) if gcd(u, period) == 1]
    loads = [sum(x % m == a for m, a in classes) for x in range(period)]
    profiles = []
    for center in range(period):
        literal = F(sum(loads[(center + u) % period] for u in units), len(units))
        formula = center_profile(classes, center)
        need(literal == formula, 'literal unit fibre disagrees with gcd formula')
        profiles.append(formula)
    return period, units, loads, profiles


def squarefree_inverse(values, prime_values):
    ps = primes(prime_values)
    need(type(values) in (list, tuple) and len(values) == prod(ps)
         and all(type(v) in (int, F) for v in values), 'complete exact profile required')
    current = list(map(F, values))
    period = len(current)
    for p in ps:
        step = period // p
        current = [sum((current[(x + k * step) % period] for k in range(p)), F())
                   - (p - 1) * current[x] for x in range(period)]
    return current


def self_check():
    ps = odd_primes_through(163)
    classes = prime_pair_family(ps)
    minimum, zero_primes = prefix_minimum(ps)
    need(len(ps) == 37 and len(classes) == 703, 'counterexample label count')
    need(max(m for m, _ in classes) == 25591, 'largest original modulus')
    need(all(2 % m != a for m, a in classes), 'integer two must be uncovered')
    need(minimum == F(11860198143615209, 11827018732969440) > 1,
         'exact strict all-centre minimum')
    need(zero_primes == (3, 5, 7, 11), 'minimizing zero-prime set')
    center = attaining_center(ps, zero_primes)
    need(center_profile(classes, center) == minimum, 'literal attaining centre')
    need(prefix_minimum(ps[:-1])[0] < 1, 'previous initial prime segment')
    squarefree_minimum, squarefree_zeros = prefix_minimum(odd_primes_through(139), True)
    need(squarefree_minimum == F(535926723659837, 532748591575200) > 1
         and squarefree_zeros == (3, 5, 7), 'squarefree-divisor comparison')

    small = []
    for selected in ((3, 5), (3, 5, 7), (3, 5, 7, 11)):
        period, units, loads, profiles = literal_fibre_control(prime_pair_family(selected))
        joint = survivor_formula(selected)
        need(sum(v == 0 for v in loads) == joint['survivors'], 'actual survivor count')
        need(F(sum(loads[x] == 0 for x in units), len(units)) == joint['unit_survival'],
             'actual unit-law survivor count')
        for x in units:
            hits = sum(x % p == 1 for p in selected)
            need(loads[x] == hits * (hits - 1) // 2, 'same-law composite load')
        need(min(profiles) == prefix_minimum(selected)[0], 'literal all-centre minimum')
        need(squarefree_inverse(profiles, selected) == loads, 'squarefree profile inverse')
        small.append({'primes': selected, 'period': period, 'survivors': joint['survivors']})

    first = literal_fibre_control(((9, 0), (27, 0)))
    second = literal_fibre_control(((9, 0), (27, 3)))
    need(first[3] == second[3], 'higher-phase profiles must coincide')
    need(sum(v > 0 for v in first[2]) == 3 and sum(v > 0 for v in second[2]) == 4,
         'higher-phase union sizes')
    literal_fibre_control(((9, 0), (27, 3), (5, 2), (15, 4)))

    invalid = [lambda: primes((True, 5)), lambda: primes((3, 3)),
               lambda: primes((3, 9)), lambda: family(((3, 0), (3, 1))),
               lambda: family(((4, 0),)), lambda: family(((3, True),)),
               lambda: family(((3, 3),)), lambda: center_profile(classes, 0.0),
               lambda: squarefree_inverse([0.0] * 15, (3, 5))]
    rejected = 0
    for operation in invalid:
        try:
            operation()
        except ValueError:
            rejected += 1
    need(rejected == len(invalid), 'malformed input accepted')
    return {'scope': 'actual noncovering family; analytic exchange proof gives all centres',
            'primes': ps, 'original_classes': len(classes), 'largest_modulus': 25591,
            'uncovered_integer': 2, 'minimum_profile': minimum,
            'margin_over_one': minimum - 1, 'attaining_center': center,
            'joint_survivors': survivor_formula(ps), 'small_CRT_controls': small,
            'same_profile_union_counts_mod_27': (3, 4), 'rejected_inputs': rejected}


def jsonable(value):
    if type(value) is F:
        return str(value)
    if type(value) is dict:
        return {key: jsonable(item) for key, item in value.items()}
    if type(value) in (list, tuple):
        return [jsonable(item) for item in value]
    return value


if __name__ == '__main__':
    print(json.dumps(jsonable(self_check()), indent=2))
