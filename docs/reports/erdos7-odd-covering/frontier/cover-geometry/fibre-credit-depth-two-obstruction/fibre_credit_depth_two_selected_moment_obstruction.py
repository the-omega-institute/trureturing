#!/usr/bin/env python3
"""Exact selected-field moment obstructions; no actual covering is asserted."""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def cube_floor(value, scale=1000):
    low, high = 0, 1
    bound = value.numerator * scale**3
    while high**3 * value.denominator <= bound:
        high *= 2
    while high - low > 1:
        mid = (low + high) // 2
        if mid**3 * value.denominator <= bound:
            low = mid
        else:
            high = mid
    need(low**3 * value.denominator <= bound < (low + 1)**3 * value.denominator,
         'exact downward cubic rounding')
    return F(low, scale)


def instance(primes, probability, levels):
    dimension = len(primes)
    supports = tuple(J for size in range(1, dimension + 1)
                     for J in combinations(range(dimension), size))
    need(sum(probability) == 1 and min(probability) > 0, 'one probability law')
    records, fields, slots = [], {}, 0
    for J in supports:
        symbols = levels[J]
        need(len(symbols) == len(probability), 'all fields have the same source')
        alpha = F(0)
        for exponents in product((1, 2), repeat=len(J)):
            alpha += prod((F(primes[j] - 1, primes[j]**e)
                           for j, e in zip(J, exponents)), start=F(1))
            slots += 1
        need(alpha == prod((1 - F(1, primes[j]**2) for j in J), start=F(1)),
             'all finite exponent slots and constant-one padding')
        field = tuple(1 + alpha * (value - 1) for value in symbols)
        need(all(1 <= c <= value for c, value in zip(field, symbols)),
             'padded fields retain the unit floor')
        moments = []
        for values in (symbols, field):
            moment = tuple(sum((p * value**k for p, value in zip(probability, values)), F(0))
                           for k in (1, 2, 3))
            need(moment[0] < 18 and moment[1] < 320 and moment[2] <= 5680,
                 'all three moments on the same source')
            moments.append(list(map(str, moment)))
        fields[J] = field
        records.append(dict(support=list(J), geometric_weight=str(alpha),
                            symbols=list(map(str, symbols)),
                            symbol_moments=moments[0], field_moments=moments[1]))
    need(slots == 3**dimension - 1, 'complete finite support/exponent inventory')
    rows = []
    for atom, probability_atom in enumerate(probability):
        u = tuple(F(prime - 1) - fields[(j,)][atom] for j, prime in enumerate(primes))
        need(min(u) > 0, 'strictly positive unary factors')
        P = prod(u, start=F(1))
        fee = sum((fields[J][atom] * prod((u[j] for j in range(dimension) if j not in J),
                                         start=F(1))
                   for J in supports if len(J) >= 2), F(0))
        need(fee > P, 'zero clipped response at every atom')
        rows.append(dict(atom=atom, probability=str(probability_atom),
                         unary_factors=list(map(str, u)), product=str(P), fee=str(fee),
                         fee_over_product=str(fee / P), W='0'))
    return dict(primes=list(primes), probability=list(map(str, probability)), height=2,
                support_count=len(supports), exponent_slots=slots, fields=records, rows=rows,
                minimum_fee_ratio=str(min(F(row['fee_over_product']) for row in rows)),
                expected_W='0')


def calculate():
    G2, G3 = F(2607189975, 7283281), F(906617738995, 159166336)
    need(320 < G2 and 5680 < G3 and 5680**2 < 320**3 and 5680 < 18**3,
         'the obstruction meets strictly stronger ceilings than the source bounds')
    primes = (29, 31, 37, 41, 43)
    probability = tuple(F(n, 100000) for n in (34625, 28046, 15971, 11494, 9864))
    supports = tuple(J for size in range(1, 6) for J in combinations(range(5), size))
    levels = {}
    for J in supports:
        active = cube_floor(1 + F(5679) / sum(probability[i] for i in J))
        levels[J] = tuple(active if i in J else F(1) for i in range(5))
    five = instance(primes, probability, levels)
    need(F(five['minimum_fee_ratio']) ==
         F(122185235033456772894749, 121954252494589465783560), 'five-atom exact margin')

    seven_primes = (29, 31, 37, 41, 43, 47, 53)
    seven_levels = {J: (F(17),) for size in range(1, 8)
                    for J in combinations(range(7), size)}
    seven = instance(seven_primes, (F(1),), seven_levels)
    u = tuple(F(value) for value in seven['rows'][0]['unary_factors'])
    t = tuple(1 - F(1, p**2) for p in seven_primes)
    P = prod(u, start=F(1))
    generating_fee = (prod((v + 1 for v in u), start=F(1))
                      + 16 * prod((v + w for v, w in zip(u, t)), start=F(1))
                      - 17 * P - sum(((1 + 16 * w) * P / v for v, w in zip(u, t)), F(0)))
    need(generating_fee == F(seven['rows'][0]['fee']), 'independent generating-product fee')
    need(F(seven['minimum_fee_ratio']) ==
         F(185899170306847704706627330172, 179895021493724830240504479897),
         'seven-axis exact margin')
    seven_records = seven.pop('fields')
    seven['maximum_field_moments'] = [str(max(F(row['field_moments'][k])
                                               for row in seven_records)) for k in range(3)]
    atoms = (1, 2, 3, 4, 5, 6, 8, 12)
    weights = tuple(map(F, ('581/6966', '3031/6966', '146/1053', '425/2106',
                           '10/1443', '45/481', '1/37', '1/74')))
    need(sum(weights) == 1, 'inherited increasing-convex comparator is a probability')
    raw_fourth = sum(p * x**4 for p, x in zip(weights, atoms))
    multiplier = prod((1 + F(15, p - 1) for p in (11, 13, 17, 19, 23)), start=F(1))
    G4 = raw_fourth * multiplier / F(1243487, 13077504)
    formal_fourths = [sum(p * F(value)**4 for p, value in zip(probability, row['symbols']))
                      for row in five['fields']]
    need(G4 == F(3350218780205, 16165331) < max(formal_fourths),
         'inherited fourth moment rejects this particular five-atom table')
    divisor_count = 3 * 2**7
    need(divisor_count == 384 and 17**3 < G3 < divisor_count**3,
         'actual singleton source violates the complete-query ceiling')
    return dict(scope='Formal selected-query fields on one law with finite height-two padding. '
                      'No actual numerical-divisor incidence, full query closure, congruence realization '
                      'or covering is asserted. Ordinary exact verification, not Lean.',
                square_ceiling=str(G2), cubic_ceiling=str(G3),
                five_atom=five, seven_axis_integer_comparison=seven,
                fourth_moment_boundary=dict(inherited_raw_fourth=str(raw_fourth),
                    pure_prime_multiplier=str(multiplier), old_source_fourth_upper=str(G4),
                    largest_formal_query_fourth=str(max(formal_fourths)),
                    scope='This particular table fails the stronger fourth-moment condition. '
                          'No positivity claim for the whole strengthened relaxation.'),
                actual_singleton_full_query_load=divisor_count)


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate()
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
             'retained result agrees with the exact selected-field obstruction')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
