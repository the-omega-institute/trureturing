#!/usr/bin/env python3
"""Exact full-density constants for books with common prime spine {3,5}.

The half-threshold kernels, original-label convex comparison, and full-law
Haar transport are ordinary proof premises in Chapter 37. This program
checks the finite rational fees, complete geometric moments, analytic tail
constant, density factors, and the actual zero-fibre counterexample.
Python 3.10+; --output FILE works independently of the current directory.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import lcm, prod
from pathlib import Path
import sys


PARAMETERS = ((3, Q(2)), (5, Q(4, 3)), (7, Q(12, 5)))


def mass(n, prime, cap):
    """Mass of N=1+K, with Pr(K>=e)=cap/prime**e for e>=1."""
    return 1 - cap / prime if n == 1 else cap * (prime - 1) / prime**n


def moments(prime, cap):
    """Tail-sum identities, including every exponent, for E N, N^2, N^3."""
    ratio = Q(1, prime)
    s0 = ratio / (1 - ratio)
    s1 = ratio / (1 - ratio)**2
    s2 = ratio * (1 + ratio) / (1 - ratio)**3
    return (1 + cap * s0, 1 + cap * (2 * s1 + s0),
            1 + cap * (3 * s2 + 3 * s1 + s0))


def fee(prime, parameters):
    """Exact E(Z-prime/2)_+ via its finite complementary lower tail."""
    cutoff = (prime - 1) // 2
    correction = Q(0)
    terms = 0
    for indices in product(range(1, cutoff + 1), repeat=len(parameters)):
        value = prod(indices)
        if value <= cutoff:
            weight = prod(mass(n, p, c) for n, (p, c)
                          in zip(indices, parameters))
            correction += (Q(prime, 2) - value) * weight
            terms += 1
    mean = prod(moments(p, c)[0] for p, c in parameters)
    return 2 * (mean - Q(prime, 2) + correction) / (prime - 2), terms


def zero_fibre():
    root_classes = ((3, 1), (5, 1))
    page_classes = ((7, 0), (21, 15), (63, 9), (189, 108),
                    (35, 25), (105, 75), (315, 90))
    full_support_class = (1155, 2)
    classes = root_classes + page_classes + (full_support_class,)
    assert len({m for m, _ in classes}) == len(classes)
    assert all(m > 1 and m % 2 == 1 for m, _ in classes)
    assert all(2 % m != a for m, a in root_classes + page_classes)
    assert 2 % full_support_class[0] == full_support_class[1]
    forbidden_residues = []
    for m, a in page_classes:
        cofactor = m // 7
        assert a % cofactor == 0 and 135 % cofactor == 0
        forbidden_residues.append(a % 7)
    assert forbidden_residues == list(range(7))
    period = lcm(*(m for m, _ in classes))
    cylinder = [n for n in range(period) if n % 27 == n % 5 == 0]
    assert all(all(n % m != a for m, a in root_classes) for n in cylinder)
    assert all(any(n % m == a for m, a in page_classes) for n in cylinder)
    uncovered = sum(all(n % m != a for m, a in classes) for n in range(period))
    assert uncovered > 0
    return dict(classes=[dict(modulus=m, residue=a) for m, a in classes],
                period=period, zero_fibre_cylinder_size=len(cylinder),
                forbidden_seven_residues=forbidden_residues,
                uncovered_count=uncovered, full_support_nonredundancy_witness=2)


def main():
    if sys.version_info < (3, 10) or not __debug__:
        raise SystemExit('Python 3.10+ with assertions enabled is required')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    auxiliary = []
    for p, c in PARAMETERS:
        # The mass at 1 and the complete geometric remainder sum to one.
        assert 0 < c / p < 1
        assert mass(1, p, c) + c * (p - 1) / p**2 / (1 - Q(1, p)) == 1
        auxiliary.append(dict(prime_proxy=p, tail_cap=str(c),
                              moments=[str(x) for x in moments(p, c)]))
    moment_rows = [moments(p, c) for p, c in PARAMETERS]
    assert moment_rows == [(Q(2), Q(5), Q(31, 2)),
                           (Q(4, 3), Q(13, 6), Q(107, 24)),
                           (Q(7, 5), Q(7, 3), Q(14, 3))]
    rows = []
    ceilings = ((7, 174), (11, 148), (13, 92), (17, 42), (19, 30), (23, 16))
    for p, numerator in ceilings:
        parameters = PARAMETERS[:2] if p == 7 else PARAMETERS
        actual, terms = fee(p, parameters)
        assert 0 < actual < Q(numerator, 1000)
        rows.append(dict(prime=p, factors=len(parameters), exact_fee=str(actual),
                         strict_upper=str(Q(numerator, 1000)),
                         finite_complement_terms=terms))
    assert Q(rows[0]['exact_fee']) == Q(8804, 50625)
    assert Q(rows[1]['exact_fee']) == Q(253372547128, 1722980109375)
    finite_ceiling = sum(Q(row['strict_upper']) for row in rows)
    assert finite_ceiling == Q(251, 500)
    y3 = (prod(m[2] for m in moment_rows) - 3 * prod(m[1] for m in moment_rows)
          + 3 * prod(m[0] for m in moment_rows) - 1)
    assert y3 == Q(92467, 360)
    # (2u-3t)^2(u+3t) = 4u^3 - 27t^2(u-t) >= 0 for u>=t>0.
    cubic_factor = Q(32, 27) * y3
    odd_tail = Q(1, 27**3) + Q(1, 4 * 27**2)
    tail = cubic_factor * odd_tail
    assert tail == Q(2866477, 23914845) < Q(3, 25)
    private_fee = finite_ceiling + Q(3, 25)
    mixed_spine_fee = Q(2) * Q(4, 3) * Q(1, 2) * Q(1, 4)
    assert mixed_spine_fee == Q(1, 3)
    survivor = 1 - mixed_spine_fee - private_fee
    spine_density_cap = Q(2) * Q(4, 3)
    prefactor = survivor / spine_density_cap
    page_factor = Q(7 - 2, 2 * (7 - 1)) * Q(11 - 2, 2 * (11 - 1))
    assert survivor == Q(67, 1500) and prefactor == Q(67, 4000)
    assert page_factor == Q(3, 16)
    result = dict(
        schema='spine-book-full-density-v2',
        scope='One shared spine {3,5}; disjoint nonempty private pages of at most two primes; arbitrary original finite heights and residues.',
        auxiliary_laws=auxiliary, early_fee_rows=rows,
        finite_exact_fee_sum=str(sum(Q(r['exact_fee']) for r in rows)),
        strict_finite_fee_upper=str(finite_ceiling),
        third_moment_product_minus_one=str(y3),
        cubic_tail_factor=str(cubic_factor),
        odd_integer_tail_upper=str(odd_tail), prime_tail_upper=str(tail),
        strict_total_private_fee_upper=str(private_fee),
        mixed_spine_fee_upper=str(mixed_spine_fee),
        strict_normalized_survivor_lower=str(survivor),
        spine_joint_density_cap=str(spine_density_cap),
        full_haar_density_bound=dict(prefactor=str(prefactor),
                                    per_page_factor=str(page_factor),
                                    formula='prefactor * per_page_factor^N',
                                    N='number of nonempty private pages'),
        zero_fibre_counterexample=zero_fibre(),
        verification='Exact rational fee and moment calculations with a finite arithmetic counterexample. Conditional comparison, kernel construction and arbitrary-height reduction are ordinary proof obligations; no new Lean verification.')
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: six exact fees, full geometric moments, cubic tail, density and zero fibre.')
    print('Full Haar density >', prefactor, '* (', page_factor, ')^N')


if __name__ == '__main__':
    main()
