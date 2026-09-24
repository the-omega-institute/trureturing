#!/usr/bin/env python3
"""Exact AP witnesses and root-of-unity polynomial moment diagnostics.

The angular inequalities in the accompanying proof are ordinary mathematics;
this program checks their rational consequences and polynomial identities.
It uses no floating-point eigenvalue or trigonometric evaluation.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt, lcm


def require(test, message):
    if not test:
        raise ValueError(message)


def prime(q):
    return q >= 2 and all(q % p for p in range(2, isqrt(q) + 1))


def family(q, residues):
    require(prime(q) and q >= 7, 'Prime distinct from the two old primes')
    height = len(residues) - 1
    rows = []
    for e, r in enumerate(residues):
        g = 3**e * 5**(height-e)
        residue = g * ((r * pow(g, -1, q)) % q)
        t = ((r * pow(g, -1, q) - 1) * pow(15, -1, q)) % q
        witness = g * (1 + 15*t)
        rows.append((residue, q*g, witness))
    require(len({d for _, d, _ in rows}) == len(rows), 'Distinct original moduli')
    require(all(d > 1 and d % 2 for _, d, _ in rows), 'Nonunit odd original moduli')
    private_checks = 0
    for i, (_, _, witness) in enumerate(rows):
        for j, (a, d, _) in enumerate(rows):
            require((witness % d == a) == (i == j), 'Original private point')
            private_checks += 1
    require(all(a != 0 for a, _, _ in rows), 'Integer zero is actually uncovered')
    old_period = 15**height
    require(lcm(*(d for _, d, _ in rows)) == old_period*q, 'Complete period')
    multiplicity = []
    membership_checks = 0
    for z in range(q):
        # Use the physical q-coordinate, not the affine parameter of N=D*t.
        n = old_period * ((z * pow(old_period, -1, q)) % q)
        count = 0
        for i, (a, d, _) in enumerate(rows):
            hit = n % d == a
            require(hit == (z == residues[i]), 'Actual original/prefix pullback')
            membership_checks += 1
            count += hit
        multiplicity.append(count)
    return rows, old_period, multiplicity, private_checks, membership_checks


def moment_polynomial(g, frequencies, centre=0):
    """q E[g |sum_k zeta^(k*(z-centre))|^2], in Z[zeta]/(zeta^q-1)."""
    q = len(g)
    polynomial = [0]*q
    for z, value in enumerate(g):
        for k in frequencies:
            for ell in frequencies:
                polynomial[((k-ell)*(z-centre)) % q] += value
    return polynomial


def cyclotomic_prime_reduce(coefficients):
    # 1 + z + ... + z^(q-1) = 0 at a primitive prime-order root.
    leading = coefficients[-1]
    return [a-leading for a in coefficients[:-1]]


def strict_three_character_example():
    q = 13
    residues = [3 + e//2 for e in range(20)]
    rows, old, multiplicity, private, membership = family(q, residues)
    require(multiplicity == [0]*3 + [2]*10, 'Three missing physical q residues')
    g = [m-1 for m in multiplicity]
    mean = F(sum(g), q)
    require(mean == F(7, 13) > F(6, 13), 'All single-character triangle bounds pass')
    # For all twelve nonzero k, sum_z g(z) zeta^(-kz) equals
    # -2*(1+zeta^(-k)+zeta^(-2k)); its absolute value is at most 6.
    for k in range(1, q):
        actual = [0]*q
        expected = [0]*q
        for z, value in enumerate(g):
            actual[(-k*z) % q] += value
        for z in range(3):
            expected[(-k*z) % q] -= 2
        require(cyclotomic_prime_reduce(actual) == cyclotomic_prime_reduce(expected),
                'Every nonzero Fourier coefficient from actual multiplicity')
    actual = moment_polynomial(g, (0, 1, 2), centre=1)
    expected = [0]*q
    expected[0] = 9
    expected[1] = expected[-1] = -8
    expected[2] = expected[-2] = -4
    require(cyclotomic_prime_reduce(actual) == cyclotomic_prime_reduce(expected),
            'Exact three-character quadratic polynomial')
    # The proof uses 2*pi/13 < pi/6 and 4*pi/13 < pi/3.
    require(F(2, 13) < F(1, 6) and F(4, 13) < F(1, 3), 'Angle comparison')
    require(F(3, 4)**2 < F(3, 4), 'sqrt(3)/2 > 3/4')
    bound = (9 - 16*F(3, 4) - 8*F(1, 2))/13
    require(bound == -F(7, 13), 'Strict negative quadratic upper bound')
    require(343 - 14*25 - 7*16 - 2*25*4 == -319, 'Strict determinant upper bound')
    require(old % q == 11, 'Actual affine scale modulo 13')
    require([(k*old) % q for k in (0, 1, 2)] == [0, 11, 9], 'Transported frequencies')
    require(-bound/9 == F(7, 117) < F(3, 13), 'Certified versus exact relative hole')
    return private, membership


def rank_boundary(q):
    residues = [1 + e//2 for e in range(2*(q-1))]
    rows, old, multiplicity, private, membership = family(q, residues)
    require(multiplicity == [0]+[2]*(q-1), 'One missing residue and double multiplicity')
    g = [m-1 for m in multiplicity]
    require(F(sum(g), q) == 1-F(2, q), 'Actual diagonal')
    for k in range(1, q):
        coefficient = [0]*q
        for z, value in enumerate(g):
            coefficient[(-k*z) % q] += value
        require(cyclotomic_prime_reduce(coefficient) == [-2]+[0]*(q-2),
                'All off-diagonal coefficients are exactly -2/q')
    for size in range(1, q+1):
        eigenvalue = 1-F(2*size, q)
        require((eigenvalue > 0) == (2*size < q), 'Exact rank threshold')
    require(1-F(2*(q//2), q) > 0 and 1-F(2*(q//2+1), q) < 0,
            'First detecting character count')
    return private, membership


def maximal_conductor_example():
    moduli, frequencies, period = (45, 63, 175), (490, 575, 513), 1575
    require(all(period//gcd(period, k) == d for k, d in zip(frequencies, moduli)),
            'Each original maximal conductor')
    for i, j in combinations(range(3), 2):
        conductor = period//gcd(period, frequencies[i]-frequencies[j])
        require(conductor == lcm(moduli[i], moduli[j]), 'Full conductor of each ratio')
        require(all(d % conductor for d in moduli), 'No original label contributes to cross entry')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--rank-primes', type=int, nargs='+', default=[7, 11, 17])
    args = parser.parse_args()
    counts = [strict_three_character_example()]
    counts.extend(rank_boundary(q) for q in args.rank_primes)
    maximal_conductor_example()
    print('PASS', sum(p for p, _ in counts), 'original private checks;',
          sum(m for _, m in counts), 'literal fibre checks;',
          'exact Fourier polynomials and rank thresholds; no numerical eigensolver')


if __name__ == '__main__':
    main()
