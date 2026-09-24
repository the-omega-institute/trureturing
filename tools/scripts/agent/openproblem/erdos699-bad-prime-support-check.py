#!/usr/bin/env python3
"""Exact self-checks for the Erdős 699 bad-prime-support continuation.

The external 83-j classification and the superelliptic height theorem are
NOT proved by this program. The data realizes 83 distinct admissible j's;
combined with the known classification upper bound this is exhaustive.
Usage: python erdos699-bad-prime-support-check.py --symbolic
"""
from __future__ import annotations
import argparse
import ast
from collections import Counter
from fractions import Fraction as Q
from math import comb, gcd, isqrt, prod
from pathlib import Path
import json


def valuation(n: int, p: int) -> int:
    if n == 0 or p < 2:
        raise ValueError('requires nonzero integer and p>=2')
    n, result = abs(n), 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def rational_v2(x: Q) -> int:
    return valuation(x.numerator, 2)-valuation(x.denominator, 2)


def smooth23(n: int) -> bool:
    if not n:
        return False
    n = abs(n)
    for p in (2, 3):
        while n % p == 0:
            n //= p
    return n == 1


def read_representatives(path: Path) -> list[tuple[int, int]]:
    result = []
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        row = ast.literal_eval(line)
        if not (isinstance(row, tuple) and len(row) == 2
                and all(isinstance(x, int) for x in row)):
            raise ValueError('invalid invariant-pair data')
        result.append(row)
    return result


def curve_certificate(rows: list[tuple[int, int]]) -> dict:
    values = []
    for u, v in rows:
        raw = u**3-v*v
        assert smooth23(raw)
        alpha, beta = -27*u, -54*v
        disc = -16*(4*alpha**3+27*beta**2)
        assert disc == 64*3**9*raw and smooth23(disc)
        c4, c6 = -48*alpha, -864*beta
        assert c4 == 6**4*u and c6 == 6**6*v
        j = Q(c4**3, disc)
        assert j == Q(1728*u**3, raw)
        values.append(j)
    assert len(values) == len(set(values)) == 83
    positive = sorted(j for j in values if j > 1728)
    assert len(positive) == 32
    orders = Counter(rational_v2(j) for j in positive)
    assert min(orders) == -9 and Q(1193859, 512) in positive
    assert min(rational_v2(j) for j in values if j) == -21
    assert rational_v2(Q(-1159088625, 2097152)) == -21
    # The positive-j restriction is essential for the sharper -9 bound.
    return {'realized_distinct_j': len(values), 'j_above_1728': len(positive),
            'positive_j_v2_counts': dict(sorted(orders.items())),
            'positive_j_values': [str(x) for x in positive],
            'classification_upper_bound_external': 83,
            'classification_reproved': False}


def floor_cuberoot(n: int) -> int:
    low, high = 0, 1 << ((n.bit_length()+2)//3)
    while low < high:
        m = (low+high+1)//2
        if m**3 <= n:
            low = m
        else:
            high = m-1
    return low


def small_rows_certificate() -> dict:
    parameters = []
    for c in (1, 3):
        for a in range(2, 9):
            maximum_n = 1+floor_cuberoot((27*2**(4*a)-1)//784)
            A = c*2**a
            for d in range(1, maximum_n//A+1):
                assert 784*(A*d-1)**3 < 27*2**(4*a)
                parameters.append((c, a, d, A*d))
    assert parameters == [(1,5,1,32),(1,6,1,64),(1,7,1,128),
                          (1,8,1,256),(1,8,2,512)]
    witnesses = {32:(31,),64:(31,7),128:(127,),256:(127,5),512:(73,17)}
    def lucas_divides(n: int, j: int, p: int) -> bool:
        while n or j:
            if j % p > n % p:
                return True
            n //= p
            j //= p
        return False
    total = 0
    for n, primes in witnesses.items():
        for p in primes:
            assert all(p % q for q in range(2, isqrt(p)+1))
            assert comb(n,3) % p == 0
        for j in range(4, n//2+1):
            total += 1
            assert any(lucas_divides(n,j,p) for p in primes)
            assert any(comb(n,j) % p == 0 for p in primes)
            g = gcd(comb(n,3), comb(n,j))
            assert g // (g & -g) > 1
    assert total == 481
    return {'small_parameter_tuples': parameters, 'all_small_row_pairs': total,
            'small_row_prime_witnesses': witnesses}


def arithmetic_audit(nmax: int) -> dict:
    pairs = smooth = 0
    for n in range(8, nmax+1):
        for j in range(4,n//2+1):
            pairs += 1
            d = gcd(n,j)
            A, B = n//d, j//d
            ell = Q(3*B*(A-B), n-1)
            k = Q(B*(A-B)*(A-2*B), (n-1)*(n-2))
            W = ell**3-27*k*k
            assert W > 0
            J = Q(1728)*ell**3/W
            assert J == Q(1728*j*(n-j)*(n-2)**2,
                          n*n*(j-1)*(n-j-1))
            assert (J > 1728) == (2*j < n)
            c = 3 if A % 3 == 0 else 1
            h = A//c
            if h < 4 or h & (h-1):
                continue
            a = h.bit_length()-1
            smooth += 1
            Delta = Q(4)*W/(c**4*A*A)
            assert W == c**6*2**(2*a-2)*Delta
            assert rational_v2(J) == 8-2*a-rational_v2(Delta)
    # Remove a deliberately nonminimal odd fourth/sixth scale.
    normalization_controls = 0
    for ell, k, support in ((9,5,(2,3)), (5,1,(2,7)), (7,1,(2,79))):
        w = ell**3-27*k*k
        for scale in (1,5,7,11,25,35,55,121):
            ee, kk = ell*scale**4, k*scale**6
            ww = ee**3-27*kk*kk
            assert ww == w*scale**12
            assert rational_v2(Q(1728*ee**3,ww)) == rational_v2(Q(1728*ell**3,w))
            assert ee % scale**4 == kk % scale**6 == 0
            assert (ee//scale**4,kk//scale**6)==(ell,k)
            extracted = prod(p**min(valuation(ee,p)//4, valuation(kk,p)//6)
                             for p in (5,7,11))
            assert extracted == scale
            remainder = w
            for p in support:
                while remainder % p == 0:
                    remainder //= p
            assert remainder == 1
            normalization_controls += 1
    assert not smooth23((9*5**4)**3-27*(5*5**6)**2)
    assert smooth23(9**3-27*5**2)
    # Sextic normalization, including arbitrary large multiplicities.
    flattening_controls = 0
    for T in ((2,3),(2,3,5),(2,3,7,11)):
        Qs = prod(T)
        for a in range(2,40):
            powers = [2*a-2+((a+3*i)%17) for i,_ in enumerate(T)]
            W = prod(p**e for p,e in zip(T,powers))
            D = prod(p**(e%6) for p,e in zip(T,powers))
            V = prod(p**(e//6) for p,e in zip(T,powers))
            assert W == D*V**6 and D <= Qs**5
            assert valuation(V,2) >= (a-1)//3
            # numerator chosen odd, so its 2-adic denominator is exact.
            assert valuation(Q(3,V**3).denominator,2) == 3*valuation(V,2)
            flattening_controls += 1
    assert 14*3**3*2**3 == 3024
    assert 3*3**2*2**2 == 108
    assert 8*3**2*2**3 == 576
    assert 108+5*576 == 2988
    assert 3024+2988 == 6012
    return {'actual_rational_binomial_pairs':pairs,'smooth_denominator_pairs':smooth,
            'odd_scale_controls':normalization_controls,
            'sextic_flattening_controls':flattening_controls,
            'external_height_bound_reproved':False}


def symbolic_audit() -> dict:
    try:
        import sympy as s
    except ImportError as exc:
        raise SystemExit('--symbolic requires SymPy') from exc
    ell,k,c,A,z,B,g = s.symbols('ell k c A z B g', nonzero=True)
    F=((A*z-B)**3-ell*(A*z-B)-2*k)/(c*A*A)
    assert s.factor(s.discriminant(F,z)-(4*ell**3-108*k*k)/(c**4*A*A))==0
    assert s.expand(-16*(4*(-ell)**3+27*(2*k)**2)-64*(ell**3-27*k*k))==0
    assert s.expand((ell*g**4)**3-27*(k*g**6)**2-g**12*(ell**3-27*k*k))==0
    u,v = s.symbols('u v')
    assert s.expand(-16*(4*(-27*u)**3+27*(-54*v)**2)-64*3**9*(u**3-v*v))==0
    return {'symbolic_frey_discriminant':True,'symbolic_scaling':True,
            'symbolic_realization_models':True}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nmax',type=int,default=200)
    parser.add_argument('--data',type=Path,default=Path(__file__).with_name('erdos699-good-reduction-23-data.txt'))
    parser.add_argument('--symbolic',action='store_true')
    args=parser.parse_args()
    if args.nmax<8:
        parser.error('--nmax must be at least8')
    result={'status':'passed','whole_solution':False,'independent_review':False}
    result.update(curve_certificate(read_representatives(args.data)))
    result.update(small_rows_certificate())
    result.update(arithmetic_audit(args.nmax))
    if args.symbolic:
        result.update(symbolic_audit())
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
