#!/usr/bin/env python3
"""Exact self-audit of the Erdős 699 coupled midpoint continuation.

The periodic certificate covers ALL exponents a>=10 for the stated finite
quotient range. The six small rows close a<10. Neither result covers all k.
The explicit elliptic height theorem is an external input, not tested here.
Only optional --symbolic needs SymPy. No optimization or probable primes.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, gcd, isqrt

PERIOD = 27720
PRIMES = (3,5,7,11,13,17,19,23,29,31,37,41,43,61,67,71,73,89,
          109,113,127,151,181,199,211,241,281,331,337,353,397,421,
          433,463,617,631,661,683,881,991)


def is_prime(p: int) -> bool:
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))


def order_two(p: int) -> int:
    assert p > 2 and is_prime(p)
    x = 1
    for a in range(1, p):
        x = 2*x % p
        if x == 1:
            return a
    raise AssertionError("multiplicative order not found")


def equation(A: int, d: int, k: int, kap: int) -> int:
    return kap*A*A + 6*k*A*d - 4*(2*k*d*d+kap)**3 - 4*k


@lru_cache(None)
def square_roots(p: int) -> dict[int, tuple[int, ...]]:
    roots: dict[int, list[int]] = {}
    for x in range(p):
        roots.setdefault(x*x % p, []).append(x)
    return {q: tuple(xs) for q,xs in roots.items()}


def allowed_exponents(k: int, kap: int, p: int) -> tuple[int, set[int]]:
    """Solve the quadratic in A EXACTLY for all d modulo a checked prime."""
    order = order_two(p)
    values: set[int] = set()
    inv = pow(kap, -1, p) if kap % p else None
    roots = square_roots(p)
    for d in range(p):
        z = (2*k*d*d+kap) % p
        rhs = (4*z**3+4*k) % p
        if inv is None:
            linear = 6*k*d % p
            if linear:
                values.add(rhs*pow(linear, -1, p) % p)
            elif rhs == 0:
                return order, set(range(order))
        else:
            disc = (9*k*k*d*d+kap*rhs) % p
            for r in roots.get(disc, ()):
                A = (-3*k*d+r)*inv % p
                assert equation(A,d,k,kap) % p == 0
                values.add(A)
    return order, {a for a in range(order) if pow(2,a,p) in values}


def direct_exponents(k: int, kap: int, p: int) -> tuple[int, set[int]]:
    """Independent direct (a,d) enumeration, used for named certificates."""
    order = order_two(p)
    allowed = {a for a in range(order)
               if any(equation(pow(2,a,p), d,k,kap) % p == 0
                      for d in range(p))}
    return order, allowed


def kap_cap(k: int, c: int = 1) -> int:
    return (729*k**3-1)//(8*c**8*49**2)


def valuation_binomial(n: int, j: int, p: int) -> int:
    answer = 0
    power = p
    while power <= n:
        answer += n//power-j//power-(n-j)//power
        power *= p
    return answer


def low_rows() -> dict:
    """Every possible a<10 row after the cubic discriminant bound."""
    parameters = 0
    possible_rows: set[int] = set()
    for a in range(2, 10):
        for c in (1,3):
            A = c*(1 << a)
            # The proved discriminant bound is monotone in d. These are all d.
            d = 1
            while 784*(A*d-1)**3 < 27*(1 << (4*a)):
                possible_rows.add(A*d)
                for B in range(1, A//2):
                    if gcd(A,B)==1 and B*d>3 and not(c==3 and d%3==0):
                        parameters += 1
                d += 1
    assert possible_rows == {32,64,128,256,512,1024}
    result = []
    count = 0
    for n in sorted(possible_rows):
        cn3 = comb(n,3)
        primes = [p for p in range(3,n+1,2) if is_prime(p) and cn3%p==0]
        survived = list(range(4, n//2+1))
        trajectory = []
        for p in primes:
            survived = [j for j in survived if valuation_binomial(n,j,p)==0]
            trajectory.append([p,len(survived)])
        assert not survived
        for j in range(4,n//2+1):
            g = gcd(cn3,comb(n,j))
            assert g//(g & -g) > 1
            count += 1
        result.append({'n':n,'prime_survivor_counts':trajectory})
    assert parameters == 428 and count == 990
    return {'reduced_parameters':parameters, 'full_row_pairs':count, 'rows':result}


def periodic_certificate() -> dict:
    assert all(PERIOD % order_two(p)==0 for p in PRIMES)
    full = (1 << PERIOD)-1
    rows = []
    totals = [0,0,0]
    for k in range(1,32,2):
        if k == 27:
            # Prior cube-unit argument excludes k=27, independently of this sieve.
            continue
        cap = kap_cap(k)
        initial = two_pass = killed = 0
        used: set[int] = set()
        for kap in range(1,cap+1,2):
            initial += 1
            # a>=10 implies [(2*k*d^2+kap)^3+k] ==0 modulo512.
            if not any(((2*k*d*d+kap)**3+k)%512==0 for d in range(512)):
                continue
            two_pass += 1
            mask = full
            for p in PRIMES:
                order, allowed = allowed_exponents(k,kap,p)
                block = sum(1 << a for a in allowed)
                repetitions = full//((1 << order)-1)
                new_mask = mask & (block*repetitions)
                if new_mask != mask:
                    used.add(p)
                mask = new_mask
                if mask == 0:
                    killed += 1
                    break
            assert mask == 0, ('UNRESOLVED',k,kap,mask.bit_count())
        assert killed == two_pass
        totals = [u+v for u,v in zip(totals,(initial,two_pass,killed))]
        rows.append({'k':k,'kap_cap':cap,'kap_count':initial,
                     'after_mod512':two_pass,'excluded_periodically':killed,
                     'effective_primes':sorted(used)})
    assert totals == [2110,365,365]
    assert all(kap_cap(k,3)<3 for k in range(1,32,2))
    return {'period':PERIOD,'prime_count':len(PRIMES),
            'kap_total':totals[0],'after_mod512':totals[1],
            'periodically_excluded':totals[2],'rows':rows,
            'scope':'all a>=10 and all d for the stated bounded k sector; k=27 uses the prior cube exclusion'}


def named_controls() -> dict:
    primes = (5,7,11,31,61)
    allowed = {}
    for p in primes:
        direct = direct_exponents(5,3,p)
        assert direct == allowed_exponents(5,3,p)
        allowed[p] = direct
    survivors = [a for a in range(60)
                 if all(a%o in residues for p,(o,residues) in allowed.items() if p!=61)]
    assert survivors == [2,22,32,52]
    assert not [a for a in survivors if a%60 in allowed[61][1]]
    # Non-vacuous compatible control. It fails the original condition j>3.
    assert equation(8,1,1,1)==0
    for p in PRIMES:
        o, residues = allowed_exponents(1,1,p)
        assert 3%o in residues
    # Prior relaxed witness has an integer midpoint/curve point but non-smooth A.
    A,B,d,k = 76672,26775,1,5255
    kap = 1051
    assert equation(A,d,k,kap)==0
    Z = A//2-B
    X,Y = 4*kap*Z, 4*kap*(kap*A+3*k*d)
    assert Y*Y==X**3+18*kap*k*X-8*kap**3*k
    assert X//(4*kap)==Z and (Z-kap)//(2*k)==d*d
    assert (Y//(4*kap)-3*k*d)//kap==A
    assert A==2**7*599 and is_prime(599)
    assert valuation_binomial(A,B,599)==valuation_binomial(A,3,599)==1
    return {'k5_pre61_exponents':survivors,'k5_post61_exponents':[],
            'relaxed_curve_point':{'k':k,'kap':kap,'X':X,'Y':Y,'n':A,'j':B},
            'invalid_admissibility_control':{'A':8,'d':1,'k':1,'kap':1,'j':1}}


def rational_identities(nmax: int) -> dict:
    count = positive = 0
    for n in range(8,nmax+1):
        for j in range(4,(n-1)//2+1):
            d = gcd(n,j)
            A,B = n//d,j//d
            c = 3 if A%3==0 else 1
            Z = Q(A,2)-B
            den = (n-1)*(n-2)
            k = Q(B*(A-B)*(A-2*B),den)
            kap = Z*(4*d*d*Z*Z-3*n+2)/den
            delta = Q(108*B*B*(A-B)**2*(B*d-1)*((A-B)*d-1),
                      c**4*(n-2)**2*(n-1)**3)
            assert kap==Z-2*k*d*d
            assert kap*A*A+6*k*A*d==4*Z**3+4*k
            p = B*(A-B)
            v = (B*d-1)*((A-B)*d-1)
            ratio = 1458*p*v*v*(4*d*d*Z*Z-3*n+2)/(c**8*Z*Z*(n-2)**2*(n-1)**4)
            assert kap*delta*delta/k**3==ratio
            if kap > 0:
                assert 8*c**8*kap*delta*delta < 729*k**3
                positive += 1
            X,Y = 4*kap*Z,4*kap*(kap*A+3*k*d)
            assert Y*Y==X**3+18*kap*k*X-8*kap**3*k
            count += 1
    assert 2**12*3**4 == 331776 and 50*3**4 == 4050
    return {'actual_rational_parameter_pairs':count,'positive_midpoint_pairs':positive,
            'note':'these are actual binomial parameters for algebra checks, NOT asserted counterexamples'}


def symbolic() -> dict:
    import sympy as s
    A,B,d,c = s.symbols('A B d c')
    n = A*d
    Z = A/2-B
    den = (n-1)*(n-2)
    k = B*(A-B)*(A-2*B)/den
    kap = Z*(4*d*d*Z*Z-3*n+2)/den
    delta = 108*B**2*(A-B)**2*(B*d-1)*((A-B)*d-1)/(c**4*(n-2)**2*(n-1)**3)
    assert s.factor(kap-Z+2*k*d*d)==0
    assert s.factor(kap*A*A+6*k*A*d-4*Z**3-4*k)==0
    ratio = 1458*B*(A-B)*((B*d-1)*((A-B)*d-1))**2*(4*d*d*Z*Z-3*n+2)/(c**8*Z**2*(n-2)**2*(n-1)**4)
    assert s.factor(kap*delta**2/k**3-ratio)==0
    X,Y = 4*kap*Z,4*kap*(kap*A+3*k*d)
    assert s.factor(Y**2-X**3-18*kap*k*X+8*kap**3*k)==0
    K,C,x = s.symbols('k kap x')
    assert s.factor(s.discriminant(x**3+18*C*K*x-8*C**3*K,x)) == -864*C**3*K**2*(2*C**3+27*K)
    return {'symbolic_midpoint':True,'symbolic_coupled_ratio':True,
            'symbolic_elliptic_map':True,'symbolic_nonsingularity':True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nmax',type=int,default=160)
    parser.add_argument('--symbolic',action='store_true')
    args = parser.parse_args()
    if args.nmax<8:
        parser.error('--nmax must be >=8')
    result = {'status':'PASS','whole_solution':False,
              'limitations':'self-audit; no independent review or Lean; all k>31 remain outside the periodic certificate',
              'identities':rational_identities(args.nmax),
              'small_a':low_rows(),'periodic':periodic_certificate(),
              'controls':named_controls()}
    if args.symbolic:
        result.update(symbolic())
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
