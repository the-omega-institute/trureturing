#!/usr/bin/env python3
"""Exact self-audit: central-divisor obstruction for the Erdos 699 i=3 lane.

This is not a whole-problem proof or an independent review. The written
argument proves k < 729*r**3/(8*c**9), r=gcd(k,A/2-B). This program supplies
the declared finite arithmetic certificate excluding r=1,3,5 for c=1,
with unbounded a,d; the c=3 lower bound r>=41 is elementary.

Usage: python erdos699-central-divisor-check.py [--nmax 200] [--symbolic]
All mandatory arithmetic uses only the Python standard library.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from functools import lru_cache
import json
from math import comb, gcd, isqrt

PERIOD = 27720
PRIMES = (3,5,7,11,13,17,19,23,29,31,37,41,43,61,67,71,73,89,
          109,113,127,151,181,199,211,241,281,331,337,353,397,421,
          433,463,617,631,661,683,881,991)


def is_prime(p: int) -> bool:
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))


@lru_cache(None)
def order_two(p: int) -> int:
    if p <= 2 or not is_prime(p):
        raise ValueError('an odd prime is required')
    v = 1
    for order in range(1, p):
        v = 2*v % p
        if v == 1:
            return order
    raise AssertionError('order not found')


@lru_cache(None)
def square_roots(p: int) -> dict[int, tuple[int, ...]]:
    out: dict[int, list[int]] = {}
    for v in range(p):
        out.setdefault(v*v % p, []).append(v)
    return {k:tuple(v) for k,v in out.items()}


def equation(A: int, d: int, u: int, r: int, h: int) -> int:
    z = 2*u*d*d + h
    return h*A*A + 6*u*A*d - 4*r*r*z**3 - 4*u


def allowed_exponents(u: int, r: int, h: int, p: int) -> tuple[int, set[int]]:
    """Exact quadratic solution in A, for every d modulo p, including h=0."""
    order = order_two(p)
    values: set[int] = set()
    roots = square_roots(p)
    inv = pow(h, -1, p) if h % p else None
    for d in range(p):
        z = (2*u*d*d+h) % p
        rhs = (4*r*r*z**3+4*u) % p
        if inv is None:
            linear = 6*u*d % p
            if linear:
                values.add(rhs*pow(linear, -1, p) % p)
            elif rhs == 0:
                return order, set(range(order))
        else:
            disc = (9*u*u*d*d+h*rhs) % p
            for root in roots.get(disc, ()):
                A = (-3*u*d+root)*inv % p
                assert equation(A,d,u,r,h) % p == 0
                values.add(A)
    return order, {a for a in range(order) if pow(2,a,p) in values}


def direct_exponents(u: int, r: int, h: int, p: int) -> tuple[int,set[int]]:
    order = order_two(p)
    out = {a for a in range(order) if any(
        equation(pow(2,a,p),d,u,r,h) % p == 0 for d in range(p))}
    return order, out


def binomial_valuation(n: int, j: int, p: int) -> int:
    answer, power = 0, p
    while power <= n:
        answer += n//power-j//power-(n-j)//power
        power *= p
    return answer


def low_rows() -> dict:
    rows: set[int] = set()
    for a in range(2,10):
        for c in (1,3):
            A, d = c*(1<<a), 1
            while 784*(A*d-1)**3 < 27*(1<<(4*a)):
                rows.add(A*d)
                d += 1
    assert rows == {32,64,128,256,512,1024}
    count, results = 0, []
    for n in sorted(rows):
        cn3 = comb(n,3)
        ps = [p for p in range(3,n+1,2) if is_prime(p) and cn3 % p == 0]
        for j in range(4,n//2+1):
            assert any(binomial_valuation(n,j,p)>0 for p in ps)
            g = gcd(cn3,comb(n,j))
            assert g//(g & -g)>1
            count += 1
        results.append({'n':n, 'common_prime_pool':ps, 'j_count':n//2-3})
    assert count == 990
    return {'count':count, 'rows':results}


def arithmetic_audit(nmax: int) -> dict:
    pairs = positive = 0
    for n in range(8,nmax+1):
        for j in range(4,n//2+1):
            d = gcd(n,j); A, B = n//d, j//d
            Z = Q(A,2)-B
            ell = Q(3*B*(A-B),n-1)
            k = Q(B*(A-B)*(A-2*B),(n-1)*(n-2))
            Delta = Q(108*B*B*(A-B)**2*(B*d-1)*((A-B)*d-1),
                      (n-2)**2*(n-1)**3)
            kap = Z-2*k*d*d
            assert ell*Z == 3*k*Q(n-2,2)
            assert ell**3-27*k*k == Q(A*A,4)*Delta
            assert kap*A*A+6*k*A*d == 4*Z**3+4*k
            pairs += 1
            if kap>0:
                assert 8*kap*Delta*Delta < 729*k**3
                positive += 1
    # Non-vacuous divisibility controls, deliberately not original counterexamples.
    controls = 0
    for a in range(2,31):
        for c in (1,3):
            M = c**6*(1<<(2*a-2))
            for u in (1,5,7,11):
                ell, k = 3*u*u+M*u, u**3
                Delta = (ell**3-27*k*k)//M
                assert (ell**3-27*k*k) % M == 0
                assert gcd(u,M)==1 and Delta>0 and Delta % (u*u)==0
                controls += 1
    # An actual integral relaxed witness, whose A is not c*2**a.
    A,B,d = 76672,26775,1
    n=A*d; Z=A//2-B
    k=Q(B*(A-B)*(A-2*B),(n-1)*(n-2))
    ell=Q(3*B*(A-B),n-1)
    Delta=Q(4*ell**3-108*k*k,A*A)
    assert (k,ell,Delta)==(5255,52275,97200)
    r=gcd(int(k),Z); u=int(k)//r; kap=Z-2*int(k)*d*d
    assert (u,r,kap//r,Delta//(u*u))==(5,1051,1,3888)
    assert gcd(u,r)==gcd(u,kap//r)==1
    assert 8*(kap//r)*u*(Delta//(u*u))**2 < 729*r*r
    return {'actual_rational_pairs':pairs,'positive_midpoint_pairs':positive,
            'synthetic_square_divisibility_controls':controls,
            'relaxed_integral_witness':[A,B,d,u,r,3888],
            'all_controls_are_not_counterexamples':True}


def periodic_certificate() -> dict:
    assert all(PERIOD % order_two(p)==0 for p in PRIMES)
    full=(1<<PERIOD)-1
    rows=[]; direct_checks=0
    for r in (1,3,5):
        initial=after2=killed=0; left=[]; used=set()
        for u in range(1,(729*r*r-1)//8+1,2):
            if gcd(u,r)!=1:
                continue
            delta_min=(49+u*u-1)//(u*u)
            cap=(729*r*r-1)//(8*u*delta_min**2)
            for h in range(1,cap+1,2):
                if gcd(u,h)!=1:
                    continue
                initial += 1
                if not any((r*r*(2*u*d*d+h)**3+u)%512==0 for d in range(512)):
                    continue
                after2 += 1
                for p in (3,5,7,11,13,17,19):
                    assert direct_exponents(u,r,h,p)==allowed_exponents(u,r,h,p)
                    direct_checks += 1
                mask=full
                for p in PRIMES:
                    order,allowed=allowed_exponents(u,r,h,p)
                    block=sum(1<<e for e in allowed)
                    new=mask & (block*(full//((1<<order)-1)))
                    if new!=mask:
                        used.add(p)
                    mask=new
                    if not mask:
                        break
                if mask:
                    left.append({'u':u,'h':h,'exponents':[e for e in range(PERIOD) if mask>>e&1]})
                else:
                    killed += 1
        expected={1:(64,11,11),3:(694,123,123),5:(2550,445,443)}[r]
        assert (initial,after2,killed)==expected
        if r<5:
            assert left==[]
        else:
            assert left==[{'u':61,'h':25,'exponents':[7867,21727]},
                          {'u':999,'h':1,'exponents':[6,13866]}]
        rows.append({'r':r,'initial_pairs':initial,'after_mod512':after2,
                     'periodically_excluded':killed,'remaining':left,'effective_primes':sorted(used)})
    # First last case: the ell/u equation z*e=3*(A*d/2-1) modulo 37.
    u,r,h,p=61,5,25,37
    assert order_two(p)==36 and 7867%36==21727%36==19
    A=pow(2,19,p)
    solutions=[d for d in range(p) if equation(A,d,u,r,h)%p==0]
    assert A==35 and solutions==[18]
    for d in solutions:
        z=(2*u*d*d+h)%p
        assert z==0 and A*d%p==1 and 3*(A*d-2)%p!=0
    # Second last case: exact coefficient valuations. All t are handled in prose.
    coeffs=(1024,75*1998,75*1998**2,25*1998**3)
    val2=lambda z:(z & -z).bit_length()-1
    assert tuple(val2(x) for x in coeffs)==(10,1,2,3)
    for t in range(81):
        for odd in (1,3,5,17):
            d=(1<<t)*odd
            T=25*(1998*d*d+1)**3+999
            assert val2(T)==min(10,1+2*t)
    # Modulus-only constraints genuinely have a solution at an inadmissible d=0.
    assert equation(64,0,999,5,1)==0
    for p in PRIMES:
        o,allowed=allowed_exponents(999,5,1,p)
        assert 6%o in allowed
    assert 8*3**9==729*216
    assert 64*3**18//729**2==46656
    assert 38**4 < 49*46656 < 39**4 and gcd(39,3)!=1 and gcd(41,3)==1
    assert 20557-6*576==17101 and 6048+12*576==12960
    assert 3456-18*576 == -6912 and 4*576==2304
    for c in (1,3):
        C=2**20557*3**6048*c**3456
        Lam=Q(2**17101*3**12960,c**6912)
        assert Lam.denominator==1 and C*Q(729**2,64*c**18)**576==Lam
    return {'period':PERIOD,'prime_count':len(PRIMES),'rows':rows,
            'initial_total':3308,'after_mod512_total':579,'periodic_exclusions':577,
            'direct_modular_crosschecks':direct_checks,
            'last_two_excluded_by':['ell_divisibility_mod37','all_t_2adic_valuation'],
            'c1_central_divisor_lower_bound':7,'c3_central_divisor_lower_bound':41,
            'a_range':'all a>=10; a<10 separately covered by low_rows',
            'k_upper_bound_assumed':False}


def symbolic_audit() -> dict:
    try:
        import sympy as s
    except ImportError as exc:
        raise SystemExit('--symbolic requires SymPy') from exc
    A,B,d=s.symbols('A B d'); n=A*d
    ell=3*B*(A-B)/(n-1)
    k=B*(A-B)*(A-2*B)/((n-1)*(n-2))
    Z=A/2-B
    assert s.factor(ell*Z-3*k*(n-2)/2)==0
    u,r,h=s.symbols('u r h')
    kap=r*h; kk=r*u; ZZ=r*(2*u*d*d+h)
    E=kap*A*A+6*kk*A*d-4*ZZ**3-4*kk
    assert s.expand(E/r-(h*A*A+6*u*A*d-4*r*r*(2*u*d*d+h)**3-4*u))==0
    T=s.Poly(s.expand(25*(1998*d*d+1)**3+999),d)
    assert T.nth(0)==1024 and T.nth(2)==75*1998
    assert T.nth(4)==75*1998**2 and T.nth(6)==25*1998**3
    return {'symbolic_normalization':True,'symbolic_last_case_expansion':True}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nmax',type=int,default=200)
    parser.add_argument('--symbolic',action='store_true')
    args=parser.parse_args()
    if args.nmax<8:
        parser.error('--nmax must be at least 8')
    out={'status':'passed','arithmetic':arithmetic_audit(args.nmax),
         'low_exponents':low_rows(),'certificate':periodic_certificate(),
         'whole_solution':False,'independent_review':False}
    if args.symbolic:
        out.update(symbolic_audit())
    print(json.dumps(out,indent=2))


if __name__=='__main__':
    main()
