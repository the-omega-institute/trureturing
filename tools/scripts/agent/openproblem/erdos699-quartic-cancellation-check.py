#!/usr/bin/env python3
"""Exact self-audit for the quartic cancellation in Erdős 699.

This tests identities on actual binomial data. It is not a counterexample
search, independent review, or a numerical proof of an ineffective bound.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from math import comb, gcd
from typing import Sequence


def invariants(c: Sequence[int | Q]) -> tuple[int | Q, int | Q, int | Q]:
    if len(c) != 5:
        raise ValueError('five descending quartic coefficients required')
    a,b,c,d,e = c
    I = 12*a*e-3*b*d+c*c
    J = 72*a*c*e+9*b*c*d-27*a*d*d-27*b*b*e-2*c**3
    return I,J,J*J-2*I**3


def quartic(n: int, j: int, h: int) -> tuple[Q, ...]:
    if not (4 < j <= n//2 and h > 0):
        raise ValueError('requires 4 < j <= n/2 and h positive')
    return tuple(Q(h*(-1)**r*comb(j,r)*comb(n-r,4-r),comb(n,4)) for r in range(5))


def predicted(n: int, j: int, h: int) -> tuple[Q,Q,Q]:
    p = j*(n-j)
    v = (j-1)*(n-j-1)
    I = Q(72*h*h*p*v,n*n*(n-3)*(n-2)*(n-1)**2)
    J = Q(-864*h**3*p*p*v,n**3*(n-3)*(n-2)**2*(n-1)**3)
    T = Q(746496*h**6*p**3*v**2*((n-1)*(n-2)-p),
          n**6*(n-3)**3*(n-2)**4*(n-1)**6)
    return I,J,T


def audit(nmax: int, imax_n: int) -> dict:
    pairs = triples = 0
    for n in range(10,nmax+1):
        for j in range(5,n//2+1):
            pairs += 1
            g = gcd(comb(n,4),comb(n,j))
            H = quartic(n,j,g)
            assert all(q.denominator == 1 for q in H)
            I,J,T = invariants(H)
            assert (I,J,T) == predicted(n,j,g)
            assert I > 0 and J < 0 and T >= 1 and T.denominator == 1
            rough = Q(729*g**6*n*n,(n-3)**3*(n-1)**6)
            sharp = Q(729*g**6*(3*n*n-12*n+8),4*(n-3)**3*(n-1)**6)
            assert T <= sharp < rough < Q(4000*g**6,n**7)
            assert n**7 < 4000*g**6
            assert 4*(n-3)**3*(n-1)**6 <= 729*g**6*(3*n*n-12*n+8)
            if 2*j == n:
                assert T == sharp
            # Control: a different invariant combination has the opposite sign.
            assert J*J-4*I**3 < 0
    for n in range(10,imax_n+1):
        for j in range(5,n//2+1):
            for i in range(4,j):
                triples += 1
                g = gcd(comb(n,i),comb(n,j))
                divisor = comb(n,i)//g
                coefficients = tuple((-1)**r*comb(j,r)*comb(n-r,i-r)
                                     for r in range(i+1))
                assert all(z % divisor == 0 for z in coefficients)
                # This is the actual integer derivative of Q_i divided by (i-4)!.
                derived = tuple(coefficients[r]//divisor*comb(i-r,i-4)
                                for r in range(5))
                h = comb(i,4)*g
                H = quartic(n,j,h)
                assert H == derived
                I,J,T = invariants(derived)
                assert (I,J,T) == predicted(n,j,h)
                assert isinstance(T,int) and T > 0
                assert n**7 < 4000*h**6
    assert Q(729*10**9,7**3*9**6) == Q(10**9,250047) < 4000
    # Applying the quartic result directly to i=3 would be invalid.
    n,j = 1024,512
    g3 = gcd(comb(n,3),comb(n,j))
    assert g3 == 682 and not all(x.denominator == 1 for x in quartic(n,j,g3))
    assert n**7 > 4000*g3**6
    # Constants / exponents in the S-part application, not the unknown C_i.
    assert Q(7,6)-Q(13,12) == Q(1,12)
    assert 4000**2 == 16000000
    return {'status':'exact checks passed','quartic_nmax':nmax,
            'quartic_actual_pairs':pairs,'derivative_nmax':imax_n,
            'derivative_actual_triples':triples,
            'boundary_control':{'n':10,'j':5,'g':42,'H':[42,-84,56,-14,1],
                                'I':112,'J':-1960,'T':1031744},
            'invalid_i3_extension':{'n':1024,'j':512,'g3':682,'rejected':True},
            'unknown_S_part_constants_computed':False,
            'whole_solution':False,
            'limitations':'Algebraic self-audit; no independent review or Lean verification.'}


def symbolic_audit() -> dict:
    import sympy as s
    n,j,h,x = s.symbols('n j h x')
    a=h
    b=-4*h*j/n
    c=6*h*j*(j-1)/(n*(n-1))
    d=-4*h*j*(j-1)*(j-2)/(n*(n-1)*(n-2))
    e=h*j*(j-1)*(j-2)*(j-3)/(n*(n-1)*(n-2)*(n-3))
    I,J,T=invariants((a,b,c,d,e))
    p=j*(n-j); v=(j-1)*(n-j-1)
    Ie=72*h*h*p*v/(n*n*(n-3)*(n-2)*(n-1)**2)
    Je=-864*h**3*p*p*v/(n**3*(n-3)*(n-2)**2*(n-1)**3)
    Te=746496*h**6*p**3*v**2*((n-1)*(n-2)-p)/(n**6*(n-3)**3*(n-2)**4*(n-1)**6)
    assert s.factor(I-Ie)==0
    assert s.factor(J-Je)==0
    assert s.factor(T-Te)==0
    sharp=729*h**6*(3*n*n-12*n+8)/(4*(n-3)**3*(n-1)**6)
    assert s.factor(Te.subs(j,n/2)-sharp)==0
    A,B,C,D,E=s.symbols('a b c d e')
    I0,J0,_=invariants((A,B,C,D,E))
    assert s.expand(4*I0**3-J0**2-27*s.discriminant(A*x**4+B*x**3+C*x*x+D*x+E,x))==0
    return {'symbolic_I':True,'symbolic_J':True,'symbolic_cancellation':True,
            'symbolic_central_maximum':True,'symbolic_discriminant_control':True}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nmax',type=int,default=160)
    parser.add_argument('--derivative-nmax',type=int,default=80)
    parser.add_argument('--symbolic',action='store_true')
    args=parser.parse_args()
    if min(args.nmax,args.derivative_nmax)<10:
        parser.error('both row limits must be at least 10')
    result=audit(args.nmax,args.derivative_nmax)
    if args.symbolic:
        result.update(symbolic_audit())
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
