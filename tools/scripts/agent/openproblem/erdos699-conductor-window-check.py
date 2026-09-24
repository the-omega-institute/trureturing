#!/usr/bin/env python3
"""Exact self-audit for the Erdos 699 conductor and real-window continuation.

This audits the explicit 2-integral model, identities, constants and controls.
The local reduction/conductor rules and von Kanel--Matschke (2016), (10.16),
are external mathematical inputs. This script does not reprove them, compute
all conductors, establish an independent review, or solve the whole problem.
Optional --symbolic requires SymPy. All other arithmetic is exact standard
library arithmetic. --models accepts the earlier essential-support checker
and reads only its literal MODELS_23 list, without executing that file.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter
from fractions import Fraction as Q
import json
from math import gcd, factorial
from pathlib import Path
from typing import Sequence


def valuation(x: int | Q, p: int = 2) -> int:
    x = Q(x)
    if x == 0 or p < 2:
        raise ValueError('requires a nonzero rational and p >= 2')
    a, b, out = abs(x.numerator), x.denominator, 0
    while a % p == 0:
        a //= p
        out += 1
    while b % p == 0:
        b //= p
        out -= 1
    return out


def factor(n: int) -> dict[int, int]:
    if n <= 0:
        raise ValueError('positive integer required')
    out: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out


def invariants(a: Sequence[int | Q]) -> tuple[Q, Q, Q]:
    if len(a) != 5:
        raise ValueError('a1,a2,a3,a4,a6 required')
    a1,a2,a3,a4,a6 = map(Q, a)
    b2 = a1*a1+4*a2
    b4 = 2*a4+a1*a3
    b6 = a3*a3+4*a6
    b8 = a1*a1*a6+4*a2*a6-a1*a3*a4+a2*a3*a3-a4*a4
    C4 = b2*b2-24*b4
    C6 = -b2**3+36*b2*b4-216*b6
    D = -b2*b2*b8-8*b4**3-27*b6*b6+9*b2*b4*b6
    assert C4**3-C6**2 == 1728*D
    return C4,C6,D


def two_integral_model(L: int, K: int) -> tuple[int, tuple[Q,...], int]:
    W = L**3-27*K*K
    if L % 2 != 1 or K % 2 != 1 or W <= 0 or W % 256:
        raise ValueError('requires odd L,K and positive W divisible by 256')
    sign = 1 if K % 4 == 3 else -1
    C4, C6 = 3*L, -27*sign*K
    b = -C6*pow(C4,-1,64) % 64
    assert b % 4 == 1
    assert (b*b-C4) % 64 == 0
    assert (b*C4+C6) % 64 == 0
    a = (Q(1),Q(b-1,4),Q(0),Q(b*b-C4,48),
         Q(b**3-3*b*C4-2*C6,1728))
    assert all(x.denominator % 2 for x in a)
    assert invariants(a) == (C4,C6,Q(W,64))
    original = invariants((0,0,0,-L,2*sign*K))
    assert original == (16*C4,64*C6,Q(64*W))
    assert valuation(C4) == 0
    assert valuation(Q(W,64)) == valuation(W)-6
    assert Q(C4**3,1)/Q(W,64) == Q(original[0]**3,original[2])
    return sign,a,W


def log_interval(n: int, terms: int = 24) -> tuple[Q,Q]:
    """Rational enclosure of log(n), using the positive atanh series."""
    if n < 1 or terms < 1:
        raise ValueError('n,terms must be positive')
    def part(t: Q) -> tuple[Q,Q]:
        lower = 2*sum((t**(2*k+1)/Q(2*k+1) for k in range(terms)),Q(0))
        remainder = 2*t**(2*terms+1)/(Q(2*terms+1)*(1-t*t))
        return lower,lower+remainder
    q = n.bit_length()-1
    y = Q(n,1 << q)
    lo2,hi2 = part(Q(1,3))
    lo,hi = part((y-1)/(y+1))
    return q*lo2+lo,q*hi2+hi


def ceiling(q: Q) -> int:
    return -(-q.numerator//q.denominator)


def audit(nmax: int, localmax: int) -> dict:
    pair_count = strict_count = central_count = endpoint_count = 0
    for n in range(8,nmax+1):
        for j in range(4,n//2+1):
            pair_count += 1
            J = Q(1728*j*(n-j)*(n-2)**2,n*n*(j-1)*(n-j-1))
            diff = Q(1728*(n-1)*(n-2*j)**2,n*n*(j-1)*(n-j-1))
            assert J-1728 == diff
            assert n*n*(n-j-1)-(n-1)*(n-2*j)**2 == j*(3*n*n-4*n-4*j*n+4*j)
            assert 3*n*n-4*n-4*j*n+4*j > 0
            if 2*j < n:
                strict_count += 1
                assert 0 < diff < Q(1728,j-1) <= 576
                assert j < 1+1728/diff
            else:
                central_count += 1
                assert diff == 0
            d = gcd(n,j)
            A,B = n//d,j//d
            c = 3 if A % 3 == 0 else 1
            if B**3 > c*A*A:
                endpoint_count += 1
                assert j**3 > c*d*n*n >= n*n
    local_count = 0
    signs: Counter[int] = Counter()
    wvals: Counter[int] = Counter()
    for K in range(1,localmax,2):
        for L in range(1,localmax,2):
            W = L**3-27*K*K
            if W > 0 and W % 256 == 0:
                sign,_,W = two_integral_model(L,K)
                local_count += 1
                signs[sign] += 1
                wvals[valuation(W)] += 1
    # Exact synthetic controls at arbitrarily selected large dyadic depths;
    # they are not claimed to satisfy the binomial counterexample hypotheses.
    deep = 0
    for m in range(8,121):
        for K in (1,3,5,7):
            residue = pow(27*K*K,pow(3,-1,1 << (m-1)),1 << m)
            L = residue+(1 << m)
            _,_,W = two_integral_model(L,K)
            assert valuation(W) >= m
            deep += 1
    # Failure premise control: high divisibility of W is indispensable.
    try:
        two_integral_model(5,1)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid dyadic premise was accepted')

    # Separate local p>=5 tests. These check the exact valuation split and
    # invariant predicates, not a fresh implementation of Tate's algorithm.
    twist_controls = local_odd_checks = 0
    types: Counter[str] = Counter()
    for u in range(1,80,2):
        fu = factor(u)
        u0 = 1
        s = 1
        for p,b in fu.items():
            u0 *= p**(b%3)
            s *= p**(b//3)
        assert u == u0*s**3
        for r in range(1,24,2):
            for e in (1,3,5,7):
                if gcd(u,r) != 1 or gcd(e,r) != 1:
                    continue
                w = u*e**3-27*r*r
                if w <= 0:
                    continue
                L,K = u0*s*e,u0*r
                C4,C6,D = invariants((0,0,0,-L,2*K))
                assert D == 64*u0*u0*w
                fw = factor(w)
                U = V = 1
                for p in sorted(set(fu)|set(fw)|set(factor(r))):
                    if p < 5:
                        continue
                    local_odd_checks += 1
                    b0 = fu.get(p,0)%3
                    if b0:
                        assert w % p != 0
                        assert valuation(D,p) == 2*b0 < 12
                        assert valuation(C4,p) > 0
                        U *= p
                        types['additive'] += 1
                    elif w % p == 0:
                        assert u*r*e % p != 0
                        assert valuation(C4,p) == 0
                        assert valuation(D,p) == fw[p]
                        V *= p
                        types['multiplicative'] += 1
                    else:
                        assert valuation(D,p) == 0
                        types['good'] += 1
                assert gcd(U,V) == 1
                assert U*U*V <= u0*u0*w <= u*u*w
                twist_controls += 1

    lo2,hi2 = log_interval(2)
    assert lo2 > Q(2,3) and hi2 < Q(7,10)
    e_upper = sum((Q(1,factorial(i)) for i in range(8)),Q(0))+Q(9,8*factorial(8))
    assert e_upper < Q(11,4) and Q(11,4)**2 < 11
    assert Q(11,8)*2+Q(2,3) < 2*2
    assert Q(1151,10) < 116
    assert 4+Q(3,4)*116 == 91
    assert Q(3,2)*(2*3**5) == 729
    # The simplified discriminant lower bound improves Delta>=49 by a=10^6.
    a0 = 10**6
    _,log_upper = log_interval(486*a0)
    assert Q(a0-91,729*49) > log_upper
    delta_bounds = []
    for delta in (49,81,229,1000,10**6):
        lo,hi = log_interval(486*delta)
        lo = 91+729*delta*lo
        hi = 91+729*delta*hi
        assert ceiling(lo) == ceiling(hi)
        # If a < exact real upper endpoint, then a <= ceil(endpoint)-1.
        delta_bounds.append({'Delta':delta,'a_max':ceiling(hi)-1})
    support_bounds = []
    for R in (5,7,11,35,385):
        bits = (486*R*R).bit_length()
        alo,ahi = log_interval(486*R*R)
        assert ahi < bits
        a_bound = 91+729*R*R*bits
        support_bounds.append({'R':R,'integer_a_upper':a_bound,
                               'n_upper_as_power_of_two':2*a_bound})
    return {'status':'passed','actual_rational_pairs':pair_count,
            'strict_real_window_pairs':strict_count,'central_equality_controls':central_count,
            'endpoint_implication_controls':endpoint_count,
            'small_two_integral_models':local_count,'twist_sign_counts':dict(signs),
            'W_valuation_counts':dict(wvals),'deep_dyadic_controls':deep,
            'odd_prime_twist_controls':twist_controls,'odd_prime_local_checks':local_odd_checks,
            'odd_prime_predicate_counts':dict(types),'exact_Delta_to_a_cutoffs':delta_bounds,
            'effective_radical_cutoffs':support_bounds,
            'Tate_algorithm_reimplemented':False,'external_modular_bound_reproved':False,
            'whole_solution':False}


def model_window(path: Path) -> dict:
    tree = ast.parse(path.read_text(encoding='utf-8'))
    models = None
    for node in tree.body:
        if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='MODELS_23' for t in node.targets):
            models = ast.literal_eval(node.value)
    if models is None:
        raise ValueError('MODELS_23 literal not found')
    js = set()
    for c4,c6 in models:
        disc = Q(c4**3-c6**2,1728)
        assert disc.denominator == 1 and disc != 0
        assert set(factor(abs(disc.numerator))) <= {2,3}
        js.add(Q(c4**3,disc))
    assert len(models) == len(js) == 83
    window = sorted(J for J in js if 1728 < J < 2304)
    assert window == [Q(1944)]
    J = window[0]
    assert 1+Q(1728,J-1728) == 9
    assert 8**3 < 23**2
    # n>=32: a=2,3,4 fail already at d=1, for both c values;
    # increasing d only increases the left side. Hence a>=5.
    assert all(784*(c*(1<<a)-1)**3 >= 27*(1<<(4*a))
               for a in range(2,5) for c in (1,3))
    return {'reused_23_models':83,'j_in_open_real_window':[str(J) for J in window],
            'only_window_value_forces_j_at_most':8,'only_window_value_forces_n_at_most':22,
            'external_83_upper_count_reproved':False}


def symbolic_audit() -> dict:
    try:
        import sympy as s
    except ImportError as exc:
        raise SystemExit('--symbolic requires SymPy') from exc
    b,C4,C6=s.symbols('b C4 C6')
    a=(1,(b-1)/4,0,(b*b-C4)/48,(b**3-3*b*C4-2*C6)/1728)
    a1,a2,a3,a4,a6=a
    b2=a1*a1+4*a2;b4=2*a4+a1*a3;b6=a3*a3+4*a6
    assert s.expand(b2*b2-24*b4-C4)==0
    assert s.expand(-b2**3+36*b2*b4-216*b6-C6)==0
    n,j=s.symbols('n j')
    J=1728*j*(n-j)*(n-2)**2/(n*n*(j-1)*(n-j-1))
    diff=1728*(n-1)*(n-2*j)**2/(n*n*(j-1)*(n-j-1))
    assert s.factor(J-1728-diff)==0
    ell=3*j*(n-j)/(n*n*(n-1))
    k=j*(n-j)*(n-2*j)/(n**3*(n-1)*(n-2))
    assert s.factor(1728*ell**3/(ell**3-27*k*k)-J)==0
    assert s.expand(n*n*(n-j-1)-(n-1)*(n-2*j)**2-j*(3*n*n-4*n-4*j*n+4*j))==0
    return {'symbolic_two_integral_invariants':True,'symbolic_real_window':True,
            'symbolic_curve_to_binomial_J':True}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nmax',type=int,default=200)
    parser.add_argument('--local-max',type=int,default=500)
    parser.add_argument('--models',type=Path)
    parser.add_argument('--symbolic',action='store_true')
    args=parser.parse_args()
    if args.nmax<8 or args.local_max<20:
        parser.error('requires nmax>=8 and local-max>=20')
    out=audit(args.nmax,args.local_max)
    if args.models is not None:
        out.update(model_window(args.models))
    if args.symbolic:
        out.update(symbolic_audit())
    print(json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
