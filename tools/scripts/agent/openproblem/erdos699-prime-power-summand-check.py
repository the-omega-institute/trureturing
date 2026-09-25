#!/usr/bin/env python3
"""Exact self-audit for the Erdos 699 prime-power endpoint exclusion.

Written theorem: under an i=3 counterexample, both reduced endpoints
j/gcd(n,j) and (n-j)/gcd(n,j) have at least two DISTINCT odd prime factors.
Consequently j=2^b or 2^b*p^t (p odd prime,t>=1,j>=4) is covered for all
n>=2j. This is a partial theorem, not a solution of unrestricted Erdos699.

The proof builds on erdos699-prime-summand-check.py and theory sections2-5:
F is integral, disc(F)=Delta>=49. Put n=Ad,A=c*2^a,B=j/d,C=A-B,
s=c*d; R1=(n-1)/eta, where eta=3 only if v3(n-1)=1.
qB=gcd(R1,B),qC=gcd(R1,C) satisfy qB*qC=R1. Prior integer
block-value/discriminant estimates give qB,qC,B/qB,C/qC>1.
Suppose one endpoint is p^beta; use it as j/d (both halves allowed).
Then qB=p^h with 1<=h<beta, h=v_p(n-1), p does not divide s,
v=p^(beta-h), H=(n-1)/p^h, J=d*v. With
T=-H^3 F(J/H)>0 and theta=(n-j)(n-j-1)/((n-2)(n-1)), one has
v_p(T)=beta-h, v_p(Delta)=2(beta-h)+v_p(108).
Thus M=(Delta/v^2)*(T/v) is a positive integer, and
c^5*d^2*M=108*theta^2*(1-theta).
For reduced theta=x/y in(0,1), integrality forces y^3|108,
so theta=1/3 or2/3, with respective values8 or16.
It follows c=1,d in{1,2,4},n=2^N. Also theta is p-integral and
is -1 modulo p: divide n-j-1 and n-1 by p^h before reducing.
p=3 is impossible; theta=1/3 would force p|4; hence p=5,theta=2/3.
The exact equation is (n-1)(n+4)=3*j*(2*n-1-j).
Since 5|n-1, N=0 mod4, and its 5-adic valuation gives
beta=v5(2^N-1)+v5(2^N+4)=2+v5(N)+v5(N-2).
The elementary lifting formula proves 5^beta<=25*N, so j<=100*N.
The theta equation gives j>n/6: at m=n-j>=5n/6 its left side
3m(m-1) exceeds2(n-1)(n-2) by at least n^2/12+7n/2-4>0.
Therefore 2^N<600N. Since 2^13>600*13 and 2^N/N increases,
N<=12. The complete residual list is N=4,8,12, d=1,2,4;
all nine exact equality checks fail. This proves the theorem without
bounds on the initial prime p, exponent beta, or original n.

Tests below check identities and finite terminal arithmetic. They do not
turn finite sampling into the unbounded proof, and give no independent
review, Lean, CI, or historical-priority certification.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import comb, gcd, isqrt
import json


def factor(n: int) -> dict[int, int]:
    if n < 1:
        raise ValueError('positive integer required')
    result: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def vp(n: int, p: int) -> int:
    if n == 0 or p < 2:
        raise ValueError('nonzero integer and p>=2 required')
    n, exponent = abs(n), 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def vpq(x: Q, p: int) -> int:
    return vp(x.numerator, p) - vp(x.denominator, p)


def vpbinom(n: int, j: int, p: int) -> int:
    result, power = 0, p
    while power <= n:
        result += n//power-j//power-(n-j)//power
        power *= p
    return result


def carry_count(n: int, j: int, p: int) -> int:
    x, y, carry, count = j, n-j, 0, 0
    while x or y or carry:
        carry = (x % p + y % p + carry)//p
        count += carry
        x //= p
        y //= p
    return count


def discriminant(f: tuple[Q, Q, Q, Q]) -> Q:
    a,b,c,d=f
    return b*b*c*c-4*a*c**3-4*b**3*d-27*a*a*d*d+18*a*b*c*d


def terminal_certificate() -> dict:
    # Rational-root denominator: a denominator must have its cube dividing108.
    denominators = [q for q in range(1,109) if 108 % (q**3) == 0]
    assert denominators == [1,3]
    allowed = [(str(t),int(108*t*t*(1-t))) for t in (Q(1,3),Q(2,3))]
    assert allowed == [('1/3',8),('2/3',16)]
    scales = [(c,d,M) for c in (1,3) for d in range(1,5)
              for M in range(1,17) if c**5*d*d*M in (8,16)]
    assert all(c == 1 and d in (1,2,4) for c,d,M in scales)
    assert 2**13 > 600*13
    rows=[]
    for N in (4,8,12):
        n=1<<N
        beta=2+vp(N,5)+vp(N-2,5)
        assert beta == vp(n-1,5)+vp(n+4,5)
        for d in (1,2,4):
            j=d*5**beta
            residual=(n-1)*(n+4)-3*j*(2*n-1-j)
            assert residual != 0
            rows.append({'N':N,'d':d,'beta':beta,'n':n,'j':j,
                         'legal_half_range':4<=j<=n//2,'residual':residual})
    # The LTE formula is proved in the text; these are finite regression tests.
    lte_controls=0
    for N in range(4,1201,4):
        beta=vp((1<<N)-1,5)+vp((1<<N)+4,5)
        assert beta == 2+vp(N,5)+vp(N-2,5)
        assert 5**beta<=25*N
        lte_controls+=1
    return {'rational_denominators':denominators,'theta_integer_values':allowed,
            'terminal_cases':rows,'terminal_case_count':len(rows),
            'lte_regression_cases':lte_controls}


def valuation_controls() -> dict:
    count=0
    for p in (3,5,7,11,13,17,19):
        for d in (1,2,3,4,5):
            if d%p == 0:
                continue
            for c in (1,3):
                if c%p == 0:
                    continue
                for h in (1,2):
                    for beta in (h+1,h+2):
                        j=d*p**beta
                        q=p**h
                        # A whole arithmetic progression supplies actual n,j.
                        n=2*j+((1-2*j)*pow(d,-1,q)%q)*d
                        if vp(n-1,p)>h:
                            n+=d*q
                        assert n%d==0 and gcd(n,j)==d and vp(n-1,p)==h
                        H,J=(n-1)//q,j//q
                        v=p**(beta-h)
                        s=c*d
                        T=Q(J*(H-J)*(2*H-J),s*(n-2))
                        Delta=Q(108*j*j*(n-j)**2*(j-1)*(n-j-1),
                                s**4*(n-2)**2*(n-1)**3)
                        theta=Q((n-j)*(n-j-1),(n-2)*(n-1))
                        assert vpq(T,p)==beta-h
                        assert vpq(Delta,p)==2*(beta-h)+vp(108,p)
                        assert theta.denominator%p != 0
                        assert theta.numerator*pow(theta.denominator,-1,p)%p == p-1
                        assert Delta*T/v**3 == 108*theta**2*(1-theta)/(c**5*d*d)
                        count+=1
    # Here the rational cubic need not be integral. No counterexamples claimed.
    return {'local_valuation_controls':count}


def direct_audit(nmax: int) -> dict:
    pairs=covered=thin_columns=both_endpoint_control=new_columns=0
    witnesses=0
    for n in range(8,nmax+1):
        cn3=comb(n,3)
        cnj=comb(n,4)
        for j in range(4,n//2+1):
            if j>4:
                cnj=cnj*(n-j+1)//j
            d=gcd(n,j)
            B,C=j//d,(n-j)//d
            bfac,cfac=factor(B),factor(C)
            oddj={p:e for p,e in factor(j).items() if p>2}
            column=len(oddj)<=1
            # Conditional proof forces each endpoint odd with >=2 primes.
            criterion=(B%2==0 or C%2==0 or len(bfac)<=1 or len(cfac)<=1)
            if column:
                thin_columns+=1
            if len(bfac)<=1 or len(cfac)<=1:
                both_endpoint_control+=1
            if column or criterion:
                g=gcd(cn3,cnj)
                oddprime=next((p for p in factor(g) if p>2),None)
                assert oddprime is not None,(n,j,B,C,g)
                for jj in (3,j):
                    value=vpbinom(n,jj,oddprime)
                    assert value>0 and value==carry_count(n,jj,oddprime)
                witnesses+=1
                covered+=1
            # Detect columns not handled by the earlier three easy criteria.
            if len(oddj)==1 and next(iter(oddj.values()))>=2:
                m=j//(j & -j)
                p0=next(iter(oddj))
                old_extra=49*(j & -j)**2>16*(m//p0)**3
                odd_previous={p for p in factor(j-1) if p>2}
                if len(odd_previous)>=2 and not old_extra:
                    new_columns+=1
            pairs+=1
    # j121 was not covered by the prime-only or j-1 thin-column criteria.
    assert factor(121)=={11:2}
    assert len([p for p in factor(120) if p>2])==2
    assert 49<=16*11**3
    # Equalities theta=1/3,2/3 can occur without the counterexample hypotheses.
    assert Q((56-11)*(56-12),(56-2)*(56-1))==Q(2,3)
    assert gcd(56-1,11)==11  # cofactor v=1, violating v>1 in the proof.
    assert discriminant((Q(1),Q(-3),Q(3),Q(-1)))==0  # nonzero premise essential.
    return {'actual_half_pairs':pairs,'covered_pairs_with_explicit_odd_prime':covered,
            'oddpart_one_or_prime_power_column_pairs':thin_columns,
            'at_most_one_distinct_prime_in_a_reduced_endpoint_pairs':both_endpoint_control,
            'new_column_pairs_beyond_old_prime_and_j_minus_one_and_two_adic_tests':new_columns,
            'legendre_and_carry_witnesses':witnesses,
            'counts_overlap':True,'whole_problem_solved':False}


def symbolic_audit() -> dict:
    try:
        import sympy as S
    except ImportError as exc:
        raise SystemExit('--symbolic requires SymPy') from exc
    n,j,s,q,H,J,X,t=S.symbols('n j s q H J X t')
    F=(n*X**3-3*j*X**2+3*j*(j-1)/(n-1)*X
       -j*(j-1)*(j-2)/((n-1)*(n-2)))/s
    Delta=S.discriminant(F,X)
    theta=(n-j)*(n-j-1)/((n-2)*(n-1))
    T=-H**3*F.subs(X,J/H)
    lhs=(Delta*T).subs({n:q*H+1,j:q*J})
    rhs=(108*(j/q)**3*theta**2*(1-theta)/s**5).subs({n:q*H+1,j:q*J})
    assert S.factor(lhs-rhs)==0
    assert S.expand(S.Rational(4,27)-t*t*(1-t)-(t-S.Rational(2,3))**2*(t+S.Rational(1,3)))==0
    assert S.expand(3*(n-j)*(n-j-1)-2*(n-1)*(n-2)
                    -((n-1)*(n+4)-3*j*(2*n-1-j)))==0
    assert S.expand(3*(5*n/6)*(5*n/6-1)-2*(n-1)*(n-2)
                    -(n*n/12+7*n/2-4))==0
    assert S.factor(F.subs(j,n-j)+F.subs(X,1-X))==0
    return {'symbolic_product_identity':True,'symbolic_theta_equation':True,
            'symbolic_n_over_six_bound':True,'complement_polynomial':True}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nmax',type=int,default=500)
    parser.add_argument('--symbolic',action='store_true')
    args=parser.parse_args()
    if args.nmax<8:
        parser.error('--nmax must be at least8')
    result={'status':'passed','nmax':args.nmax,'unbounded_proof_by_sampling':False}
    result.update(terminal_certificate())
    result.update(valuation_controls())
    result.update(direct_audit(args.nmax))
    if args.symbolic:
        result.update(symbolic_audit())
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
