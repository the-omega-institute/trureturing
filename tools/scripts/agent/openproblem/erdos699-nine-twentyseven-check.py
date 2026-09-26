#!/usr/bin/env python3
"""# Erdős 699: complete 9-p and 27-p column exclusions

Research continuation of issue #9670 and PR #9769, read at commit
`a3fc3f085695acb2653384da3202a18c1c40261c` on 2026-09-26.

## Result and boundary

For every prime p>=5, b>=0, t>=1, and s in {2,3}, put
j=2^b*3^s*p^t. For every n>=2j there is an odd prime dividing BOTH C(n,3)
and C(n,j). Thus the entire 9-p and 27-p column families satisfy the
original i=3 assertion, without an initial bound on p,b,t,n or an order
condition on p. The p=3 case is already covered by the deposited
prime-power endpoint theorem.

This is a written proof with explicitly identified finite arithmetic lemmas.
It is not the unrestricted i=3 theorem or the full Erdős 699 theorem.
No independent reviewer, Lean, CI, or historical priority is claimed.
No new elliptic-curve or analytic-height input is used.

## Inherited premises and their exact roles

Use the normalized integral cubic F and Delta=disc(F)>=49 from sections
2-5 of ERDOS_699_BINOMIAL_COMMON_PRIME.md. For a hypothetical counterexample,
write d=gcd(n,j), A=n/d=c*2^a, B=j/d, C=(n-j)/d, c in {1,3}. Both reduced
endpoints have at least two distinct odd prime factors, by the deposited
`erdos699-prime-power-summand-check.py` (commit 97325142).

Let eta=3 precisely when v3(n-1)=1 and eta=1 otherwise; put
R1=(n-1)/eta, q=gcd(R1,B), qC=gcd(R1,C), v=B/q.
Complete low prime-power conditions and the previously proved block-value
bound give q*qC=R1 and q,qC,v,C/qC>1.
With H=(n-1)/q, J=j/q and theta=(n-j)(n-j-1)/((n-2)(n-1)),

    T=-H^3 F(J/H)=J(H-J)(2H-J)/(c*d*(n-2)) in Z_{>0},
    Delta*T=108*v^3*theta^2*(1-theta)/(c^5*d^2),
    0<theta<1.

The partial cancellation lemma in `erdos699-mixed-support-check.py`
(commit a3fc3f08) says: if w is v's full part supported on n(n-1), then
Delta/w^2 and T/w are positive integers. Consequently, for an integer M>0,

    c^5*d^2*M=108*(v/w)^3*theta^2*(1-theta).                 (1)

For completeness, its local check is as follows. At a prime dividing n,
vp(Delta)=2vp(v)+vp(108) and vp(T)=vp(v). At a retained prime dividing
n-1 the same formulas hold for the excess exponent vp(v). At the omitted
single 3, vp(Delta)>=2vp(v)+1 and vp(T)>=vp(v)+2. These follow directly
from the displayed T and the normalized cubic discriminant formula.
Thus the separate cancellations are legitimate at every prime of w.
For reduced theta=x/y, gcd(y,x^2(y-x))=1; (1) implies y | 3*(v/w).
If v=w, y^3|108, so theta=1/3 or 2/3 and c=1,d in {1,2,4}.
These are inherited lemmas, not new results of the present finite checks.

## 1. Reduction to a dyadic row

Assume j=2^b*3^s*p^t, p>=5 and s=2 or3, is a counterexample.
The prime-power endpoint theorem forces B to retain both 3 and p;
in particular c=1. If an odd prime divides d, it cannot divide n-1.
Because q>1, the other prime of B must divide n-1. Thus every prime of v
is supported on n(n-1). Equation (1) would force d in {1,2,4}, a
contradiction. (If both odd primes divide d, q=1 already contradicts q>1.)
Hence

    d=2^b, n=2^N, B=3^s*p^t.                              (2)

Both families have j>=45, so n>=90 and N>=7.
Also, from j<=n/2,

    theta >= n/[4(n-1)] > 1/4.                            (3)

## 2. Odd N: only a finite set of rational parameters is possible

If N is odd, 3 does not divide n-1. Thus q=p^h, with
h=vp(n-1)>=1 and t>=h. Cancel w=p^(t-h) in (1). The reduced denominator
of theta is a power of 3. In its original expression both numerator
factors are 3-units, so the denominator is EXACTLY

    y=3^alpha, alpha=v3(n-2).

If alpha>=2 then 2^(N-1)=1 mod9, so N=1 mod3, since ord_9(2)=6.
If alpha>s, then alpha>=2, 3 divides C(n,3), and
j mod 3^alpha is a nonzero multiple of 3^s, larger than 2. This contradicts
the complete low-digit condition n mod 3^alpha=2. Therefore

    1<=alpha<=s, y=3^alpha, y/4<x<y, gcd(x,3)=1.            (4)

The linear coefficient of -F(1-X) is 3theta(n-2)/d, an integer. Since
v2(n-2)=1 and y is odd,

    d=2^b, 0<=b<=1+v2(x).                                 (5)

### 2a. Strict p-excess is impossible

Suppose t>h. Cancelling p^h in the original theta expression gives

    theta=(n-j)(H-J)/[(n-2)H], H=(n-1)/p^h, J=j/p^h,

so theta is p-integral and theta=-1 mod p. Hence p divides x+y.
If y=3, only p=5 can occur; its order4 cannot divide odd N.
If y=9, the only odd primes of the possible x+y are 7,13,17.
(The full set x is 4,5,7,8.) Orders for 13,17 are even; p=7 has order3,
but alpha=2 implies N=1 mod3. All are impossible.
For y=27 the x values are 7,8,10,11,13,14,16,17,19,20,22,23,25,26.
Primes of x+y with even order are again impossible; p=7 contradicts
N=1 mod3. The only residual pairs are

    (p,x,y)=(23,19,27) or (47,20,27).

Here s=3. The equation defining theta, reduced modulo64 (N>=7), requires

    27*j*(j+1)-2*x = 0 mod64,
    j=2^b*27*p^t, 0<=b<=1+v2(x).                          (6)

The FULL powers of 23 modulo64 are
1,23,17,7,33,55,49,39. The full powers of 47 are 1,47,33,15.
For p=23 the residual sets in (6), for b=0,1 respectively, are

    {6,12,22,28,38,44,54,60}, {4,24,36,56}.

For p=47 and b=0,1,2,3 they are respectively

    {18,20,50,52}, {18,22}, {36,44}, {16,32}.

None contains zero. This checks complete residue cycles, not a bound on t.
Thus t=h in EVERY remaining odd-N case.

### 2b. Equality of exponents leaves a complete small integer certificate

Put P=p^t, Q=(n-1)/P, and M0=d*3^s. Then

    n=P*Q+1, j=P*M0, P>=5 odd, Q odd, Q>=2*M0+1.

The exact equation theta=x/y becomes

    P*[y*(Q-M0)^2-x*Q^2]=y*M0-(x+y)*Q.                    (7)

The right side is negative. Thus the bracket is negative and

    2*M0<Q<2*y*M0/(y-x).                                 (8)

Equations (4),(5),(8) are a COMPLETE finite domain, independent of the
initial p,t,b,N. For each Q, (7) determines P by exact integer division.
Even allowing P to be any odd integer>=5, exhaustive exact arithmetic gives

    s=2: 2606 Q checks; only (x,y,d,Q,P,n,j)=(2,3,1,49,109,5342,981).
    s=3: 19832 Q checks; only (7,27,1,55,163,8966,4401).

Both n are 2 mod4, contradicting (2). Two separately written finite
enumerations, one scanning Q and the other scanning P and solving the
quadratic in Q by exact integer square roots, verify the same singleton
lists. This finite calculation is an explicit lemma of the proof.
No bound on p, t or n was guessed; all finite bounds are consequences of
(4),(5),(8). The maximum Q checked is2591 for s=2 and7775 for s=3.

## 3. Even N: a four-case or two-case local contradiction

Write h3=v3(n-1). If h3>s, the retained 3-power low digits already
contradict v3(j)=s. Otherwise theta is 3-integral, since
(n-j-1)=(n-1)-j contains the complete 3^h3, also when h3=1 was omitted.
If p divided n-1, all of v would cancel in (1), forcing theta=1/3 or2/3,
contrary to 3-integrality. Therefore p does not divide n-1. Then q=3^h
with 2<=h<=s. The denominator restriction from (1), together with
3-integrality and 0<theta<1, forces p to divide n-2. Thus

    2*3^(h-1) divides N, ord_p(2) divides N-1,
    gcd(ord_p(2),6)=1.                                   (9)

Here the first divisibility uses only ord_9(2)=6 and ord_27(2)=18.
Let Q=(n-1)/3^h, C=Q*w0 with w0 odd>=3, and d=2^b. Since n=d(B+C),

    d*3^(s+h)*p^t=(3^h-d*w0)*n+d*w0,
    3<=d*w0<3^h,
    p divides 2*3^h-d*w0.                                (10)

For h=2, the entire (d,w0) list is (1,3),(1,5),(1,7),(2,3).
The integers in the last divisibility are15,13,11,12. Their prime divisors
>=5 are5,13,11, all of even order, contradicting (9).
For h=3, only s=3 is possible. Factoring every 54-d*w0 with d a power of2,
w0 odd>=3 and d*w0<27, and retaining (9), leaves exactly

    (d,w0,p)=(1,7,47), (1,23,31).

For p=47, (10) is 729*47^t=20*n+7. Since18|N, n=1 mod19; hence
9^t=12 mod19. The full powers of9 are1,9,5,7,6,16,11,4,17, never12.
For p=31, (10) is 729*31^t=4*n+23. Mod7, where n=1, it gives
t=3 mod6. Mod19, where n=1, it gives t=1 mod6. Contradiction.
This exhausts even N, including arbitrary t.

## 4. Conclusion, value and remaining obligations

Every hypothetical counterexample in either stated column family has been
excluded, so the theorem follows. In particular j=414=2*9*23 and
j=621=27*23 are covered for every n>=2j. The previously deposited
order-conditioned theorem does not cover p=23, whose order is11; neither
column meets the earlier j-1 single-odd-prime condition. These examples
explain the strict extension, not a completion percentage.

What is still missing: arbitrary s>=4 for order coprime to6, two-prime
columns without3, more general multi-prime endpoints, and the remaining
4<=i<=324 cases. This proof does not provide a global counterexample bound
or solve the full problem. Its finite lemmas are disclosed above. The
checker does not independently reprove the earlier normalized-cubic and
prime-power endpoint premises. Historical reviews are not reviews of this
new proof.

"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import json
from math import comb, gcd, isqrt

@lru_cache(None)
def factor(n: int) -> dict[int, int]:
    if n < 1:
        raise ValueError('positive integer required')
    out: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0)+1
            n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        out[n] = out.get(n, 0)+1
    return out

def v2(n: int) -> int:
    if n <= 0:
        raise ValueError('positive integer required')
    return (n & -n).bit_length()-1

def vp(x: int | F, p: int) -> int:
    z = F(x)
    if not z or p < 2:
        raise ValueError('nonzero rational and p>=2 required')
    a,b,e = abs(z.numerator),z.denominator,0
    while a % p == 0:
        a//=p; e+=1
    while b % p == 0:
        b//=p; e-=1
    return e

@lru_cache(None)
def power_cycle(base: int, modulus: int) -> tuple[int, ...]:
    if modulus < 2 or gcd(base,modulus) != 1:
        raise ValueError('unit base and modulus>=2 required')
    values = [1]
    x = base % modulus
    while x != 1:
        assert x not in values
        values.append(x)
        x = x*base % modulus
    return tuple(values)

def theta_cases(s: int):
    for alpha in range(1,s+1):
        y=3**alpha
        for x in range(y//4+1,y):
            if x % 3:
                for b in range(v2(x)+2):
                    yield x,y,1<<b

def no_excess_certificate(s: int) -> dict:
    q_steps=p_steps=0
    scan_q: set[tuple[int,...]]=set()
    scan_p: set[tuple[int,...]]=set()
    max_q=0
    for x,y,d in theta_cases(s):
        M=d*3**s
        hi=(2*y*M-1)//(y-x)
        max_q=max(max_q,hi)
        for Q in range(2*M+1,hi+1,2):
            q_steps+=1
            den=y*(Q-M)**2-x*Q*Q
            num=y*M-(x+y)*Q
            if den >= 0 or num % den:
                continue
            P=num//den
            if P>=5 and P%2:
                assert P*den==num
                scan_q.add((x,y,d,Q,P,P*Q+1,M*P))
        # Independent enumeration: bound P by |numerator|, solve for Q.
        p_hi=(x+y)*hi-y*M
        for P in range(5,p_hi+1,2):
            p_steps+=1
            aa=P*(y-x)
            bb=-2*P*y*M+(x+y)
            cc=P*y*M*M-y*M
            D=bb*bb-4*aa*cc
            if D < 0:
                continue
            root=isqrt(D)
            if root*root!=D:
                continue
            for num in {-bb-root,-bb+root}:
                if num % (2*aa):
                    continue
                Q=num//(2*aa)
                if Q%2 and 2*M<Q<=hi:
                    assert P*(y*(Q-M)**2-x*Q*Q)==y*M-(x+y)*Q
                    scan_p.add((x,y,d,Q,P,P*Q+1,M*P))
    assert scan_q==scan_p
    expected={2:{(2,3,1,49,109,5342,981)},
              3:{(7,27,1,55,163,8966,4401)}}
    assert scan_q==expected[s]
    assert all(row[5]%4==2 for row in scan_q)
    assert q_steps=={2:2606,3:19832}[s]
    return {'s':s,'Q_domain_size':q_steps,'independent_P_checks':p_steps,
            'maximum_Q_bound':max_q,'integer_candidates':sorted(scan_q),
            'all_candidates_fail_mod4':True,'two_enumerations_agree':True}

def strict_excess_certificate() -> dict:
    possible=set()
    rejected=set()
    for alpha in range(1,4):
        y=3**alpha
        for x in range(y//4+1,y):
            if x%3==0:
                continue
            for p in factor(x+y):
                if p<5:
                    continue
                o=len(power_cycle(2,p))
                if o%2==0 or (alpha>=2 and o%3==0):
                    rejected.add((p,x,y,o))
                else:
                    possible.add((p,x,y))
    assert possible=={(23,19,27),(47,20,27)}
    expected={(23,0):[6,12,22,28,38,44,54,60],(23,1):[4,24,36,56],
              (47,0):[18,20,50,52],(47,1):[18,22],
              (47,2):[36,44],(47,3):[16,32]}
    out=[]
    for p,x,y in sorted(possible):
        cycle=power_cycle(p,64)
        for b in range(v2(x)+2):
            residues=sorted({(y*((1<<b)*27*z)*((1<<b)*27*z+1)-2*x)%64
                             for z in cycle})
            assert residues==expected[p,b] and 0 not in residues
            out.append({'p':p,'x':x,'y':y,'b':b,'cycle':cycle,'residues':residues})
    return {'residual_triples':sorted(possible),'mod64_tables':out,
            'excluded_order_triples':len(rejected),'full_exponent_cycles':True}

def even_certificate() -> dict:
    cases={}
    total=0
    for h in (2,3):
        q=3**h
        kept=[]
        for b in range(q.bit_length()):
            d=1<<b
            for w in range(3,q//d+1,2):
                if d*w>=q:
                    continue
                total+=1
                for p in factor(2*q-d*w):
                    if p>=5 and gcd(len(power_cycle(2,p)),6)==1:
                        kept.append((d,w,p))
        cases[h]=kept
    assert cases=={2:[],3:[(1,7,47),(1,23,31)]}
    assert 12 not in power_cycle(9,19)
    assert len(power_cycle(2,19))==18 and len(power_cycle(2,7))==3
    assert len(power_cycle(2,9))==6 and len(power_cycle(2,27))==18
    t7=[t for t in range(6) if (729*pow(31,t,7)-4-23)%7==0]
    t19=[t for t in range(6) if (729*pow(31,t,19)-4-23)%19==0]
    assert t7==[3] and t19==[1]
    assert len(power_cycle(31,7))==len(power_cycle(31,19))==6
    return {'complete_cofactor_cases':total,'residual_cases':cases,
            'p47_full_powers_mod19':power_cycle(9,19),
            'p31_t_mod6_from7':t7,'p31_t_mod6_from19':t19}

def vpbinom(n: int,j: int,p: int) -> int:
    value,power=0,p
    while power<=n:
        value+=n//power-j//power-(n-j)//power
        power*=p
    return value

def carries(n: int,j: int,p: int) -> int:
    a,b,carry,value=j,n-j,0,0
    while a or b or carry:
        carry=(a%p+b%p+carry)//p
        value+=carry;a//=p;b//=p
    return value

def rational_audit(nmax: int) -> dict:
    pairs=local=0
    for n in range(8,nmax+1):
        for j in range(4,n-3):
            d=gcd(n,j);A=n//d;B=j//d;c=3 if A%3==0 else 1;lead=A//c
            if lead<4 or lead&(lead-1):
                continue
            eta=3 if vp(n-1,3)==1 else 1
            q=gcd((n-1)//eta,B);v=B//q;H=(n-1)//q;J=j//q
            T=F(J*(H-J)*(2H-J),c*d*(n-2))
            D=F(108*B*B*(A-B)**2*(j-1)*(n-j-1),c**4*(n-2)**2*(n-1)**3)
            theta=F((n-j)*(n-j-1),(n-2)*(n-1))
            assert D*T==F(108*v**3,c**5*d*d)*theta**2*(1-theta)
            for p,e in factor(v).items():
                if n*(n-1)%p==0:
                    assert vp(T,p)>=e and vp(D,p)>=2*e
                    local+=1
            pairs+=1
    return {'rational_pairs_both_halves':pairs,'supported_valuation_checks':local,
            'hypothetical_counterexamples_used_as_samples':False}

def column_audit(nmax: int) -> dict:
    columns=[];outside_order=[];new_columns=[]
    for j in range(4,nmax//2+1):
        f=factor(j);s=f.get(3,0);ps=[p for p in f if p>=5]
        if s not in (2,3) or len(ps)!=1:
            continue
        p=ps[0];columns.append(j)
        if gcd(len(power_cycle(2,p)),6)==1:
            outside_order.append(j)
            if sum(q>2 for q in factor(j-1))>=2:
                new_columns.append(j)
    pairs=direct=old_gap_pairs=0
    for j in columns:
        for n in range(2*j,nmax+1):
            cn3=n*(n-1)*(n-2)//6
            shared=next((p for p in factor(cn3) if p>=3 and vpbinom(n,j,p)>0),None)
            assert shared is not None,(n,j)
            assert carries(n,j,shared)==vpbinom(n,j,shared)>0
            assert vpbinom(n,3,shared)>0
            if n<=500:
                assert comb(n,j)%shared==0 and gcd(cn3,comb(n,j))%shared==0
                direct+=1
            pairs+=1
            old_gap_pairs+=j in outside_order
    assert all(j in new_columns for j in (414,621)) if nmax>=1242 else True
    return {'nmax':nmax,'original_columns':len(columns),'original_pairs':pairs,
            'direct_binomial_crosschecks':direct,'valuation_and_carry_crosschecks':pairs,
            'columns_outside_prior_order_theorem':outside_order,
            'pairs_outside_prior_order_theorem':old_gap_pairs,
            'columns_also_outside_j_minus_one_thin_predicate':new_columns,
            'regression_is_not_the_unbounded_proof':True}

def symbolic_audit() -> dict:
    try:
        import sympy as S
    except ImportError as exc:
        raise SystemExit('--symbolic requires sympy') from exc
    n,j,X,d=S.symbols('n j X d',nonzero=True)
    theta=(n-j)*(n-j-1)/((n-2)*(n-1))
    f=(n*X**3-3*j*X**2+3*j*(j-1)/(n-1)*X-j*(j-1)*(j-2)/((n-1)*(n-2)))/d
    assert S.cancel(S.diff(f,X).subs(X,1)-3*theta*(n-2)/d)==0
    x,y,P,Q,M=S.symbols('x y P Q M')
    expr=y*(n-j)*(n-j-1)-x*(n-1)*(n-2)
    reduced=S.expand(expr.subs({n:P*Q+1,j:P*M})/P)
    target=P*(y*(Q-M)**2-x*Q**2)-(y*M-(x+y)*Q)
    assert S.expand(reduced-target)==0
    assert S.expand(expr.subs(n,0)-(y*j*(j+1)-2*x))==0
    assert S.expand(4*(n-j)*(n-j-1)-n*(n-2)-(n-2*j)*(3*n-2*j-2))==0
    return {'linear_coefficient_identity':True,'cofactor_equation_identity':True,
            'binary_residue_identity':True,'quarter_window_identity':True}

def main() -> None:
    parser=argparse.ArgumentParser(description='Finite proof lemmas and regression for the 9-p/27-p theorem.')
    parser.add_argument('--nmax',type=int,default=2000)
    parser.add_argument('--local-nmax',type=int,default=200)
    parser.add_argument('--symbolic',action='store_true')
    args=parser.parse_args()
    if args.nmax<10 or args.local_nmax<8:
        parser.error('requires nmax>=10 and local-nmax>=8')
    report={'theorem_scope':'i=3; j=2^b*3^s*p^t, p>=5 prime, s=2 or3, all n>=2j',
            'no_excess':[no_excess_certificate(s) for s in (2,3)],
            'strict_excess':strict_excess_certificate(),'even':even_certificate(),
            'rational':rational_audit(args.local_nmax),'columns':column_audit(args.nmax),
            'whole_erdos699_solved':False,'independent_review':False}
    if args.symbolic:
        report['symbolic']=symbolic_audit()
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
