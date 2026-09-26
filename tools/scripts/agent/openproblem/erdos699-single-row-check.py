#!/usr/bin/env python3
"""# Erdos 699: a single-row reduction for EVERY 3-p column

Continuation of #9670 / #9769 at ff8a182d7841ad86d911d15004d20b14d59765e2.
Written partial proof with two disclosed terminal square checks and an
optional finite prime-base certificate. Not unrestricted Erdos699, not an
independent review, not Lean verification, and not a priority claim.

THEOREM. Let p>=5 be prime, b>=0, s,t>=1, j=2^b*3^s*p^t and n>=2j.
If gcd(C(n,3),C(n,j)) has no odd prime, then, writing o=ord_p(2),

  n=2^o, o=1 mod6, t=v_p(2^o-1), gcd(n,j)=2^b.            (A)

Put P=p^t, Q=(2^o-1)/P, alpha=1+v3(o-1), D=3^alpha.
Additionally s>=alpha, Q>1, 4*(2^o-2)<D*P^2 and
2^o-2<2*D*Q^2. The reduced ratio

  theta=(n-j)*(n-j-1)/((n-1)*(n-2))=x/D

has D/4<x<D, 3 does not divide x, and b<=1+v2(x).
Thus a given prime p leaves ONE possible original row n and ONE exponent t;
b and s have the explicit finite ranges in candidate_row() below.
No initial bound on n,p,b,s,t is assumed. In particular ALL columns are
proved whenever ord_p(2) is not1 mod6. This includes arbitrary exponents
for23,31,47,89; their orders are11,5,23,11. It removes the previously
unresolved order5 mod6 sector, rather than incrementing a fixed s cutoff.

A further disclosed finite corollary checks EVERY prime5<=p<=1000000:
76049 have excluded order;2444 fail the first gap; the other3 have Q=1
(p127,8191,524287). Hence ALL their 3-p columns, with arbitrary b,s,t,n,
are covered. This finite list of bases is not a universal-prime theorem
or a percentage of Erdos699. The unrestricted residue1 mod6 remains.

## Inherited premises, used exactly at their original scope

Use the normalized integral cubic F and Delta>=49 from the main theory
sections2-5, the prime-power endpoint theorem in
`erdos699-prime-power-summand-check.py`, and the partial cancellation lemma
in `erdos699-mixed-support-check.py`. Under a hypothetical counterexample:
 n=A*d,A=c*2^a,c in{1,3},d=gcd(n,j),B=j/d,C=(n-j)/d;
 B,C each have at least two distinct odd primes. Put eta=3 only when
 v3(n-1)=1, otherwise1; R1=(n-1)/eta, q=gcd(R1,B), qC=gcd(R1,C).
Then q*qC=R1 and q,qC,B/q,C/qC>1. For v=B/q and w its full part supported
on n(n-1), there is a positive integer H0 with

  c^5*d^2*H0=108*(v/w)^3*theta^2*(1-theta).               (B)

The separate integrality of Delta/w^2 and T/w proves this, including the
omitted single3. If theta=x/y is reduced, (B) gives y|3*(v/w).
At a retained prime l with v_l(B)>v_l(n-1), theta is l-integral and
 theta=-1 mod l. The complementary cubic is -F(1-X).
These are inherited written premises, not reproved or Lean-certified here.

The theorem in merged#10024, D5/S3/Arith/Erdos699DenominatorGap.lean,
blob982eb26f0fcd5b1363961f8023f2558bee790855, supplies this interface:
 n-1=L*R,j=1+m*R,0<2m<L,D*theta integer =>4(n-2)<D*L^2.
We restate its elementary proof to make the application auditable. Writing
D*theta=x, the integer K=D*(L-m)^2-x*L^2 satisfies
 K*(n-2)=D*m*(L-m)>0, hence K>=1. Thus
 4(n-2)<=4D*m*(L-m)<D*L^2.                              (C)
The +1 in j=1+mR is essential. No assertion that#10024 certifies the new
number-theoretic premises or this new column theorem is made.

## 1. All candidate rows are dyadic

B must retain3 and p, so c=1. If an odd prime divides d, q>1 forces the
other endpoint prime into n-1; both primes of v then divide n(n-1).
Equation(B) has v/w=1, forcing theta=1/3 or2/3 and d in{1,2,4}, a
contradiction. If both divide d, q=1 is already impossible. Consequently
 n=2^N,d=2^b,B=3^s*p^t,N>=5.                            (D)
The half-range is strict: its equality would give B=1. Also theta>1/4.

## 2. Close ALL even N, for arbitrary s and p

Let h=v3(n-1)=1+v3(N). Full low3-digits give s>=h if h>=2; when h=1,
3|j already suffices to show theta is3-integral. If p|n-1, all of v is
cancellable in(B), so theta=1/3 or2/3, contradiction. Hence p does not
divide n-1, q=3^h with h>=2, and6|N. The reduced denominator of theta is
D=p^e, with p|n-2. Its exponent is exactly e=v_p(n-2), since j=0 modp
and n=2 modp make its numerator a p-unit. Full low p-digits give D|j.

Take L=3^h and R=(n-1)/L. Because R|n-j, j=1+mR with0<2m<L.
Since D|n-2=L*R-1 and D|j=1+mR, D|L+m. Thus D<=L+m<3L/2.
Apply(C):
 8*(2^N-2)<3*L^3, L=3^(1+v3(N))<=3N/2,
 so64*(2^N-2)<81*N^3.                                 (E)
But s>=h>=2 implies j>=45 and N>=7. Together with6|N this gives N>=12.
At N12,64*(4096-2)=262016>139968=81*12^3. The ratio(2^N-2)/N^3 is
strictly increasing for N>=4: its numerator more than doubles and
2*N^3>(N+1)^3 (the polynomial difference is positive for N>=4).
Hence(E) is impossible. This closes an unbounded parity branch, not a
finite upper limit on s. D was the FULL prime power, not just p.

## 3. Close ALL odd N with alpha=v3(n-2)=1

For odd N,3 does not divide n-1; q=p^h,1<=h<=t. Cancelling p^(t-h) in(B)
shows theta has only3 in its denominator. Its numerator is a3-unit, so
its exact denominator is3^alpha. If alpha=1, theta=x/3,x=1 or2.
Equation(B) bounds d by4 through its2-adic valuation.
If t>h then theta=-1 modp, forcing x=2,p=5; but5|2^N-1 requires even N.
Thus t=h. Set P=p^t,Q=(n-1)/P,W=d*3^s. Then n=P*Q+1,j=P*W and Q>2W.
The exact equation is
 P*[3*(Q-W)^2-x*Q^2]=3W-(x+3)Q.                        (F)
Its right side is negative, and the integer bracket is <=-1. Consequently
 P<(x+3)Q, Q<6W/(3-x)<=6W, so n<180W^2+1.

For x1, rearrangement gives2(n-1)(n+1)=3j(2n-1-j); for x2 it gives
(n-1)(n+4)=3j(2n-1-j). The latter factor on the right is divisible by3.
Elementary lifting at3 gives respectively s<=v3(N)-1 or s<=v3(N-2)-1.
Therefore W<=4N/3 and2^N<320N^2+1. At N17 this fails, and
(2^N-1)/N^2 increases for N>=3. Thus N<=16. Since s>=1, x1 requires9|N
and x2 requires9|N-2. The COMPLETE remaining pairs are(N,x)=(9,1),(11,2).
The required squares1+4x*(2^N-1)*(2^N-2)/3 are347481 and11168433.
They lie strictly between589^2 and590^2, and3341^2 and3342^2. Both fail.
These two square checks are explicit terminal arithmetic in the proof.

## 4. The remaining odd row equals the multiplicative order

Now alpha>=2, so N=1 mod6; alpha=1+v3(N-1) and
 D=3^alpha<=3(N-1)/2. The low3-digits force alpha<=s.
Let o=ord_p(2),lambda=v_p(2^o-1), N=k*o. Both o>=3 and k are odd.
Elementary lifting gives h=lambda+v_p(k), and p does not divide o.
Let L=p^h,R=(n-1)/L. Again R|n-j, so(C) yields
 4*(2^N-2)<D*L^2.                                     (G)

If k3, p>=5 gives L=p^lambda<2^o. Since4*(2^N-2)>2^(N+1), (G) would
force2^o<(9/4)o, false for every o>=3 (base8>27/4 and monotonicity).
If k>=5, L=p^lambda*p^v_p(k)<2^o*k. Equation(G) would force
 2^((k-2)o)<(3/4)*o*k^3.                              (H)
The reverse holds for all o>=3,k>=5: at(3,5),512>1125/4; increasing o
multiplies the left-to-right ratio by2^(k-2)*o/(o+1)>1, and increasing k
multiplies it by2^o*(k/(k+1))^3>1. Thus k=1, N=o.
This step keeps lambda arbitrary; no non-Wieferich assumption is used.

## 5. No strict p-excess remains, and the finite one-row test

Since p-1 is a multiple of odd N, p=2rN+1. N=1 mod3 makes r1 impossible
for a prime p>=5, so p>=4N+1. If t>h, theta=-1 modp gives p|x+D, yet
 0<x+D<2D<=3(N-1)<p, contradiction. Therefore t=h=lambda.
The linear coefficient of -F(1-X) is3*theta*(n-2)/d; its integrality gives
 b<=1+v2(x). Since x<D, b<=1+floor(log2(D-1)).
With Q=(2^N-1)/P, the range is2^(b+1)*3^s<=Q-1, a finite exact bound.
For each resulting b,s compute x=D*(n-j)*(n-j-1)/((n-1)*(n-2)); it must
be an integer prime to3. This gives a complete finite necessary set for
EACH specified p, without enumerating any other n or any t.

For a cheap second cutoff put W=2^b*3^s. The general cofactor equation is
 P*[D*(Q-W)^2-x*Q^2]=D*W-(D+x)*Q.
The integer K=x*Q^2-D*(Q-W)^2 is positive and satisfies
 K*(n-2)=D*(Q-W)*(2Q-W). Thus n-2<2D*Q^2.
This is only a necessary bound; a surviving one-row candidate must still
pass the original binomial conditions. No unrestricted closure is claimed.

## Lifting and finite-certification conventions

For odd prime l, v_l(z-1)=lambda>=1 implies
v_l(z^m-1)=lambda+v_l(m). Factor m=l^a*m0; binomial expansion shows a
unit m0 preserves the valuation and each l-th power raises it by exactly1.
Apply this to z=4 for even binary exponents, z=-2 for odd plus-exponents,
and z=2^o at p. These are proofs for arbitrary exponents, not regressions.
prime_base_certificate() uses a full deterministic sieve and exact order
certificates (2^o=1 modp,2^(o/l)!=1 for every prime l|o). Lambda is measured
by modular powers, including any Wieferich cases. Integer comparisons use
bit lengths only with their exact proven meaning. Candidate regression
below is separate from the universal proof and the finite base certificate.

New work actually consumes the unrestricted integer theorem in#10024;
the strengthened denominator-divisor link D|L+m and its use in(G) were
not supplied by that Lean theorem. No new Lean certification is claimed.
The inherited normal form and cancellation premises still await independent
review. General i=3, prime bases with an unresolved one-row candidate, and
i=4..324 are not closed. No CI, truth counter, or governance change is made.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import json
from math import comb, gcd, isqrt


def primes(limit: int) -> list[int]:
    if limit < 2:
        return []
    flag=bytearray(b'\x01')*(limit+1)
    flag[:2]=b'\x00\x00'
    for p in range(2,isqrt(limit)+1):
        if flag[p]:
            flag[p*p::p]=b'\x00'*((limit-p*p)//p+1)
    return [p for p in range(2,limit+1) if flag[p]]


@lru_cache(None)
def factor(n: int) -> tuple[tuple[int,int], ...]:
    if n < 1:
        raise ValueError('positive factor input required')
    out=[]; p=2
    while p*p<=n:
        e=0
        while n%p==0:
            e+=1; n//=p
        if e: out.append((p,e))
        p=3 if p==2 else p+2
    if n>1: out.append((n,1))
    return tuple(out)


def vp(n: int,p: int) -> int:
    if n==0 or p<2:
        raise ValueError('nonzero n and p>=2 required')
    n=abs(n); e=0
    while n%p==0: n//=p; e+=1
    return e


@lru_cache(None)
def order2(p: int) -> int:
    if p<3 or p%2==0 or factor(p)!=((p,1),):
        raise ValueError('odd prime required')
    o=p-1
    for l,_ in factor(o):
        while o%l==0 and pow(2,o//l,p)==1: o//=l
    assert pow(2,o,p)==1
    assert all(pow(2,o//l,p)!=1 for l,_ in factor(o))
    return o


def component(p: int,o: int) -> tuple[int,int]:
    P=p; e=1
    while pow(2,o,P*p)==1:
        e+=1; P*=p
    assert pow(2,o,P)==1 and pow(2,o,P*p)!=1
    return e,P


def power_at_least(exponent: int,bound: int) -> bool:
    """Exact test2^exponent>=bound, without constructing huge powers."""
    if exponent<0 or bound<1: raise ValueError('invalid power comparison')
    if exponent>=bound.bit_length(): return True
    if exponent<bound.bit_length()-1: return False
    return (1<<exponent)>=bound


def prime_base_certificate(limit: int) -> dict:
    categories=Counter(); exceptions=[]; cofactor_one=[]; count=0
    for p in primes(limit):
        if p<5: continue
        count+=1; o=order2(p)
        if o%6!=1:
            categories['excluded_order']+=1
            continue
        lam,P=component(p,o)
        D=3**(1+vp(o-1,3))
        if power_at_least(o+2,D*P*P+8):
            categories['first_gap']+=1
            continue
        n=1<<o; Q=(n-1)//P
        assert P*Q==n-1
        if Q==1:
            categories['cofactor_one']+=1; cofactor_one.append(p)
        elif n-2>=2*D*Q*Q:
            categories['second_gap']+=1
        else:
            categories['unresolved']+=1; exceptions.append([p,o,lam,D,Q])
    if limit==1000000:
        assert count==78496
        assert dict(categories)=={'excluded_order':76049,'cofactor_one':3,'first_gap':2444}
        assert cofactor_one==[127,8191,524287] and not exceptions
    return {'prime_bound':limit,'prime_bases_at_least5':count,
            'reasons':dict(categories),'cofactor_one_primes':cofactor_one,
            'unresolved_bases':exceptions,'all_bases_closed':not exceptions,
            'scope':'finite prime bases; all their b,s,t,n are covered by the proof'}


def candidate_row(p: int) -> dict:
    o=order2(p)
    if o%6!=1: return {'p':p,'order':o,'excluded_by_order':True}
    lam,P=component(p,o); n=1<<o; Q=(n-1)//P
    alpha=1+vp(o-1,3); D=3**alpha
    if Q==1: return {'p':p,'order':o,'lambda':lam,'excluded_by_cofactor_one':True}
    bound_b=(D-1).bit_length()
    tested=0; survivors=[]
    # All larger s violate the half-range; all larger b violate coefficient integrality.
    for b in range(bound_b+1):
        d=1<<b; s=alpha; j=d*(3**s)*P
        while 2*j<=n:
            tested+=1
            x=F(D*(n-j)*(n-j-1),(n-1)*(n-2))
            if x.denominator==1 and x.numerator%3 and b<=1+vp(x.numerator,2):
                assert D<4*x<4*D
                survivors.append({'b':b,'s':s,'t':lam,'j':j,'x':x.numerator})
            s+=1; j*=3
    return {'p':p,'order':o,'lambda':lam,'D':D,'Q':Q,
            'first_gap':4*(n-2)<D*P*P,'second_gap':n-2<2*D*Q*Q,
            'candidate_tests':tested,'survivors':survivors,
            'scope':'one necessary row only; survivors would not be counterexamples'}


def gap_and_terminal_audit() -> dict:
    cases=divisor_cases=0; examples=[]
    for L in range(3,41):
        for R in range(1,31):
            n=L*R+1
            if n<8: continue
            for m in range(1,(L-1)//2+1):
                j=1+m*R
                theta=F((n-j)*(n-j-1),(n-1)*(n-2))
                x,D=theta.numerator,theta.denominator
                K=D*(L-m)**2-x*L*L
                assert K*(n-2)==D*m*(L-m)>0 and K>=1
                assert 4*(n-2)<D*L*L
                cases+=1
                if (n-2)%D==0 and j%D==0:
                    assert (L+m)%D==0 and 2*D<3*L
                    assert 8*(n-2)<3*L**3
                    divisor_cases+=1
                    if len(examples)<3:examples.append([n,j,L,R,m,D])
    assert divisor_cases>0
    terminals=[]
    for N,x in ((9,1),(11,2)):
        n=1<<N; z=1+4*x*(n-1)*(n-2)//3
        assert 4*x*(n-1)*(n-2)%3==0
        r=isqrt(z)
        assert r*r<z<(r+1)*(r+1)
        terminals.append([N,x,z,r,z-r*r,(r+1)**2-z])
    assert terminals==[[9,1,347481,589,560,619],[11,2,11168433,3341,6152,531]]
    assert 64*((1<<12)-2)>81*12**3
    assert (1<<17)>320*17**2+1
    assert 4*(1<<9)>3*3*5**3
    for N in range(4,301):
        assert 2*N**3>(N+1)**3
        assert ((1<<(N+1))-2)*N**3>((1<<N)-2)*(N+1)**3
    for o in range(3,151):
        assert 4*(1<<o)>9*o
        for k in range(5,36):
            assert 4*(1<<((k-2)*o))>3*o*k**3
    # Independent binary-order regression and arbitrary lambda controls, including Wieferich primes.
    lifting=0
    for p in primes(1100):
        if p<5:continue
        o=order2(p); lam,P=component(p,o)
        assert vp((1<<o)-1,p)==lam
        for k in (1,3,5,p):
            if o*k<=2000000:
                assert vp((1<<(o*k))-1,p)==lam+vp(k,p)
                lifting+=1
    assert component(1093,order2(1093))[0]>=2
    return {'formal_gap_interfaces':cases,'denominator_divisor_interfaces':divisor_cases,
            'nonempty_interface_examples':examples,'complete_terminal_squares':terminals,
            'lifting_regressions':lifting,'wieferich_1093_retained':True,
            'infinite_monotonicity_proved_in_text':True}


def valuation_binomial(n: int,j: int,p: int) -> int:
    e=0; power=p
    while power<=n:
        e+=n//power-j//power-(n-j)//power; power*=p
    return e


def carries(n: int,j: int,p: int) -> int:
    a,b,carry,total=j,n-j,0,0
    while a or b or carry:
        carry=(a%p+b%p+carry)//p; total+=carry; a//=p; b//=p
    return total


def column_audit(nmax: int,cert_limit: int) -> dict:
    columns=[]; new_columns=[]
    for j in range(4,nmax//2+1):
        f=dict(factor(j)); other=[p for p in f if p>=5]
        if f.get(3,0)==0 or len(other)!=1:continue
        p=other[0]
        if order2(p)%6==1 and p>cert_limit:continue
        columns.append(j)
        if order2(p)%6==5 and f[3]>=4:new_columns.append(j)
    supported={n:[p for p,e in factor(n*(n-1)*(n-2)//6) if p>=3]
               for n in range(8,nmax+1)}
    tests=direct=new_pairs=0
    for j in columns:
        for n in range(2*j,nmax+1):
            witness=next((p for p in supported[n] if valuation_binomial(n,j,p)>0),None)
            assert witness is not None,(n,j)
            assert valuation_binomial(n,3,witness)>0
            assert valuation_binomial(n,j,witness)==carries(n,j,witness)>0
            if n<=200:
                assert comb(n,j)%witness==0 and comb(n,3)%witness==0; direct+=1
            tests+=1; new_pairs+=j in new_columns
    return {'nmax':nmax,'columns':len(columns),'original_pairs':tests,
            'direct_binomial_checks':direct,
            'order5_mod6_and_s_at_least4_columns':new_columns,
            'pairs_in_those_columns':new_pairs,
            'regression_is_not_unbounded_proof':True}


def symbolic_audit() -> dict:
    try:
        import sympy as S
    except ImportError as exc:
        raise SystemExit('--symbolic requires SymPy') from exc
    L,R,m,D,x,P,Q,W,n,j=S.symbols('L R m D x P Q W n j')
    E=D*(n-j)*(n-j-1)-x*(n-1)*(n-2)
    E1=S.expand(E.subs({n:L*R+1,j:1+m*R}))
    core=(D*(L-m)**2-x*L**2)*(L*R-1)-D*m*(L-m)
    assert S.expand(L*E1-R*core)==0
    E2=S.expand(E.subs({n:P*Q+1,j:P*W}))
    block=P*(D*(Q-W)**2-x*Q**2)-D*W+(D+x)*Q
    assert S.expand(E2-P*block)==0
    K=x*Q**2-D*(Q-W)**2
    second=K*(P*Q-1)-D*(Q-W)*(2*Q-W)
    assert S.expand(second+Q*block)==0
    X=S.symbols('X')
    F=(n*X**3-3*j*X**2+3*j*(j-1)/(n-1)*X-j*(j-1)*(j-2)/((n-1)*(n-2)))
    theta=(n-j)*(n-j-1)/((n-1)*(n-2))
    assert S.cancel(S.diff(F,X).subs(X,1)-3*theta*(n-2))==0
    return {'formal_gap_residual':True,'cofactor_equation':True,
            'second_gap_residual':True,'coefficient_identity':True}


def main() -> None:
    parser=argparse.ArgumentParser(description='Exact audits and finite prime-base certificate for the single-row theorem.')
    parser.add_argument('--pmax',type=int,default=1000000)
    parser.add_argument('--nmax',type=int,default=5000)
    parser.add_argument('--symbolic',action='store_true')
    args=parser.parse_args()
    if args.pmax<5 or args.nmax<8:parser.error('requires pmax>=5 and nmax>=8')
    prime_cert=prime_base_certificate(args.pmax)
    if not prime_cert['all_bases_closed']:
        # Do not silently extend the finite corollary beyond its completed certificate.
        raise SystemExit(json.dumps(prime_cert,indent=2))
    small=primes(1000)
    assert small==[p for p in range(2,1001) if factor(p)==((p,1),)]
    for a in range(60):
        for B in (1,2,3,(1<<a),(1<<a)+1):assert power_at_least(a,B)==((1<<a)>=B)
    samples=[candidate_row(p) for p in (23,31,47,89,127,601,1801,2099863,616318177)]
    assert all(not sample.get('survivors') for sample in samples)
    out={'scope':'partial i=3 theorem; all 3-p candidates have the single row in(A)',
         'prime_base_certificate':prime_cert,'gap_and_terminals':gap_and_terminal_audit(),
         'one_row_examples':samples,'columns':column_audit(args.nmax,args.pmax),
         'whole_erdos699_solved':False,'independent_review':False,'lean_verified':False}
    if args.symbolic:out['symbolic']=symbolic_audit()
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
