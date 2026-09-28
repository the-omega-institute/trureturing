#!/usr/bin/env python3
r"""Erdos 699: arithmetic rank collapse, quadratic synchronization, infinite supports.

CONTINUITY. Read #9670 / #9769 at f521fb0c00a26a56d39fc92768169c12717d5cde.
This is a written PARTIAL theorem using explicitly inherited arithmetic.
No unrestricted Erdos699 solution, new Lean certification, independent
review or worldwide priority is claimed. All finite tests are self-audits;
there is NO new finite-search lemma in the unbounded proof.

THEOREM. Fix r in {5,13} and epsilon in {+1,-1}. Let S be a finite set of
primes congruent to r modulo24, with (q/p)=epsilon for every distinct p,q
in S. Then EVERY j=2^b*product(p^a_p)>=4, with arbitrary nonnegative
exponents, satisfies the original i=3 assertion for EVERY n>=2j.
There is no bound on support size, exponents, row or gcd(n,j).

Moreover EVERY such finite S has infinitely many one-prime extensions
preserving the same r,epsilon. Thus for each of the FOUR choices (r,epsilon)
there exists a strictly increasing infinite prime sequence such that every
integer>=4 supported on2 and finitely many of its terms is a proved column.
The extension uses classical CRT, quadratic reciprocity and Dirichlet's
theorem; those classical facts and homogeneous prime sets are not claimed
as new. The new application is their original-binomial column conclusion.
This does not say arbitrary supports or arbitrary j are covered.

EXAMPLE. S={5,29,149} has all pairwise quadratic symbols+1. Its normalized
fourth-character matrix is (*,2,2);(2,*,2);(0,0,*), so the previous quartic
synchronization theorem does not apply. The prior generated-group target
criterion also fails: 2^10*29^3=(1,-1) modulo(5,149). New arithmetic removes
the29 generator in the ONLY ratio branch where this target is relevant.
Consequently all2^b*5^s*29^t*149^u columns, including all s,t,u positive,
are covered, with unrestricted gcd and n. This compares named predicates,
not every earlier theorem or an asserted completion percentage.

0. PRECISE INHERITED INTERFACE
Under an original i=3 counterexample, use the previously deposited normal
form and mixed-support lemmas, NOT the later analytic3-p closure:
 d=gcd(n,j)=2^b*e, e odd, v2(j)=b, n=c*2^N*e,
 c in{1,3}, N>=b+2;
 some odd prime P divides j and n-1;
 some odd prime R divides j and neither n nor n-1;
 theta=(n-j)(n-j-1)/((n-1)(n-2))=x/y reduced,0<theta<1,
 y|3z, with all primes of z dividing j but not n(n-1).
For the present supports3 does not divide j, e or z. Active primes p|j,
p not|d are precisely the endpoint primes not dividing n. Every field
map below is at an active prime. The inherited existence of two different
roles excludes empty/singleton active sets. The current proof does not
independently verify these premises from the binomial definition.
Sources: the main theory sections2-5 and erdos699-mixed-support-check.py;
follow-on interface: erdos699-restricted-diagonal-check.py.

1. STANDALONE EXACT GCD COLLAPSE
For integers n,j,D,x with n>=3,1<=j<n and
 D(n-j)(n-j-1)=x(n-1)(n-2), let d=gcd(n,j).
Reduction modulo d gives0=2x, so d|2x. No reduced-fraction or primality
hypothesis is required. Also gcd(n-2,j)|2D, by reducing the same equation
modulo gcd(n-2,j). These are independent integer statements.

In particular theta=1/3 implies d|2, and theta=2/3 implies d|4.
Thus both exceptional branches in the original normal form have e=1.
Their exact residuals are respectively
 2(n-1)(n+1)=3j(2n-1-j),
 (n-1)(n+4)=3j(2n-1-j).
Neither residual permits3|n, as reduction modulo3 shows. Hence n=2^N.
The previously allowed shared-prime generators have actually disappeared;
this follows from an integer identity, not from dropping a group condition.

2. BRANCH-SENSITIVE GROUP TARGET THEOREM
For any finite S of primes>=5 and ordered p!=q, let
 K_pq=< (2,2),(r modp,r modq):r in S\{p,q} >,
 H_pq=< (2,2) >, both subgroups of F_p^* x F_q^*.
A sufficient whole-support criterion is
 (1,2),(1/3,2/3) outside K_pq for every ordered pair;
 (1,-1),(1,-4) outside H_pq for every ordered pair.
When all support primes are1 mod4 the (1,-4) test can be omitted, by the
independent two-thirds integer contradiction below.

Proof: n/c has restricted support, so its active pair lies in K. For c3
or for c1 with an endpoint prime of n-2, the inherited denominator and
role argument forces one of the first two targets. Otherwise theta=1/3
or2/3. Section1 makes e=1, so this time the active pair lies in the SMALLER
H; the exact residual forces the corresponding sign target there.
For all primes1 mod4, oddpart(j)=1 mod4. If theta2/3 and j is odd, the
exact equality3(n-j)(n-j-1)=2(n-1)(n-2) reads2=0 mod4. If j is even,
v2 of its two sides is respectively b and2 because N>=b+2. Thus b2,
N>=4, n0 mod16 and j4 mod16: the equality reads12=4. Contradiction.
This proves the refined target criterion without a fixed-order assumption.
It does not assert that every support satisfies the criterion.

3. LOCAL QUADRATIC SYNCHRONIZATION LEMMA
Assume all odd primes of j are in ONE class r=5 or13 modulo24. It is
sufficient that (e/p)=xi be the SAME sign at every active p. xi may be-1;
the fourth phases may disagree. All such p are5 mod8, so (2/p)=-1,
v2(ord_p(2))=2, and their (3/p)=sigma have one common sign (respectively
-1 and+1 for r5 and13). The supplementary laws and Gauss counting give
these facts; the order statement follows since p-1=4m,m odd and2^((p-1)/2)=-1.

For c1 the value(n/p)=(-1)^N*xi is common at all active primes. The n-1
role forces it+1; an n-2 role would force it-1. Hence none exists. The
exact denominator restriction implies y|3, so theta1/3 or2/3.
For theta1/3, section1 forces e1. The n-1 prime then implies4|N. The
external R divides n+1, so2^N=-1 modR. An element of order4 times an odd
integer reaches-1 only at exponents2 mod4. Thus N=2 mod4, contradiction.
For theta2/3 use the original mod4/mod16 argument in section2.
NOTICE: no assertion is made that xi or the original fourth phase is0;
we use the exact ratio to remove e before returning to fourth-order data.

For c3, (n/p)=sigma*(-1)^N*xi is common. The n-1 role gives+1 and any
n-2 role would give-1. But the raw theta denominator is prime to3, and
its nontrivial reduced denominator must supply such an n-2 endpoint
prime. Contradiction. Both c branches are exhausted, proving the lemma.

4. ALL SHARED FACTORIZATIONS AT ONCE
For a support S in the theorem, write e=product(q^f_q). At active p,
none of those q equals p, hence
 (e/p)=product((q/p)^f_q)=epsilon^(sum f_q),
independent of p. Apply section3. The same proof handles zero exponents
and empty or singleton actual support. This proves the whole-column claim.
The product sign is the diagonal in(C2)^U. The previous C4 diagonal was
sufficient but stronger. Coarsening succeeds only AFTER the additional
integer collapse; a quadratic character alone cannot separate(1,-1)
when all support primes are1 mod4.

5. A REAL INDUCTION STEP, FOR SUPPORTS RATHER THAN ALL COUNTEREXAMPLES
Fix a finite eligible S and any requested lower bound. Put M=24*product S.
For epsilon+1 prescribe a=1 modulo each p in S; for epsilon-1 prescribe
a=2 modulo each p. Prescribe a=r modulo24 in both cases. CRT gives one
unit class modulo M, because the moduli are pairwise coprime and every
prescribed residue is nonzero. Dirichlet gives a prime q in that class,
larger than the bound and all of S. Then(q/p)=epsilon for every p in S,
using(2/p)=-1 in the negative case. Since p,q are1 mod4, reciprocity gives
(p/q)=(q/p)=epsilon. Therefore S union{q} is eligible. Infinitely many q
work at each step. Repeating produces a strictly increasing infinite
sequence; any finite subset lies in a prefix and satisfies section4.
This is a constructive existence argument with an unbounded terminating
prime search if desired, not a practical bound on the next prime.
It does NOT turn the unresolved arbitrary-support problem into an induction.

6. ACTUAL REMOTE FORMAL INTERFACES AND CLASSICAL INPUTS
Read dev GeneralPowerCharacterLayer.lean, blob
79c32483be14a2333e043f151744877c4ea30fb8: its joint-character kernel equals
powerSubgroup, with quotient exponent/universal properties. Here use k2
and the diagonal product of quadratic characters, then the arithmetic
collapse before passing back to the labelled fourth-order generator.

Also read dev D5/S3/PrimeForms/Splitting/ThreeRingProfileFactorization.lean,
blob890daca76ead377cbe0be08032fc1a07e584bfaa. It actually imports
Mathlib.NumberTheory.LSeries.PrimesInAP and invokes
Nat.forall_exists_prime_gt_and_eq_mod. Official Mathlib documentation for
that theorem and legendreSym.quadratic_reciprocity_one_mod_four was read.
CRT/Dirichlet/reciprocity and the elementary group facts are classical.
No new analytic estimate or p-adic-logarithm theorem is used.
The remote files were read, not recompiled here. They do not certify the
new arithmetic application or the inherited normal form/mixed-support chain.

FORMALIZATION HANDOFF: first the independent ratio-to-gcd divisibilities;
then the branch-sensitive subgroup reduction; the labelled quadratic sign
and order lemma; the synchronized-sign arithmetic contradiction; finite
support products; and finally CRT plus the existing prime-in-progression
interface for the infinite support extension. No private axiom or untested
Lean truth declaration is added. The current environment has no Lean binary.

BOUNDARY. The example S={5,29,53} has nonconstant quadratic signs and is NOT
covered; its full pair subgroup remains a genuine local limitation. General
nonsynchronized supports, unrestricted i3 and the original i4..324 gaps
remain unresolved by this work. New conclusions are written partial proofs.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
import json
from math import comb, gcd, isqrt, prod


@lru_cache(None)
def factors(n: int) -> tuple[tuple[int, int], ...]:
    if n < 1:
        raise ValueError('positive integer required')
    out=[];p=2
    while p*p<=n:
        e=0
        while n%p==0:n//=p;e+=1
        if e:out.append((p,e))
        p=3 if p==2 else p+2
    if n>1:out.append((n,1))
    return tuple(out)


def prime(n: int) -> bool:
    return n>=2 and all(n%p for p in range(2,isqrt(n)+1))


def v2(n: int) -> int:
    if n<=0:raise ValueError('positive integer required')
    return (n&-n).bit_length()-1


def leg(a: int,p: int) -> int:
    if a%p==0:return 0
    t=pow(a%p,(p-1)//2,p)
    assert t in (1,p-1)
    return 1 if t==1 else -1


def quartic(a: int,p: int) -> int:
    assert p%8==5 and a%p
    u=pow(2,(p-1)//4,p); z=pow(a%p,(p-1)//4,p)
    assert pow(u,2,p)==p-1
    return tuple(pow(u,k,p) for k in range(4)).index(z)


def order2(p: int) -> int:
    o=p-1
    for q,_ in factors(o):
        while o%q==0 and pow(2,o//q,p)==1:o//=q
    assert pow(2,o,p)==1
    assert all(pow(2,o//q,p)!=1 for q,_ in factors(o))
    return o


def eligible(S: tuple[int,...]) -> bool:
    if len(set(S))!=len(S) or not all(prime(p) for p in S):return False
    if not S:return True
    if S[0]%24 not in (5,13) or len({p%24 for p in S})!=1:return False
    return len({leg(q,p) for p in S for q in S if p!=q})<=1


def old_diagonal(S: tuple[int,...]) -> bool:
    return all(len({quartic(q,p) for p in S if p!=q})<=1 for q in S)


def ratio_audit(limit: int) -> dict:
    count=0
    for n in range(3,limit+1):
        for j in range(1,n):
            th=Fraction((n-j)*(n-j-1),(n-1)*(n-2));x,D=th.numerator,th.denominator
            assert (2*x)%gcd(n,j)==0
            assert (2*D)%gcd(n-2,j)==0
            assert (n-1)*((D-x)*n+2*x)==D*j*(2*n-1-j)
            count+=1
    thin=[]
    for n in range(4,5001):
        for x in (1,2):
            E=Fraction(4*x*(n-1)*(n-2),3)+1
            if E.denominator!=1:continue
            z=isqrt(E.numerator)
            if z*z!=E or z%2==0:continue
            j=n-(z+1)//2
            if 0<j<n:
                d=gcd(n,j)
                assert (2*x)%d==0 and n%3!=0
                thin.append((n,j,x,d))
    assert (56,11,2,1) in thin and (134,57,1,1) in thin
    return {'unrestricted_actual_ratios':count,'nonempty_thin_controls':thin}


def subgroup(p: int,q: int,rs: tuple[int,...]) -> dict:
    gs=((2%p,2%q),)+tuple((r%p,r%q) for r in rs)
    found={(1,1):(0,)*len(gs)};todo=deque([(1,1)])
    while todo:
        a=todo.popleft()
        for i,g in enumerate(gs):
            b=(a[0]*g[0]%p,a[1]*g[1]%q)
            if b not in found:
                ex=list(found[a]);ex[i]+=1;found[b]=tuple(ex);todo.append(b)
    return found


def group_audit() -> dict:
    S=(5,29,149)
    assert eligible(S) and not old_diagonal(S)
    matrix=[[None if p==q else quartic(q,p) for q in S] for p in S]
    assert matrix==[[None,2,2],[2,None,2],[0,0,None]]
    rows=[];ops=0
    for p,q in combinations(S,2):
        rs=tuple(r for r in S if r not in(p,q))
        K=subgroup(p,q,rs);H=subgroup(p,q,())
        A=((1,2),(2,1))
        a,b=pow(3,-1,p),pow(3,-1,q)
        E=((a,2*b%q),(2*a%p,b))
        B=((1,q-1),(p-1,1))
        assert all(t not in K for t in A+E)
        assert all(t not in H for t in B)
        for u,v in K:
            assert leg(u,p)*leg(v,q)==1
            ops+=1
        rows.append({'p':p,'q':q,'K_size':len(K),'H_size':len(H),
                     'K_index':(p-1)*(q-1)//len(K),
                     'sign_targets_in_K':[t in K for t in B]})
    assert [r['K_index'] for r in rows]==[4,2,2]
    assert pow(2,10,5)*pow(29,3,5)%5==1
    assert pow(2,10,149)*pow(29,3,149)%149==148
    n=29*(1<<102);j=5*29*149
    assert n>=2*j and gcd(n,j)==29 and n%5==1 and n%149==148
    assert Fraction((n-j)*(n-j-1),(n-1)*(n-2))!=Fraction(1,3)
    assert vpbinom(n,3,3)>0 and vpbinom(n,j,3)>0
    assert not eligible((5,29,53))
    return {'strict_support':S,'quartic_matrix':matrix,'pairs':rows,
            'quadratic_kernel_elements_checked':ops,
            'old_target_is_admitted_but_new_branch_forbids_its_generator':True,
            'noncounterexample_control':{'n':n,'j':j,'common_prime':3}}


PREFIXES=(
 (5,1,(5,101,26261,1220086061)),
 (5,-1,(5,197,2957,183496637)),
 (13,1,(13,157,73477,8997993421)),
 (13,-1,(13,613,278917,264500059189)),
)


def extension_audit() -> dict:
    out=[];pair_checks=0
    for r,eps,S in PREFIXES:
        assert all(prime(p) and p%24==r for p in S)
        trail=[]
        for i,q in enumerate(S[1:],1):
            old=S[:i];M=prod(old);a=1 if eps==1 else 2
            A=(a+M*((r-a)*pow(M,-1,24)%24))%(24*M)
            assert gcd(A,24*M)==1 and q>A-24*M and q>max(old)
            assert q%(24*M)==A
            for p in old:
                assert q%p==a and leg(q,p)==eps and leg(p,q)==eps
                pair_checks+=2
            trail.append({'new_prime':q,'unit_class':A,'modulus':24*M})
        assert eligible(S)
        out.append({'r':r,'epsilon':eps,'prefix':S,'steps':trail,
                    'quartic_synchronized':old_diagonal(S)})
    return {'four_explicit_prefixes':out,'directed_reciprocity_checks':pair_checks,
            'infinite_extension_uses_Dirichlet_not_finite_sampling':True}


def sign_audit() -> dict:
    supports=((5,29,149),(5,53,173,797),(13,61,757),(13,37,109))
    count=nonquartic=oddgcd=0
    for S in supports:
        assert eligible(S)
        eps=leg(S[1],S[0])
        for exponents in product(range(4),repeat=len(S)):
            U=[p for p,f in zip(S,exponents) if f==0]
            if len(U)<2:continue
            e=prod(p**f for p,f in zip(S,exponents))
            vals=[leg(e,p) for p in U]
            assert vals==[eps**sum(exponents)]*len(U)
            phases=[quartic(e,p) for p in U]
            nonquartic+=len(set(phases))>1
            oddgcd+=e>1;count+=1
    return {'shared_factor_allocations':count,'genuine_odd_shared_factors':oddgcd,
            'quadratic_synchronized_but_not_quartic':nonquartic}


def vpbinom(n: int,j: int,p: int) -> int:
    a=p;v=0
    while a<=n:
        v+=n//a-j//a-(n-j)//a;a*=p
    return v


def carry_count(n: int,j: int,p: int) -> int:
    a,b,carry,v=j,n-j,0,0
    while a or b or carry:
        carry=(a%p+b%p+carry)//p;v+=carry;a//=p;b//=p
    return v


@lru_cache(None)
def cn3_primes(n: int) -> tuple[int,...]:
    out=set()
    for m in (n,n-1,n-2):out.update(p for p,_ in factors(m))
    return tuple(sorted(p for p in out if p>=3 and vpbinom(n,3,p)>0))


def witness(n: int,j: int,direct: bool=False) -> int:
    ps=cn3_primes(n)
    p=next((p for p in ps if vpbinom(n,j,p)>0),None)
    assert p is not None,(n,j)
    assert carry_count(n,j,p)==vpbinom(n,j,p)>0
    if direct:
        assert comb(n,j)%p==0 and comb(n,3)%p==0
    return p


def original_audit(nmax: int) -> dict:
    columns=[];pairs=direct=0
    for j in range(4,nmax//2+1):
        S=tuple(p for p,_ in factors(j) if p>2)
        if eligible(S):columns.append(j)
    for j in columns:
        for n in range(2*j,nmax+1):
            witness(n,j,n<=160);pairs+=1;direct+=n<=160
    targeted=[]
    for S in ((5,29,149),(5,53,173,797),(13,61,757)):
        for r in S:
            for f in (1,2,3):
                j=prod(S)*r**(f-1);e=r**f
                N=max(4,((2*j-1)//e).bit_length())
                for offset in range(3):
                    n=e*(1<<(N+offset))
                    assert n>=2*j and gcd(n,j)==e
                    p=witness(n,j)
                    U=[q for q in S if q!=r]
                    assert len({leg(e,q) for q in U})==1
                    targeted.append({'S':S,'f':f,'n':n,'j':j,'gcd':e,'witness':p,
                                     'old_quartic_local_condition':len({quartic(e,q) for q in U})==1})
    return {'nmax':nmax,'small_box_columns':len(columns),'small_box_pairs':pairs,
            'direct_binomial_checks':direct,'targeted_three_or_four_prime_pairs':len(targeted),
            'targeted_pairs_outside_old_quartic_local_condition':sum(not r['old_quartic_local_condition'] for r in targeted),
            'targeted':targeted,'regression_is_not_unbounded_proof':True}


def symbolic_audit() -> dict:
    try:import sympy as s
    except ImportError as exc:raise SystemExit('--symbolic requires sympy') from exc
    n,j,D,x=s.symbols('n j D x')
    eq=D*(n-j)*(n-j-1)-x*(n-1)*(n-2)
    res=(n-1)*((D-x)*n+2*x)-D*j*(2*n-1-j)
    assert s.expand(eq-res)==0
    assert s.expand(eq.subs({n:0,j:0}))==-2*x
    assert s.expand(eq.subs({n:2,j:0}))==2*D
    assert s.expand(res.subs({D:3,x:1})-(2*(n-1)*(n+1)-3*j*(2*n-1-j)))==0
    assert s.expand(res.subs({D:3,x:2})-((n-1)*(n+4)-3*j*(2*n-1-j)))==0
    return {'original_residual':True,'both_gcd_divisibility_remainders':True,'exceptional_target_residuals':True}


def main() -> None:
    ap=argparse.ArgumentParser(description='Exact self-audit of the quadratic-collapse proof.')
    ap.add_argument('--nmax',type=int,default=1200)
    ap.add_argument('--ratio-nmax',type=int,default=250)
    ap.add_argument('--symbolic',action='store_true')
    args=ap.parse_args()
    if args.nmax<8 or args.ratio_nmax<4:ap.error('positive nonempty test ranges required')
    result={'whole_erdos699_solved':False,'independent_review':False,'new_Lean_verification':False,
            'ratio':ratio_audit(args.ratio_nmax),'group':group_audit(),
            'extension':extension_audit(),'signs':sign_audit(),'original':original_audit(args.nmax)}
    if args.symbolic:result['symbolic']=symbolic_audit()
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
