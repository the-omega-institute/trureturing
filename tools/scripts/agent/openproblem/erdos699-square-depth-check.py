#!/usr/bin/env python3
"""Erdos 699: eliminate three complete denominator depths.

Continuation of issue #9670 and PR #9769 from commit
 a86c9013249cc64f6dbd5a0b8035e93d2af28d4b.

THE STANDALONE LEMMA. Let N>=3 be odd and a=1+v3(N-1) belong to {2,3,4}.
Put n=2^N, D=3^a. There is no integer j with 3<j<=n/2 such that
 theta=(n-j)(n-j-1)/((n-1)(n-2)) has reduced denominator D.
This lemma uses only the finite arithmetic certificate below and periodicity.
No inherited cubic or discriminant claim is a premise of this lemma.

ORIGINAL-PROBLEM COROLLARY. Combining the lemma with the previously deposited
single-row theorem in erdos699-single-row-check.py, any i=3 counterexample
with j=2^b*3^s*p^t (p>=5 prime, b>=0, s,t>=1) must satisfy
 n=2^o, o=ord_p(2)=1 mod162, t=v_p(2^o-1),
 a=1+v3(o-1)>=5, s>=a, gcd(n,j)=2^b.
Thus ALL such columns hold for every n>=2j if o is not1 mod162.
In particular ALL j=2^b*81*p^t columns are now covered for arbitrary p,b,t.
Together with the prior single-row theorem, s=1,2,3,4 are all covered.
The p=3 overlap follows from the previously deposited prime-power theorem.
The unrestricted union over o=1 mod162 is not proved empty.

PROOF OF THE STANDALONE LEMMA.
Write theta=x/D in lowest terms. With m=n-j, m>=n/2 and m<n-1, we have
 n/(4(n-1))<=theta<1; hence D/4<x<D and 3 does not divide x.
Completing the square gives the NECESSARY INTEGER SQUARE
 (2m-1)^2 = E(N,x,D) = 1+4*x*(2^N-1)*(2^N-2)/D.           (1)
Because N is odd, elementary lifting gives v3(2^N-2)=1+v3(N-1)=a,
so E is an integer. Lifting follows by binomial expansion applied to
4^((N-1)/2)-1, with v3(4-1)=1, and is also implicit in the assumed ratio.

For depth a the certificate specifies an even period L divisible by2*3^a
and a list of odd primes q!=3. Every listed q is checked by deterministic
trial division, and pow(2,L,q)=1 is checked exactly. The COMPLETE residue
domain is
 R_a={r:0<=r<L, r=1 mod(2*3^(a-1)), r!=1 mod(2*3^a)}.
It records precisely odd N with v3(N-1)=a-1, not a finite prefix of N.
For every possible numerator x and every r in R_a, at least one listed q
has E(r,x,D) a quadratic nonresidue modulo q. Formula(1) and 2^L=1 modq
show that the SAME q excludes EVERY exponent N=r+kL, k>=0.
Thus an integer square in(1) is impossible. All divisions modq are legal
because q!=3. This proves the lemma for unbounded N and j.

EXACT FINITE CERTIFICATE. The ordered prime lists and the numbers of cases
first rejected by each prime are:
 a2: L36, primes73,13,37,19; first-rejection counts10,3,2,1 (16 total).
 a3: L324, primes279073,2593,262657,87211,37;
     counts84,44,25,12,3 (168 total).
 a4: L972, primes1459,2593,71119,135433,487;
     counts280,126,48,20,6 (480 total).
There are664 complete numerator/residue pairs, not664 original n samples.
Primality, the asserted periods, nonresidues, coverage and counts are all
recomputed below. Nonresidues are independently checked by direct square
residue tables, not solely by Euler's criterion. Formula(1) is also checked
using exact integer division, independently of modular inversion.

DEPENDENCY AND SCOPE OF THE COROLLARY.
The fetched single-row module proves that any counterexample in the stated
3-p family already has N=o=1 mod6, t=v_p(2^o-1), a>=2, s>=a and denominator
D=3^a. Our lemma removes a2,3,4, so a>=5, 81 divides o-1, and o odd gives
162 divides o-1. If s=4, s>=a is impossible. This is a written dependent
partial theorem; the standalone lemma does not independently certify the
prior normal form, prime-power exclusion or cancellation arguments.
No original i>=4 case, all-699 solution, historical priority, independent
review, Lean proof or CI claim is made.

WHY THIS IS NOT YET INDUCTION OVER ALL DEPTHS.
One must construct a lower-depth counterexample while preserving integer
squarehood (and, for an original descent, the binomial hypotheses). No such
map has been proved here. Checking three complete depths does not establish
an induction step. In fact all witness periods divide972. At N=973 and
D729, n=2 modulo EVERY listed witness prime, so E(N,x,D)=1 modulo ALL of
them for every x. For example x184 is reduced and in the required interval;
it passes this entire witness-prime set. It is NOT a counterexample: its
actual E is separately checked to be nonsquare. This exact control shows
that the same fixed certificate cannot simply be asserted to handle all
higher depths. Higher depths require a new argument or new certificates.

The code below is an exact self-audit and finite proof certificate. The
optional original-binomial regression is separated from the proof lemmas.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import lru_cache
from fractions import Fraction
from math import comb, gcd, isqrt
import hashlib
import json

CERTIFICATES = {
    2: (36, (73, 13, 37, 19), (10, 3, 2, 1)),
    3: (324, (279073, 2593, 262657, 87211, 37), (84, 44, 25, 12, 3)),
    4: (972, (1459, 2593, 71119, 135433, 487), (280, 126, 48, 20, 6)),
}

@lru_cache(None)
def prime(p: int) -> bool:
    return p >= 2 and (p == 2 or (p % 2 and all(p % d for d in range(3,isqrt(p)+1,2))))

@lru_cache(None)
def factors(n: int) -> tuple[tuple[int,int], ...]:
    if n < 1: raise ValueError('factor input must be positive')
    out=[]; p=2
    while p*p <= n:
        e=0
        while n%p == 0: n//=p; e+=1
        if e: out.append((p,e))
        p=3 if p==2 else p+2
    if n>1: out.append((n,1))
    return tuple(out)

def vp(n: int, p: int) -> int:
    if not n or p<2: raise ValueError('nonzero integer and p>=2 required')
    n=abs(n); a=0
    while n%p == 0: n//=p; a+=1
    return a

@lru_cache(None)
def order2(p: int) -> int:
    if p<=2 or not prime(p): raise ValueError('odd prime required')
    o=p-1
    for r,_ in factors(o):
        while o%r==0 and pow(2,o//r,p)==1: o//=r
    assert pow(2,o,p)==1
    assert all(pow(2,o//r,p)!=1 for r,_ in factors(o))
    return o

@lru_cache(None)
def squares_mod(p: int) -> bytearray:
    table=bytearray(p)
    for y in range(p//2+1): table[y*y%p]=1
    return table

def square_candidate(N: int, x: int, D: int) -> int:
    n=1<<N
    numerator=4*x*(n-1)*(n-2)
    assert numerator%D==0
    return 1+numerator//D

def proof_certificate() -> dict:
    rows=[]; total=0; witness_records=[]; lift_checks=0
    for a,(period,ps,expected) in CERTIFICATES.items():
        D=3**a
        assert period%(2*D)==0
        assert all(prime(p) and p!=3 and pow(2,period,p)==1 for p in ps)
        residues=[r for r in range(period) if (r-1)%(2*3**(a-1))==0
                  and (r-1)%(2*3**a)!=0]
        numerators=[x for x in range(D//4+1,D) if x%3]
        counts=Counter()
        for x in numerators:
            for r in residues:
                assert r>=3 and r%2==1 and 1+vp(r-1,3)==a
                integer_E=square_candidate(r,x,D)
                witness=None
                for p in ps:
                    nmod=pow(2,r,p)
                    e=(1+4*x*(nmod-1)*(nmod-2)*pow(D,-1,p))%p
                    assert e==integer_E%p
                    euler_nonresidue=(pow(e,(p-1)//2,p)==p-1)
                    enumeration_nonresidue=not bool(squares_mod(p)[e])
                    assert euler_nonresidue==enumeration_nonresidue
                    if euler_nonresidue:
                        witness=(p,e); counts[p]+=1; break
                assert witness is not None,(a,x,r)
                p,e=witness
                witness_records.append([a,x,r,p,e])
                for k in (1,2,17):
                    N=r+k*period
                    assert 1+vp(N-1,3)==a
                    assert pow(2,N,p)==pow(2,r,p)
                    lift_checks+=1
                total+=1
        assert tuple(counts[p] for p in ps)==expected
        rows.append({'depth':a,'denominator':D,'period':period,
                     'numerators':numerators,'exponent_residues':residues,
                     'primes':list(ps),'first_rejections':[counts[p] for p in ps],
                     'complete_pairs':len(numerators)*len(residues)})
    assert total==664
    payload=json.dumps(witness_records,separators=(',',':')).encode()
    return {'levels':rows,'complete_pairs':total,'period_lift_regressions':lift_checks,
            'witness_sha256':hashlib.sha256(payload).hexdigest(),
            'primality_method':'deterministic trial division',
            'nonresidue_methods':['Euler criterion','explicit square-residue table'],
            'unbounded_coverage_reason':'proved periodicity, not sampled exponents'}

def vpbinom(n: int,j: int,p: int)->int:
    out=0; power=p
    while power<=n:
        out+=n//power-j//power-(n-j)//power
        power*=p
    return out

def carries(n: int,j: int,p: int)->int:
    a,b,c,out=j,n-j,0,0
    while a or b or c:
        c=(a%p+b%p+c)//p; out+=c
        a//=p; b//=p
    return out

def regression(nmax: int)->dict:
    columns=[]; new_columns=[]; old_single_row_columns=[]
    for j in range(4,nmax//2+1):
        f=dict(factors(j)); ps=[p for p in f if p>=5]
        if f.get(3,0)<1 or len(ps)!=1: continue
        p=ps[0]; o=order2(p)
        if o%162==1 and f[3]>4: continue
        columns.append((j,p,f[3],o))
        if o%6==1 and o%162!=1 and f[3]>=4:
            new_columns.append(j)
        if o%6!=1: old_single_row_columns.append(j)
    pairs=direct=newpairs=0
    cn3_factors={n:[p for p,_ in factors(n*(n-1)*(n-2)//6) if p>=3]
                 for n in range(8,nmax+1)}
    newset=set(new_columns)
    for j,p,s,o in columns:
        for n in range(2*j,nmax+1):
            witness=next((q for q in cn3_factors[n] if vpbinom(n,j,q)>0),None)
            assert witness is not None,(n,j)
            assert vpbinom(n,3,witness)>0
            assert carries(n,j,witness)==vpbinom(n,j,witness)>0
            if n<=300:
                assert comb(n,j)%witness==0; direct+=1
            pairs+=1; newpairs+=j in newset
    return {'nmax':nmax,'column_count':len(columns),'original_pairs':pairs,
            'direct_binomial_checks':direct,
            'columns_outside_old_order_and_s2_s3_tests':new_columns,
            'pairs_in_those_columns':newpairs,
            'not_a_completion_percentage':True}

def independent_identity_checks(nmax: int)->dict:
    count=0
    for n in range(8,nmax+1):
        for j in range(4,n//2+1):
            theta=Fraction((n-j)*(n-j-1),(n-1)*(n-2))
            x,D=theta.numerator,theta.denominator
            assert Fraction(1,4)<theta<1
            assert (2*(n-j)-1)**2==1+4*x*((n-1)*(n-2))//D
            count+=1
    return {'original_square_identity_pairs':count}

def beyond_certificate_control()->dict:
    N,x,D=973,184,729
    assert D//4<x<D and gcd(x,D)==1 and 1+vp(N-1,3)==6
    ps=sorted({p for _,primes,_ in CERTIFICATES.values() for p in primes})
    E=square_candidate(N,x,D)
    assert all(pow(2,N,p)==2 and E%p==1 for p in ps)
    r=isqrt(E)
    assert r*r<E<(r+1)*(r+1)
    return {'N':N,'x':x,'D':D,'depth':6,
            'all_current_witness_primes_see_square_residue_one':True,
            'actual_E_is_nonsquare':True,'is_original_counterexample':False,
            'meaning':'fixed finite witness set does not establish arbitrary-depth induction'}

def illustrative_large_prime()->dict:
    p=1113491139767; o=79
    assert prime(p) and prime(o) and pow(2,o,p)==1 and pow(2,1,p)!=1
    assert pow(2,o,p*p)!=1
    N=o; n=1<<N; P=p; Q=(n-1)//P; D=3**(1+vp(N-1,3))
    assert P*Q==n-1 and Q>1
    assert 4*(n-2)<D*P*P and n-2<2*D*Q*Q
    assert o%6==1 and o%162!=1 and D==9
    return {'p':p,'order':o,'lambda':1,'D':D,'Q':Q,
            'passes_previous_two_coarse_gaps':True,
            'excluded_by_new_unbounded_depth_lemma':True,
            'entire_family':'j=2^b*3^s*p^t, all b>=0,s,t>=1,n>=2j',
            'not_claimed_to_pass_all_old_filters':True}

def targeted_columns()->dict:
    out=[]
    for p in (127,1801,8191):
        assert prime(p) and order2(p)%6==1 and order2(p)%162!=1
        j=81*p
        cases=[]
        for offset in (0,1,2,3,5,8,16,31):
            n=2*j+offset
            q=next((q for q,_ in factors(n*(n-1)*(n-2)//6)
                    if q>=3 and vpbinom(n,j,q)>0),None)
            assert q is not None
            assert carries(n,j,q)==vpbinom(n,j,q)>0 and vpbinom(n,3,q)>0
            cases.append([n,q])
        out.append({'p':p,'order':order2(p),'j':j,'n_and_shared_prime':cases})
    return {'targeted_columns':out,'exact_valuation_checks':24,
            'purpose':'regression outside the old order/s2/s3 predicates; not priority evidence'}

def symbolic_audit()->dict:
    try: import sympy as S
    except ImportError as exc: raise SystemExit('--symbolic needs sympy') from exc
    n,j,x,D=S.symbols('n j x D',nonzero=True)
    theta=(n-j)*(n-j-1)/((n-1)*(n-2))
    assert S.cancel((2*(n-j)-1)**2-(1+4*theta*(n-1)*(n-2)))==0
    assert S.expand(4*(n-j)*(n-j-1)-n*(n-2)
                    -(n-2*j)*(3*n-2*j-2))==0
    # Independently derive the completed-square residual under the ratio equation.
    ratio=D*(n-j)*(n-j-1)-x*(n-1)*(n-2)
    residual=D*(2*(n-j)-1)**2-D-4*x*(n-1)*(n-2)
    assert S.expand(residual-4*ratio)==0
    return {'symbolic_completed_square_and_ratio_residual':True}

def main()->None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--nmax',type=int,default=1200)
    ap.add_argument('--identity-nmax',type=int,default=200)
    ap.add_argument('--symbolic',action='store_true')
    args=ap.parse_args()
    if args.nmax<8 or args.identity_nmax<8: ap.error('bounds must be >=8')
    report={'scope':'standalone depths2,3,4; dependent 3-p order1mod162 restriction',
            'certificate':proof_certificate(),
            'identity':independent_identity_checks(args.identity_nmax),
            'regression':regression(args.nmax),
            'induction_boundary':beyond_certificate_control(),
            'large_prime_example':illustrative_large_prime(),
            'targeted_original_columns':targeted_columns(),
            'arbitrary_depth_induction_proved':False,
            'whole_erdos699_solved':False,'independent_review':False}
    if args.symbolic: report['symbolic']=symbolic_audit()
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
