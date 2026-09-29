#!/usr/bin/env python3
r"""Erdos 699: shared-exponent prime-square lifting closes every 11-23 column.

CONTINUITY AND SCOPE
Read issue #9670 / Draft PR #9769 at
99f3ea8ac33ac01310c6ebdc1546af4cfd233fe3. New written partial theorem:
for all b>=0,s,t>=1 and j=2^b*11^s*23^t, every n>=2j has an odd prime
common to C(n,3) and C(n,j). All four integer parameters are unrestricted.
This does not settle arbitrary i=3, indices4..324, or WSS. Independent
review and full Lean formalization remain outstanding. The proof uses
explicitly inherited number-theoretic premises and the complete 8064-case
periodic arithmetic lemma below. Regression is separate from that lemma.

READ REMOTE CONNECTIONS
Loning's merged #11272, FIBONACCI_ATOMIC_RELATION_GENERATION.md §§115.2,
115.4,115.5 (head277f3f1a, blob0d715c89), keeps the actual affine lift fiber
and intersects all previous conditions on ONE source. WSS #9761 source
D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod.lean at d1ee521e, blob
c197fa923c43e4cae9f1ab28866f0185966d2643, proves the exact first-return
matrix and period tau*p^max(a-h,0), retaining h rather than assuming h1.
We reuse that proof mechanism in scalar units, not its golden-unit theorem
as a theorem about2. A base2 Wieferich condition is not a WSS condition.
The original denominator gap is read from dev, blob982eb26f0fcd5b1363961f8023f2558bee790855.
None of those sources is recompiled by this script. Their individual
formalization does not certify this new whole-column conclusion.

1. GENERAL AFFINE LIFT WITH RETAINED HISTORY
Let p be prime, h>=1, and let a,c,delta be p-units with
 a^m=1+p^h U,  c*a^r=delta+p^h V
for integers m>0,r>=0,U,V. For every z>=0, binomial expansion yields
 c*a^(r+m*z)=delta+p^h*(V+delta*U*z) mod p^(h+1).        (L)
Terms of degree>=2 vanish since2h>=h+1. Let Z be the set of exponent
multipliers satisfying ALL other retained conditions, and B its image
modulo p. A lift exists for some z in Z iff B intersects
{z:V+delta*U*z=0 modp}. For a known over-approximation of B only the
empty-intersection obstruction is inferred.
If the intersection is empty, EVERY such actual exponent has exact
valuation h. If U=0 modp, do not invert it: the lift locus is all F_p or
empty according as V=0 or not. This retains the exceptional flat branch.
The phrase 'exists among residues' does not assert that any unrelated
integer or binomial condition has an actual solution.

A useful return-depth corollary: let a>1,p,q be distinct odd primes not
dividing a, m=ord_p(a), h=v_p(a^m-1), and p|ord_q(a). If p|a^N-1 and
q|a^(N-1)-1, then p does not divide N and v_p(a^N-1)=h. If q|a^N-1 and
p|a^(N-1)-1, then p|N and v_p(a^(N-1)-1)=h. Here N>=2. The order
conditions give the p-divisibility of N or N-1; m|p-1, and the elementary
lifting formula v_p((a^m)^k-1)=h+v_p(k) gives the stated depths. That
formula follows by the binomial theorem: a multiplier prime to p keeps
the leading term; multiplication of the exponent by p raises the depth
exactly one for odd p. No assumption h=1 is made in this general lemma.

2. INHERITED ORIGINAL-BINOMIAL INTERFACE
Assume H: j=2^b11^s23^t, s,t>=1, 3<j<=n/2, and the two binomials have no
common odd prime. The committed normalized-cubic/mixed-support chain
(erdos699-mixed-support-check.py and the main theory §§2-5) supplies:
 n=c*2^N, c in{1,3}, N>=b+2, n>=32;
 one of11,23 divides n-1 and the other divides neither n nor n-1;
 theta=(n-j)(n-j-1)/((n-1)(n-2))=x/D reduced, 0<theta<1,
 D|3z, with every prime of z dividing j but not n(n-1).
The first two facts follow because the two distinct mixed-support roles
exhaust the two odd primes of j; hence gcd(n,j)=2^b. The bound j<=n/2
also gives D/4<x<D. The inherited normalized-cubic and mixed-support
proofs retain their separate review obligations; no new checker is a
proof of those premises from scratch. This result does not use the
analytic3-p theorem, its scan, or any Chebotarev theorem.

A low-digit consequence is proved directly here. For ell>=5 with
ell^h||(n-rho), rho1 or2, ell divides C(n,3). Under H, Legendre's
nonnegative summands for v_ell C(n,j) all vanish, so
 j mod ell^h <= n mod ell^h = rho.
If ell divides j, this forces ell^h|j. If rho1 and ell does not divide j,
it forces ell^h|j-1. The same rho1 statement holds for ell3 when its
exponent in n-1 is at least2; exponent1 is omitted because C(n,3) loses
one3. Put eta3 if v3(n-1)=1, else eta1. All complete prime powers of
(n-1)/eta must therefore be allocated to j or j-1. This argument keeps
full prime powers; a merely mod-prime assertion is insufficient.

3. FOUR CROSS-PRIME CAPS, ALL WITH THE SAME N
Exact local data: ord_11(2)=10, ord_23(2)=11,
2^8=3 mod11 and mod23; 2^10=1+5*11 mod121.
The order modulo121 is110: reduction requires a multiple of10 and the
nonzero slope5 makes the first return occur at multiplier11.
Both roots 2^22=1/3 and 2^23=2/3 modulo121 are checked exactly.

Write n=c*2^N. The complete table of necessary classes is:
 c | p|n-1 | q|n-2 | N mod110 | exact capped valuation
 1 |   11  |   23  |   100    | v11(n-1)=1
 3 |   11  |   23  |    92    | v11(n-1)=1
 1 |   23  |   11  |    11    | v11(n-2)=1
 3 |   23  |   11  |     3    | v11(n-2)=1.
The putative 121 lifts require, respectively, N=0,22,1,23 mod110,
whose residues modulo11 are0,0,1,1. The23 conditions instead require
N=1,4,0,3 mod11. Every intersection is empty.
Equivalently, in (L) at p11,m10,h1,U5, the four (c,r,delta,V,z mod11)
rows are(1,0,1,0,10),(3,2,1,1,9),(1,1,2,0,1),(3,3,2,2,0).
The lift residuals are6,2,10,2 modulo11, all nonzero. Ordinary mod11
and mod23 tests are compatible; it is their joint 121 lift that fails.

4. CLOSE THE ORIENTATION 11|(n-1),23|(n-2)
Let h=v23(n-2). Low digits force23^h|j, and the raw theta numerator is a
23-unit, so D is23^h or3*23^h (the latter only potentially when c1).
The cap gives v11(n-1)=1. Put L=eta*11<=33, R=(n-1)/L. The low-digit
allocation above gives R|j-1, hence j=1+mR, m>0,2m<L. Also
 23^h | m(n-2)-L*j = -(m+L).
Thus23^h<=m+L<3L/2<=99/2, forcing h1. If L11 this already contradicts
23<=m+L<33/2. Otherwise L33,D<=69. The exact premises of the remote
Erdos699DenominatorGap theorem now hold with numerator x, so
 4(n-2)<D*L^2<=69*33^2=75141.
Hence n<=18787. But the table requires N>=100 for c1 or N>=92 for c3,
contradiction. No original n cutoff was assumed; the bound is derived.

5. CLOSE THE REVERSED ORIENTATION AND THE NO-n-2 BRANCH
If23|n-1 and11|n-2, the cap gives v11(n-2)=1. The numerator is an11-unit;
the denominator-support condition gives D11 or33 for c1, D11 for c3.
The exponent class is N11 mod110 for c1, N3 mod110 for c3.

If neither endpoint prime divides n-2, c3 is impossible: the nontrivial
raw denominator is prime to3 and must supply an exterior endpoint prime
of n-2. For c1, D|3 and0<theta<1 force theta1/3 or2/3. Their exact
residuals are2(n-1)(n+1)=3j(2n-1-j) and
(n-1)(n+4)=3j(2n-1-j). If11|n-1, the exterior23 must divide n+1 or n+4.
Its order11 is odd, so neither2^N=-1 nor2^(N-2)=-1 modulo23 is possible.
If23|n-1, the exterior11 gives N55 mod110 for theta1/3, or N77 mod110
for theta2/3. These and the reversed orientation are EXACTLY the five
cases of the finite certificate below.

For all cases, completing the original square requires
 E(c,N,x,D)=1+4*x*(c*2^N-1)*(c*2^N-2)/D=(2*(n-j)-1)^2. (S)
Use period27720, divisible by110. The full numerator/exponent domains are
 c1,D11,N11 mod110:8*252=2016 pairs;
 c1,D33,N11 mod110:14*252=3528 pairs;
 c3,D11,N3 mod110:8*252=2016 pairs;
 c1,D3,x1,N55 mod110:252 pairs;
 c1,D3,x2,N77 mod110:252 pairs.
All8064 pairs have an explicit quadratic-nonresidue witness in the22-prime
list below. Each witness is prime, coprime to D, and satisfies2^27720=1.
Hence one finite residue case excludes EVERY exponent in that class,
not just N<27720. Modular division does not presume a rational E is an
integer; an actual original j would make (S) an integer square, which
must remain a square modulo every witness prime. The implementation
verifies each case by Euler criterion and a separately computed complete
square-residue set. All numerator candidates, branches and periods are
exhausted. This proves the whole11-23 family, conditional only on the
explicit inherited interface, with no unexamined finite exceptions.

FORMALIZATION AND LIMITS
Formalize (L) at general first-return depth, keeping the zero-slope branch;
then its intersection with the common exponent conditions; original
prime-power allocations; composition with the already formal denominator
gap; and the five decidable periodic-square certificates. The golden
matrix theorem and loning's projective affine model motivate the shared
interface but are not interchangeable with the scalar theorem. WSS is
not solved or strengthened by a claimed new exclusion of golden primes.
No Lean/frozen source, CI setting, or whole-solution count is changed.
This result directly removes one previously unresolved two-prime family
without3, not merely a homogeneous-support existence construction.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from math import comb, gcd, isqrt

PERIOD = 27720
WITNESSES = (5,7,13,17,19,29,31,37,41,43,61,67,71,73,109,113,181,199,241,353,397,463)
# c,D,exponent residue modulo110, explicit numerators or None for full reduced interval
CASES = ((1,11,11,None),(1,33,11,None),(3,11,3,None),(1,3,55,(1,)),(1,3,77,(2,)))
EXPECTED = (2016,3528,2016,252,252)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def prime(p: int) -> bool:
    return p >= 2 and all(p % d for d in range(2,isqrt(p)+1))


def valuation(n: int, p: int) -> int:
    if n == 0 or not prime(p):
        raise ValueError('finite valuation requires nonzero n and prime p')
    n=abs(n); v=0
    while n % p == 0:
        n//=p; v+=1
    return v


def factor(n: int) -> dict[int,int]:
    if n < 1:
        raise ValueError('positive integer required')
    ans={}; p=2
    while p*p<=n:
        while n%p==0:
            ans[p]=ans.get(p,0)+1; n//=p
        p=3 if p==2 else p+2
    if n>1: ans[n]=1
    return ans


def order2(m: int) -> int:
    require(m>1 and m%2==1,'odd modulus')
    x=1
    for o in range(1,m+1):
        x=x*2%m
        if x==1:return o
    raise AssertionError('unit failed to return')


def certificate() -> dict:
    require(PERIOD%110==0,'period must retain original exponent classes')
    square_sets={q:{a*a%q for a in range(q)} for q in WITNESSES}
    orders={q:order2(q) for q in WITNESSES}
    for q in WITNESSES:
        require(prime(q) and PERIOD%orders[q]==0,'prime-period certificate')
        for z in range(q):
            require((z in square_sets[q]) == (z==0 or pow(z,(q-1)//2,q)==1),
                    'independent Euler/square table agreement')
    stream=sha256(); stream2=sha256(); total=0; rows=[]; lifts=0
    for case_id,(c,D,r,specified) in enumerate(CASES):
        xs=specified if specified else tuple(x for x in range(D//4+1,D) if gcd(x,D)==1)
        require(all(D<4*x and x<D and gcd(x,D)==1 for x in xs),'full numerator domain')
        inv={q:pow(D,-1,q) for q in WITNESSES}
        counts=Counter(); count=0
        residues={q:c*pow(2,r,q)%q for q in WITNESSES}
        step={q:pow(2,110,q) for q in WITNESSES}
        for N in range(r,PERIOD,110):
            for x in xs:
                first=second=None
                for q in WITNESSES:
                    n=residues[q]
                    v=(1+4*x*(n-1)*(n-2)*inv[q])%q
                    if pow(v,(q-1)//2,q)==q-1:
                        first=(q,v); break
                # Independent residue construction and full square-set membership.
                for q in WITNESSES:
                    n=c*pow(2,N,q)%q
                    v=(D+4*x*(n-1)*(n-2))*pow(D,-1,q)%q
                    if v not in square_sets[q]:
                        second=(q,v); break
                require(first is not None and first==second,'uncovered or mismatched finite case')
                q,v=first
                for jump in (1,7):
                    n2=c*pow(2,N+jump*PERIOD,q)%q
                    require((1+4*x*(n2-1)*(n2-2)*inv[q])%q==v,'period lift')
                    lifts+=1
                payload=f'{case_id},{N},{x},{q},{v}\n'.encode()
                stream.update(payload); stream2.update(f'{case_id},{N},{x},{second[0]},{second[1]}\n'.encode())
                counts[q]+=1; count+=1
            residues={q:residues[q]*step[q]%q for q in WITNESSES}
        require(count==EXPECTED[case_id],'incomplete finite domain')
        rows.append({'c':c,'D':D,'N_mod110':r,'numerators':list(xs),
                     'cases':count,'first_rejections':dict(sorted(counts.items()))})
        total+=count
    require(total==8064 and stream.digest()==stream2.digest(),'complete certificate binding')
    return {'period':PERIOD,'witness_orders':orders,'cases':rows,'total':total,
            'period_lift_regressions':lifts,'two_engines_witness_sha256':stream.hexdigest()}


def local_lifts() -> dict:
    require(order2(11)==10 and order2(121)==110 and order2(23)==11,'exact orders')
    require(pow(2,8,11)==3 and pow(2,8,23)==3,'base logs')
    require(pow(2,10,121)==56,'first-return slope')
    require(3*pow(2,22,121)%121==1 and 3*pow(2,23,121)%121==2,'square-level logs')
    rows=((1,1,2,0,10,100),(3,1,2,2,9,92),(1,2,1,1,1,11),(3,2,1,3,0,3))
    out=[]; nchecks=0
    for c,delta11,delta23,r,z0,residue in rows:
        V=(c*2**r-delta11)//11
        affine=(V+delta11*5*z0)%11
        require(affine!=0,'other-prime history must avoid lifted root')
        actual=[N for N in range(110) if c*pow(2,N,11)%11==delta11 and
                c*pow(2,N,23)%23==delta23]
        require(actual==[residue],'complete initial simultaneous classes')
        for N in range(residue,11001,110):
            require((N-r)%10==0 and ((N-r)//10)%11==z0,'same lift parameter')
            n=c*(1<<N)
            require(valuation(n-delta11,11)==1,'exact capped depth')
            nchecks+=1
        out.append({'c':c,'delta11':delta11,'delta23':delta23,
                    'N_mod110':residue,'z_mod11':z0,'lift_residual':affine})
    # General-depth identity, including nonzero/zero slopes, all residue digits.
    affine_checks=flat=0
    for p in (3,5,7,11,13):
        for h in (1,2,3):
            mod=p**(h+1)
            for U in range(p):
                for V in range(p):
                    delta=2
                    a=1+p**h*U; c=delta+p**h*V
                    for z in range(p):
                        lhs=c*pow(a,z,mod)%mod
                        rhs=(delta+p**h*(V+delta*U*z))%mod
                        require(lhs==rhs,'general affine identity')
                        require((lhs==delta%mod)==((V+delta*U*z)%p==0),'lift iff')
                        affine_checks+=1
                        flat+=int(U==0)
    # A genuine base-2 flat lift is retained, with the first nonzero depth found exactly.
    require(prime(1093), 'flat control prime')
    flat_order=order2(1093)
    flat_depth=valuation((1<<flat_order)-1,1093)
    require(flat_order==364 and flat_depth==2, 'actual flat first-return control')
    require(pow(2,flat_order,1093**2)==1 and pow(2,flat_order,1093**3)!=1,
            'flat at first level, nonflat at true initial depth')
    # An actual ordinary-prime lift exists if the other-prime condition is forgotten.
    require(pow(2,110,121)==1 and pow(2,110,23)==1,'separate-lift boundary')
    require(pow(2,100,11)==1 and pow(2,100,23)==2 and pow(2,100,121)!=1,
            'joint history boundary')
    # First case gap cap, derived bound and exponent minima.
    require(2*23**2>99 and 4*(18788-2)>69*33**2,'exact finite bound')
    require(2**100>18787 and 3*2**92>18787,'all first-orientation classes excluded')
    return {'four_caps':out,'exact_depth_regressions':nchecks,
            'general_affine_checks':affine_checks,'zero_slope_checks':flat,'actual_base2_flat_control':{'p':1093,'order':flat_order,'depth':flat_depth},
            'separate_lift_control':{'N110_mod121':pow(2,110,121),'N110_mod23':pow(2,110,23)},
            'first_orientation_n_upper':18787}


def vp_binomial(n: int,j: int,p: int) -> int:
    a,b,z=n,j,n-j; total=0
    while a:
        a//=p; b//=p; z//=p; total+=a-b-z
    return total


def carry_count(n: int,j: int,p: int) -> int:
    a,b=j,n-j; carry=total=0
    while a or b or carry:
        carry=(a%p+b%p+carry)//p; total+=carry; a//=p;b//=p
    return total


def ratio_audit(limit: int) -> dict:
    count=gap=0
    for n in range(8,limit+1):
        for j in range(4,n//2+1):
            theta=Fraction((n-j)*(n-j-1),(n-1)*(n-2));x,D=theta.numerator,theta.denominator
            require(D*(2*(n-j)-1)**2==D+4*x*(n-1)*(n-2),'original square')
            require(2*x%gcd(n,j)==0 and 2*D%gcd(n-2,j)==0,'gcd bridge')
            for L in range(1,isqrt(n-1)+1):
                if (n-1)%L:continue
                for ll in {L,(n-1)//L}:
                    R=(n-1)//ll
                    if (j-1)%R:continue
                    m=(j-1)//R
                    if not (m>0 and 2*m<ll):continue
                    require((D*(ll-m)**2-x*ll**2)*(n-2)==D*(ll-m)*m,'gap core')
                    require(4*(n-2)<D*ll**2,'formal-gap interface')
                    require(m*(n-2)-ll*j==-(m+ll),'cofactor coupling')
                    gap+=1
            count+=1
    return {'actual_ratio_pairs':count,'nonempty_denominator_gap_interfaces':gap}


def regression(limit: int) -> dict:
    js=set(); a=11
    while 2*a*23<=limit:
        b=a*23
        while 2*b<=limit:
            j=b
            while 2*j<=limit:js.add(j);j*=2
            b*=23
        a*=11
    count=direct=0; witnesses=Counter()
    for n in range(8,limit+1):
        relevant=sorted(j for j in js if 2*j<=n)
        if not relevant:continue
        candidates=sorted(p for p in (set(factor(n))|set(factor(n-1))|set(factor(n-2)))
                          if p>2 and vp_binomial(n,3,p)>0)
        for j in relevant:
            good=next((p for p in candidates if vp_binomial(n,j,p)>0),None)
            require(good is not None,'actual binomial counterexample in regression')
            require(vp_binomial(n,j,good)==carry_count(n,j,good)>0,'full high carries')
            if n<=1200:
                require(gcd(comb(n,3),comb(n,j))%good==0,'direct binomial check');direct+=1
            witnesses[good]+=1;count+=1
    return {'scope':'regression, not the universal proof','columns':sorted(js),
            'original_pairs':count,'direct_binomial_checks':direct,'witness_counts':dict(sorted(witnesses.items()))}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--nmax',type=int,default=6000)
    parser.add_argument('--ratio-nmax',type=int,default=200)
    args=parser.parse_args()
    require(args.nmax>=506 and args.ratio_nmax>=8,'audit limits too small')
    report={'theorem':'all j=2^b*11^s*23^t, b>=0,s,t>=1, n>=2j, i=3',
            'boundary':'written dependent partial theorem, not full699, WSS or Lean certification',
            'finite_proof_certificate':certificate(),'joint_lifts':local_lifts(),
            'ratio_self_audit':ratio_audit(args.ratio_nmax),
            'original_regression':regression(args.nmax)}
    print(json.dumps(report,ensure_ascii=False,sort_keys=True,indent=2))

if __name__=='__main__':main()
