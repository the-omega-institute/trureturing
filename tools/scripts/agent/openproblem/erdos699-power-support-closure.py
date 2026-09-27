#!/usr/bin/env python3
"""# Erdos 699: whole finite-support columns from mutual power residues

Continuation of issue #9670 and PR #9769 after the common-quotient proof.
Written partial theorems. No full Erdos699 solution, independent review,
new Lean verification, or priority assertion. The inherited normalized
cubic and mixed-support arithmetic must still be separately reviewed.

## The stronger result: no gcd restriction at all

Let S be a finite set of primes, all in ONE residue class r modulo24,
where r is5 or13. Suppose that for every distinct p,q in S there exists
u with u^4=q modp. Then EVERY column

 j=2^b * product_{p in S} p^(e_p), b>=0, e_p>=0, j>=4,

satisfies the original i=3 assertion for ALL n>=2j. There is no bound on
S's size, the exponents, n, or gcd(n,j), and no requirement that the gcd
be a perfect power. Concrete eligible supports are
 {13,61,2557} and {5,101,12821}.
Hence the entire families2^b*13^s*61^t*2557^u and
2^b*5^s*101^t*12821^u are covered for arbitrary nonnegative exponents
when j>=4, in particular for all three odd exponents positive.
The finite root/primality checks establish eligibility of these examples;
the unbounded n/exponent conclusion comes from the general proof below.
No assertion is made that every set of three primes satisfies the premise.

## 1. The local-kernel lemma

Let all odd primes of j belong to one class r in{5,11,13,19} mod24.
Put d=gcd(n,j), e=oddpart(d), and k=2 for r11,19 or k=4 for r5,13.
Assume that at every odd prime p|j with p not dividing d, the class of e
is in (F_p^*)^k. Equivalently, e^((p-1)/k)=1 modp, since v2(p-1)=log2(k)
and that power subgroup has odd order. Then the original pair(n,3,j)
has a common odd prime. This hypothesis includes but is strictly weaker
than e being an integer kth power: the required roots may differ with p.

PROOF. Under a putative counterexample inherit the exact premises of
`erdos699-common-quotient-check.py`:
 n=c*2^a*d, c in{1,3}, a>=2;
 a prime P|j,n-1 and another prime R|j outside n(n-1);
 theta=(n-j)(n-j-1)/((n-1)(n-2))=x/y in lowest terms,0<theta<1,
 y divides3z, where primes of z divide j but not n(n-1).
Write N=a+v2(d), so n=c*2^N*e. All prime-field maps below are ONLY at
p not dividing d, where e is a unit; since3 does not divide j, these
are exactly the endpoint primes outside n.

For c1, work in Gamma_p=F_p^*/(F_p^*)^k. This is cyclic of order k and
[2] generates it, by the elementary sign table in the companion proof.
The local-kernel assumption kills [e] even though e need not be a global
integer kth power. At P|n-1 we get N=0 modk. A prime of j dividing n-2
would instead require N=1 modk; hence no such prime exists. Since3 does
not divide z, the denominator condition now forces theta=1/3 or2/3.

The two exact residual equations force the external prime R to divide
n+1 or n+4, respectively. In Gamma_R these require
 0=k/2 modk, or 0=k/2+2 modk.
Only k4 in the second case survives. All odd primes of j are then1 mod4,
so oddpart(j)=1 mod4. Also4|N implies16|n. Odd j gives the contradiction
2=0 mod4 in3(n-j)(n-j-1)=2(n-1)(n-2). For even j, N>v2(j), so the same
equality forcesv2(j)=2; it then gives12=4 mod16. Thus c1 is excluded.

For c3 project to the square quotient. The local-kernel assumption still
kills[e]. All eligible endpoint primes have Legendre(2,p)=-1 and one
common Legendre(3,p)=sigma. At P|n-1, sigma*(-1)^N=1, whereas any endpoint
prime of n-2 would require that same expression to be-1. No such prime
exists. However the raw theta denominator is now prime to3, and its
nontrivial reduced denominator must contain exactly such an endpoint
prime. Contradiction. This proves the local-kernel lemma.

## 2. Why mutual power residues handle EVERY possible common factor

Fix an arbitrary n, with j supported on S and2. The odd part e of d is a
product of prime powers from S. If p|j and p does not divide d, NONE of
those prime factors equals p. For each q|e the hypothesis puts q in
(F_p^*)^4. Since a power subgroup is closed under products and powers,
 e=product q^(v_q(e)) also belongs to (F_p^*)^4.
Thus EVERY allocation of shared prime factors to d, with ANY exponents,
satisfies the local-kernel lemma at every eligible p. The preceding lemma
excludes the putative counterexample and proves the whole-support theorem.
This is the key uniform step: there is no enumeration of gcd allocations.

## 3. Exact example certificates and edge conditions

The executable code checks primality by deterministic trial division and
finds explicit fourth roots for both orientations of all three prime pairs
in each displayed support. The resulting six roots per support can be
verified directly by modular fourth powers. It also checks supports with
missing edges and local square/fourth-power residue examples whose gcd is
NOT an integer square/fourth power. Such roots vary with the target prime.
The set condition is a sufficient condition, not an equivalence to the
original Erdos assertion. Failure of an edge produces no counterexample.

The general local-kernel statement remains valid at r11,19 with squares.
The whole-support corollary is stated at r5,13 because these explicit
nontrivial mutually fourth-residual examples exist. It does not assert
nontrivial mutual-square families of primes3 mod4.

## Repository formalization interface

`D5/S3/Factorization/Galois/GeneralPowerCharacterLayer.lean`, read blob
79c32483be14a2333e043f151744877c4ea30fb8, already identifies the joint kernel
of all mu_k characters with G^k and proves the exponent quotient property.
Use its actual powerSubgroup definition for section2: membership is
preserved under finite products and powers. Here the prime fields differ;
one uses that theorem separately in each field, retaining the labelled
class of2. No arbitrary isomorphism is allowed to move this label.
New obligations are the labelled finite-field quotient, local-kernel
arithmetic lemma, and composition with the original number-theoretic
premises. This is not already a Lean proof of those new obligations.

This result advances beyond two-odd-prime columns to an entire structural
class with arbitrarily many support primes, including explicit three-prime
families and unrestricted gcd. General finite supports without the mutual
residue condition, unrestricted i=3, and i=4..324 remain unresolved here.
No statement from the prior3-p or its analytic estimates is required.

"""
from __future__ import annotations
import argparse
import importlib.util
import json
from math import gcd
from pathlib import Path

PATH=Path(__file__).with_name('erdos699-common-quotient-check.py')
spec=importlib.util.spec_from_file_location('erdos699_common_quotient',PATH)
if spec is None or spec.loader is None: raise RuntimeError(f'cannot load companion: {PATH}')
base=importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def eligible_support(S: tuple[int,...]) -> bool:
    if not S or len(set(S))!=len(S) or not all(base.prime(p) for p in S):return False
    r=S[0]%24
    return r in (5,13) and all(p%24==r for p in S) and all(
        pow(q,(p-1)//4,p)==1 for p in S for q in S if p!=q)


def root_certificate(S: tuple[int,...]) -> list[dict]:
    assert eligible_support(S)
    rows=[]
    for p in S:
        for q in S:
            if p==q:continue
            root=next(a for a in range(1,p) if pow(a,4,p)==q%p)
            assert pow(root,4,p)==q%p
            rows.append({'target_prime':p,'element_prime':q,'fourth_root':root})
    return rows


def local_kernel(n: int,j: int) -> bool:
    case=base.power_class(j)
    if case is None:return False
    _,k=case;d=gcd(n,j);e=base.oddpart(d)
    return all(pow(e,(p-1)//k,p)==1 for p,_ in base.factor(j) if p>2 and d%p)


def local_regression(nmax: int) -> dict:
    tests=not_global_power=0
    for j in range(4,nmax//2+1):
        if base.power_class(j) is None:continue
        for n in range(2*j,nmax+1):
            if not local_kernel(n,j):continue
            base.witness(n,j);tests+=1
            if not base.power_pair(n,j):not_global_power+=1
    examples=[]
    # These have three support primes; the common odd factor is only a first power.
    for r,a,p,q in ((11,11,83,107),(19,19,67,211),(5,5,101,149),(13,13,61,181)):
        B=a*p*q;j=a*B; N=(2*B).bit_length();n=a*(1<<N)
        assert gcd(n,j)==a and local_kernel(n,j) and not base.power_pair(n,j)
        rows=base.factor(j)
        assert len([p for p,_ in rows if p>2])==3
        ell=next(r for r in range(3,5001,2) if base.prime(r) and base.vpbinom(n,3,r)>0 and base.vpbinom(n,j,r)>0)
        base.verify_witness(n,j,ell)
        examples.append({'class':r,'n':n,'j':j,'gcd':a,'shared_prime':ell})
    return {'nmax':nmax,'all_checked_pairs':tests,'outside_integer_power_gcd_predicate':not_global_power,
            'genuine_three_prime_nonglobal_power_examples':examples}


def support_regression() -> dict:
    small=[p for p in range(3,5001,2) if base.prime(p)]
    supports=((13,61,2557),(5,101,12821))
    results=[];total=0
    for S in supports:
        roots=root_certificate(S);targets=[]
        B=S[0]*S[1]*S[2]
        for chosen in S:
            for exponent in (1,2,3):
                d0=chosen**exponent
                for b in (0,1):
                    j=(1<<b)*d0*B
                    for c in (1,3):
                        N=max(b+2,(2*j//(c*d0)).bit_length())
                        while c*d0*(1<<N)<2*j:N+=1
                        n=c*d0*(1<<N)
                        assert gcd(n,j)==(1<<b)*d0 and local_kernel(n,j)
                        ell=next((r for r in sorted(set(small)|set(S)) if base.vpbinom(n,3,r)>0 and base.vpbinom(n,j,r)>0),None)
                        assert ell is not None,(S,n,j)
                        base.verify_witness(n,j,ell)
                        targets.append({'n':n,'j':j,'gcd':gcd(n,j),'shared_prime':ell})
                        total+=1
        # Independently verify that every allowed shared-prime monomial lies in
        # each eligible local kernel. This audits the finite-product mechanism.
        monomials=0
        for p in S:
            other=[q for q in S if q!=p]
            for e1 in range(7):
                for e2 in range(7):
                    value=other[0]**e1*other[1]**e2
                    assert pow(value,(p-1)//4,p)==1
                    monomials+=1
        results.append({'support':S,'root_certificate':roots,'shared_monomial_checks':monomials,
                        'unrestricted_gcd_regression_pairs':targets})
    assert not eligible_support((5,29,53))
    assert not eligible_support((13,37,61))
    return {'supports':results,'total_original_regression_pairs':total,
            'failed_edge_controls_preserved':True,'infinite_exponents_proved_by_subgroup_closure':True}


def main() -> None:
    p=argparse.ArgumentParser(description='Power-support closure proof with explicit residue witnesses.')
    p.add_argument('--nmax',type=int,default=1000)
    a=p.parse_args()
    if a.nmax<16:p.error('nmax>=16 required')
    print(json.dumps({'local_kernel':local_regression(a.nmax),'support':support_regression(),
                      'whole_erdos699_solved':False,'new_Lean_verification':False,
                      'independent_review':False},indent=2))

if __name__=='__main__':main()
