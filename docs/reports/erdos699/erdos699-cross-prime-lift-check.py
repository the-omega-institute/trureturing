#!/usr/bin/env python3
r"""Erdos 699: conditional shared-exponent 11/23 exclusion certificate.

The mathematical derivation is in ERDOS_699_BINOMIAL_COMMON_PRIME.md,
sections 42--46. The exclusion assumes the normalized-cubic and
mixed-support interface of section 43: n=c*2**N, c in {1,3}, the two
endpoint-prime roles, and reduced denominator support D|3*z. Its
implication from an arbitrary original no-common-odd-prime obstruction
is ASSUMED-UNVERIFIED. This program does not establish that implication.

The complete 8064-pair periodic certificate excludes every exponent in
its five conditional domains. Original-binomial and local lift checks
are separate bounded regressions. Scalar base-2 lifting is not a
Fibonacci, golden-unit, or Wall--Sun--Sun result. No whole-problem
conclusion or formal certification is asserted.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
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
    """Export every witness, including the full mathematical domain metadata."""
    require(PERIOD % 110 == 0, 'period must retain exponent classes')
    square_sets = {q: {a*a % q for a in range(q)} for q in WITNESSES}
    for q in WITNESSES:
        require(prime(q) and pow(2, PERIOD, q) == 1, 'prime-period condition')
        for z in range(q):
            require((z in square_sets[q]) == (z == 0 or pow(z, (q-1)//2, q) == 1),
                    'Euler/square table agreement')
    domains = []
    rows = []
    for case_id, (c, D, r, specified) in enumerate(CASES):
        xs = specified if specified else tuple(x for x in range(D//4+1, D) if gcd(x, D) == 1)
        require(all(D < 4*x and x < D and gcd(x, D) == 1 for x in xs), 'numerator domain')
        count = 0
        for N in range(r, PERIOD, 110):
            for x in xs:
                witness = None
                for q in WITNESSES:
                    n = c * pow(2, N, q) % q
                    residue = (1 + 4*x*(n-1)*(n-2)*pow(D, -1, q)) % q
                    if pow(residue, (q-1)//2, q) == q-1:
                        require(residue not in square_sets[q], 'nonresidue agreement')
                        witness = {'case_id': case_id, 'N': N, 'x': x,
                                   'q': q, 'residue': residue}
                        break
                require(witness is not None, 'uncovered finite case')
                rows.append(witness)
                count += 1
        require(count == EXPECTED[case_id], 'incomplete finite domain')
        domains.append({'case_id': case_id, 'c': c, 'D': D, 'N_mod110': r,
                        'numerators': list(xs), 'count': count})
    require(len(rows) == 8064, 'complete certificate count')
    return {'schema_version': 1, 'period': PERIOD, 'class_modulus': 110,
            'square_expression': '1+4*x*(c*2^N-1)*(c*2^N-2)/D',
            'witness_primes': list(WITNESSES), 'domains': domains,
            'total': len(rows), 'rows': rows}


def certificate_summary(data: dict) -> dict:
    counts = Counter(row['case_id'] for row in data['rows'])
    witnesses = Counter(row['q'] for row in data['rows'])
    return {'period': data['period'], 'total': data['total'],
            'domain_counts': [counts[i] for i in range(5)],
            'witness_counts': dict(sorted(witnesses.items())),
            'scope': 'complete periodic domains, conditional on section 43 interface'}


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
    # Bounded checks of the general-depth identity, including zero slopes.
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
                    require(4*(n-2)<D*ll**2,'denominator-gap interface')
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
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--nmax', type=int, default=6000)
    parser.add_argument('--ratio-nmax', type=int, default=200)
    parser.add_argument('--certificate-only', action='store_true',
                        help='export all 8064 witnesses without bounded regressions')
    parser.add_argument('--output', type=Path, help='write deterministic JSON to this path')
    args = parser.parse_args()
    if args.certificate_only:
        report = certificate()
    else:
        require(args.nmax >= 506 and args.ratio_nmax >= 8, 'audit limits too small')
        report = {
            'claim': 'no obstruction satisfying section 43 normalized/mixed-support interface',
            'assumed_unverified': 'original-predicate to normalized/mixed-support implication',
            'boundary': 'conditional written mathematics; not whole699, WSS or formal certification',
            'periodic_certificate': certificate_summary(certificate()),
            'joint_lifts': local_lifts(),
            'ratio_self_audit': ratio_audit(args.ratio_nmax),
            'original_regression': regression(args.nmax)}
    rendered = json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered, encoding='utf-8')
    else:
        print(rendered, end='')


if __name__ == '__main__':
    main()
