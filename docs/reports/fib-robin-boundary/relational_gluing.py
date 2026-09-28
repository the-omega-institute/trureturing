#!/usr/bin/env python3
"""Exact finite diagnostics of divisor seams and future multiplier pruning."""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import gcd, isqrt
from pathlib import Path
import sys
sys.dont_write_bytecode = True

import argparse
import hashlib
import json


@lru_cache(None)
def divisors(n):
    out = []
    for d in range(1, isqrt(n)+1):
        if n % d == 0:
            out.append(d)
            if d*d != n:
                out.append(n//d)
    return tuple(sorted(out))


@lru_cache(None)
def Z(n):
    return sum((Q(1,d) for d in divisors(n)), Q(0))


@lru_cache(None)
def valuations(n):
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p,0)+1
            n //= p
        p += 1
    if n > 1:
        out[n] = 1
    return out


@lru_cache(None)
def G(p,a):
    return sum((Q(1,p**j) for j in range(a+1)), Q(0))


def factor_ratio(n,m,multiplier_exponents):
    a,b=valuations(n),valuations(m)
    out=Q(1)
    for p in a.keys() | b.keys() | multiplier_exponents.keys():
        t=multiplier_exponents.get(p,0)
        out*=G(p,a.get(p,0)+t)/G(p,b.get(p,0)+t)
    return out


def future_inf(n,m,allowed):
    a,b=valuations(n),valuations(m)
    result=Z(n)/Z(m)
    for p in allowed:
        if a.get(p,0)>b.get(p,0):
            result*=G(p,b.get(p,0))/G(p,a[p])
    return result


def seam_factor(a,b):
    return Z(a)*Z(b)/Z(a*b)


def local_correction(p,exponents):
    out=Q(1)
    for a in exponents:
        out*=G(p,a)
    return out/G(p,sum(exponents))


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,required=True,help='output directory')
    args=ap.parse_args()
    seam_checks=0
    for A,B in product(range(1,65),repeat=2):
        gamma=[(u,v) for u in divisors(A) for v in divisors(B)
               if gcd(v,A//u)==1]
        actual=sorted(u*v for u,v in gamma)
        assert actual==list(divisors(A*B))
        assert len(set(actual))==len(actual)
        for d in divisors(A*B):
            u=gcd(d,A);v=d//u
            assert (u,v) in gamma
        probability=sum((Q(1,u*v)/(Z(A)*Z(B)) for u,v in gamma),Q(0))
        assert probability==1/seam_factor(A,B)
        for u,v in gamma:
            conditioned=Q(1,u*v)/(Z(A)*Z(B))/probability
            assert conditioned==Q(1,u*v)/Z(A*B)
        seam_checks+=1

    cocycle_checks=0
    for A,B,C in product(range(1,17),repeat=3):
        assert seam_factor(A,B)*seam_factor(A*B,C)==seam_factor(B,C)*seam_factor(A,B*C)
        cocycle_checks+=1

    local_checks=0
    for p in (2,3,5,7,11):
        for a,b in product(range(13),repeat=2):
            value=local_correction(p,(a,b))
            assert value>=1
            assert value<=local_correction(p,(a+1,b))
            assert value<=local_correction(p,(a,b+1))
            local_checks+=1
        for aa in product(range(5),repeat=3):
            value=local_correction(p,aa)
            for i in range(3):
                bb=list(aa);bb[i]+=1
                assert value<=local_correction(p,tuple(bb))
                local_checks+=1

    # The product is over all allowed channels, not independently optimized histories.
    future_checks=0
    for n,m in product(range(1,25),repeat=2):
        for allowed in ((),(2,),(3,),(2,3),(2,3,5)):
            floor=future_inf(n,m,allowed)
            for exps in product(range(3),repeat=len(allowed)):
                c=1
                for p,t in zip(allowed,exps):c*=p**t
                observed=Z(n*c)/Z(m*c)
                assert floor<=observed
                assert observed==factor_ratio(n,m,dict(zip(allowed,exps)))
                future_checks+=1
            if floor<1:
                advantage=[p for p in allowed if valuations(n).get(p,0)>valuations(m).get(p,0)]
                T=0
                while factor_ratio(n,m,{p:T for p in advantage})>=1:
                    T=max(1,2*T)
                    assert T<=128,(n,m,allowed,'finite probe not found')

    universal_checks=0
    for n,m in product(range(1,65),repeat=2):
        support=valuations(n).keys() | valuations(m).keys()
        assert (future_inf(n,m,support)>=1)==(n % m == 0)
        universal_checks+=1

    # Cost for three blocks must telescope, rather than sum all pair costs.
    pairwise=(local_correction(2,(1,1)))**3
    true_three=local_correction(2,(1,1,1))
    assert pairwise>true_three

    reversals=[]
    for scale in (1,5040):
        n,m=6*scale,8*scale
        before,after=Z(n)/Z(m),Z(3*n)/Z(3*m)
        assert n<m and before>1 and after<1
        reversals.append({'n':n,'m':m,'c':3,'before':str(before),'after':str(after),
                          'future_floor_S3':str(future_inf(n,m,(3,)))})

    blocks=(5040,6,8)
    actual=Z(blocks[0])*Z(blocks[1])*Z(blocks[2])/Z(blocks[0]*blocks[1]*blocks[2])
    lower=local_correction(2,(1,1,1))*local_correction(3,(1,1,0))
    refined=local_correction(2,(4,1,3))*local_correction(3,(2,1,0))
    assert 1<=lower<=refined==actual
    assert Z(5040)*Z(2)/Z(10080)==Q(31,21)
    assert Z(5040)*Z(3)/Z(15120)==Q(13,10)

    # A partial-factor certificate: n=A*r, unknown channels cost at worst Z(r).
    rough_checks=0
    for n in range(1,129):
        A,r=n,1
        for p,e in list(valuations(n).items()):
            if p>3:
                A//=p**e;r*=p**e
        assert gcd(A,r)==1
        for m in range(1,65):
            known=Q(1)
            for p in (2,3):
                known*=min(Q(1),G(p,valuations(m).get(p,0))/G(p,valuations(n).get(p,0)))
            certified=Z(n)/Z(m)*known/Z(r)
            exact=future_inf(n,m,valuations(n).keys() | valuations(m).keys())
            assert certified<=exact
            rough_checks+=1

    # Eight labelled prime occurrences; the seam keeps one prefix per prime.
    labels=(2,2,2,2,3,3,5,7)
    histories=list(product((0,1),repeat=len(labels)))
    normal=[]
    independent_weight=Q(0)
    for bits in histories:
        d=1
        for p,t in zip(labels,bits):
            d*=p**t
        independent_weight+=Q(1,d)
        if all(bits[i]>=bits[j] for i in range(len(labels))
               for j in range(i+1,len(labels)) if labels[i]==labels[j]):
            normal.append(d)
    assert len(histories)==256 and len(normal)==60
    assert sorted(normal)==list(divisors(5040))
    assert independent_weight/Z(5040)==Q(1296,403)

    result={'5040_labelled_occurrences':{'histories':len(histories),'normal_seams':len(normal),
              'weight_ratio':str(independent_weight/Z(5040))},'status':'PASS','seam_pairs_checked':seam_checks,
            'cocycle_triples_checked':cocycle_checks,'local_monotonicity_checks':local_checks,
            'future_multiplier_comparisons':future_checks,
            'unrestricted_support_pairs_checked':universal_checks,
            'partial_factor_floor_checks':rough_checks,
            'dominance_reversals':reversals,
            '5040_seam_factors':{'with_2':'31/21','with_3':'13/10'},
            'three_block_5040_6_8':{'partial_lower_factor':str(lower),'refined_exact_factor':str(actual)},
            'all_pairs_overcount_example':{'blocks':[2,2,2],'all_pairs_factor':str(pairwise),'true_factor':str(true_three)},
            'unattained_inf_example':'n=2,m=1,S={2}: every finite ratio is >1, with infimum 1',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'limits':['Finite exact diagnostics, not a proof of universal claims.',
                      'No Lean compilation or kernel verification.']}
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
