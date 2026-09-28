#!/usr/bin/env python3
"""Fourteen-prime fixed profile: exact shared-support and same-source query certificate."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import prod, factorial
from collections import Counter
from functools import lru_cache
from pathlib import Path
import json
import argparse


def need(ok,message):
    if not ok:
        raise RuntimeError(message)

qs=(5,7,11,13,17,19,23,29,31,37)
n=len(qs)
b=tuple(F(1,q-2) for q in qs)
c=tuple(F(q-1,q-2) for q in qs)
p=tuple(c[i]/q for i,q in enumerate(qs))
m=tuple(tuple(1-b[i]*((i==0)==(r==0)) for i in range(n)) for r in range(2))
# Count nonsingleton set partitions by their unordered block-size profiles.
N={(0,0):1}
for size in range(1,n+1):
    for k in range(1,size//2+1):
        count=F(0)
        for sizes in combinations_with_replacement(range(2,size+1),k):
            if sum(sizes)==size:
                count+=F(factorial(size),prod(factorial(j) for j in sizes)*prod(factorial(v) for v in Counter(sizes).values()))
        need(count.denominator==1,'integer partition count')
        N[size,k]=int(count)
coeff=tuple(sum((-2)**k*N.get((size,k),0) for k in range(size//2+1)) for size in range(n+1))
# Every coordinate residual via elementary symmetric polynomials, independent
# of the producer's coordinate-mask Shearer recurrence.
bridges=[]
for r in range(2):
    tq=tuple(b[i]/m[r][i] for i in range(n))
    vals={}
    for mask in range(1<<n):
        es=[F(1)]
        for i in range(n):
            if mask>>i&1:
                es.append(F(0))
                for j in range(len(es)-1,0,-1):
                    es[j]+=tq[i]*es[j-1]
        vals[mask]=sum(coeff[j]*es[j] for j in range(len(es)))
    mins=[min(v for mask,v in vals.items() if mask.bit_count()==j) for j in range(n+1)]
    need(all(v>0 for mask,v in vals.items() if mask.bit_count()<=8),'all low residuals root '+str(r))
    if r==1:
        need(all(v>0 for v in vals.values()),'root1 entire maximal-cap box positive')
    bridges.append(dict(root=r,minima=list(map(str,mins)),bad_counts=[sum(v<=0 for mask,v in vals.items() if mask.bit_count()==j) for j in range(n+1)]))
need(F(bridges[0]['minima'][8])==F(888304,23856525),'root0 low eight minimum')
need(F(bridges[1]['minima'][10])==F(59873459,5322670080),'root1 top minimum')

need(all(m[r][i]>=p[i] for r in range(2) for i in range(n)),
     'nonnegative root query zero atoms')

support_data=[]
for mask in range(1,1<<n):
    size=mask.bit_count()
    if size<2:
        continue
    bu=prod((b[i] for i in range(n) if mask>>i&1),start=F(1))
    gl=tuple(prod((m[r][i] for i in range(n) if not mask>>i&1),start=F(1)) for r in range(2))
    support_data.append((size,bu,gl))

def source(w):
    val=w*prod(m[0])+(1-w)*prod(m[1])
    for size,bu,gl in support_data:
        for k in range(1,size//2+1):
            terms=[w*gl[0]*2**j+(1-w)*gl[1]*2**(k-j) for j in range(k+1)]
            val+=(-1)**k*N[size,k]*bu*(max(terms) if k%2 else min(terms))
    return val

@lru_cache(None)
def atom(inds,value):
    if not inds:
        return F(value==1)
    if 2**len(inds)>value:
        return F(0)
    i,*rest=inds
    return sum((c[i]*F(qs[i]-1,qs[i]**v)*atom(tuple(rest),value//v) for v in range(2,value+1) if value%v==0),F(0))

def query(w,t=8):
    val=F(0)
    for mask in range(1<<n):
        inds=tuple(i for i in range(n) if mask>>i&1)
        a=tuple((w if r==0 else 1-w)*prod((m[r][i]-p[i] for i in range(n) if not mask>>i&1),start=F(1)) for r in range(2))
        total=prod((p[i] for i in inds),start=F(1))
        first=prod((p[i]+b[i] for i in inds),start=F(1))
        slope=sum(a)+max(a)
        subtotal=first*slope-t*total*sum(a)
        for value in range(1,t):
            mass=atom(inds,value)
            if not mass:
                continue
            actual=max(a[0]*max(2*value-t,0)+a[1]*max(value-t,0),a[0]*max(value-t,0)+a[1]*max(2*value-t,0))
            linear=value*slope-t*sum(a)
            need(actual>=linear,'nonnegative low-product correction')
            subtotal+=mass*(actual-linear)
        val+=subtotal
    return val

outside=(41,43,47)
Q=prod(F(q-1,q-2) for q in outside)-1
s=sum((F(1,q-2) for q in outside),F(0))
target=(1+s)/Q-1
need(target==F(23943,1775),'pure outside target')
need(source(F(1,2))==F(22569883991,435858711750),'old equal-root source anchor')
rows=[]
for w in (F(19,50),):
    G=source(w)
    need(G==F(8712921199,128193738750),'declared changed-weight source fraction')
    H=query(w)
    score=(target+1-8)*G-H
    R=7+H/G
    need(score>F(1,20) and G>0 and R<F(51,4)<target,'simple rational positive fixed-profile witness')
    rows.append(dict(w0=str(w),w1=str(1-w),threshold=8,G=str(G),H=str(H),score=str(score),score_decimal=float(score),R=str(R),R_decimal=float(R)))
A8=1+s-8*Q
cap=3*max(w,1-w)*prod((F(q-1,q-2) for q in qs+outside),start=F(1))
reserve=A8*G-Q*H
density=reserve/cap
need(A8==F(886,1845) and cap==F(1495269376,295615125),'changed-root-weight full Haar cap')
need(reserve==Q*score and density>F(3,4000),'same-source full-family Haar density')
result=dict(scope='One fixed ten-coordinate height-one star profile with actual-mask domination and finite dominated-measure thinning. No uniform fourteen-prime theorem and no new Lean claim.',
    core_nonternary_primes=qs,reference_mass_by_root=[[str(x) for x in row] for row in m],
    partition_method='Unordered block-size profiles with factorial multiplicities.',
    probability_method='Signed partition coefficients times elementary symmetric polynomials; all1024 subsets per root.',
    query_method='Inside-integral two-corner maximum; complete first moment plus exact low-product corrections.',
    bridges=bridges,outside_primes=outside,continuation_Q=str(Q),continuation_s=str(s),
    continuation_A8=str(A8),target=str(target),certificate=rows[0],
    root_Haar_density_cap=str(3*max(w,1-w)),full_Haar_density_cap=str(cap),
    unnormalized_survivor_reserve=str(reserve),full_Haar_survivor_lower=str(density),
    stated_Haar_lower='3/4000',strict_Haar_surplus=str(density-F(3,4000)),
    height_boundary='Every original, including outside-touching originals, hasv3<=1; all nonternary exponents are arbitrary finite.',
    source_boundary='Actual core singleton survivor masses dominate the reference masses on their two named roots. All original phases and shared numerical-label inventories are retained.')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
rendered=json.dumps(result,sort_keys=True,indent=2)+'\n'
if args.output is None:
    expected=Path(__file__).resolve().with_suffix('.json')
    need(json.loads(expected.read_text())==json.loads(rendered),'retained result matches exact replay')
    print(rendered,end='')
else:
    args.output.write_text(rendered)
