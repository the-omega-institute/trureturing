"""Exact CRT control for independent prefix certificates and a coherent color plan.

Python 3.10 or later; standard library only. Run with --out PATH.
The prescribed source is not the residual of a whole covering system.
"""
from itertools import combinations, product
from math import prod, gcd
from fractions import Fraction
import argparse
import json
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument("--out", type=Path, required=True)
args=parser.parse_args()
if not __debug__:
    raise RuntimeError("Assertions must be enabled")

primes=[p for p in range(5,110) if all(p%d for d in range(2,int(p**0.5)+1))]
assert len(primes)==27
blocks=[primes[3*i:3*i+3] for i in range(9)]
owners=[]
color=0

def crt(pairs):
    n=prod(m for m,_ in pairs)
    return sum(a*(n//m)*pow(n//m,-1,m) for m,a in pairs)%n

for g,ps in enumerate(blocks):
    divs=[c for k in range(1,4) for c in combinations(ps,k)][:6]
    for j in range(3):
        for bit,cs in enumerate(divs[2*j:2*j+2]):
            conditions={p:bit for p in cs}
            owners.append(dict(color=color,m=prod(cs),rho=crt(list(conditions.items())),conditions=conditions))
        color+=1

for g,h in combinations(range(9),2):
    choices=list(product(blocks[g],blocks[h]))
    for j in range(2):
        for pattern,cs in zip(product(range(2),repeat=2),choices[4*j:4*j+4]):
            conditions=dict(zip(cs,pattern))
            owners.append(dict(color=color,m=prod(cs),rho=crt(list(conditions.items())),conditions=conditions))
        color+=1

for gs in list(combinations(range(9),3))[:11]:
    choices=list(product(*(blocks[g] for g in gs)))[:8]
    for pattern,cs in zip(product(range(2),repeat=3),choices):
        conditions=dict(zip(cs,pattern))
        owners.append(dict(color=color,m=prod(cs),rho=crt(list(conditions.items())),conditions=conditions))
    color+=1
assert color==110 and len(owners)==430
assert len({o['m'] for o in owners})==len(owners)
W=prod(primes)
patterns=list(product(range(2),repeat=9))
source_words=[]
incidence=[]
for bits in patterns:
    coordinates={p:bits[g] for g,ps in enumerate(blocks) for p in ps}
    w=crt(list(coordinates.items()))
    active=[i for i,o in enumerate(owners) if w%o['m']==o['rho']]
    assert len(active)==110
    assert sorted(owners[i]['color'] for i in active)==list(range(110))
    source_words.append(w)
    incidence.append(sum(1<<i for i in active))
assert len(set(incidence))==512
for i,bits in enumerate(patterns):
    disjoint=[j for j,mask in enumerate(incidence) if incidence[i]&mask==0]
    assert disjoint==[patterns.index(tuple(1-b for b in bits))]

safe27=[r for r in range(27) if r%3!=0 and r%9!=1]
assert len(safe27)==15
plan=[]
for c,r in enumerate(safe27):
    for o in owners:
        if o['color']==c:
            plan.append((27*o['m'],crt([(27,r),(o['m'],o['rho'])])))
assert len(plan)==30 and len({m for m,_ in plan})==30
for r in safe27:
    for w in source_words:
        x=crt([(27,r),(W,w)])
        assert any(x%m==a for m,a in plan)

originals=[(113*o['m'],crt([(113,o['color']),(o['m'],o['rho'])])) for o in owners]
originals += [(113,110),(339,crt([(3,2),(113,111)])),(1017,crt([(9,2),(113,112)])),(3,0),(9,1)]
assert len(originals)==435 and len({m for m,_ in originals})==435
for i,(m,a) in enumerate(originals):
    for n,b in originals[i+1:]:
        if m%n==0 or n%m==0:
            assert (a-b)%gcd(m,n)!=0
for i,o in enumerate(owners):
    idx=next(j for j,mask in enumerate(incidence) if mask>>i&1)
    x=crt([(9,2),(113,o['color']),(W,source_words[idx])])
    assert [j for j,(m,a) in enumerate(originals) if x%m==a]==[i]
alltwo=crt([(p,2) for p in primes])
for offset,(qcolor,z) in enumerate([(110,2),(111,2),(112,2),(0,0),(0,1)]):
    x=crt([(9,z),(113,qcolor),(W,alltwo)])
    assert [j for j,(m,a) in enumerate(originals) if x%m==a]==[430+offset]
hole=crt([(9,2),(113,0),(W,alltwo)])
assert not any(hole%m==a for m,a in originals)
miss=Fraction(14,15)**110
assert 7680*miss>1
assert 2*7665*miss>1
result={
 'primes':primes,'blocks':blocks,'colors':110,'owners':430,'originals_with_guards':435,
 'cofactor_points':512,'serving_colors_each':110,'cofactor_capacity':1,'safe_depth3_words':15,
 'distinct_candidate_rows':15*512,'dependency_degree':15*512-1-15,
 'positive_plan_outputs':30,'all_originals_have_private_integer':True,
 'all_comparable_original_pairs_disjoint':True,'divisor_closed':False,'is_whole_cover':False,
 'explicit_uncovered_integer':str(hole),'exact_source_is_mask':False,
 'independent_singleton_miss_probability':str(miss),'independent_singleton_miss_decimal':float(miss),
 'union_bound_product_exact':str(7680*miss),
 'twice_dependency_factor_product_exact':str(2*7665*miss),
 'union_bound_condition_fails':True,'symmetric_LLL_condition_fails_using_e_gt_2':True
}
print(json.dumps(result,indent=2))
args.out.write_text(json.dumps(result,indent=2)+'\n')
