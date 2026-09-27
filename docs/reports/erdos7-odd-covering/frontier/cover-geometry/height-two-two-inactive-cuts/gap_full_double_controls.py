#!/usr/bin/env python3
"""Actual-source and necessary-column controls for Report449 GF.1--GF.6.

No flow value or universal source verification is inferred from the controls.
"""
import argparse
from itertools import combinations, combinations_with_replacement, product
from collections import Counter, defaultdict
from fractions import Fraction as Q
from math import lcm
import json
from pathlib import Path


def require(ok,msg):
    if not ok: raise ValueError(msg)


V=[]
for a,b in combinations_with_replacement(range(7),2):
    v=[0]*7;v[a]+=1;v[b]+=1;V.append(tuple(v))
triples=list(combinations(range(5),3))
shape_counts={}
for name,s in [('22',(2,2,0,0,0,0,0)),('211',(2,1,1,0,0,0,0)),('1111',(1,1,1,1,0,0,0))]:
    checked=0;survivors=0
    for idx in combinations_with_replacement(range(len(V)),5):
        checked+=1
        bs=[V[i] for i in idx]
        good=True
        for i,j,k in triples:
            if sum(s[h]+bs[i][h]+bs[j][h]+bs[k][h]>=3 for h in range(7))<3:
                good=False;break
        survivors+=good
    require(checked==201376 and survivors==0,'balanced-four necessary triple counterexample')
    shape_counts[name]=dict(five_owner_multisets=checked,survivors=survivors)

D=(1,5,7,25,35,49,175,245,1225)
coeff=(1,3,3,5,9,5,15,15,25)
require(tuple(sum(lcm(a,b)==d for a in D for b in D) for d in D)==coeff,'81 ordered numerical LCM multiplicities')
psi_caps=tuple(map(Q,('1','1/3','1/2','1/5','1/6','1/6','1/10','1/18','1/30')))
eta_caps=tuple(map(Q,('1','1','1','1/4','1','1/4','1/4','1/4','1/4')))
cap=(Q(1),)+tuple(max(Q(6,7)*a,Q(1,7)*b) for a,b in zip(psi_caps[1:],eta_caps[1:]))
require(cap==tuple(map(Q,('1','2/7','3/7','6/35','1/7','1/7','3/35','1/21','1/28'))),'all nine common mixture caps')
require(sum(a*b for a,b in zip(cap,coeff))==Q(249,28)<9,'ordered LCM envelope')


def measure_caps(law):
    require(sum(law.values())==1 and all(w>=0 for w in law.values()),'probability')
    values=[]
    for d in D:
        masses=defaultdict(Q)
        for (r,c,g,h),w in law.items():
            a5=r+5*c;a7=g+7*h
            n=a5+25*((a7-a5)*2%49)
            require(n%25==a5 and n%49==a7,'original CRT numerical label')
            masses[n%d]+=w
        values.append(max(masses.values(),default=Q(0)))
    return tuple(values)


def actual_control(name,gap,candidates):
    fibres={(0,c):set(gap[c]) for c in range(4)}
    fibres.update({(1,c):{(1,c),(2,c)} for c in range(5)})
    fibres.update({(r,c):set(product(range(7),repeat=2)) for r in (2,3) for c in range(5)})
    require(all(fibres[0,c] and fibres[0,c]<=set(candidates[c]) and len(candidates[c])==2 for c in range(4)), 'actual nonempty gap containment')
    choices={r:list(combinations(range(4 if r==0 else 5),2 if r==0 else 3)) for r in range(4)}
    tests=0
    for r,s in combinations(range(4),2):
        for a,b in product(choices[r],choices[s]):
            union=set().union(*(fibres[r,c] for c in a),*(fibres[s,c] for c in b))
            require(sum(sum(g==j for g,h in union)>=3 for j in range(7))>=3,'actual literal pair tree')
            tests+=1
    require(tests==480,'all legal original pairs')
    total=set().union(*fibres.values())
    require(sum(sum(g==j for g,h in total)>=5 for j in range(7))>=5,'standalone control only')
    actualK=[{h for g,h in fibres[0,c] if g==0} for c in range(4)]
    require(all(len(a|b)>=3 for a,b in combinations(actualK,2)),'actual pair unions')
    sdr=next((v for v in product(*actualK) if len(set(v))==4),None)
    require(sdr is not None,'actual four owner SDR')
    anchor=next((cs for cs in choices[0] if all(all(g==0 for g,h in fibres[0,c]) for c in cs)),None)
    require(anchor is not None,'entire legal monochromatic anchor')
    psi=defaultdict(Q)
    for r in (1,2,3):
        for cs in choices[r]:
            owners=defaultdict(list)
            for c in cs:
                for leaf in fibres[r,c]:owners[leaf].append((r,c,*leaf))
            cols=[g for g in range(1,7) if sum(gg==g for gg,h in owners)>=3][:2]
            require(len(cols)==2,'actual two outside branches')
            for g in cols:
                leaves=sorted(h for gg,h in owners if gg==g)[:3]
                for h in leaves:psi[min(owners[g,h])]+=Q(1,3*10*6)
    pc=measure_caps(psi)
    require(all(a<=b for a,b in zip(pc,psi_caps)),'one simultaneous psi')
    require(all(r!=0 and g!=0 for r,c,g,h in psi),'both support separations')
    eta={(0,c,0,h):Q(1,4) for c,h in enumerate(sdr)}
    law=defaultdict(Q,{p:Q(6,7)*w for p,w in psi.items()})
    for p,w in eta.items():law[p]+=w/7
    require(all((g,h) in fibres[r,c] for r,c,g,h in law),'same-source actual support')
    caps=measure_caps(law)
    require(all(a<=b for a,b in zip(caps,cap)),'one simultaneous final law')
    return dict(name=name,source_points=sum(map(len,fibres.values())),pair_tests=tests,
                phantom_gap_candidates=sum(len(set(candidates[c])-fibres[0,c]) for c in range(4)),
                monochromatic_original_owners=anchor,actual_K_representatives=sdr,
                law_support_points=len(law),actual_caps=list(map(str,caps)),
                actual_cap_envelope=str(sum(a*b for a,b in zip(caps,coeff))))

mixed=[{(0,0),(0,1)},{(0,0),(0,2)},{(0,1),(0,2)},{(0,3),(1,6)}]
phantom=[{(0,0)},{(0,1),(0,2)},{(0,1),(0,3)},{(0,2),(0,3)}]
phantom_candidates=[{(0,0),(0,6)},*phantom[1:]]
result=dict(result='PASS',balanced_four=shape_counts,cap_vector=list(map(str,cap)),bound='249/28',
            controls=[actual_control('one_nonpure_gap_owner',mixed,mixed),
                      actual_control('one_nonactual_gap_candidate',phantom,phantom_candidates)],
            scope='Necessary column controls and two actual-source common laws; no flow value or universal source verification.')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
if args.output is not None:
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps(result, indent=2))
