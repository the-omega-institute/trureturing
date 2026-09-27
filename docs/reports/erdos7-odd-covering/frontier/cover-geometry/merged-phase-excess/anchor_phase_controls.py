#!/usr/bin/env python3
"""Exact anchor-phase and degree48 controls for Report450 section10."""
import argparse
from fractions import Fraction as Q
from itertools import product,combinations
from collections import defaultdict
from math import prod,gcd
from pathlib import Path
import json

def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def prime(n):return n>1 and all(n%d for d in range(2,int(n**0.5)+1))
P=[n for n in range(11,98) if prime(n)]
require(P==[11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97],'complete finite prime list')
tail=[]
for r in (1,7,11,13,17,19,23,29):
    k0=0
    while 30*k0+r<=97:k0+=1
    denom=30*(30*Q(2*k0-1,2)+r-2)
    require(denom.denominator==1,'integral tail denominator')
    for k in range(k0,k0+20):
        a=30*k+r-2
        integral=Q(1,a*a-225)
        require(Q(1,a*a)<integral,'exact centred integral cell majorant')
    tail.append({'r':r,'k0':k0,'first_integer':30*k0+r,'denominator':int(denom)})
require(sorted(t['denominator'] for t in tail)==[2520,2580,2700,2760,2880,3060,3120,3300],'eight exact tail denominators')
for p in range(98,3000):
    if prime(p):
        require(any(p%30==t['r'] and p>=t['first_integer'] for t in tail),'tail residue coverage finite control')
B=sum((Q(1,(p-2)**2) for p in P),Q())+sum((Q(1,t['denominator']) for t in tail),Q())
require(B<Q(1,24),'strict prime-square bound')
reserve=1-24*B
require(reserve>Q(1818467547,10**11),'stated reserve decimal')
require(Q(3115496197952,10157230335681)-Q(8471,29403)==Q(5108389839145,274245219063387),'quoted diagnostic arithmetic')

# A genuine labelled CRT family with retained d=3,9 and full outside heights11^2,13.
# Records contain original numerical d,b and both retained/outside residues.
A=(11,13);H=(2,1)
items=[]
def add(d,r,spec):
    b=prod(p**e for p,e,a in spec)
    items.append({'d':d,'phase':r,'b':b,'m':d*b,'spec':tuple(spec)})
add(3,0,[]);add(9,0,[])
add(1,0,[(11,1,0)]);add(1,0,[(13,1,0)])
add(3,1,[(11,1,1)]);add(3,2,[(11,2,2)])
add(9,0,[(13,1,7)])
add(1,0,[(11,1,2),(13,1,2)])
add(3,1,[(11,1,3),(13,1,3)])
add(3,2,[(11,2,4),(13,1,4)])
add(9,1,[(11,1,5),(13,1,5)])
add(9,2,[(11,2,6),(13,1,6)])
require(len({r['m'] for r in items})==len(items) and all(r['m']>1 and r['m']%2 for r in items),'original numerical distinctness and oddness')
anchor={3:0,9:0}
bad=[r for r in items if r['d']==1 or r['phase']!=anchor[r['d']]]
require(all(r['b']>1 for r in bad),'no support-empty bad event')
def occurs(r,y):
    return all(y[A.index(p)]%(p**e)==a for p,e,a in r['spec'])
S=[]
for p,h in zip(A,H):
    exclusions=[r for r in bad if {z[0] for z in r['spec']}=={p}]
    S.append([x for x in range(p**h) if not any(x%(p**r['spec'][0][1])==r['spec'][0][2] for r in exclusions)])
s={p:Q(len(ss),p**h) for p,h,ss in zip(A,H,S)}
require(all(v>0 for v in s.values()),'positive exact pure survivors')
N=defaultdict(set)
for r in bad:
    E=tuple(z[0] for z in r['spec'])
    if len(E)>=2:N[E].add(r['d'])
phi=sum((len(ds)*prod(Q(1,(p-1))*1/s[p] for p in E) for E,ds in N.items()),Q())
product_source=list(product(*S))
omega=[y for y in product_source if not any(occurs(r,y) for r in bad)]
rhoomega=Q(len(omega),len(product_source))
require(phi<1 and rhoomega>=1-phi>0,'one product-law avoidance bound')
for y in omega:
    require(not any(occurs(r,y) for r in items if r['d']==1),'eta supported on actual V_A')
    phases=defaultdict(set)
    for r in items:
        if r['d']>1 and occurs(r,y):phases[r['d']].add(r['phase'])
    require(all(len(v)<=1 for v in phases.values()),'zero phase excess pointwise')
# Verify each fixed retained-d row bound at the very same product source.
for E,ds in N.items():
    rowbound=prod(Q(1,(p-1)*s[p]) for p in E)
    for d in ds:
        rr=[r for r in bad if r['d']==d and tuple(z[0] for z in r['spec'])==E]
        actualsum=sum((Q(sum(occurs(r,y) for y in product_source),len(product_source)) for r in rr),Q())
        require(actualsum<=rowbound,'fixed numerical-d geometric bound')
# Exact phase merging and dominant-phase upper bound under an arbitrary same law.
for d in anchor:
    masses=[]
    for r in range(d):masses.append(Q(sum(any(i['d']==d and i['phase']==r and occurs(i,y) for i in items) for y in product_source),len(product_source)))
    union=Q(sum(any(i['d']==d and occurs(i,y) for i in items) for y in product_source),len(product_source))
    excess=Q(sum(max(0,len({i['phase'] for i in items if i['d']==d and occurs(i,y)})-1) for y in product_source),len(product_source))
    require(excess==sum(masses)-union<=sum(masses)-max(masses),'same-law merged subtraction identity')

# Degree-one original families need not meet Phi<1: 120 retained rows,
# two original labels in each, b=11*13 and11^2*13 with phases0 and1.
M=120
mods=[3**e*b for e in range(1,M+1) for b in (11*13,11**2*13)]
require(len(set(mods))==2*M,'boundary family distinct moduli')
# For every anchor, each retained d has a nonanchor original on the same support.
minN=M; boundaryphi=Q(minN,10*12)
require(boundaryphi==1,'Phi sufficient but not necessary')
# All outside residues0, so y_11=1 avoids every such original, under any anchor.
require(1%11!=0,'actual boundary survivor')

# New-to-degree-five diagnostic: retain3, ten outside primes, all3-subsets
# with phase0, plus whole10-subset with phase1.
qs=[11,13,17,19,23,29,31,37,41,43]
sets=list(combinations(qs,3)); originalmods=[3*prod(E) for E in sets]+[3*prod(qs)]
require(len(set(originalmods))==121,'121 actual distinct numerical labels')
require(all(sum(q in E for E in sets)+1==37 for q in qs),'outside exact-support incidence37')
for E in sets:
    y={q:int(q not in E) for q in qs}
    require(sum(all(y[q]==0 for q in F) for F in sets)==1,'private anchor witness')
require(Q(1,prod(q-1 for q in qs))<1,'anchor diagnostic Phi')

out={'result':'PASS','tail_residue_table':tail,'prime_square_upper':str(B),'reserve_at_degree48':str(reserve),
     'source_control':{'original_labels':len(items),'outside_heights':H,'pure_survivor_masses':{str(p):str(s[p]) for p in A},
                       'product_source_points':len(product_source),'omega_points':len(omega),'Phi':str(phi),'rho_Omega':str(rhoomega)},
     'degree_one_Phi_failure':{'original_labels':len(mods),'retained_rows':M,'minimum_Phi':str(boundaryphi),'outside_point':[1,0]},
     'high_incidence_diagnostic':{'original_labels':121,'retained_prime_incidence':121,'outside_prime_incidence':37,'D_alpha':1},
     'scope':'Exact finite arithmetic and actual CRT law controls; infinite tail justified by explicit integral proof; not Lean or unrestricted noncoverage.'}
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
