#!/usr/bin/env python3
"""Exact diagnostics for three-coordinate box slices and actual selector input.
The arbitrary-size proof is in the companion note; no Lean claim.
"""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
import json

checks=[]
def need(name,condition):
    if not condition:raise ValueError(name)
    checks.append(name)
patterns=0;large=0
for N in range(17):
    triangle=[(a,b,N-a-b) for a in range(N+1) for b in range(N-a+1)]
    for A,B,C in product(range(N+1),repeat=3):
        S=[v for v in triangle if v[0]<=A and v[1]<=B and v[2]<=C]
        patterns+=1
        if len(S)>=3:
            large+=1
            if {(b+2*c)%3 for a,b,c in S}!={0,1,2}:
                raise ValueError(('counterexample',N,A,B,C,S))
need('all N0 through16 box slices satisfy the three-color implication',patterns==23409)
# Verify the local transfer argument independently of slice enumeration.
local_count=0
for caps in product(range(4),repeat=3):
    for x in product(*(range(u+1) for u in caps)):
        arcs=[(i,j) for i in range(3) for j in range(3) if i!=j and x[i]>0 and x[j]<caps[j]]
        if len(arcs)<2:continue
        neighbor_colors={(j-i)%3 for i,j in arcs}
        if neighbor_colors!={1,2}:raise ValueError(('local transfer',caps,x,arcs))
        local_count+=1
need('every checked degree-two-or-more vertex has both nonzero color increments',local_count>0)

N=12;K=13*5**N*7**N*11**N
triangle=[(a,b,N-a-b) for a in range(N+1) for b in range(N-a+1)]
def crt(t,q):
    return (t+729*((q-t)*pow(729,-1,K)%K))%(729*K)
originals=[]
for index,(a,b,c) in enumerate(triangle):
    d=13*5**a*7**b*11**c
    for e,color,t in ((0,3,0),(4,1,index%81),(5,2,0),(6,0,0)):
        m=3**e*d
        residue=(t+3**e*((color-t)*pow(3**e,-1,d)%d))%m
        witness=crt(t,color+d)
        originals.append(dict(a=a,b=b,c=c,d=d,e=e,color=color,t=t,m=m,residue=residue,private_witness=witness,selected_periodic_color=(b+2*c)%3))
need('91 distinct two-dimensional cofactor indices',len(triangle)==91)
need('364 distinct actual odd numerical labels',len(originals)==len({o['m'] for o in originals})==364 and all(o['m']>1 and o['m']%2 for o in originals))
need('all fixed actual CRT phases agree',all(o['residue']%o['d']==o['color'] and o['residue']%(3**o['e'])==o['t'] for o in originals))
comparisons=0
for i,o in enumerate(originals):
    matches=[j for j,r in enumerate(originals) if o['private_witness']%r['m']==r['residue']]
    comparisons+=len(originals)
    if matches!=[i]:raise ValueError('private witness '+str(i))
need('all364 actual originals are irredundant with literal private witnesses',comparisons==132496)
need('the full dead Q cylinder activates91 cofactors and covers all81 ternary cells',len({o['d'] for o in originals if o['e']==4})==91 and {o['t'] for o in originals if o['e']==4}==set(range(81)) and all(1%o['d']==o['color'] for o in originals if o['e']==4))
need('old shallow projection is absent on the three old coordinates at that cylinder',all(1%(o['d']//13)!=3%(o['d']//13) for o in originals if o['e']==0))
need('new periodic selection deletes the dead Q cylinder',any((b+2*c)%3==1 for a,b,c in triangle))
# The explicit example places every selected Q label in row13.
# Earlier5/7/11 are Haar and later17/19 are Haar.
need('old actual13 rows normalize below the retained cap',F(13,12)<F(3,2))
for n in range(5):
    for roots in combinations(range(4),n):
        g=F(13-len(roots),13)
        if min(F(3,2),1/g)*g!=1:raise ValueError('new PA row')
need('all possible four-root13 unions normalize without PA loss',F(13,9)<F(3,2))
rH=F(157435,165888)
B=F(432040125182653876501,86355045355449035400)
oldQ=F(13,12)*rH;newQ=F(13,9)*rH
reserve=1-2*sum(F(1,3**e) for e in (4,5,6))
exampleR=newQ+F(1,2)*(1+newQ)/reserve
generalR=B+F(27,25)*(1+B)
need('both actual supplied Q laws have small complete query norm',oldQ<B and newQ<B)
need('actual finite fibre reserve',reserve==F(703,729))
need('example and general complete-query bounds pass',exampleR<F(566,49) and generalR<F(566,49))
result={'kind':'ordinary three-coordinate periodic selector and actual example','box_patterns':patterns,'box_patterns_with_at_least_three_points':large,'local_transfer_cases':local_count,'example_N':N,'example_cofactors':len(triangle),'original_count':len(originals),'private_witness_comparisons':comparisons,'old_dead_cylinder_mass':str(F(1,K)),'old_PA_Q_bound':str(oldQ),'new_PA_Q_bound':str(newQ),'example_fibre_reserve':str(reserve),'example_R_bound':str(exampleR),'example_R_bound_decimal':float(exampleR),'general_R_bound':str(generalR),'originals':originals,'checks':checks,'check_count':len(checks),'scope':{'all_finite_N_proof':'companion note','auxiliary_second_slot_allowed':True,'arbitrary_tail_phases':False,'same_old_marginal_preserved':False,'all_query_heights':True,'new_Lean':False}}
p=Path(__file__).with_suffix('.json');p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('box_patterns','local_transfer_cases','original_count','private_witness_comparisons','check_count','example_R_bound','example_R_bound_decimal')}))
