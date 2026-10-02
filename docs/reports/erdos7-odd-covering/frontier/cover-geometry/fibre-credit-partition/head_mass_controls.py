"""Small exact controls for supported-head min caps and geometric depth sums."""
import argparse
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json
import random

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output',required=True)
args=ap.parse_args()
checks=0
P,Q=(5,7),(11,13)
V=P+Q


def need(ok,msg):
    global checks
    checks+=1
    if not ok:
        raise ValueError(msg)


def mul(xs):
    return prod(xs,start=F(1))


def values(heads,depths,c,w,table,gamma,mode='min'):
    candidates=[]
    for address,T in table.items():
        row=dict(zip(heads,address))
        local={}
        for r in (1,2):
            factors=[]
            for p in heads:
                cap=c[p]/p**depths[p]
                mass=w[p][r][row[p]]
                factors.append(min(cap,mass) if mode=='min' else
                               cap*int(mass>0) if mode=='zero' else cap)
            local[r]=gamma[r]*T[r]*mul(factors)
        candidates.append((sum(local.values()),max(local.values())))
    return tuple(max(t[k] for t in candidates) for k in (0,1))


def threshold(heads,lower,c,w):
    result={}
    for p in heads:
        positive=[v for r in (1,2) for v in w[p][r] if v>0]
        n=lower[p]
        if positive:
            while c[p]/p**n>min(positive):
                n+=1
        result[p]=n
    return result


def sum_depths(heads,lower,c,w,table,gamma,upper=None,extra=0):
    n={p:k+extra for p,k in threshold(heads,lower,c,w).items()}
    labels=[]
    for p in heads:
        end=n[p]-1 if upper is None else min(n[p]-1,upper[p])
        axis=[(e,F(1)) for e in range(lower[p],end+1)]
        if upper is None or upper[p]>=n[p]:
            factor=F(p,p-1) if upper is None else sum(F(1,p**t) for t in range(upper[p]-n[p]+1))
            axis.append((n[p],factor))
        labels.append(axis)
    total=[F(0),F(0)]
    for cell in product(*labels):
        depth={p:e for p,(e,_) in zip(heads,cell)}
        scale=mul(f for _,f in cell)
        val=values(heads,depth,c,w,table,gamma)
        for k in (0,1):
            total[k]+=scale*val[k]
    return tuple(total),n


stats={'actual_finite_sources':0,'actual_original_root_bounds':0,
       'actual_free_same_address_bounds':0,'actual_selected_once_bounds':0,
       'strict_min_vs_zero_candidate_bounds':0,'geometric_inventory_controls':0}
geometric_examples=[]
for seed in range(12):
    rng=random.Random(880000+seed)
    universes={p:set(range(p*p)) for p in V}
    def cyl(p,e,a):
        return {t for t in universes[p] if t%p**e==a}
    base={p:universes[p]-cyl(p,1,rng.randrange(p))-cyl(p,2,rng.randrange(p*p)) for p in V}
    c={p:F(p*p,len(base[p])) for p in V}
    stars={p:{r:set() for r in (1,2)} for p in V}
    for p in V:
        for e in (1,2):
            stars[p][1+rng.randrange(2)] |= cyl(p,e,rng.randrange(p**e))
    keep={p:{r:base[p]-stars[p][r] for r in (1,2)} for p in V}
    g={p:{r:F(len(keep[p][r]),len(base[p])) for r in (1,2)} for p in V}
    need(all(g[p][r]>0 for p in V for r in (1,2)),'Actual positive coordinate carriers')
    w={p:{r:[F(len(cyl(p,1,i)&keep[p][r]),len(base[p])) for i in range(p)]
          for r in (1,2)} for p in P}
    projections={p:{q:{r:[set() for _ in range(p)] for r in (1,2)} for q in Q} for p in P}
    for p,q,e in product(P,Q,(1,2)):
        i,a=rng.randrange(p),rng.randrange(q**e)
        for r in (1,2):
            projections[p][q][r][i] |= cyl(q,e,a)
        i,a,r=rng.randrange(p),rng.randrange(q**e),1+rng.randrange(2)
        projections[p][q][r][i] |= cyl(q,e,a)
    x={q:{r:[F(len(A&keep[q][r]),len(keep[q][r])) for A in projections[5][q][r]]
          for r in (1,2)} for q in Q}
    y={q:{r:[F(len(A&keep[q][r]),len(keep[q][r])) for A in projections[7][q][r]]
          for r in (1,2)} for q in Q}
    gamma={1:F(2,5),2:F(3,5)}
    for D,e in (((5,11),{5:2,11:1}),((5,7),{5:1,7:1}),
                 ((5,11,13),{5:1,11:2,13:1}),((11,13),{11:1,13:2})):
        heads=tuple(p for p in P if p in D)
        table={}
        for address in product(*(range(p) for p in heads)):
            fixed=dict(zip(heads,address))
            table[address]={}
            for r in (1,2):
                total=F(0)
                for i,j in product(range(5),range(7)):
                    row={5:i,7:j}
                    if any(row[p]!=fixed[p] for p in heads):
                        continue
                    total+=mul(w[p][r][row[p]] for p in P if p not in D)*mul(
                        1-max(x[q][r][i],y[q][r][j]) for q in Q if q not in D)
                table[address][r]=total*mul(g[q][r] for q in Q if q not in D)
        phases={p:rng.randrange(p**e[p]) for p in D}
        original={p:cyl(p,e[p],phases[p]) for p in D}
        address=tuple(phases[p]%p for p in heads)
        private_cap=mul(c[q]/q**e[q] for q in Q if q in D)
        actual={}
        for r in (1,2):
            actual[r]=F(0)
            for i,j in product(range(5),range(7)):
                row={5:i,7:j}
                factors=[]
                for p in P:
                    A=cyl(p,1,row[p])&keep[p][r]
                    if p in D:
                        A &= original[p]
                    factors.append(F(len(A),len(base[p])))
                for q in Q:
                    A=keep[q][r]-(projections[5][q][r][i]|projections[7][q][r][j])
                    if q in D:
                        A &= original[q]
                    factors.append(F(len(A),len(base[q])))
                actual[r]+=mul(factors)
            strong=private_cap*table[address][r]*mul(
                min(c[p]/p**e[p],w[p][r][phases[p]%p]) for p in heads)
            zero=private_cap*table[address][r]*mul(
                c[p]/p**e[p]*int(w[p][r][phases[p]%p]>0) for p in heads)
            old=private_cap*table[address][r]*mul(c[p]/p**e[p] for p in heads)
            need(actual[r]<=strong<=zero<=old,'HM2 actual original intersection and min/zero/old ordering')
            stats['actual_original_root_bounds']+=1
            stats['strict_min_vs_zero_candidate_bounds']+=int(strong<zero)
        depth={p:e[p] for p in heads}
        strong=values(heads,depth,c,w,table,gamma)
        zero=values(heads,depth,c,w,table,gamma,'zero')
        old=values(heads,depth,c,w,table,gamma,'old')
        need(all(strong[k]<=zero[k]<=old[k] for k in (0,1)),'HM5 after correct free/selected maxima')
        need(sum(gamma[r]*actual[r] for r in (1,2))<=private_cap*strong[0],
             'Free original same physical address across roots')
        stats['actual_free_same_address_bounds']+=1
        active=1+seed%2
        need(gamma[active]*actual[active]<=private_cap*strong[1], 'Selected original active only once')
        stats['actual_selected_once_bounds']+=1
        lower={p:2 if len(D)==2 and len(heads)==1 else 1 for p in heads}
        exact,n=sum_depths(heads,lower,c,w,table,gamma)
        later,_=sum_depths(heads,lower,c,w,table,gamma,extra=2)
        need(exact==later,'HM10 independent later valid tail cutoff agrees exactly')
        upper={p:n[p]+2 for p in heads}
        finite,_=sum_depths(heads,lower,c,w,table,gamma,upper=upper)
        direct=[F(0),F(0)]
        for exp in product(*(range(lower[p],upper[p]+1) for p in heads)):
            val=values(heads,dict(zip(heads,exp)),c,w,table,gamma)
            for k in (0,1):
                direct[k]+=val[k]
        need(finite==tuple(direct),'Finite-window geometric algorithm versus literal per-depth maxima')
        # A separate original-cap bound controls everything outside the finite box.
        full_cap=mul(c[p]*F(1,p**lower[p])*F(p,p-1) for p in heads)
        box_cap=mul(sum(c[p]/p**j for j in range(lower[p],upper[p]+1)) for p in heads)
        free_T=max(sum(gamma[r]*T[r] for r in (1,2)) for T in table.values())
        selected_T=max(gamma[r]*T[r] for T in table.values() for r in (1,2))
        for k,T in enumerate((free_T,selected_T)):
            need(direct[k]<=exact[k]<=direct[k]+(full_cap-box_cap)*T,
                 'Infinite exact sum between literal finite sum and independent cap-tail bound')
        stats['geometric_inventory_controls']+=1
        if seed==0:
            geometric_examples.append({'support':list(D),'lower':lower,'tail_start':n,
                                       'free':str(exact[0]),'selected':str(exact[1])})
    stats['actual_finite_sources']+=1

# Exact sum/max interchange counterexample; it is an algebraic fixture.
c={5:F(5,4)}
w={5:{r:[F(1,4),F(1,20),F(0),F(0),F(0)] for r in (1,2)}}
table={(i,):{r:(F(1,2) if i==0 else F(1) if i==1 else F(0)) for r in (1,2)} for i in range(5)}
summed,_=sum_depths((5,),{5:1},c,w,table,{1:F(1),2:F(0)})
need(summed[0]==F(3,16),'Sum of depthwise address maxima')
fixed_sums=(F(5,32),F(9,80))
need(max(fixed_sums)==F(5,32)<summed[0] and summed[0]-max(fixed_sums)==F(1,32),
     'Moving max outside depth sum loses required fee')

# An all-positive uniform head source recovers the old depth inventory exactly.
c={p:F(1) for p in P}
w={p:{r:[F(1,p)]*p for r in (1,2)} for p in P}
gamma={1:F(1,3),2:F(2,3)}
for heads,lower in (((5,),{5:2}),((5,),{5:1}),((5,7),{5:1,7:1}), ((),{})):
    table={address:{1:F(1),2:F(1)} for address in product(*(range(p) for p in heads))}
    total,_=sum_depths(heads,lower,c,w,table,gamma)
    inventory=mul(F(1,p**lower[p])*F(p,p-1) for p in heads)
    need(total==(inventory,F(2,3)*inventory),'Correct shallow group exclusion and both-head first powers')

# 275: original depth cap and row mass are alternative upper bounds.
support5={x for x in range(25) if x%5!=0}
support11=set(range(1,11))
cap5=F(5,4)/25
row5=F(len({x for x in support5 if x%5==1}),len(support5))
actual=F(1,len(support5))*F(1,len(support11))
need(actual==F(1,200)==min(cap5,row5)*F(1,10),'HM1 retains literal275 true mass')
need(cap5*row5*F(1,10)==F(1,800)<actual,'Multiplying cap and row mass remains invalid')
empty_row=F(len({x for x in support5 if x%5==0}),len(support5))
need(empty_row==0 and min(cap5,empty_row)==0 and cap5>0,
     'A supported original in a pure-deleted row has zero mass at every depth')

# Every-zero supported head is a valid boundary case of the finite tail algorithm.
zw={5:{r:[F(0)]*5 for r in (1,2)}}
table={(i,):{r:F(1) for r in (1,2)} for i in range(5)}
zero,n=sum_depths((5,),{5:2},{5:F(4,3)},zw,table,gamma)
need(zero==(F(0),F(0)) and n[5]==2,'All-zero head tail convention')
need(stats['strict_min_vs_zero_candidate_bounds']>0,'Actual controls exercise finite positive partial-row caps')

result={
    'contract':'Supported-head actual probability min cap and exact geometric allowance; no new optimization or uniform survivor claim.',
    'checks':checks,'statistics':stats,'geometric_examples':geometric_examples,
    'counterexamples':{
        'sum_max':{'correct':'3/16','incorrect_max_sum':'5/32','undercharge':'1/32',
                   'scope':'Scalar algebraic interchange counterexample, not claimed as a complete AP family.'},
        'cap_times_row':{'modulus':275,'actual_mass':'1/200','correct_min_bound':'1/200',
                         'incorrect_product':'1/800'},
    },
    'limits':['The complete geometric result sums per-original upper allowances, not actual deleted mass.',
              'All head-depth maxima remain inside the numerical-original sums.',
              'Zero-row tests use exact rational zero; no approximation to row positivity.',
              'No array optimization or Lean verification is asserted.'],
}
Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'checks':checks,'statistics':stats,'output':args.output}))
