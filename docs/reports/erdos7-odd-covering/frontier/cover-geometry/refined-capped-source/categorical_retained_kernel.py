#!/usr/bin/env python3
"""Finite exact controls for a categorical retained-submeasure interface.

No LP optimizer or large vertex product is run. Literal finite cylinders,
fractional retention, common-colour menus and full query hinges are checked.
Ordinary mathematics and arithmetic controls, not Lean or general positivity.
"""
from fractions import Fraction as F
from itertools import combinations,product
from math import prod
from pathlib import Path
import argparse
import json

LEAVES=(4,7,2,5,8)
CHECKS=0


def unique_object(pairs):
    result={}
    for key,value in pairs:
        if key in result:raise ValueError('duplicate JSON key: '+key)
        result[key]=value
    return result


def read_json(path):
    return json.loads(path.read_text(),object_pairs_hook=unique_object)


def need(ok,label):
    global CHECKS
    CHECKS+=1
    if not ok:raise ValueError(label)


def simplex_vertices(caps):
    vertices=set()
    for free in range(len(caps)):
        fixed=[i for i in range(len(caps)) if i!=free]
        for ends in product((0,1),repeat=len(fixed)):
            x=[F(0)]*len(caps)
            for i,e in zip(fixed,ends):x[i]=caps[i]*e
            x[free]=1-sum(x)
            if all(0<=x[i]<=caps[i] for i in range(len(caps))):vertices.add(tuple(x))
    return sorted(vertices)


def menus(table,probabilities):
    sizes=tuple(len(p) for p in probabilities)
    patterns=list(product(*(range(n) for n in sizes)))
    outputs={}
    for D in range(1<<len(sizes)):
        active=[i for i in range(len(sizes)) if D>>i&1]
        entries={}
        for kappa in product(*(range(sizes[i]) for i in active)):
            response=[]
            for leaf in range(5):
                value=F(0)
                for s in patterns:
                    if any(s[i]!=c for i,c in zip(active,kappa)):continue
                    weight=prod((probabilities[i][s[i]] for i in range(len(sizes)) if not D>>i&1),start=F(1))
                    value+=weight*table[leaf][s]
                response.append(value)
            entries[kappa]=response
        F0=max(sum(v,F(0)) for v in entries.values())
        F1=max(max(sum(v[:2],F(0)),sum(v[2:],F(0))) for v in entries.values())
        F2=max(max(v) for v in entries.values())
        need(0<=F2<=F1<=F0<=1,'common-colour epigraphs are valid bounded responses')
        outputs[D]=(entries,(F0,F1,F2))
    return outputs


def inventories(primes,caps,selected):
    beta=[prod((caps[i]/(p-1) for i,p in enumerate(primes) if D>>i&1),start=F(1))
          for D in range(1<<len(primes))]
    residual=[[beta[D] if D and (h>0 or D.bit_count()>=2) else F(0)
               for D in range(len(beta))] for h in range(3)]
    need(len({m for m,a in selected})==len(selected),'selected numerical labels occur once')
    for m,a in selected:
        h,n=0,m
        while n%3==0:h+=1;n//=3
        D=sum(1<<i for i,p in enumerate(primes) if n%p==0)
        need(h<=2 and D and (h>0 or D.bit_count()>=2),'selected shallow mixed support type')
        residual[h][D]-=prod((caps[i] for i in range(len(primes)) if D>>i&1),start=F(1))/n
    need(all(x>=0 for row in residual for x in row),'nonnegative complete residual inventory')
    return beta,residual


def lower(table,probabilities,beta,residual):
    responses=menus(table,probabilities)
    mass=responses[0][1][0]
    high=sum((beta[D]*responses[D][1][2]/2 for D in range(len(beta))),F(0))
    shallow=sum((residual[h][D]*responses[D][1][h] for h in range(3) for D in range(len(beta))),F(0))
    return mass-high-shallow,mass,high,shallow,responses


def hinge(primes,caps,h,r,v):
    need(0<=v<=r<=1 and all(1<=c<=p for p,c in zip(primes,caps)),
         'query comparison has genuine probability tails')
    atoms={1:F(1)}
    for axis,p in enumerate((3,)+tuple(primes)):
        def tail(j):
            if j==1:return F(1)
            if axis==0:return r if j==2 else v/3**(j-3)
            return caps[axis-1]/p**(j-1)
        new={}
        for n,mass in atoms.items():
            for j in range(1,max(0,h-1)//n+1):
                z=tail(j)-tail(j+1)
                need(z>=0,'nonnegative auxiliary atom')
                new[n*j]=new.get(n*j,F(0))+mass*z
        atoms=new
    mean=(1+r+3*v/2)*prod((1+c/(p-1) for p,c in zip(primes,caps)),start=F(1))
    return mean-h+sum(((h-n)*mass for n,mass in atoms.items()),F(0))


def small_counterexamples(data):
    weights=tuple(map(F,data['weights']))
    need(sum(weights)==1 and all(w>=0 for w in weights),'nonmonotone example normalized law')
    def keep(leaf,x5):return x5==0 if leaf%3==1 else x5!=0
    actual=sum((weights[LEAVES.index(x%9)]/5 for x in range(45)
                if x%9 in LEAVES and keep(x%9,x%5) and x%15==10),F(0))
    responses=[[w*int(keep(l,d)) for l,w in zip(LEAVES,weights)] for d in range(5)]
    wrong=F(4,15)*max(sum(responses[1][:2]),sum(responses[1][2:]))
    valid=F(4,15)*max(max(sum(x[:2]),sum(x[2:])) for x in responses)
    common=max(map(sum,responses));separate=sum(max(x[i] for x in responses) for i in range(5))
    need((actual,wrong,valid)==tuple(map(F,data['expected_masses'])) and wrong<actual<=valid,
         'nonmonotone force-miss counterexample and valid common-colour bound')
    need(common==F(4,5) and separate==1,'one common colour cannot be optimized independently per leaf')
    deep=[]
    for hole in (1,6):
        digit=[sum((F(1,24) for x in range(25) if x!=hole and x%5==d),F(0)) for d in range(5)]
        mass=sum((F(1,120) for x in range(225) if x%9 in LEAVES and x%25!=hole and x%75==1),F(0))
        need(digit==[F(5,24),F(1,6),F(5,24),F(5,24),F(5,24)],'entire first-digit laws agree')
        need(mass==(0 if hole==1 else F(1,60)),'deep nullity differs under identical first-digit law')
        deep.append(dict(pure25hole=hole,first_digit=list(map(str,digit)),mixed75mass=str(mass)))
    caps=(F(4,15),F(4,15),F(4,5));vertices=simplex_vertices(caps)
    need(len(vertices)==5 and tuple(map(F,data['all_upper_colour_vertex'])) in vertices,
         'tight categorical cap simplex keeps its all-upper two-colour vertex')
    counts=[]
    for p in (5,7,11,13,17,19,23):
        c=F(p-1,p*(p-2));rest=1-(p-2)*c
        need(rest==F(1,p) and 0<rest<c and (p-2)*c<1<(p-1)*c,'full-digit vertex shape')
        counts.append(dict(prime=p,vertices=p*(p-1)))
    count=prod(row['vertices'] for row in counts)
    need(count==data['expected_product_vertices'],'full-digit product vertex count')
    return dict(nonmonotone=dict(actual=str(actual),false_bound=str(wrong),valid_bound=str(valid),
                                common_colour_max=str(common),separate_leaf_maxima=str(separate)),
                deep_nullity=deep,capped5_vertices=[list(map(str,x)) for x in vertices],
                full_digit_local_counts=counts,product_vertex_count=count)


def calculate(cert):
    global CHECKS
    CHECKS=0
    need(cert['schema']=='categorical-retained-kernel-v1','certificate schema')
    need(cert['normalization']=='mu=lambda_w restricted to U / lambda_w(U)',
         'continuation normalizes the full actual source restriction')
    qs=tuple(cert['example']['primes']);caps=tuple(map(F,cert['example']['caps']))
    need(qs==(5,7) and caps==(F(4,3),F(6,5)),'declared small prime/cap example')
    need(all(1<=c<=p for p,c in zip(qs,caps)),'valid complete-query cap range')
    partitions=cert['example']['partitions'];colour=[]
    for p,parts in zip(qs,partitions):
        need(all(parts) and sorted(x for part in parts for x in part)==list(range(p)),
             'nonempty disjoint colour classes partition each first-digit carrier')
        colour.append({x:i for i,part in enumerate(parts) for x in part})
    patterns=list(product(*(range(len(parts)) for parts in partitions)))
    weights=tuple(map(F,cert['example']['weights']))
    need(len(weights)==5 and all(w>=0 for w in weights) and sum(weights)==1,'fixed normalized five-leaf law')
    raw=cert['example']['kernel'];need(len(raw)==5 and all(len(row)==len(patterns) for row in raw),'complete finite retained table')
    table=[{s:F(x) for s,x in zip(patterns,row)} for row in raw]
    for l in range(5):
        for s in patterns:need(0<=table[l][s]<=weights[l],'retention is a genuine dominated submeasure')
    need(any(0<table[l][s]<weights[l] for l in range(5) for s in patterns),'example contains fractional retention')
    selected=[tuple(x) for x in cert['example']['selected']]
    family=[tuple(x) for x in cert['example']['actual_family']]
    need(len({m for m,a in family})==len(family),'distinct numerical actual originals')
    need((3,0) in family and (9,1) in family and (25,6) in family,'literal pure source exclusions')
    need(set(selected)<=set(family),'selected phases refer to this same actual family')
    for m,a in family:
        need(type(m) is int and m>1 and m%2==1 and type(a) is int and 0<=a<m,'odd canonical actual class')
        n=m
        for p in (3,5,7):
            while n%p==0:n//=p
        need(n==1 and 4725%m==0,'full finite carrier resolves this old family')
        if m in (3,9):
            need(all(leaf%m!=a for leaf in LEAVES),'shallow pure ternary original is null on the actual source')
        if m in (5,25,7):
            need((m,a)==(25,6),'every actual pure nonternary original is absorbed in its source law')
    for m,a in selected:
        h,n=0,m
        while n%3==0:h+=1;n//=3
        for l,leaf in enumerate(LEAVES):
            if h and leaf%3**h!=a%3**h:continue
            for s in patterns:
                if all(n%p!=0 or s[i]==colour[i][a%p] for i,p in enumerate(qs)):
                    need(table[l][s]==0,'selected actual phase is pointwise null in the same retained table')
    local=[tuple(F(0) if x==6 else F(1,24) for x in range(25)),(F(1,7),)*7]
    probabilities=[tuple(sum((local[i][x] for x in range(len(local[i])) if colour[i][x%p]==c),F(0))
                         for c in range(len(partitions[i]))) for i,p in enumerate(qs)]
    beta,residual=inventories(qs,caps,selected)
    L,M,high,shallow,response=lower(table,probabilities,beta,residual)
    points=[]
    fullmass=rawmass=survivor=fullsurvivor=F(0)
    for x in range(4725):
        if x%9 not in LEAVES:continue
        l=LEAVES.index(x%9);s=tuple(colour[i][x%p] for i,p in enumerate(qs))
        p=local[0][x%25]*local[1][x%7]/3
        w,nu=weights[l]*p,table[l][s]*p
        need(0<=nu<=w,'literal pointwise domination')
        fullmass+=w;rawmass+=nu
        live=all(x%m!=a for m,a in family)
        if live:survivor+=nu;fullsurvivor+=w
        points.append((x,l,w,nu))
    need(fullmass==1 and rawmass==M,'literal submeasure mass agrees with the categorical formula')
    need(L<=survivor<=fullsurvivor<=1,'complete inventory bound uses the one actual old survivor')
    moduli=[3**h*5**e*7**f for h in range(4) for e in range(3) for f in range(2)]
    bins={m:[F(0)]*m for m in moduli}
    for x,l,w,nu in points:
        if nu:
            for m in moduli:bins[m][x%m]+=nu
    cylinder_checks=0
    for h in range(4):
        for e in range(3):
            for f in range(2):
                n=5**e*7**f;D=int(e>0)+2*int(f>0);m=3**h*n
                bound=prod((caps[i] for i in range(2) if D>>i&1),start=F(1))/n
                bound*=response[D][1][min(h,2)]*(F(1,3) if h==3 else 1)
                for a,value in enumerate(bins[m]):
                    need(value<=bound,'literal arbitrary-phase cylinder obeys the common-colour menu')
                    cylinder_checks+=1
    factor_checks=0
    for e in range(3):
        for f in range(2):
            n=5**e*7**f;D=int(e>0)+2*int(f>0);active=[i for i in range(2) if D>>i&1]
            leafbins=[[F(0)]*n for l in range(5)]
            for x,l,w,nu in points:leafbins[l][x%n]+=nu
            for a in range(n):
                kappa=tuple(colour[i][a%qs[i]] for i in active)
                cylinder=F(1)
                for i,power in enumerate((5**e,7**f)):
                    if power>1:cylinder*=sum((mass for x,mass in enumerate(local[i]) if x%power==a%power),F(0))
                for l in range(5):
                    need(leafbins[l][a]==cylinder*response[D][0][kappa][l],
                         'exact common-colour factorization before any cap inequality')
                    factor_checks+=1
    local_vertices=[]
    for p,c,parts in zip(qs,caps,partitions):
        local_vertices.append(simplex_vertices(tuple(min(F(1),len(part)*c/p) for part in parts)))
    vertex_rows=[]
    for i,ps in enumerate(product(*local_vertices)):
        v=lower(table,ps,beta,residual)[0]
        vertex_rows.append(dict(index=i,probabilities=[list(map(str,p)) for p in ps],lower=str(v)))
    minimum=min(F(v['lower']) for v in vertex_rows)
    need(L>=minimum,'actual source vector respects the product-vertex lower bound')
    concavity=0
    for axis in range(2):
        other=1-axis
        for left,right in combinations(local_vertices[axis],2):
            for fixed in local_vertices[other]:
                ps=[None,None];ps[other]=fixed;ps[axis]=left;vl=lower(table,ps,beta,residual)[0]
                ps[axis]=right;vr=lower(table,ps,beta,residual)[0]
                ps[axis]=tuple((a+b)/2 for a,b in zip(left,right));vm=lower(table,ps,beta,residual)[0]
                need(2*vm>=vl+vr,'whole-local-simplex block concavity control')
                concavity+=1
    affine=[];r=max(sum(weights[:2]),sum(weights[2:]));v=max(weights)
    for h in range(28):
        H0=hinge(qs,caps,h,F(0),F(0));Hr=hinge(qs,caps,h,F(1),F(0))-H0
        Hv=hinge(qs,caps,h,F(1),F(1))-H0-Hr;actual=hinge(qs,caps,h,r,v)
        need(H0>=0 and Hr>=0 and Hv>=0 and actual==H0+Hr*r+Hv*v,
             'complete query hinge is affine with nonnegative coefficients')
        affine.append(dict(h=h,constant=str(H0),root=str(Hr),leaf=str(Hv),actual=str(actual)))
    small=small_counterexamples(cert['counterexamples'])
    return dict(schema='categorical-retained-kernel-result-v1',check_count=CHECKS,
                scope='Small exact controls for the ordinary categorical retained-submeasure theorem; no LP optimization, general positive solution or Lean claim.',
                literal_example=dict(period=4725,weights=list(map(str,weights)),categorical_probabilities=[list(map(str,p)) for p in probabilities],
                    full_source_mass=str(fullmass),retained_mass=str(M),retained_survivor_mass=str(survivor),full_survivor_mass=str(fullsurvivor),
                    inventory_lower=str(L),high_charge=str(high),shallow_charge=str(shallow),uniform_vertex_lower=str(minimum),
                    cylinder_checks=cylinder_checks,factorization_checks=factor_checks,block_concavity_checks=concavity,
                    product_vertices=vertex_rows),hinge_coefficients=affine,counterexamples=small)


def main():
    here=Path(__file__);parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=here.with_name(here.stem+'_certificate.json'))
    parser.add_argument('--result',type=Path,default=here.with_suffix('.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args();result=calculate(read_json(args.certificate))
    if args.write_result:args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(result==read_json(args.result),'retained exact result replay')
    example=result['literal_example']
    print(json.dumps(dict(check_count=result['check_count'],retained_survivor_mass=example['retained_survivor_mass'],full_survivor_mass=example['full_survivor_mass'],inventory_lower=example['inventory_lower'],uniform_vertex_lower=example['uniform_vertex_lower'],product_vertex_count=result['counterexamples']['product_vertex_count'])))


if __name__=='__main__':main()
