#!/usr/bin/env python3
"""Exact degree-five signed matching polynomials and actual joint avoidance ratios."""
import argparse
from fractions import Fraction as F
from collections import defaultdict
from itertools import combinations, product
from math import prod
from pathlib import Path
import importlib.util
import hashlib
import json
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/cover-geometry/support_degree_five.json'
SOURCES = ('certificate_io.py', 'problem-details/50-prime-support-incidence-at-most-five.md', '../../../Library/Arith/scottsokal2003repulsive.md')

def require(c,msg):
    if not c:raise ValueError(msg)
def t(p):return F(5,12) if p==5 else F(4,17) if p==7 else F(1,p-3)
def b(p):return F(1,p-2)

def polynomial_fixture(name,edges):
    edges=tuple(sorted({frozenset(E) for E in edges},key=lambda E:(len(E),sorted(E))))
    n=len(edges);primes=sorted(set().union(*edges))
    require(all(len(E)>=2 for E in edges),'all original supports nonsingleton')
    require(max(sum(p in E for E in edges) for p in primes)<=5,'actual support incidence at most5')
    w=tuple(prod(b(p) for p in E) for E in edges)
    inc={p:sum(1<<i for i,E in enumerate(edges) if p in E) for p in primes}
    incompatible=[sum(1<<j for j,T in enumerate(edges) if E&T) for E in edges]
    Z=[F(1)]*(1<<n)
    for mask in range(1,1<<n):
        low=mask&-mask;i=low.bit_length()-1
        Z[mask]=Z[mask^low]-w[i]*Z[mask&~incompatible[i]]
        require(Z[mask]>0,'every induced support-event polynomial positive')
    mindeg4=F(1);minroot=F(1);ratio_count=0;deletion_count=0
    for mask in range(1<<n):
        for p in primes:
            away=mask&~inc[p]
            # Independent vertex-deletion identity compared against edge recursion.
            rhs=Z[away]
            for i,E in enumerate(edges):
                if mask>>i&1 and p in E:
                    withoutE=mask
                    for q in E:withoutE&=~inc[q]
                    rhs-=w[i]*Z[withoutE]
            require(rhs==Z[mask],'vertex deletion identity retains entire supports')
            deletion_count+=1
            if p==3:
                R=Z[mask]/Z[away];require(R>=F(1,40),'ternary root ratio')
                minroot=min(minroot,R);ratio_count+=1
            elif not (mask&inc.get(3,0)) and (mask&inc[p]).bit_count()<=4:
                R=Z[mask]/Z[away];require(R>=b(p)/t(p),'degree-drop conditional ratio')
                mindeg4=min(mindeg4,R);ratio_count+=1
    full=(1<<n)-1
    return dict(name=name,supports=[sorted(E) for E in edges],subfamilies=1<<n,Z=str(Z[full]),
                ternary_free_Z=str(Z[full&~inc.get(3,0)]),min_root_ratio=str(minroot),
                min_away_degree4_ratio=str(mindeg4),ratio_checks=ratio_count,vertex_deletion_checks=deletion_count)


def label(exponents,residues):
    ee={p:e for p,e in exponents.items() if e};rr={p:residues.get(p,0)%p**e for p,e in ee.items()}
    d=prod(p**e for p,e in ee.items())
    a=sum(rr[p]*(d//p**e)*pow(d//p**e,-1,p**e) for p,e in ee.items())%d
    require(all(a%p**e==rr[p] for p,e in ee.items()),'actual CRT label')
    return dict(d=d,a=a,e=ee,r=rr)

def fixture(name,labels):
    require(len(labels)==len({l['d'] for l in labels}),'distinct original numerical moduli')
    primes=sorted(set().union(*(set(l['e']) for l in labels)))
    heights={p:max(l['e'].get(p,0) for l in labels) for p in primes}
    groups={};pures={p:[] for p in primes}
    for l in labels:
        E=frozenset(l['e'])
        if len(E)==1:pures[next(iter(E))].append(l)
        else:groups.setdefault(E,[]).append(l)
    edges=tuple(sorted(groups,key=lambda E:(len(E),sorted(E))));n=len(edges);full=(1<<n)-1
    degree={p:sum(p in E for E in edges) for p in primes}
    require(max(degree.values())<=5,'original distinct-support incidence<=5')
    def match(l,p,x):return p not in l['e'] or x%p**l['e'][p]==l['r'][p]
    atoms={}
    for p in primes:
        signatures=defaultdict(list)
        for x in range(p**heights[p]):
            if any(match(l,p,x) for l in pures[p]):continue
            signatures[tuple(match(l,p,x) for l in labels)].append(x)
        atoms[p]=[(xs[0],len(xs)) for xs in signatures.values()]
        require(F(sum(c for x,c in atoms[p]),p**heights[p])>=F(p-2,p-1),'actual pure survivor mass')
    purecount=prod(sum(c for x,c in atoms[p]) for p in primes)
    histogram=[0]*(1<<n)
    for choice in product(*(atoms[p] for p in primes)):
        values={p:choice[j][0] for j,p in enumerate(primes)}
        count=prod(v[1] for v in choice);mask=0
        for i,E in enumerate(edges):
            if any(all(match(l,p,values[p]) for p in E) for l in groups[E]):mask|=1<<i
        histogram[mask]+=count
    require(sum(histogram)==purecount,'entire actual pure-survivor product counted')
    subcount=histogram.copy()
    for i in range(n):
        for mask in range(1<<n):
            if mask>>i&1:subcount[mask]+=subcount[mask^(1<<i)]
    avoid=[subcount[full^mask] for mask in range(1<<n)]
    w=[prod(F(1,p-2) for p in E) for E in edges]
    inc={p:sum(1<<i for i,E in enumerate(edges) if p in E) for p in primes}
    conflict=[sum(1<<j for j,T in enumerate(edges) if E&T) for E in edges]
    Z=[F(1)]*(1<<n)
    for mask in range(1,1<<n):
        low=mask&-mask;i=low.bit_length()-1
        Z[mask]=Z[mask^low]-w[i]*Z[mask&~conflict[i]]
        require(Z[mask]>0,'all induced signed polynomials positive')
        require(F(avoid[mask],purecount)>=Z[mask],'actual all-subfamily Shearer lower bounds')
    pairchecks=0;ratio_checks=0
    for i,E in enumerate(edges):
        actual_event=F(purecount-avoid[1<<i],purecount)
        require(actual_event<=w[i],'actual grouped original-label probability cap')
        for j,T in enumerate(edges[:i]):
            if not E&T:
                pairprob=1-F(avoid[1<<i]+avoid[1<<j]-avoid[(1<<i)|(1<<j)],purecount)
                other=F(purecount-avoid[1<<j],purecount)
                require(pairprob==actual_event*other,'actual disjoint-support event independence')
                pairchecks+=1
        for mask in range(1<<n):
            if mask>>i&1:
                prev=mask^(1<<i)
                require(avoid[prev]>0,'actual conditioning event positive')
                require(F(avoid[mask],avoid[prev])>=Z[mask]/Z[prev],'actual conditional avoidance ratio')
                ratio_checks+=1
    old=full&~inc.get(3,0)
    require(F(avoid[old],purecount)>=F(721,1440),'actual ternary-free complete survivor reserve')
    ratio=F(avoid[full],avoid[old]);poly_ratio=Z[full]/Z[old]
    require(ratio>=poly_ratio>=F(1,40),'actual joint old-source ternary conditional ratio')
    rho=F(avoid[full],purecount)
    require(rho>=F(721,57600),'actual full survivor lower bound')
    period=prod(p**heights[p] for p in primes)
    density=F(period,avoid[full]);cap=F(57600,721)*prod(F(p-1,p-2) for p in primes)
    require(density<=cap,'uniform full survivor Haar density')
    return dict(name=name,labels=labels,period=period,supports=[sorted(E) for E in edges],
                max_support_incidence=max(degree.values()),compressed_carrier=prod(len(atoms[p]) for p in primes),
                pure_survivor_count=purecount,full_survivor_count=avoid[full],rho_survival=str(rho),
                old_source_survival=str(F(avoid[old],purecount)),conditional_survival=str(ratio),
                polynomial_ratio=str(poly_ratio),signed_polynomial=str(Z[full]),
                all_subfamilies=len(Z),conditional_ratio_checks=ratio_checks,
                disjoint_support_independence_checks=pairchecks,actual_density=str(density),density_cap=str(cap))


def polynomial_checks():
    P=(5,7,11,13,17,19)
    monomials=sorted([(prod(t(p) for p in S),S) for k in range(1,len(P)+1) for S in combinations(P,k)],reverse=True)
    require(sum(v for v,S in monomials[:5])==F(39,40),'five largest monomial exact sum')
    require([set(S) for v,S in monomials[:5]]==[{5},{7},{11},{13},{5,7}],'five largest identities')
    require(F(1,14)<F(5,51) and F(5,96)<F(5,51),'infinite omitted singleton/pair screen')
    for p,expected,cap in ((5,F(2531,4760),F(3,5)),(7,F(599,840),F(3,4))):
        vals=[v for v,S in monomials if p not in S]
        require(sum(vals[:4])==expected<cap,'four largest refined cosupport budget')
    require(F(1,9)+F(1,36)+F(1,25)+F(1,48)==F(719,3600),'convex progression tail')
    require((1-F(5,2)*F(719,3600))/40==F(721,57600),'global mass reserve')

    six=(3,5,7,11,13,17)
    results=[polynomial_fixture('all pair supports on six primes',list(combinations(six,2)))]
    require(F(results[0]['Z'])==F(52,825),'K6 exact full matching polynomial')
    results.append(polynomial_fixture('six rank-five complements', [set(six)-{p} for p in six]))
    results.append(polynomial_fixture('five arbitrary-rank ternary cosupports near the certificate',
      [{3,5},{3,7},{3,11},{3,13},{3,5,7},{5,7,17},{5,11,19},{5,13,17,19},
       {7,11,13,17},{7,11,13,19},{11,13,17,19}]))
    results.append(polynomial_fixture('ternary-free rank mixtures with incidence5',
      list(combinations((5,7,11,13,17),2))+[{5,7,11,13,17}]))

    return dict(top_monomials=[dict(value=str(v),support=list(S)) for v,S in monomials[:5]],
                        fixtures=results,scope='All induced polynomials and exact ratios for actual simple support systems; finite checks supplement the rank-uniform induction.')


def actual_checks():
    six=(3,5,7,11,13,17)
    labels=[label({p:1},{p:0}) for p in six]+[label({3:2},{3:1})]
    for i,E in enumerate(combinations(six,2)):
        labels.append(label({p:1 for p in E},{p:(1+(i%max(1,p-1))) for p in E}))
    labels += [label({3:2,5:1},{3:4,5:2}),label({3:1,5:2},{3:1,5:7}),
               label({3:2,5:2},{3:4,5:7}),label({7:2,11:1},{7:8,11:3})]
    results=[fixture('K6 pair supports with higher original exponents',labels)]

    labels=[label({p:1},{p:0}) for p in six]
    for i,p in enumerate(six):
        E=set(six)-{p};labels.append(label({q:1 for q in E},{q:1+i%(q-1) for q in E}))
        high={q:1 for q in E};q=min(E);high[q]=2
        labels.append(label(high,{q:1 for q in E}))
    results.append(fixture('six rank-five supports with independent repeated exponent labels',labels))

    # Published source qualification example: a genuine old point has no ternary lift.
    labels=[label({5:1},{5:1}),label({3:1,5:1},{3:0,5:0}),
            label({3:1,5:2},{3:1,5:0}),label({3:1,5:3},{3:2,5:0})]
    results.append(fixture('actual impossible point source despite conditional Haar extension',labels))
    # Direct old point x=0 mod125 has ternary residues n=0,125,250 mod375.
    require(all(any(n%l['d']==l['a'] for l in labels[1:]) for n in (0,125,250)),
            'genuine old point has no avoiding ternary extension')
    require(all(n%5!=1 for n in (0,125,250)),'point survives all old-only originals')

    return dict(fixtures=results,scope='Actual original congruence events under complete pure-survivor product law; no projected-label distinctness or assumed joint factorization.')


def calculate(base):
    result = dict(schema='support-degree-five-v1', polynomials=polynomial_checks(), actual=actual_checks())
    result['source_sha256'] = {p:hashlib.sha256((base/p).read_bytes()).hexdigest() for p in SOURCES}
    result['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return json.loads(json.dumps(result))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('support_degree_five_io',args.base/'certificate_io.py')
    require(spec is not None and spec.loader is not None,'readable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact support-degree-five certificate replay')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
