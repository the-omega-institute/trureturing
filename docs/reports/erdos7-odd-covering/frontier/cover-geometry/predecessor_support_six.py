#!/usr/bin/env python3
"""Exact shared ternary budget and actual original-label joint-law certificates."""
from fractions import Fraction as F
from collections import defaultdict
from itertools import combinations, combinations_with_replacement, product
from math import prod
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/cover-geometry/predecessor_support_six.json'
SOURCES = ('certificate_io.py', 'problem-details/53-shared-small-prime-budgets-for-six-or-seven-predecessor-supports.md', 'problem-details/52-two-or-four-exact-predecessor-supports.md', 'problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md', 'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md', 'problem-details/41-natural-four-predecessor-orders-are-noncovering.md', '../../../Library/Arith/schroeder2026noncoverage.md')

def require(c,msg):
    if not c: raise ValueError(msg)


def make_label(exponents, residues):
    exponents={p:e for p,e in exponents.items() if e}
    residues={p:residues.get(p,0) % p**e for p,e in exponents.items()}
    modulus=prod(p**e for p,e in exponents.items())
    residue=sum(residues[p]*(modulus//p**e)*pow(modulus//p**e,-1,p**e)
                for p,e in exponents.items()) % modulus
    require(all(residue%p**e==residues[p] for p,e in exponents.items()),'actual CRT label')
    return dict(e=exponents,r=residues,d=modulus,a=residue)


def fixture(name,primes,labels):
    require(len({l['d'] for l in labels})==len(labels),'distinct original numerical moduli')
    require(primes==sorted(primes),'numerical prime order')
    rank={p:i for i,p in enumerate(primes)}
    require(3 not in rank or rank[3]==0,'ternary first')
    heights={p:max(l['e'].get(p,0) for l in labels) for p in primes}
    groups={p:[] for p in primes}; pure={p:[] for p in primes}
    for l in labels:
        if len(l['e'])==1: pure[next(iter(l['e']))].append(l)
        else: groups[max(l['e'],key=rank.get)].append(l)
    patterns={}
    for p,ls in groups.items():
        ss={tuple(sorted(set(l['e'])-{p})) for l in ls}
        require(len(ss)<=6 and all(ss0 for ss0 in ss),'at most six exact nonempty predecessor supports')
        patterns[p]=tuple(frozenset(S) for S in sorted(ss))
    ternary_count=sum(3 in S for sets in patterns.values() for S in sets)
    require(ternary_count<=6,'shared count of original distinct mixed supports containing3')
    nominal_gram=[F(299,44),F(3403,330),F(373,30),F(443,30),F(491,30),F(521,30),F(3073,165)]
    def local_match(l,p,x): return p not in l['e'] or x%p**l['e'][p]==l['r'][p]
    # Partition the ACTUAL finite carrier by all original cylinder predicates.
    # Uniformity inside each cell is exact and preserved by every kernel.
    atoms={}; puremass={}
    for p in primes:
        signatures=defaultdict(list)
        for x in range(p**heights[p]):
            if any(local_match(l,p,x) for l in pure[p]): continue
            signatures[tuple(local_match(l,p,x) for l in labels)].append(x)
        n=sum(map(len,signatures.values())); require(n>0,'actual pure survivor nonempty')
        puremass[p]=F(n,p**heights[p])
        require(puremass[p]>=F(p-2,p-1),'pure survivor cap')
        atoms[p]=[(xs[0],len(xs),F(len(xs),n)) for xs in signatures.values()]
    delta={p:(F(2,5) if p==7 else F(1,2)) for p in primes}
    kappa={p:1/(1-delta[p]) if groups[p] and p!=5 else F(1) for p in primes}
    c={p:F(p-1,p-2) for p in primes}
    def matches(l,state,upto):
        return all(local_match(l,q,atoms[q][state[j]][0]) for j,q in enumerate(primes[:upto]))
    laws={():F(1)}; stages=[]
    for i,p in enumerate(primes):
        nxt=defaultdict(F); square=F(0); mean=F(0); badmass=F(0); killed=0; overhalf=0
        for state, mass in laws.items():
            active=[l for l in groups[p] if matches(l,state,i)]
            forbidden=[any(local_match(l,p,a[0]) for l in active) for a in atoms[p]]
            alpha=sum((a[2] for a,flag in zip(atoms[p],forbidden) if flag),F(0))
            square+=mass*alpha**2; mean+=mass*alpha
            killed+=int(alpha==1); overhalf+=int(alpha>delta[p])
            normalization=F(0); fibre_bad=F(0)
            for j,(a,flag) in enumerate(zip(atoms[p],forbidden)):
                if p==5: k=F(1)
                elif alpha<=delta[p]: k=F(0) if flag else 1/(1-alpha)
                else: k=(alpha-delta[p])/(alpha*(1-delta[p])) if flag else 1/(1-delta[p])
                require(0<=k<=kappa[p],'pointwise normalized-kernel cap')
                probability=k*a[2]; normalization+=probability
                fibre_bad+=probability*flag
                if probability: nxt[state+(j,)]+=mass*probability
            require(normalization==1,'exact fibre normalization including alpha=1')
            if p==5: require(fibre_bad==alpha,'unbiased fifth stage exact first moment')
            else: require(fibre_bad==max(F(0),alpha-delta[p])/(1-delta[p])<=alpha**2/(4*delta[p]*(1-delta[p])),'actual general-delta loss')
            badmass+=mass*fibre_bad
        if groups[p]:
            def d(q): return kappa[q]*F(q+1,(q-1)*(q-2))
            def t(q): return F(kappa[q],q-2)
            gram=sum((prod(d(q) for q in S&T)*prod(t(q) for q in S^T)
                      for S,T in product(patterns[p],repeat=2)),F(0))
            envelope=F(1,(p-2)**2)*gram
            require(gram<=(F(2) if p==5 else F(13,2) if p==7 else nominal_gram[sum(3 in S for S in patterns[p])]),'ternary-count-sensitive stage Gram cap')
            require(square<=envelope,'actual squared load versus full-support Gram')
        else: envelope=F(0)
        if p==5: require(badmass==mean<=F(1,3),'unbiased stage global first-moment cost')
        stages.append(dict(p=p,labels=len(groups[p]),alpha_mean=str(mean),alpha_square=str(square),bad_mass=str(badmass),
                           envelope=str(envelope),killed_fibres=killed,overthreshold_fibres=overhalf,delta=(None if p==5 else str(delta[p]))))
        require(sum(nxt.values(),F(0))==1,'entire prefix law normalized')
        # Every earlier full joint atom retains its source mass, not only its marginals.
        marg=defaultdict(F)
        for state,mass in nxt.items(): marg[state[:-1]]+=mass
        require(dict(marg)==laws,'complete earlier joint source preserved')
        laws=dict(nxt)
    alln=len(primes)
    survivor=sum((mass for state,mass in laws.items() if not any(matches(l,state,alln) for l in labels)),F(0))
    require(survivor>=F(314761,16465680),'complete actual survivor lower bound')
    require(1-survivor<=sum(F(s['bad_mass']) for s in stages),'joint union loss')
    # Pair-cylinder queries use actual residues, intersection and full joint law.
    queries=0
    for l,r in combinations_with_replacement(labels,2):
        union=set(l['e'])|set(r['e']); incompatible=False; bound=F(1)
        for p in union:
            a=l['e'].get(p,0);b=r['e'].get(p,0)
            if a and b and (l['r'][p]-r['r'][p])%p**min(a,b): incompatible=True
            bound*=kappa[p]*c[p]/p**max(a,b)
        actual=sum((mass for st,mass in laws.items() if matches(l,st,alln) and matches(r,st,alln)),F(0))
        require(actual==0 if incompatible else actual<=bound,'selected pair-cylinder cap')
        queries+=1
    D=prod(kappa[p]*c[p] for p in primes)
    maxdensity=F(0)
    for state,mass in laws.items():
        haar=prod(F(atoms[p][state[i]][1],p**heights[p]) for i,p in enumerate(primes))
        maxdensity=max(maxdensity,mass/haar)
    require(maxdensity<=D,'full joint Haar density, with pure-conditioning cost')
    raw_survivor=F(0); actual_count=0
    for state in product(*(range(len(atoms[p])) for p in primes)):
        if any(matches(l,state,alln) for l in labels):continue
        count=prod(atoms[p][state[i]][1] for i,p in enumerate(primes));actual_count+=count
        raw_survivor+=F(count,prod(p**heights[p] for p in primes))
    require(raw_survivor>=survivor/D,'actual Haar survivor lower bound')
    require(maxdensity/survivor<=F(16465680,314761)*D,'fully conditioned survivor density')
    return dict(name=name,ternary_support_count=ternary_count,primes=primes,heights=heights,original_labels=labels,period=prod(p**heights[p] for p in primes),
                compressed_carrier=prod(len(atoms[p]) for p in primes),positive_law_cells=len(laws),
                mixed_patterns={p:[sorted(S) for S in sets] for p,sets in patterns.items() if groups[p]},stages=stages,
                pair_cylinder_checks=queries,survivor_mass=str(survivor),haar_survivor=str(raw_survivor),
                actual_survivor_count=actual_count,max_density=str(maxdensity),theorem_density_cap=str(D))



# Pair-complete K7 has incidence6 and a six-predecessor final stage.

def scalar_checks():
    D=[F(1,2),F(4,9),F(4,15),F(2,9),F(7,33),F(3,20)]
    S=[sum(D[:b],F(0)) for b in range(7)]
    def bound(a,b,e):
        if a==0:
            if e:return None
            AA=F(0)
        elif e:
            r=a-1
            AA=2+2*S[r]+F(r*(r+3),3)
        else:
            AA=2*S[a]+F(a*(a-1),3)
        BB=S[b]+F(b*(b-1),6)
        AB=F(a*b,3)+F(2*min(a-e,b),3)+F(e*b,3)
        return AA+BB+AB
    G=[max(bound(a,6-a,e) for e in range(min(a,1)+1)) for a in range(7)]
    extra=[v-G[0] for v in G]
    primes=[11,13,17,19,23,29]
    def budget(B):
        dp={0:(F(0),[])}
        for p in primes[:B]:
            nd={}
            for used,(v,pat) in dp.items():
                for a in range(B-used+1):
                    val=v+extra[a]/(p-2)**2
                    if used+a not in nd or val>nd[used+a][0]:nd[used+a]=(val,pat+[(p,a)])
            dp=nd
        return max(dp.values())
    d={3:F(2),5:F(1,2)};t={3:F(1),5:F(1,3)}
    sets=[{3},{5},{3,5}]
    def entry(A,B):
        v=F(1)
        for p in A|B:v*=d[p] if p in A&B else t[p]
        return v
    base=G[0]*(F(1,81)+F(1,35))
    rows=[]
    for flag5 in (0,1):
        for mask in range(8):
            es=[sets[i] for i in range(3) if mask>>i&1]
            a=sum(3 in E for E in es)
            fee7=sum((entry(E,F_) for E in es for F_ in es),F(0))/24
            ex,allocation=budget(6-flag5-a)
            total=F(flag5,3)+fee7+base+ex
            rows.append(dict(flag5=flag5,mask7=mask,three_used=flag5+a,fee7=str(fee7),base=str(base),extra=str(ex),allocation=allocation,total=str(total),decimal=float(total)))
    result=dict(diagonal_top=[str(x) for x in D],gram=[str(x) for x in G],extra=[str(x) for x in extra],cases=rows,worst=max(rows,key=lambda x:F(x['total'])))
    require(all(v>=0 for v in extra),'nonnegative shared-budget increments')
    require(F(result['worst']['total'])==F(16150919,16465680)<1,'exact common-source fee')
    require(1-F(result['worst']['total'])==F(314761,16465680),'exact survivor reserve')
    return result


def actual_checks():
    ps=[3,5,7,11,13,17,19]
    ls=[make_label({p:1},{p:0}) for p in ps]
    for i,p in enumerate(ps):
        for q in ps[i+1:]:
            ls.append(make_label({p:1,q:1},{p:1,q:1}))
            if (p+q)%4==0:
                ls.append(make_label({p:2,q:1},{p:1+p,q:2}))
    results=[fixture('K7 pair supports with repeated original exponent inventories',ps,ls)]
    require(len(results[0]['mixed_patterns'][19])==6,'genuine six-support stage')
    require(results[0]['ternary_support_count']==6,'full shared ternary budget used')

    # The negative Shearer support envelope nevertheless has actual survivors.
    ss=[(3,5),(3,7),(3,11),(3,13),(3,17),(5,7),(5,11),(5,13),(5,17),
        (7,11),(7,13),(7,19),(11,13),(11,17),(11,19),(3,5,7)]
    ls=[make_label({p:1},{p:0}) for p in ps]
    for i,S in enumerate(ss):
        ls.append(make_label({p:1 for p in S},{p:(i%2+1) for p in S}))
        if i%4==0:
            ex={p:1 for p in S};ex[min(S)]=2
            ls.append(make_label(ex,{p:(1+p if p==min(S) else 1) for p in S}))
    results.append(fixture('actual mixed-rank family with negative support-Shearer polynomial',ps,ls))

    # Large ranks and six ternary supports at a single late stage.
    ps=[3,5,7,11,13,17,19,23,29]
    ls=[make_label({p:1},{p:0}) for p in ps]
    base={3,5,7,11,13}
    for i,T in enumerate((set(),{17},{19},{23},{17,19},{17,19,23})):
        S=base|T|{29}
        ls.append(make_label({p:1 for p in S},{p:(i+1 if p==29 else 1) for p in S}))
        ex={p:1 for p in S};ex[3]=2;ex[5]=2
        ls.append(make_label(ex,{p:(i+11 if p==29 else 6 if p==5 else 1) for p in S}))
    results.append(fixture('six high-rank predecessor supports and higher original digits',ps,ls))

    # All3 budget concentrated on small stages; genuine killed fibres at5.
    ps=[3,5,7,11]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({3:a,5:1},{3:1,5:a}) for a in range(1,5)]
    ls += [make_label({3:a,7:1},{3:1,7:a}) for a in range(1,7)]
    ls += [make_label({5:1,7:1},{5:1,7:1}),make_label({3:1,5:1,7:1},{3:1,5:1,7:2})]
    for i,S in enumerate(({3},{5},{7},{3,5},{3,7},{5,7})):
        ls.append(make_label({p:1 for p in S|{11}},{p:(i+1 if p==11 else 1) for p in S|{11}}))
    results.append(fixture('six small predecessor supports with killed fibres and shared budget',ps,ls))
    require(any(s['killed_fibres'] for s in results[-1]['stages']),'actual killed prefix')

    # No3: six distinct nonternary supports, overlapping intersections.
    ps=[5,7,11,13,17,19,23]
    ls=[make_label({p:1},{p:0}) for p in ps]
    for i,S in enumerate(({5},{7},{11},{5,7},{13},{17})):
        ls.append(make_label({p:1 for p in S|{23}},{p:(i+1 if p==23 else 1) for p in S|{23}}))
    results.append(fixture('six nonternary supports with absent3',ps,ls))

    # Missing5 and missing7 retain the actual source and numerical ordering.
    for ps in ([3,7,11,13],[3,5,11,13]):
        q=ps[1]
        ls=[make_label({p:1},{p:0}) for p in ps]
        ls += [make_label({3:1,q:1},{3:1,q:1})]
        for p,parents in ((11,({3},{q},{3,q})),(13,({3,q},{3,11},{q,11},{3,q,11}))):
            for i,S in enumerate(parents):
                ls.append(make_label({a:1 for a in S|{p}},{a:(i+1 if a==p else 1) for a in S|{p}}))
        results.append(fixture('5 absent' if q==7 else '7 absent',ps,ls))

    return dict(scope='Actual original-label arithmetic under a single joint law; six predecessor supports and total ternary support count at most six.',fixtures=results)

def calculate(base):
    result = dict(schema='predecessor-support-six-v1', scalars=scalar_checks(), actual=actual_checks())
    result['source_sha256'] = {name:hashlib.sha256((base/name).read_bytes()).hexdigest() for name in SOURCES}
    result['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return json.loads(json.dumps(result))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('six_support_certificate_io',args.base/'certificate_io.py')
    require(spec is not None and spec.loader is not None,'readable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),'exact six-support certificate replay')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
