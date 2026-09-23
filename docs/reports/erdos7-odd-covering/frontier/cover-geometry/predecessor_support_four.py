#!/usr/bin/env python3
"""Exact predecessor-support Gram bounds and full actual original-label laws."""
import argparse
from fractions import Fraction as F
from collections import defaultdict
from itertools import combinations, combinations_with_replacement, product
from math import prod, isqrt
from pathlib import Path
import importlib.util
import hashlib
import json
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/cover-geometry/predecessor_support_four.json'
SOURCES = ('certificate_io.py', 'problem-details/52-two-or-four-exact-predecessor-supports.md', 'problem-details/07-ordered-local-kernels-unbounded-feedback-sets-and-treewidth.md', 'problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md', 'problem-details/41-natural-four-predecessor-orders-are-noncovering.md')

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
        require(len(ss)<=4 and all(ss0 for ss0 in ss),'at most four exact nonempty predecessor supports')
        patterns[p]=tuple(frozenset(S) for S in sorted(ss))
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
            require(gram<=(F(2) if p==5 else F(13,2) if p==7 else F(169,18)),'four-support universal Gram cap')
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
    require(survivor>=F(4763,408240),'complete actual survivor lower bound')
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
    require(maxdensity/survivor<=F(408240,4763)*D,'fully conditioned survivor density')
    return dict(name=name,primes=primes,heights=heights,original_labels=labels,period=prod(p**heights[p] for p in primes),
                compressed_carrier=prod(len(atoms[p]) for p in primes),positive_law_cells=len(laws),
                mixed_patterns={p:[sorted(S) for S in sets] for p,sets in patterns.items() if groups[p]},stages=stages,
                pair_cylinder_checks=queries,survivor_mass=str(survivor),haar_survivor=str(raw_survivor),
                actual_survivor_count=actual_count,max_density=str(maxdensity),theorem_density_cap=str(D))



def scalar_checks():
    ps=(3,5,7,11)
    k={3:F(1),5:F(1),7:F(5,3),11:F(2)}
    d={p:k[p]*F(p+1,(p-1)*(p-2)) for p in ps}
    t={p:k[p]/(p-2) for p in ps}
    require(d=={3:F(2),5:F(1,2),7:F(4,9),11:F(4,15)},'ordered diagonal factors')
    require(t=={3:F(1),5:F(1,3),7:F(1,3),11:F(2,9)},'ordered differing factors')

    def gram(fam):
        return sum((prod(d[p] for p in A&B)*prod(t[p] for p in A^B) for A in fam for B in fam),F(0))

    def finite(n,count,expected):
        ss=[frozenset(p for j,p in enumerate(ps[:n]) if mask>>j&1) for mask in range(1,2**n)]
        rows=[];mx=F(0);maximizers=[]
        for fam in combinations(ss,count):
            v=gram(fam);require(v<=expected,'complete finite Gram comparison')
            row=dict(masks=[sum(2**ps.index(p) for p in S) for S in fam],gram=str(v))
            rows.append(row)
            if v>mx:mx=v;maximizers=[row['masks']]
            elif v==mx:maximizers.append(row['masks'])
        require(mx==expected,'attained sharp nominal finite Gram')
        return dict(coordinates=list(ps[:n]),support_count=count,cases=len(rows),maximum=str(mx),maximizers=maximizers,rows=rows)
    checks=[finite(2,3,F(13,2)),finite(3,4,F(169,18)),finite(4,4,F(169,18))]
    require([c['cases'] for c in checks]==[1,35,1365],'finite completeness')

    # General projection witness mechanism, tested on every family in five coordinates.
    qs=(3,5,7,11,13)
    ss=[frozenset(p for j,p in enumerate(qs) if mask>>j&1) for mask in range(1,2**len(qs))]
    projection_count=0
    for fam in combinations(ss,4):
        if not any(3 in S for S in fam):continue
        objs=(frozenset(),)+fam; kept={3}
        while len({S&kept for S in objs})<len(objs):
            A,B=next((A,B) for A,B in combinations(objs,2) if A&kept==B&kept)
            q=min(A^B);require(q not in kept and q!=3,'new distinguishing coordinate')
            kept.add(q)
        require(len(kept)<=4,'three additional coordinates suffice')
        images=[S&kept for S in fam]
        require(all(images) and len(set(images))==4,'empty protected, no merged support')
        projection_count+=1

    head=[p for p in range(13,212) if all(p%q for q in range(2,isqrt(p)+1))]
    require(len(head)==42 and head[-1]==211,'all primes in finite head')
    tail=sum((F(1,(p-2)**2) for p in head),F(0))+F(1,1260)+F(1,1272)
    require(tail<F(1,35),'full mod6 tail bound')
    fee5=F(1,3)
    fee7=F(13,2)*F(1,25)/F(24,25)
    require(fee7==F(13,48),'special seventh stage loss')
    fee=fee5+fee7+F(169,18)*(F(1,81)+F(1,35))
    require(fee==F(403477,408240)<1,'global fee')
    require(1-fee==F(4763,408240),'global reserve')
    return dict(gram_checks=checks,projection_count=projection_count,prime_head=head,tail_bound=str(tail),tail_slack=str(F(1,35)-tail),fee5=str(fee5),fee7=str(fee7),fee_total=str(fee),reserve=str(1-fee))


def growth_checks():
    cutoff=10**6
    pointwise=2*F(cutoff+1,cutoff-1)**2
    require(pointwise<F(21,10),'uniform cutoff multiplier')
    # Integral_N^infty x^-3/2 dx=2/sqrt(N), with sqrt(10^6)=1000.
    integral=F(2,1000)
    fee=F(21,10)*integral
    require(fee==F(21,5000),'complete integer-tail fee')
    four_fee=F(403477,408240)
    reserve=1-four_fee-fee
    require(reserve==F(381049,51030000)>F(1,150),'exact positive full reserve')
    require(1/reserve==F(51030000,381049)<150,'final conditioning factor')
    return dict(cutoff=cutoff,pointwise_multiplier=str(pointwise),integer_tail_integral=str(integral),additional_fee=str(fee),four_support_fee=str(four_fee),reserve=str(reserve),conditioning_factor=str(1/reserve),scope='Exact scalar certificate; arbitrary-rank Gram bound and infinite integral tail are proved in the accompanying text.')


def calculate(base):
    # p5 is genuinely left unbiased, even when actual mixed classes kill its fibre.
    ps=[3,5,7,11]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({3:a,5:1},{3:1,5:a}) for a in range(1,5)]
    ls += [make_label({3:a,7:1},{3:1,7:a}) for a in range(1,7)]
    ls += [make_label({5:1,7:1},{5:1,7:1}),
           make_label({3:1,5:1,7:1},{3:1,5:1,7:2}),
           make_label({3:2,5:2,7:2},{3:1,5:6,7:9}),
           make_label({3:1,11:1},{3:1,11:1}),
           make_label({5:1,11:1},{5:1,11:2}),
           make_label({3:1,5:1,11:1},{3:1,5:1,11:3}),
           make_label({3:1,7:1,11:1},{3:1,7:1,11:4}),
           make_label({3:2,7:2,11:2},{3:1,7:8,11:15})]
    results=[fixture('unbiased5, special7 threshold, four exact11 supports and killed fibres',ps,ls)]
    stage5=next(s for s in results[0]['stages'] if s['p']==5)
    require(stage5['alpha_mean']==stage5['bad_mass'] and F(stage5['bad_mass'])>0,'positive unbiased mixed5 loss')
    require(any(s['killed_fibres'] for s in results[0]['stages']),'actual killed fibre')

    # Four supports need all three nonternary distinction coordinates after 3.
    # Retaining empty prevents collapse of a singleton into the empty support.
    ps=[3,5,7,11,13,17,19]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({3:1,5:1},{3:1,5:1}),make_label({3:1,7:1},{3:1,7:1})]
    for i,S in enumerate(({3,13,17},{3,5,13,17},{3,7,13,17},{3,11,13,17})):
        ls.append(make_label({p:1 for p in S|{19}},{p:(i+1 if p==19 else 1) for p in S|{19}}))
        ex={p:1 for p in S|{19}};ex[3]=2;ex[13]=2
        ls.append(make_label(ex,{p:(i+20 if p==19 else 14 if p==13 else 1) for p in ex}))
    results.append(fixture('four high-rank supports retaining three distinction coordinates',ps,ls))

    # All-nonternary branch with four supports and nontrivial common intersections.
    ps=[5,7,11,13,17]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({5:1,7:1},{5:1,7:1}),make_label({5:1,11:1},{5:1,11:1})]
    for i,S in enumerate(({5,7},{5,11},{7,13},{5,7,11,13})):
        ls.append(make_label({p:1 for p in S|{17}},{p:(i+1 if p==17 else 1) for p in S|{17}}))
    results.append(fixture('3 absent with four different exact supports',ps,ls))

    # Virtual-coordinate domination with missing5 and with missing7.
    for ps in ([3,7,11,13],[3,5,11,13]):
        q=ps[1]
        ls=[make_label({p:1},{p:0}) for p in ps]
        ls += [make_label({3:1,q:1},{3:1,q:1})]
        for p,parents in ((11,({3},{q},{3,q})),(13,({3,q},{3,11},{q,11},{3,q,11}))):
            for i,S in enumerate(parents):
                ls.append(make_label({a:1 for a in S|{p}},{a:(i+1 if a==p else 1) for a in S|{p}}))
        results.append(fixture('5 absent' if q==7 else '7 absent',ps,ls))
    result = dict(schema='predecessor-support-four-v1', scalars=scalar_checks(), actual_fixtures=results, growing_inventory=growth_checks())
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
    spec = importlib.util.spec_from_file_location('predecessor_certificate_io',args.base/'certificate_io.py')
    require(spec is not None and spec.loader is not None,'readable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact predecessor-support certificate replay')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
