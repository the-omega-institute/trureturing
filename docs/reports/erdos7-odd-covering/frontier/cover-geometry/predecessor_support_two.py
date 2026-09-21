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

CERTIFICATE = 'certificates/source_norms/cover-geometry/predecessor_support_two.json'
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
        require(len(ss)<=2 and all(ss0 for ss0 in ss),'at most two exact nonempty predecessor supports')
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
    kappa={p:2 if groups[p] else 1 for p in primes}
    c={p:F(p-1,p-2) for p in primes}
    def matches(l,state,upto):
        return all(local_match(l,q,atoms[q][state[j]][0]) for j,q in enumerate(primes[:upto]))
    laws={():F(1)}; stages=[]
    for i,p in enumerate(primes):
        nxt=defaultdict(F); square=F(0); badmass=F(0); killed=0; overhalf=0
        for state, mass in laws.items():
            active=[l for l in groups[p] if matches(l,state,i)]
            forbidden=[any(local_match(l,p,a[0]) for l in active) for a in atoms[p]]
            alpha=sum((a[2] for a,flag in zip(atoms[p],forbidden) if flag),F(0))
            square+=mass*alpha**2
            killed+=int(alpha==1); overhalf+=int(alpha>F(1,2))
            normalization=F(0); fibre_bad=F(0)
            for j,(a,flag) in enumerate(zip(atoms[p],forbidden)):
                if alpha<=F(1,2): k=F(0) if flag else 1/(1-alpha)
                else: k=(2*alpha-1)/alpha if flag else F(2)
                require(0<=k<=kappa[p],'pointwise normalized-kernel cap')
                probability=k*a[2]; normalization+=probability
                fibre_bad+=probability*flag
                if probability: nxt[state+(j,)]+=mass*probability
            require(normalization==1,'exact fibre normalization including alpha=1')
            require(fibre_bad==max(F(0),2*alpha-1)<=alpha**2,'actual local loss')
            badmass+=mass*fibre_bad
        if groups[p]:
            def d(q): return kappa[q]*F(q+1,(q-1)*(q-2))
            def t(q): return F(kappa[q],q-2)
            gram=sum((prod(d(q) for q in S&T)*prod(t(q) for q in S^T)
                      for S,T in product(patterns[p],repeat=2)),F(0))
            envelope=F(1,(p-2)**2)*gram
            earlier_non3=[q for q in primes[:i] if q!=3]
            r=min(earlier_non3) if earlier_non3 else 11
            D=F(2*(r+1),(r-1)*(r-2));Tcap=F(2,r-2)
            require(gram<=2*(1+D+2*Tcap),'actual full-support Gram cap')
            require(square<=envelope,'actual squared load versus full-support Gram')
        else: envelope=F(0)
        stages.append(dict(p=p,labels=len(groups[p]),alpha_square=str(square),bad_mass=str(badmass),
                           envelope=str(envelope),killed_fibres=killed,overhalf_fibres=overhalf))
        require(sum(nxt.values(),F(0))==1,'entire prefix law normalized')
        # Every earlier full joint atom retains its source mass, not only its marginals.
        marg=defaultdict(F)
        for state,mass in nxt.items(): marg[state[:-1]]+=mass
        require(dict(marg)==laws,'complete earlier joint source preserved')
        laws=dict(nxt)
    alln=len(primes)
    survivor=sum((mass for state,mass in laws.items() if not any(matches(l,state,alln) for l in labels)),F(0))
    require(survivor>=F(277,13500),'complete actual survivor lower bound')
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
    require(maxdensity/survivor<=F(13500,277)*D,'fully conditioned survivor density')
    return dict(name=name,primes=primes,heights=heights,original_labels=labels,period=prod(p**heights[p] for p in primes),
                compressed_carrier=prod(len(atoms[p]) for p in primes),positive_law_cells=len(laws),
                mixed_patterns={p:[sorted(S) for S in sets] for p,sets in patterns.items() if groups[p]},stages=stages,
                pair_cylinder_checks=queries,survivor_mass=str(survivor),haar_survivor=str(raw_survivor),
                actual_survivor_count=actual_count,max_density=str(maxdensity),theorem_density_cap=str(D))



def scalar_checks():
    def constants(r):
        D=F(2*(r+1),(r-1)*(r-2)); T=F(2,r-2)
        return D,T,2*(1+D+2*T)
    rows=[]
    for r,ps in ((5,(3,5,7,11,13)),(7,(3,7,11,13,17)),(11,(3,11,13,17,19))):
        D,T,K=constants(r)
        require(0<D<=1 and 0<T<1,'contraction')
        require(K-5*D==F(2*((r-1)**2-6),(r-1)*(r-2))>0,'mixed shared-coordinate subcase')
        supports=[frozenset(p for j,p in enumerate(ps) if n>>j&1) for n in range(1,2**len(ps))]
        d={p:F(2) if p==3 else F(2*(p+1),(p-1)*(p-2)) for p in ps}
        t={p:F(1) if p==3 else F(2,p-2) for p in ps}
        maximum=F(0); maximizers=[];count=0
        for S,Tset in combinations(supports,2):
            value=prod(d[p] for p in S)+prod(d[p] for p in Tset)+2*prod(d[p] for p in S&Tset)*prod(t[p] for p in S^Tset)
            require(value<=K,'complete two-support Gram at r='+str(r))
            count+=1
            if value>maximum:maximum=value;maximizers=[(sorted(S),sorted(Tset))]
            elif value==maximum:maximizers.append((sorted(S),sorted(Tset)))
        require(maximum==K,'bound attained on exact support pair')
        rows.append(dict(r=r,K=str(K),pairs=count,maximum=str(maximum),maximizers=maximizers))
    S=F(719,3600);K5=constants(5)[2];K7=constants(7)[2];K11=constants(11)[2]
    case1=K5*S-(K5-K11)/9
    case2=K5*S-(K5-K7)/9-(K5-K11)/25
    case3=K5*(S-F(1,9))
    require(case1==F(1573,1620),'5 before7 exact fee')
    require(case2==F(13223,13500),'7 before5 exact fee')
    require(case3<case2 and case1<case2<1,'uniform maximum fee')
    require(1-case2==F(277,13500),'exact uniform reserve')
    return dict(rows=rows,prime_square_envelope=str(S),fees=dict(five_before_seven=str(case1),seven_before_five=str(case2),five_absent=str(case3)),reserve=str(1-case2))


def calculate(base):
    # Two genuinely different nonternary predecessor supports, with 7 before 5.
    ps=[3,7,5]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({3:a,5:1},{3:1,5:a}) for a in range(1,5)]
    ls += [make_label({3:1,7:1},{3:1,7:2}),
           make_label({7:1,5:1},{7:1,5:3}),
           make_label({7:2,5:2},{7:8,5:8})]
    results=[fixture('7 before 5; exact supports {3} and {7}; killed fibre',ps,ls)]
    require(any(s['killed_fibres'] for s in results[0]['stages']),'actual killed-fibre fixture')

    # The other prime-order branch; repeated full exponents and two pairs of supports.
    ps=[3,5,7,11]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({3:1,5:1},{3:1,5:1}),
           make_label({3:2,5:1},{3:1,5:2}),
           make_label({3:1,7:1},{3:1,7:1}),
           make_label({5:1,7:1},{5:1,7:2}),
           make_label({5:2,7:2},{5:6,7:9}),
           make_label({3:1,5:1,11:1},{3:1,5:1,11:1}),
           make_label({5:1,7:1,11:1},{5:1,7:1,11:2}),
           make_label({5:2,7:1,11:2},{5:6,7:1,11:13})]
    results.append(fixture('5 before 7; one ternary support with shared coordinate',ps,ls))

    # No prime 5: the missing-prime branch is an actual full arithmetic family.
    ps=[3,7,11]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({3:1,7:1},{3:1,7:1}),
           make_label({3:1,11:1},{3:1,11:1}),
           make_label({7:1,11:1},{7:1,11:2}),
           make_label({7:2,11:2},{7:8,11:13})]
    results.append(fixture('5 absent with two exact predecessor supports',ps,ls))

    # No prime 3: different nonempty predecessor supports still use a common joint law.
    ps=[7,5,11,13]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({7:1,5:1},{7:1,5:1}),
           make_label({7:1,11:1},{7:1,11:1}),
           make_label({5:1,11:1},{5:1,11:2}),
           make_label({5:1,7:1,13:1},{5:1,7:1,13:1}),
           make_label({7:1,11:1,13:1},{7:1,11:1,13:2})]
    results.append(fixture('3 absent with nonnumerical order and shared supports',ps,ls))

    # Two distinct supports both containing 3 realize the largest Gram case.
    ps=[3,5,11]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({3:1,5:1},{3:1,5:1}),
           make_label({3:1,11:1},{3:1,11:1}),
           make_label({3:1,5:1,11:1},{3:1,5:1,11:2}),
           make_label({3:2,5:2,11:1},{3:1,5:6,11:3})]
    results.append(fixture('7 absent; both exact supports contain 3',ps,ls))
    result = dict(schema='predecessor-support-two-v1', scalars=scalar_checks(), actual_fixtures=results)
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
