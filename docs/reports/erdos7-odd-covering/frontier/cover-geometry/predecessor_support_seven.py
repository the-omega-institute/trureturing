#!/usr/bin/env python3
"""Exact two-small-prime budget and actual original-label joint-law certificates."""
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

CERTIFICATE = 'certificates/source_norms/cover-geometry/predecessor_support_seven.json'
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
        require(len(ss)<=7 and all(ss0 for ss0 in ss),'at most seven exact nonempty predecessor supports')
        patterns[p]=tuple(frozenset(S) for S in sorted(ss))
    ternary_count=sum(3 in S for sets in patterns.values() for S in sets)
    require(ternary_count<=7,'shared original mixed3-support count')
    quinary_count=sum(5 in S or p==5 for p,sets in patterns.items() for S in sets)
    require(quinary_count<=7,'shared original mixed5-support count')
    gram_no5=[F(9179,1980),F(4184374,530145),F(856481,75735),F(59236,4455),F(21667,1485),F(67454,4455),F(1140742,75735),F(7308458,530145)]
    gram_with5=[F(386,55),F(1549507,151470),F(39701,2970),F(48589,2970),F(1633,90),F(28294,1485),F(56137,2970),F(1398037,75735)]
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
            require(gram<=(F(2) if p==5 else F(13,2) if p==7 else (gram_with5 if any(5 in S for S in patterns[p]) else gram_no5)[sum(3 in S for S in patterns[p])]),'shared3/5-budget row-bound stage Gram cap')
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
    require(survivor>=F(630132709,12596245200),'complete actual survivor lower bound')
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
    require(maxdensity/survivor<=F(12596245200,630132709)*D,'fully conditioned survivor density')
    return dict(name=name,ternary_support_count=ternary_count,quinary_support_count=quinary_count,primes=primes,heights=heights,original_labels=labels,period=prod(p**heights[p] for p in primes),
                compressed_carrier=prod(len(atoms[p]) for p in primes),positive_law_cells=len(laws),
                mixed_patterns={p:[sorted(S) for S in sets] for p,sets in patterns.items() if groups[p]},stages=stages,
                pair_cylinder_checks=queries,survivor_mass=str(survivor),haar_survivor=str(raw_survivor),
                actual_survivor_count=actual_count,max_density=str(maxdensity),theorem_density_cap=str(D))




# K8 pair support has incidence7 and seven distinct final predecessors.

def scalar_checks():
    K=7

    def factors(p):
     return (F(1,2),F(1,3)) if p==5 else (F(4,9),F(1,3)) if p==7 else (F(2*(p+1),(p-1)*(p-2)),F(2,p-2))
    def table(no5):
     ps=[7,11,13,17,19,23,29,31] if no5 else [5,7,11,13,17,19,23,29]
     nxt=37 if no5 else 31
     d={p:factors(p)[0] for p in ps};t={p:factors(p)[1] for p in ps}
     D=sorted([prod(d[p] for p in C) for k in range(1,len(ps)+1) for C in combinations(ps,k)],reverse=True)[:K]
     T=sorted([prod(t[p] for p in C) for k in range(1,len(ps)+1) for C in combinations(ps,k)],reverse=True)[:K]
     if not D[-1]>factors(nxt)[0] or not T[-1]>factors(nxt)[1]:raise ValueError('monomial tail')
     R=lambda j:sum(T[:j],F(0))
     C=lambda j:sum((max(F(0),v-F(1,6)) for v in D[:j]),F(0))
     Ms=[F(0)];hrows=[]
     for j in range(1,K+1):
      h=[(d[p]*(1+(j-1)*max(t[q] for q in ps if q!=p)),[p]) for p in ps]
      h +=[(d[p]*(d[q]+(j-1)*t[q]),[p,q]) for p,q in combinations(ps,2)]
      h=sorted(h,reverse=True)
      if h[j-1][0]<=j*prod(d[p] for p in ps[:3]):raise ValueError('rank3 tail')
      if h[j-1][0]<=j*d[ps[0]]*factors(nxt)[0]:raise ValueError('pair tail')
      if h[j-1][0]<=factors(nxt)[0]*(1+(j-1)*max(t.values())):raise ValueError('singleton tail')
      Ms.append(sum((v for v,S in h[:j]),F(0)))
      hrows.append([(str(v),S) for v,S in h[:j]])
     def g(a,b,e):
      r=a-e
      return 2*Ms[r]+(2+4*R(r) if e else 0)+Ms[b]+F(r*b,3)+2*C(min(r,b))+2*e*R(b)
     G=[max(g(a,K-a,e) for e in range(min(a,1)+1)) for a in range(K+1)]
     return G,dict(no5=no5,D=list(map(str,D)),T=list(map(str,T)),M=list(map(str,Ms)),G=list(map(str,G)),row_caps=hrows)
    G0,info0=table(True);G1,info1=table(False)
    base=G0[0]
    extra={(a,e):max(F(0),(G1 if e else G0)[a]-base) for a in range(K+1) for e in (0,1)}
    r=[13,17,19,23,29,31,37,41,43,47,53,59,61,67]
    dp={(0,0):(F(0),[])}
    for p in r:
     nd={}
     for (u,v),(val,pat) in dp.items():
      for a in range(K-u+1):
       for e in range(min(1,K-v)+1):
        key=(u+a,v+e);candidate=val+extra[a,e]/(p-2)**2
        if key not in nd or candidate>nd[key][0]:nd[key]=(candidate,pat+([(p,a,e)] if a or e else []))
     dp=nd
    V={}
    for B3 in range(K+1):
     for B5 in range(K+1):
      V[B3,B5]=max((v for (u,w),v in dp.items() if u<=B3 and w<=B5),key=lambda x:x[0])
    def gram(fam):
     def w(S,T):return prod((F(2) if p==3 else factors(p)[0]) if p in S&T else F(1) if p==3 else factors(p)[1] for p in S|T)
     return sum((w(S,T) for S in fam for T in fam),F(0))
    S7=[{3},{5},{3,5}]
    S11=[{p for i,p in enumerate([3,5,7]) if m>>i&1} for m in range(1,8)]
    rows=[]
    for f in (0,1):
     for m7 in range(8):
      F7=[S7[i] for i in range(3) if m7>>i&1]
      for m11 in range(128):
       F11=[S11[i] for i in range(7) if m11>>i&1]
       B3=K-f-sum(3 in S for S in F7+F11)
       B5=K-f-sum(5 in S for S in F7+F11)
       if min(B3,B5)<0:continue
       ext,pat=V[B3,B5]
       fee=F(f,3)+gram(F7)/24+gram(F11)/81+base/35+ext
       rows.append(dict(f=f,m7=m7,m11=m11,B3=B3,B5=B5,fee=str(fee),decimal=float(fee),extra=str(ext),allocation=pat))
    result=dict(scope='Exact scalar certificate; the actual source and analytic transfer are proved in the accompanying text.',tables=[info0,info1],base=str(base),cases=len(rows),worst=max(rows,key=lambda r:F(r['fee'])),rows=rows)
    require(F(result['worst']['fee'])==F(11966112491,12596245200)<1,'exact shared two-budget fee')
    require(1-F(result['worst']['fee'])==F(630132709,12596245200),'exact survivor reserve')
    return result


def actual_checks():
    ps=[3,5,7,11,13,17,19,23]
    ls=[make_label({p:1},{p:0}) for p in ps]
    for i,p in enumerate(ps):
        for q in ps[i+1:]:
            ls.append(make_label({p:1,q:1},{p:1,q:1}))
            if (p+q)%8==0:
                ls.append(make_label({p:2,q:1},{p:1+p,q:2}))
    results=[fixture('K8 pair supports with higher original exponents',ps,ls)]
    require(len(results[0]['mixed_patterns'][23])==7,'genuine seventh predecessor at last stage')
    require(results[0]['ternary_support_count']==results[0]['quinary_support_count']==7,'both shared budgets exhausted')

    # Six of the seven p11 patterns leave one shared incidence of3 and5.
    ps=[3,5,7,11,13]
    ls=[make_label({p:1},{p:0}) for p in ps]
    ls += [make_label({3:a,5:1},{3:1,5:a}) for a in range(1,5)]
    ls += [make_label({3:a,7:1},{3:1,7:a}) for a in range(1,7)]
    ls += [make_label({5:1,7:1},{5:1,7:1}),make_label({3:1,5:1,7:1},{3:1,5:1,7:2})]
    for i,S in enumerate(({3},{5},{7},{3,5},{3,7},{5,7})):
        ls.append(make_label({p:1 for p in S|{11}},{p:(i+1 if p==11 else 1) for p in S|{11}}))
    ls.append(make_label({3:1,5:1,13:1},{3:1,5:1,13:1}))
    ls.append(make_label({3:2,5:2,13:2},{3:4,5:6,13:14}))
    results.append(fixture('both budgets consumed across5,7,11,13 including killed fibres',ps,ls))
    require(any(s['killed_fibres'] for s in results[-1]['stages']),'actual killed prefix')

    # Seven large predecessor sets, full original ranks and additional digits.
    ps=[3,5,7,11,13,17,19,23,29]
    ls=[make_label({p:1},{p:0}) for p in ps]
    base={3,5,7,11,13}
    for i,T in enumerate((set(),{17},{19},{23},{17,19},{17,23},{17,19,23})):
        S=base|T|{29}
        ls.append(make_label({p:1 for p in S},{p:(i+1 if p==29 else 1) for p in S}))
        ex={p:1 for p in S};ex[3]=2;ex[5]=2
        ls.append(make_label(ex,{p:(i+11 if p==29 else 6 if p==5 else 1) for p in S}))
    results.append(fixture('seven high-rank original supports with both budgets exhausted',ps,ls))

    # Remove small coordinates altogether: virtual bounds still apply.
    for missing in ({3},{5},{7},{3,5}):
        ps=[p for p in (3,5,7,11,13,17,19,23,29,31) if p not in missing][:8]
        ls=[make_label({p:1},{p:0}) for p in ps]
        for i,p in enumerate(ps):
            for q in ps[i+1:]:ls.append(make_label({p:1,q:1},{p:1,q:1}))
        results.append(fixture('K8 with absent'+','.join(map(str,sorted(missing))),ps,ls))
    # A mixed-rank ten-prime family exceeds the old support/rank/graph hypotheses.
    ps=[3,5,7,11,13,17,19,23,29,31]
    ls=[make_label({p:1},{p:0}) for p in ps]
    removed={frozenset(E) for E in ((3,19),(5,17),(7,13),(11,19))}
    original_supports=[]
    for i,p in enumerate(ps[:8]):
        for q in ps[i+1:8]:
            if frozenset((p,q)) not in removed:original_supports.append({p,q})
    original_supports.append({3,5,7,11,29,31})
    for S in original_supports:
        ls.append(make_label({p:1 for p in S},{p:1 for p in S}))
    require(all(sum(p in S for S in original_supports)<=7 for p in ps),'maximum full prime incidence seven')
    scalar=sum((prod(F(1,p-2) for p in S) for S in original_supports),F(0))
    require(scalar>1,'the elementary full-support union upper bound does not close')
    new=fixture('ten-prime mixed-rank incidence7 family with support-union envelope above1',ps,ls)
    new['support_union_envelope']=str(scalar)
    results.append(new)
    return dict(scope='Actual original-label arithmetic under one joint law; seven predecessor supports with shared3/5 counts.', fixtures=results)

def calculate(base):
    result = dict(schema='predecessor-support-seven-v1', scalars=scalar_checks(), actual=actual_checks())
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
    spec = importlib.util.spec_from_file_location('seven_support_certificate_io',args.base/'certificate_io.py')
    require(spec is not None and spec.loader is not None,'readable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),'exact seven-support certificate replay')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
