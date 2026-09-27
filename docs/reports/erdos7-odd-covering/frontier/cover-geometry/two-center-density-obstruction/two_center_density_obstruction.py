"""Exact actual-law verification, independently of optimization and its matrix.

Only the standard library is used. Coordinate residue orbits are enumerated
literally (each coordinate has at most 729 points). Their query projections
are checked to be disjoint or equal and uniformly populated. Thus grouping
these literal projections computes every phase maximum on the large CRT
product without enumerating that product. Tail summation is exact.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import prod,lcm
from pathlib import Path
import hashlib,json

def need(condition,message):
    if not condition:
        raise ValueError(message)

def unique_pairs(pairs):
    d={}
    for k,v in pairs:
        need(k not in d,'duplicate JSON key '+str(k))
        d[k]=v
    return d

def valuation_truncated(n,p,h):
    k=0
    while k<h and n%p==0:
        n//=p;k+=1
    return k

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('certificate',nargs='?',default=str(Path(__file__).with_name('two_center_density_obstruction_weights.json')))
    ap.add_argument('--output')
    args=ap.parse_args()
    raw=Path(args.certificate).read_bytes()
    d=json.loads(raw,object_pairs_hook=unique_pairs)
    need(d['schema']=='two-center-actual-orbit-law-v1','schema')
    P=tuple(d['primes']);H=tuple(d['height'])
    need(P==(3,5,7,11,13,17,19) and H==(6,2,2,1,1,1,1),'domain')
    need(d['centers']=={'a':[0]*7,'b':[1,0,0,0,0,0,0]},'centers')
    need(d['query_target']=='70871/3375' and d['density_cap']=='6075000000000/7235955529' and d['lower_density']=='1/5','targets')
    rows=d['weights'];Z=d['denominator'];K=prod(p**h for p,h in zip(P,H))
    b=(K//3**H[0])*pow(K//3**H[0],-1,3**H[0])%K
    need(d['integer_centers']=={'a':0,'b':b},'finite integer centers')
    need(type(Z) is int and Z>0,'normalizer')
    need(sum(r['integer_weight'] for r in rows)==Z,'weight sum')
    seen=set();local_orbits={};sizes=[]
    for row in rows:
        c=row['branch'];v=tuple(row['v']);w=row['integer_weight']
        need(type(c) is int and c in (0,1),'third root excluded')
        need(len(v)==7 and all(type(a) is int and 0<=a<=h for a,h in zip(v,H)) and v[0]>=1,'valuation range')
        need(type(w) is int and w>0,'positive integer weight')
        need((c,v) not in seen,'duplicate state');seen.add((c,v))
        C=prod(a+1 for a in v[1:]);qa=(v[0]+1 if c==0 else 1)*C;qb=(v[0]+1 if c==1 else 1)*C
        need(max(22-qa,0)*max(28-qb,0)<=qa,'whole orbit not in B')
        need(c!=0 or any(v[1:]),'support meets the test box')
        ns=1
        for i,(p,h,a) in enumerate(zip(P,H,v)):
            center=c if i==0 else 0;key=(i,center,a)
            if key not in local_orbits:
                local_orbits[key]=tuple(x for x in range(p**h) if valuation_truncated(x-center,p,h)==a)
            need(bool(local_orbits[key]),'empty orbit')
            ns*=len(local_orbits[key])
        sizes.append(ns)
    densities=[F(r['integer_weight']*K,Z*n) for r,n in zip(rows,sizes)]
    lo=min(densities);hi=max(densities)
    need(lo>=F(d['lower_density']),'lower density')
    need(hi<=F(d['density_cap']),'upper density')
    # Build literal coordinate projection data. Uniformity and partition
    # checks are independent of the closed-form LP coefficients.
    projections={};phase_sets={}
    for key,orbit in local_orbits.items():
        i,center,a=key;p=P[i]
        for e in range(H[i]+1):
            counts=Counter(x%(p**e) for x in orbit)
            need(len(set(counts.values()))==1,'nonuniform projection')
            support=frozenset(counts)
            projections[key,e]=(support,len(support))
            phase_sets.setdefault((i,e),set()).add(support)
    phase_ids={}
    for ie,ss in phase_sets.items():
        sets=sorted(ss,key=lambda s:tuple(sorted(s)))
        for i,s in enumerate(sets):
            for t in sets[:i]:need(not(s&t),'phase projections overlap without equality')
            phase_ids[ie,s]=i
    # A fixed test box T: ternary root a, and nonzero roots at the other primes.
    # Literal projection labels suffice to detect EVERY zero cylinder meeting T.
    # At each fixed query depth its positive cylinder masses under Haar|T agree.
    test_projections={}
    for i,(p,h) in enumerate(zip(P,H)):
        test=tuple(x for x in range(p**h) if
                   (x%p==0 if i==0 else x%p!=0))
        for e in range(h+1):
            counts=Counter(x%(p**e) for x in test)
            need(len(set(counts.values()))==1,'test-box projection uniformity')
            lookup={x:phase_ids[(i,e),ss] for ss in phase_sets[(i,e)] for x in ss}
            ids=frozenset(lookup.get(x,-1) for x in counts)
            test_projections[i,e]=(ids,F(next(iter(counts.values())),len(test)))
    denominator=lcm(*sizes)
    zero_cover_bound=F();zero_cover_labels=0
    query_sum=F();max_table=[];phase_classes=0
    for e in product(*(range(h+1) for h in H)):
        masses={}
        for row in rows:
            c=row['branch'];v=row['v'];phase=[];count=1
            for i,a in enumerate(v):
                supp,mult=projections[(i,c if i==0 else 0,a),e[i]]
                phase.append(phase_ids[(i,e[i]),supp]);count*=mult
            need(denominator%count==0,'projection divisor')
            key=tuple(phase)
            masses[key]=masses.get(key,0)+row['integer_weight']*(denominator//count)
        maximum=F(max(masses.values()),Z*denominator)
        beta=prod(F(p,p-1) if a==h else F(1) for p,a,h in zip(P,e,H))
        query_sum+=maximum*beta;phase_classes+=len(masses)
        max_table.append(str(maximum))
        test_ids=[test_projections[i,a][0] for i,a in enumerate(e)]
        possible=prod(len(ids) for ids in test_ids)
        represented=sum(all(k in ids for k,ids in zip(key,test_ids)) for key in masses)
        need(represented<=possible,'test-box phase partition')
        if represented<possible:
            zero_cover_labels+=1
            zero_cover_bound+=beta*prod(test_projections[i,a][1] for i,a in enumerate(e))
    R=query_sum-1
    need(R<=F(d['query_target']),'all-depth query budget')
    need(zero_cover_bound<1,'zero-cylinder cover obstruction')
    out={
        'certificate_sha256':hashlib.sha256(raw).hexdigest(),
        'verification':'passed exact standard-library checks',
        'positive_orbits':len(rows),'finite_period':K,'coarse_query_labels':len(max_table),'nonzero_phase_classes':phase_classes,
        'integer_centers':d['integer_centers'],
        'normalizer':Z,'support_haar':str(F(sum(sizes),K)),
        'density_min':str(lo),'density_min_float':float(lo),'density_max':str(hi),'density_max_float':float(hi),
        'R_all_depth':str(R),'R_all_depth_float':float(R),'R_target':d['query_target'],'margin':str(F(d['query_target'])-R),
        'third_root_mass':0,'B_probability':1,
        'test_box_zero_query_labels':zero_cover_labels,'test_box_zero_cover_upper':str(zero_cover_bound),
        'test_box_uncovered_mass_lower':str(1-zero_cover_bound),
        'maxima_sha256':hashlib.sha256('\n'.join(max_table).encode()).hexdigest(),
        'scope':'actual finite CRT law with Haar tails on fixed seven primes; the zero-cylinder test-box bound excludes E as the complete survivor set of any odd-distinct family on these seven primes; no covering counterexample'
    }
    text=json.dumps(out,indent=2)+'\n'
    if args.output:Path(args.output).write_text(text)
    print(text,end='')

if __name__=='__main__':main()
