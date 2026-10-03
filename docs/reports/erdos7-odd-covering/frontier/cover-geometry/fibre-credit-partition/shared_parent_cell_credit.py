#!/usr/bin/env python3
"""Exact fixed-source joint old-35/descendant phase-slot relaxation."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import prod
from pathlib import Path

def need(ok,msg):
    if not ok:raise ValueError(msg)

def factor(d,primes):
    out={}
    for p in primes:
        e=0
        while d%p==0:d//=p;e+=1
        if e:out[p]=e
    need(d==1,'unsupported factor')
    return out

def matchings(rows,cols,allowed):
    def rec(i,used,edges):
        if i==len(rows):
            yield tuple(edges);return
        yield from rec(i+1,used,edges)
        for col in cols:
            if col not in used and (rows[i],col) in allowed:
                yield from rec(i+1,used|{col},edges+[(rows[i],col)])
    yield from rec(0,set(),[])

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--input',required=True,type=Path)
    parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args()
    raw=args.input.read_bytes();data=json.loads(raw)
    primes=data['primes'];heights=dict(zip(primes,data['heights']))
    c={p:Fraction((p-1)*p**heights[p],(p-2)*p**heights[p]+1) for p in primes}
    b={p:c[p]-1 for p in primes}
    sr={(p,e):r for p,e,r in data['star_roots']}
    need(all(sr[p,e]==(1 if p==5 else 2) for p in primes for e in range(1,heights[p]+1)),'fixed FC36 star assignment')
    selected=dict(data['selected_witness'])
    bucket=[]
    for d,r in selected.items():
        f=factor(d,primes)
        if r==1 and f.get(5)==1 and f.get(7)==1:
            charge=prod((c[p]/p**e for p,e in f.items()),start=Fraction(1))
            bucket.append((charge,d,f))
    bucket.sort(reverse=True)
    need(len(bucket)==8,'eight-label fixed bucket')
    need(35 in selected and selected[35]==2,'same original h is not in root-1 bucket')
    u0=c[5]*c[7]/35
    need(all(a<=u0 for a,d,f in bucket),'descendant coefficient upper bound')
    R={p:{r:{} for r in (1,2)} for p in (5,7)}
    for p in (5,7):
        H=heights[p];period=p**H
        pure=[(p,0)]+[(p**e,1+p**(e-1)) for e in range(2,H+1)]
        stars=[(p,2)]+[(p**e,3+p**(e-1)) for e in range(2,H+1)]
        S={x for x in range(period) if not any(x%m==a for m,a in pure)}
        B={x for x in range(period) if any(x%m==a for m,a in stars)}
        need(B<=S and Fraction(period,len(S))==c[p],'actual source normalizer')
        for r in (1,2):
            live=S-B if sr[p,1]==r else S
            for a in range(p):
                R[p][r][a]=Fraction(sum(x%p==a for x in live),len(S))/(c[p]/p)
    alpha=R[5][1][1];rho=R[7][1][1]
    need(Fraction(0)<alpha<rho<1,'source row/column ordering')
    need([R[5][1][a] for a in range(5)]==[0,alpha,0,alpha,1],'root-1 five matrix')
    need([R[7][1][a] for a in range(7)]==[0,rho,1,1,1,1,1],'root-1 seven matrix')
    gout2=prod((1-b[p] for p in primes if p not in (5,7)),start=Fraction(1))
    rows=(1,3,4);cols=(1,2,3,4,5,6)
    matrix={(a,z):R[5][1][a]*R[7][1][z] for a in rows for z in cols}
    phase_rows=[];count_matchings=0
    for old5 in range(1,5):
        for old7 in range(1,7):
            old=(old5,old7);allowed=set(matrix)-{old}
            best={k:Fraction(-1) for k in range(1,9)}
            for matching in matchings(rows,cols,allowed):
                count_matchings+=1
                slots=sorted([matrix[e] for e in allowed]+[matrix[e] for e in matching],reverse=True)
                for k in best:
                    value=sum((bucket[i][0]*slots[i] for i in range(k)),Fraction())
                    best[k]=max(best[k],value)
            norm={r:R[5][r][old5]*R[7][r][old7] for r in (1,2)}
            if old5==4 and old7!=1:
                pattern8=[1]*5+[rho,alpha,alpha]
                pattern6=[1]*5+[rho]
                category='maximal root-1 old cell'
            elif old5==4:
                pattern8=[1]*6+[alpha,alpha]
                pattern6=[1]*6
                category='partial-column old cell'
            else:
                pattern8=[1]*6+[rho,alpha]
                pattern6=[1]*6
                category='other old cell'
            need(best[8]==sum((bucket[i][0]*pattern8[i] for i in range(8)),Fraction()),'eight-slot conditional majorant sharpness')
            need(best[6]==sum((bucket[i][0]*pattern6[i] for i in range(6)),Fraction()),'six-slot conditional majorant sharpness')
            phase_rows.append(dict(phase=list(old),category=category,root_norm={str(r):str(norm[r]) for r in (1,2)},best_by_k={str(k):str(v) for k,v in best.items()}))
    a=[z[0] for z in bucket]
    delta6=(1-rho)*a[5]
    delta8=(1-rho)*a[5]+(1-alpha)*(a[6]+a[7])
    old_delta8=(1-rho)*a[6]+(1-alpha)*a[7]
    need(delta8>old_delta8>0,'strict replacement improvement')
    weight_checks=[]
    for k in range(1,9):
        fullslots=[1]*min(k,5)+([rho] if k>=6 else [])+([alpha]*(k-6) if k>=7 else [])
        target_mixed=sum((a[i]*fullslots[i] for i in range(k)),Fraction())
        loss=sum(a[:k],Fraction())-target_mixed
        for w in (Fraction(),Fraction(1,10),Fraction(1,3),Fraction(1,2),Fraction(9,10),Fraction(1)):
            best_joint=max(w*(u0*Fraction(row['root_norm']['1'])+Fraction(row['best_by_k'][str(k)]))
                +(1-w)*gout2*u0*Fraction(row['root_norm']['2']) for row in phase_rows)
            claimed=w*(u0+target_mixed)+(1-w)*gout2*u0
            need(best_joint==claimed,'joint one-old-phase weighted optimum')
            weight_checks.append(dict(k=k,w=str(w),optimum=str(best_joint),gap_from_independent=str(w*loss)))
    result=dict(scope='Fixed FC36 85-class pure/star source, one shared original35 phase, JP1 slot constraints on its same root-1 descendant bucket. Phase-slot optimum only; no actual globally extremal cover or simultaneous full inventory realization.',
       input=str(args.input),input_sha256=sha256(raw).hexdigest(),
       alpha=str(alpha),rho=str(rho),u35=str(u0),outside_root2=str(gout2),
       bucket=[dict(cofactor=d,label=3*d,exponents={str(p):e for p,e in f.items()},coefficient=str(a),coefficient_decimal=float(a)) for a,d,f in bucket],
       gap6=str(delta6),gap6_decimal=float(delta6),gap8=str(delta8),gap8_decimal=float(delta8),
       prior_bucket_only_gap8=str(old_delta8),prior_bucket_only_gap8_decimal=float(old_delta8),increment=str(delta8-old_delta8),
       original35_phase_cases=len(phase_rows),partial_matchings_examined=count_matchings,phase_rows=phase_rows,weighted_equalities=weight_checks,
       all_checks_passed=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('alpha','rho','u35','bucket','gap6','gap6_decimal','gap8','gap8_decimal','prior_bucket_only_gap8','prior_bucket_only_gap8_decimal','increment','original35_phase_cases','partial_matchings_examined')},indent=2))
if __name__=='__main__':main()
