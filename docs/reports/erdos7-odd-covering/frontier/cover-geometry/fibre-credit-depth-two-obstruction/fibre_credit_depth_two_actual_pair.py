#!/usr/bin/env python3
"""All100 root/leaf budget vertices for one actual5x7 source; full tails."""
import argparse
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import json

Q=(5,7)
B=tuple(F(1,q-2) for q in Q)
C=tuple(F(q-1,q-2) for q in Q)
P=tuple(c/q for c,q in zip(C,Q))
W=(F(1,4),F(1,4),F(1,6),F(1,6),F(1,6))
ROOTS=((0,1),(2,3,4))
V=tuple(tuple(1+int(l in root)+int(l==s) for l in range(5)) for root in ROOTS for s in range(5))


def dot(a,b):return sum((x*y for x,y in zip(a,b)),F(0))


def query(m,t):
    h=F(0)
    for E in range(4):
        a=tuple(W[l]*prod((m[i][l]-P[i] for i in range(2) if not E>>i&1),start=F(1))
                for l in range(5))
        mass=prod((P[i] for i in range(2) if E>>i&1),start=F(1))
        first=prod((P[i]+B[i] for i in range(2) if E>>i&1),start=F(1))
        low={1:F(1)}
        for i,q in enumerate(Q):
            if not E>>i&1:continue
            new={}
            for n,p in low.items():
                for v in range(2,t):
                    if n*v<t:new[n*v]=new.get(n*v,F(0))+p*C[i]*F(q-1,q**v)
            low=new
        low={n:p for n,p in low.items() if n<t}
        tail_mass=mass-sum(low.values(),F(0))
        tail_first=first-sum((n*p for n,p in low.items()),F(0))
        if tail_mass<0 or tail_first<t*tail_mass:
            raise RuntimeError('tail inconsistency')
        h+=tail_first*max(dot(a,v) for v in V)-t*tail_mass*sum(a,F(0))
        h+=sum((p*max(dot(a,tuple(max(v[l]*n-t,0) for l in range(5))) for v in V)
                for n,p in low.items()),F(0))
    return h



def query_closed(m):
    z=tuple(tuple(m[k][l]-P[k] for l in range(5)) for k in range(2))
    a5=tuple(W[l]*z[0][l] for l in range(5))
    a7=tuple(W[l]*z[1][l] for l in range(5))
    def moment(a):
        return sum(a,F(0))+max(sum((a[l] for l in root),F(0)) for root in ROOTS)+max(a)
    return (max(W[l]*z[0][l]*z[1][l] for l in range(5))
            +(B[0]+P[0])*moment(a7)-2*P[0]*sum(a7,F(0))
            +(B[1]+P[1])*moment(a5)-2*P[1]*sum(a5,F(0))
            +F(7,4)*(B[0]+P[0])*(B[1]+P[1])-2*P[0]*P[1])


def certificate():
    profiles=[]
    for i,j in product(range(10),repeat=2):
        m=tuple(tuple(1-B[k]*(V[o][l]-1) for l in range(5)) for k,o in enumerate((i,j)))
        if not all(m[k][l]>=P[k] for k in range(2) for l in range(5)):
            raise RuntimeError('negative query zero atom')
        star=dot(W,tuple(m[0][l]*m[1][l] for l in range(5)))
        g=star-F(7,4)*B[0]*B[1]
        if g<=0:
            raise RuntimeError('nonpositive source normalization')
        h=query(m,2)
        if h!=query_closed(m):
            raise RuntimeError('closed full-tail formula differs')
        profiles.append((1+h/g,i,j,star,g,h,2*g-h))
    if min(p[3] for p in profiles)!=F(37,60):
        raise RuntimeError('uniform joint-star lower differs')
    if min(p[4] for p in profiles)!=F(1,2):
        raise RuntimeError('uniform supported-source lower differs')
    if min(p[6] for p in profiles)!=F(1,700):
        raise RuntimeError('uniform paired source/query margin differs')
    r,i,j,star,g,h,margin=max(profiles)
    if r!=F(9651,3220) or not r<3:
        raise RuntimeError('uniform query ratio differs')
    if min((F(9651,3220)-1)*p[4]-p[5] for p in profiles)!=0:
        raise RuntimeError('tight ratio inequality fails at some vertex')
    return dict(scope='All actual star profiles of the retained five-leaf interface, all finite nonternary heights, whole original ternary height<=2. This is a5x7 source/query interface, not the completed nine-prime continuation.',
        method='Same fixed weights and t=2 across all100 inventory vertices; separate concavity and thinning to each actual profile own budget majorant. No mixture of corner carriers.',
        primes=Q,weights=list(map(str,W)),threshold=2,vertex_count=len(profiles),
        joint_star_mass_lower='37/60',mixed_support_union_cap='7/60',
        source_mass_lower='1/2',paired_score_lower='1/700',query_upper=str(r),
        query_upper_decimal=float(r),worst_vertex=dict(owners=[i,j],
            root_leaf_owners=[[i//5,i%5],[j//5,j%5]],
            source_lower=str(g),query_hinge_upper=str(h),paired_score=str(margin)),
        evidence='Ordinary proof and exact rational verification, not new Lean verification.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    out=json.loads(json.dumps(certificate()))
    rendered=json.dumps(out,sort_keys=True,indent=2)+'\n'
    if args.output is None:
        retained=json.loads(Path(__file__).resolve().with_suffix('.json').read_text())
        if retained!=out:
            raise RuntimeError('retained result differs from exact replay')
        print(rendered,end='')
    else:
        args.output.write_text(rendered)


if __name__=='__main__':
    main()
