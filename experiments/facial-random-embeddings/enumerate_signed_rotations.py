#!/usr/bin/env python3
"""Exact signed-rotation enumeration using doubled permutation face cycles.

Model independently implemented from the mathematical definitions in the theory.
No external dependencies; all arithmetic and enumeration are exact.
"""
from itertools import combinations,product
from collections import Counter
from fractions import Fraction

def count_types(V,edges,rotmask,twistmask,debug=False):
    nbr={v:[] for v in V}
    for a,b in edges: nbr[a].append(b); nbr[b].append(a)
    flags=[(v,w,s) for v in V for w in nbr[v] for s in (0,1)]
    idx={x:i for i,x in enumerate(flags)}; pi=[None]*len(flags); lam=[None]*len(flags)
    for j,v in enumerate(V):
        N=sorted(nbr[v]);
        if (rotmask>>j)&1: N=N[::-1]
        for x,y in zip(N,N[1:]+N[:1]):
            a,b=idx[(v,x,1)],idx[(v,y,0)];pi[a]=b;pi[b]=a
    for j,(u,v) in enumerate(edges):
        t=(twistmask>>j)&1
        for s in (0,1):
            a,b=idx[(u,v,s)],idx[(v,u,t^s)];lam[a]=b;lam[b]=a
    perm=[lam[pi[x]] for x in range(len(flags))]
    seen=set();faces=[]
    for x in range(len(flags)):
        if x in seen: continue
        f=[];y=x
        while y not in seen: seen.add(y);f.append(flags[y][:2]);y=perm[y]
        assert y==x
        faces.append(f)
    g=b=0
    for f in faces:
        for x,y in combinations(f,2):
            if x==y:g+=1
            elif x==y[::-1]:b+=1
    assert g%2==b%2==0
    counts=(g//2,b//2,len(edges)-(g+b)//2)
    assert min(counts)>=0
    return (counts,faces) if debug else counts

def analyze(V,edges,all_rotations=False):
    hist=Counter(); totals=[0,0,0]; n=0
    for r in range(1<<len(V) if all_rotations else 1):
        for t in range(1<<len(edges)):
            c=count_types(V,edges,r,t);hist[c]+=1
            totals=[a+b for a,b in zip(totals,c)];n+=1
    print('vertices',len(V),'edges',len(edges),'embeddings',n,'all_rotations',all_rotations)
    print('totals',totals,'expectations',[str(Fraction(a,n)) for a in totals])
    print('histogram',sorted(hist.items()))
    return totals,n,hist
if __name__=='__main__':
    totals,n,hist=analyze(list(range(4)),list(combinations(range(4),2)),True)
    assert n == 1024 and totals == [2208,1728,2208]

