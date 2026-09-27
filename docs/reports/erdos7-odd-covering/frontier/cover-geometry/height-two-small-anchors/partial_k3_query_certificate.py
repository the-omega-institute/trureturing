#!/usr/bin/env python3
"""Exact joint-query upper certificate for a four-plus-five-plus-five private geometry.

This is an ordinary finite certificate, not a Lean result. The manuscript supplies
one actual probability law before queries and bridges its cylinders to this table.
"""
import argparse
from itertools import product
from math import lcm
from pathlib import Path
import json

D=(1,5,7,25,35,49,175,245,1225)
ROOT_INDICES=(1,3,4,6,7,8)
COLUMN_INDICES=(2,4,5,6,7,8)
COLUMN_FREE=(0,1,3)
N=1615

def require(test,message):
    if not test:raise RuntimeError(message)

def cap(d,r,c):
    # r: -1 unqueried, 0 partial A, 1 clean B/C, 2 gap.
    # c: -1 unqueried, 0 public G, 1 H_A, 2 H_B/H_C, 3 exterior K.
    if d==1:return N
    if d==5:return (635,580,135)[r]
    if d==7:return (360,320,400,135)[c]
    if d==25:return (215,188,135)[r]
    if d==49:return (120,80,80,45)[c]
    table={
        35:((180,320,0,135),(180,0,400,0),(0,0,0,135)),
        175:((135,80,0,135),(108,0,80,0),(0,0,0,135)),
        245:((80,80,0,45),(80,0,80,0),(0,0,0,45)),
        1225:((60,80,0,45),(48,0,80,0),(0,0,0,45))}
    require(r>=0 and c>=0,'mixed divisor coordinates')
    return table[d][r][c]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    require(14*80+360+3*45==N,'probability normalization')
    maxvalue=-1;maxima=[];count=0;root_bounds=[]
    columnwords=list(product(range(4),repeat=6))
    pairs=[(i,j) for i in range(6) for j in range(i+1,6)]
    for rw in product(range(3),repeat=6):
        R=[-1]*9
        for i,r in zip(ROOT_INDICES,rw):R[i]=r
        def meet(i,j,c):
            a,b=R[i],R[j]
            if a>=0 and b>=0 and a!=b:return 0
            return cap(lcm(D[i],D[j]),max(a,b),c)
        base=sum(meet(i,j,-1) for i in COLUMN_FREE for j in COLUMN_FREE)
        unary=[]
        for i in COLUMN_INDICES:
            unary.append(tuple(meet(i,i,c)+2*sum(meet(i,j,c) for j in COLUMN_FREE) for c in range(4)))
        edges=[tuple(2*meet(COLUMN_INDICES[i],COLUMN_INDICES[j],c) for c in range(4)) for i,j in pairs]
        rootmax=-1
        for cw in columnwords:
            val=base+sum(u[c] for u,c in zip(unary,cw))
            val+=sum(e[cw[i]] for (i,j),e in zip(pairs,edges) if cw[i]==cw[j])
            require(val<=13895,'uniform integer upper bound')
            count+=1
            if val>rootmax:rootmax=val
            if val>maxvalue:maxvalue=val;maxima=[]
            if val==maxvalue:maxima.append({'roots':rw,'columns':cw})
        root_bounds.append({'roots':rw,'maximum':rootmax})
    require(count==2985984,'complete coarse-layout count')
    require(maxvalue==13895,'sharp table maximum')
    require(maxvalue<9*N,'strict target threshold')
    require(13895*323==2779*N,'reduced fraction')
    require(9*323-2779==128,'strict margin')
    result={'scope':'Every actual numerical query maps to one enumerated coarse layout with termwise domination; high-digit compatibility is relaxed. Full-source and common-law hypotheses are supplied in the manuscript. Not Lean.','private_point_mass':'80/1615','public_total_mass':'360/1615','exterior_point_mass':'45/1615','layouts':count,'maximum_numerator':maxvalue,'denominator':N,'uniform_bound':'2779/323','strict_margin':'128/323','maximizing_layouts':maxima,'root_bounds':root_bounds,'PASS':True}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='root_bounds'}))

if __name__=='__main__':main()
