#!/usr/bin/env python3
"""Exact fixed-weight original-query certificate for a two-public-label supplier."""
import argparse
from itertools import product
from math import lcm
from pathlib import Path
import json

def require(test,message):
    if not test:raise RuntimeError(message)

def component_caps(d,root,column):
    # Units1/420. Root0 is anchor R, root1 all other original roots.
    # Column0 is private H, column1 public J, column2 all other columns.
    if d==1:return 420,420
    if root==-1:
        if d==7:return ((0,300),(105,120),(315,0))[column]
        require(d==49,'unexpected root-free modulus')
        # For J, disjoint fine supports give max(t/4,(1-t)/7)=t/4.
        return ((0,60),(105,0),(105,0))[column]
    psi=0
    if root==1 and column!=0:
        psi={5:140,25:84,35:35 if column==1 else 105,
             175:21 if column==1 else 63,245:35,1225:21}[d]
    eta=0
    if root==0 and column!=2:
        eta={5:420,25:120,35:300 if column==0 else 120,
             175:60,245:60,1225:60}[d]
    return psi,eta

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    D=(1,5,7,25,35,49,175,245,1225)
    roots=[i for i,d in enumerate(D) if d%5==0]
    columns=[i for i,d in enumerate(D) if d%7==0]
    pairs=[(i,j,lcm(d,e)) for i,d in enumerate(D) for j,e in enumerate(D) if i<=j]
    require(302*11>=4*477,'fine-support maximum premise')
    vectors=set();count=0;maximum=-1;maxima=[]
    for rootword in product(range(2),repeat=6):
        R=[-1]*9
        for i,r in zip(roots,rootword):R[i]=r
        live=[]
        for i,j,d in pairs:
            if R[i]>=0 and R[j]>=0 and R[i]!=R[j]:continue
            live.append((i,j,d,max(R[i],R[j]),1 if i==j else 2))
        for colword in product(range(3),repeat=6):
            C=[-1]*9
            for i,c in zip(columns,colword):C[i]=c
            A=B=0
            for i,j,d,r,factor in live:
                if C[i]>=0 and C[j]>=0 and C[i]!=C[j]:continue
                a,b=component_caps(d,r,max(C[i],C[j]))
                A+=factor*a;B+=factor*b
            vectors.add((A,B));count+=1
            weighted=302*A+175*B
            require(weighted<=1785840,'fixed-weight query bound')
            if weighted>maximum:maximum=weighted;maxima=[]
            if weighted==maximum:maxima.append({'roots':rootword,'columns':colword,'vector':[A,B]})
    require(count==46656 and len(vectors)==6803,'query enumeration count')
    require(maximum==1785840,'sharp cap-envelope value')
    require(set(tuple(x['vector']) for x in maxima)=={(5670,420),(420,9480)},'maximizing upper vectors')
    require(1785840*477==4252*(420*477),'bound reduction')
    result={'scope':'All original queries map to this finite cap relaxation; actual source/owner hypotheses require the ordinary proof. No Lean.','layouts':count,'distinct_vectors':len(vectors),'psi_weight':'302/477','eta_weight':'175/477','component_units':'1/420','maximum_weighted_numerator':maximum,'common_denominator':420*477,'uniform_bound':'4252/477','strict_margin':'41/477','maximizing_layouts':maxima,'upper_vectors':sorted(vectors),'PASS':True}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('upper_vectors','maximizing_layouts')}))

if __name__=='__main__':main()
