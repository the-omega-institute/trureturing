#!/usr/bin/env python3
"""Necessary cut70 profile and sorted private-cost shape replay, not geometry."""
from itertools import combinations_with_replacement, product
from pathlib import Path
import json

def require(ok,msg):
    if not ok:raise ValueError(msg)

def profiles():
    n=(4,5,5,5);q=(2,3,3,3);out=[]
    for active in product((0,2,3,4),(0,3,4,5),(0,3,4,5),(0,3,4,5)):
        T=sum(3 if a==0 else nn-a for a,nn in zip(active,n))
        if T>10:continue
        rr=[i for i,a in enumerate(active) if a]
        for k in range(11-T):
            if (70-7*(T+k))%2:continue
            Z=(70-7*(T+k))//2
            if active==n and k+Z<15:continue
            u=max(0,9-k)
            dom=[range(q[i] if k==0 else 0,max(u,q[i] if k==0 else 0)+1) for i in rr]
            best=10**9;witness=None
            for pp in product(*dom):
                if any(pp[i]+pp[j]<u for i in range(len(rr)) for j in range(i+1,len(rr))):continue
                cost=sum(p+(active[i]-q[i])*((p+q[i]-1)//q[i]) for i,p in zip(rr,pp))
                if cost<best:best=cost;witness=pp
            if best<=Z:out.append({'active':active,'T':T,'k':k,'Z':Z,'minimum_sorting_cost':best,'witness_p':witness})
    require(len(out)==14,'fourteen necessary labelled profiles')
    return out

def shapes(lengths,k,Z):
    # A minimum cut never spends >=8 private units below an active child:
    # moving that whole child subtree to sink replaces them by its cap7 arc.
    # Thus each unweighted private cost is at most3.
    domains=[list(combinations_with_replacement(range(1 if k==0 else 0,4),a)) for a in lengths]
    out=[]
    for rows in product(*domains):
        if any(lengths[i]==lengths[j] and i>0 and rows[i]>rows[j]
               for i in range(1,4) for j in range(i+1,4)):continue
        if sum(map(sum,rows))!=Z:continue
        pp=[sum(row[:q]) for row,q in zip(rows,(2,3,3,3))]
        if any(pp[i]+pp[j]<9-k for i in range(4) for j in range(i+1,4)):continue
        out.append('/'.join(''.join(map(str,row)) for row in rows))
    return out

def verify():
    out={'profiles':profiles(),'shapes':{}}
    for name,lengths,k,Z,expected in [('B',(3,5,5,5),3,21,4),('C',(4,4,5,5),3,21,1),('E',(4,5,5,5),0,35,1),('F',(4,5,5,5),4,21,9)]:
        rows=shapes(lengths,k,Z)
        require(len(rows)==expected,'shape count '+name)
        out['shapes'][name]=rows
    out['scope']='Necessary arithmetic profiles and sorted cost shapes only; does not certify actual child-to-leaf incidence, laws, or all cut70.'
    return out

def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();out=verify()
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('labelled profiles',len(out['profiles']))
    for family,rows in out['shapes'].items():print(family,len(rows),rows)

if __name__=='__main__':main()
