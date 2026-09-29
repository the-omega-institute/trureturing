#!/usr/bin/env python3
"""Whole-source controls for two safe half-unit transport families."""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json
import runpy


def req(ok,msg):
    if not ok: raise ValueError(msg)


def loads(atoms):
    block=defaultdict(Q); col=defaultdict(Q); fine=defaultdict(Q)
    for (r,c,g,h),m in atoms.items():
        block[r,g]+=m;col[g]+=m;fine[g,h]+=m
    return block,col,fine


def potential(source,atoms):
    block,col,fine=loads(atoms)
    n18=n185=0
    for (r,g),m in block.items():
        if m==Q(37,2):n185+=1
        if m!=18:continue
        sets=[{h for gg,h in source.get((r,c),()) if gg==g} for c in range(5)]
        bad=any(len(set().union(*(sets[c] for c in cs)))<=2
                for cs in combinations(range(5),3))
        n18+=bad
    req(n18+n185<=4,'potential root bound')
    return n18,n185


def check(source,atoms,network,checker):
    flat={(r,c,g,h) for (r,c),labels in source.items() for g,h in labels}
    children,pairs,mono=checker(flat)
    edges,trails=network['paths'](source)
    load=defaultdict(Q)
    for p,m in atoms.items():
        req(p in flat and m>=0 and 2*m==int(2*m),'actual half-integral atom')
        for e in trails[p]:load[e]+=m
    req(sum(atoms.values())==74,'common total74')
    for e,cap in edges.items():
        req(0<=load[e]<=(Q(37,2) if e[0]==('S',) else cap),'all original capacities')
    req(all(load[(('S',),('R',r))]==Q(37,2) for r in range(4)),'same root totals')
    return pairs,len(edges),load


def complement_capacity(source,atoms,r,G):
    o=defaultdict(Q);oh=defaultdict(Q)
    for (s,c,g,h),m in atoms.items():
        if s!=r:o[g]+=m;oh[g,h]+=m
    A=defaultdict(set)
    for (s,c),labels in source.items():
        if s==r:
            for g,h in labels:
                if g!=G:A[g].add(h)
    return sum(min(21-o[g],sum(7-oh[g,h] for h in hs)) for g,hs in A.items())


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--base-helper',type=Path,required=True)
    p.add_argument('--network-helper',type=Path,required=True)
    p.add_argument('--source-helper',type=Path,required=True)
    a=p.parse_args()
    base=runpy.run_path(str(a.base_helper))
    network=runpy.run_path(str(a.network_helper))
    checker=runpy.run_path(str(a.source_helper))['source_checks']
    source,old=base['fixture']()
    for c in (0,1):source[0,c]={(g,h) for g,h in source[0,c] if g!=0 or h in (0,1)}
    old={p:m for p,m in old.items() if not(p[0]==0 and p[2]==0)}
    for c,hs in enumerate(((0,1),(0,1),(2,3,4),(2,3))):
        for h in hs:old[0,c,0,h]=Q(2)
    pairs,edge_count,oldload=check(source,old,network,checker)
    req(potential(source,old)==(1,0),'initial T3bad mass18 support')
    req(complement_capacity(source,old,0,0)==Q(1,2),'fixed-other-root repair blocked')
    # This source still has the same matching original74 cut.
    edges,_=network['paths'](source)
    cut=[e for e in edges if base['original_cut_side'](e[0]) and not base['original_cut_side'](e[1])]
    req(sum(edges[e] for e in cut)==74,'cross-control exact original maximum74')
    req(all(oldload[e]==edges[e] for e in cut),'matching cut saturation')
    cross=dict(old)
    for point,delta in (((0,0,1,0),Q(1,2)),((1,0,0,0),Q(1,2)),
                        ((1,0,1,0),-Q(1,2)),((0,0,0,0),-Q(1,2))):
        cross[point]=cross.get(point,Q())+delta
    check(source,cross,network,checker)
    req(potential(source,cross)==(0,0),'cross potential strictly decreases')
    ob,oc,of=loads(old);nb,nc,nf=loads(cross)
    req(oc==nc,'cross public coarse totals preserved')
    req(nb[0,0]==Q(35,2),'cross selected block lowers by half')
    # Add one actual off-G point to test the own-root repair. This second
    # source remains literal and balanced, but no original max74 is claimed.
    ownsource={rc:set(hs) for rc,hs in source.items()}
    ownsource[0,0].add((2,6))
    check(ownsource,old,network,checker)
    C=complement_capacity(ownsource,old,0,0)
    req(C>=1,'own-root available public complement')
    own=dict(old)
    own[0,0,1,0]=Q(0)
    own[0,0,2,6]=Q(1)
    own[0,0,0,0]-=Q(1,2)
    check(ownsource,own,network,checker)
    req(potential(ownsource,own)==(0,0),'own-root potential strictly decreases')
    req(all(own.get(p,Q())==m for p,m in old.items() if p[0]!=0),'other roots fixed')
    rows=[]
    for name,ss,new,Cval,maximum in (('cross',source,cross,Q(1,2),74),
                                    ('own_root',ownsource,own,C,None)):
        rows.append(dict(kind=name,original_maximum=maximum,initial_C=str(Cval),
                         actual_points=sum(map(len,ss.values())),original_pairs=480,
                         initial_potential=list(potential(ss,old)),final_potential=list(potential(ss,new)),
                         source=[dict(root=r,child=c,whole_fibre=sorted(hs))for (r,c),hs in sorted(ss.items())],
                         initial_flow=[dict(point=p,mass=str(m)) for p,m in sorted(old.items()) if m],
                         final_flow=[dict(point=p,mass=str(m)) for p,m in sorted(new.items()) if m]))
    out=dict(status='PASS',scope='Two complete actual balanced-value74 source controls; only the first is certified original maximum74. No terminal-trap exclusion.',
             cases=rows)
    a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',cases=[{k:v for k,v in r.items() if k not in('source','initial_flow','final_flow')}for r in rows])))


if __name__=='__main__':main()
