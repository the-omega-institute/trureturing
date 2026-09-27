#!/usr/bin/env python3
"""Exact actual-source controls for cut70 one-active and partial-public profiles."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
from math import lcm
import argparse,json

N=(4,5,5,5);QS=(2,3,3,3)
AXES=((1,1),(5,1),(1,7),(25,1),(5,7),(1,49),(25,7),(5,49),(25,49))

def require(ok,msg):
    if not ok:raise ValueError(msg)

def tree(ys,k):
    return sum(len({h for g,h in ys if g==j})>=k for j in range(7))>=k

def network(source,Dinic,inside):
    S,T=('s',),('t',);caps={}
    def add(u,v,c):
        require((u,v) not in caps,'unique edge');caps[u,v]=c
    for r,n in enumerate(N):
        add(S,('r',r),21)
        for c in range(n):
            add(('r',r),('c',r,c),7)
            for g in range(7):
                add(('c',r,c),('pg',r,c,g),6)
                for h in range(7):add(('pg',r,c,g),('ph',r,c,g,h),2)
    for g in range(7):
        add(('g',g),T,21)
        for h in range(7):add(('h',g,h),('g',g),7)
    for r,c,g,h in sorted(source):add(('ph',r,c,g,h),('h',g,h),126)
    cut=[(u,v,c) for (u,v),c in caps.items() if u in inside and v not in inside]
    require(sum(c for u,v,c in cut)==70,'explicit70 cut')
    require(all(c!=126 for u,v,c in cut),'no actual bridge crosses')
    nodes={u:i for i,u in enumerate(sorted({u for uv in caps for u in uv}))};net=Dinic(len(nodes))
    refs={uv:net.add(nodes[uv[0]],nodes[uv[1]],c) for uv,c in caps.items()}
    require(net.flow(nodes[S],nodes[T],1000)==70,'maximum70')
    balance=defaultdict(int);atoms=[]
    for (u,v),(i,j,cap) in refs.items():
        f=cap-net.g[i][j][1]
        require(0<=f<=cap,'capacity');balance[u]-=f;balance[v]+=f
        if u[0]=='ph' and v[0]=='h' and f:atoms.append([*u[1:],f])
    require(balance[S]==-70 and balance[T]==70 and all(v==0 for u,v in balance.items() if u not in(S,T)),'conservation')
    return {'edges':len(caps),'flow_units':70,'positive_bridge_flow':atoms,'cut':[[list(u),list(v),c] for u,v,c in cut]}

def actual_checks(source,law,expected):
    fibres={(r,c):{(g,h) for rr,cc,g,h in source if (rr,cc)==(r,c)} for r in range(5) for c in range(5)}
    require(tuple(sum(bool(fibres[r,c]) for c in range(5)) for r in range(5))==(*N,0),'literal4555')
    require(tree({(g,h) for r,c,g,h in source},5),'standalone tree')
    pairs=0;literal=0
    for r,s in combinations(range(4),2):
        for aa in combinations(range(N[r]),QS[r]):
            for bb in combinations(range(N[s]),QS[s]):
                require(tree(set().union(*(fibres[r,c] for c in aa),*(fibres[s,c] for c in bb)),3),'pair tree');pairs+=1
    for roots in combinations(range(5),3):
        for css in product(tuple(combinations(range(5),3)),repeat=3):
            require(tree(set().union(*(fibres[r,c] for r,cs in zip(roots,css) for c in cs)),3),'literal tree');literal+=1
    require((pairs,literal)==(480,10000),'tree counts')
    law={p:v for p,v in law.items() if v}
    require(set(law)<=source and all(v>0 for v in law.values()) and sum(law.values())==1,'actual normalized law')
    maxima={};count=0
    for (a,b),bound in zip(AXES,expected):
        table=defaultdict(Q)
        for (r,c,g,h),v in law.items():table[(r+5*c)%a,(g+7*h)%b]+=v
        for x,y in product(range(a),range(b)):
            require(table[x,y]<=bound,'numerical cylinder cap');count+=1
        maxima[a*b]=max(table.values())
    divs=list(maxima);gamma=sum(maxima[lcm(a,b)] for a,b in product(divs,repeat=2))
    theoretical=sum(dict(zip((a*b for a,b in AXES),expected))[lcm(a,b)] for a,b in product(divs,repeat=2))
    require(gamma<=theoretical<9,'complete81-pair bound')
    return {'source_points':len(source),'source':sorted(source),'pair_tests':pairs,'literal_tests':literal,'standalone_five_tree':True,
            'law':[[*p,str(v)] for p,v in sorted(law.items())], 'cylinders_checked':count,'ordered_pairs':81,
            'cylinder_maxima':{str(d):str(v) for d,v in maxima.items()},'measured_lcm_upper':str(gamma),'theoretical_lcm_upper':str(theoretical)}

def add_private(inside,r,c):
    inside.add(('c',r,c))
    for g in range(7):
        inside.add(('pg',r,c,g))
        for h in range(7):inside.add(('ph',r,c,g,h))

def one_active(active,Dinic):
    source={(r,c,g,h) for r,n in enumerate(N) for c in range(n) for g,h in ([(0,0)] if r==active else product(range(7),repeat=2))}
    inside={('s',),('r',active),('h',0,0)}
    for c in range(N[active]):add_private(inside,active,c)
    law=defaultdict(Q)
    tree9=set(product(range(3),repeat=2));punctured=tree9-{(0,0)}
    for r in range(4):
        if r==active:continue
        choices=list(combinations(range(N[r]),QS[r]))
        for cs in choices:
            # Every retained child has this whole actual projection in this fixture.
            for g,h in punctured:law[r,min(cs),g,h]+=Q(1,3*len(choices)*8)
    expected=list(map(Q,(1,)))+[Q(1,3),Q(3,8),Q(1,5),Q(1,8),Q(1,8),Q(3,40),Q(1,24),Q(1,40)]
    out=actual_checks(source,law,expected)
    require(out['theoretical_lcm_upper']=='33/4','one-active envelope')
    out['network']=network(source,Dinic,inside);out['active_root']=active
    return out

def partial_public(inactive,Dinic):
    # Every active child at root r has the same two fine leaves per branch;
    # no active root alone supplies a ternary branch, but every root pair does.
    rowleaves=({0,1},{1,2},{2,3},{3,4})
    active={r:[c for c in range(N[r]) if (r,c)!=inactive] for r in range(4)}
    source={(r,c,g,h) for r in range(4) for c in active[r] for g in range(3) for h in rowleaves[r]}
    source|={(inactive[0],inactive[1],g,h) for g,h in product(range(7),repeat=2)}
    inside={('s',)}|{('r',r) for r in range(4)}|{('g',g) for g in range(3)}|{('h',g,h) for g in range(3) for h in range(7)}
    for r in range(4):
        for c in active[r]:add_private(inside,r,c)
    law=defaultdict(Q);branch_laws=[]
    for g in range(3):
        net=Dinic(13);refs={}
        for r in range(4):
            net.add(11,r,2)
            for h in sorted(rowleaves[r]):refs[r,h]=net.add(r,4+h,1)
        for h in range(7):net.add(4+h,12,2)
        require(net.flow(11,12,6)==6,'one actual m4q2 branch law')
        branch={p:Q(cap-net.g[u][j][1],6) for p,(u,j,cap) in refs.items()}
        require(sum(branch.values())==1,'branch normalized')
        for r in range(4):
            require(sum(v for (rr,h),v in branch.items() if rr==r)<=Q(1,3),'branch row cap')
        for h in range(7):
            require(sum(v for (r,hh),v in branch.items() if hh==h)<=Q(1,3),'branch leaf cap')
        require(all(v<=Q(1,6) for v in branch.values()),'joint row/leaf cap')
        for (r,h),v in branch.items():
            choices=list(combinations(active[r],QS[r]))
            # Here the row projections, hence this same branch flow, are
            # unchanged under every full product of child restrictions.
            # Marginally averaging the deterministic actual lift is exact.
            for cs in choices:law[r,min(cs),g,h]+=v/(3*len(choices))
        branch_laws.append([[r,h,str(v)] for (r,h),v in sorted(branch.items()) if v])
    delta=max(Q(QS[r],len(active[r])) for r in range(4))
    expected=[Q(1),Q(1,3),Q(1,3),delta/3,Q(1,9),Q(1,9),delta/9,Q(1,18),delta/18]
    out=actual_checks(source,law,expected)
    require(Q(out['theoretical_lcm_upper'])==(97+85*delta)/18,'partial-public envelope')
    out['network']=network(source,Dinic,inside);out['inactive_child']=inactive;out['delta']=str(delta);out['branch_laws']=branch_laws
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();spec=spec_from_file_location('_cut70_dinic',args.base_module);mod=module_from_spec(spec);spec.loader.exec_module(mod)
    controls={f'one_active_{r}':one_active(r,mod.Dinic) for r in range(4)}
    controls.update({'partial_gap_public':partial_public((0,3),mod.Dinic),'partial_full_public':partial_public((1,4),mod.Dinic)})
    out={'controls':controls,'scope':'Six actual cut70 controls for families A and D. Universal classification, actual-support proofs for other families and unrestricted odd noncoverage are separate.'}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({name:{k:value[k] for k in ('source_points','measured_lcm_upper','theoretical_lcm_upper')} for name,value in controls.items()}))
if __name__=='__main__':main()
