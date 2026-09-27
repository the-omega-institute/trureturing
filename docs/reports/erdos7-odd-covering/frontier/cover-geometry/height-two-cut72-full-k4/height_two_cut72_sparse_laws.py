#!/usr/bin/env python3
"""Exact actual-source controls for four sparse cut72 law constructions.

Ordinary finite arithmetic, not Lean verification or unrestricted odd covering.
"""
from collections import defaultdict, deque
from fractions import Fraction as Q
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import importlib.util
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def load_dinic(path):
    spec = importlib.util.spec_from_file_location('_cut72_existing_dinic', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.Dinic


N = (4, 5, 5, 5)
CHILDREN = {(r, c) for r in range(4) for c in range(N[r])}
ALL = set(product(range(7), repeat=2))
DIVS = (1, 5, 7, 25, 35, 49, 175, 245, 1225)


def templates():
    out = []
    for r in (0, 3):
        active = tuple(N[s] if s == r else 0 for s in range(4))
        private = {(r, c): {(0, 1)} if c == N[r]-1 else set() for c in range(N[r])}
        fibres = {child: ({(0, 0)} | private[child]) if child[0] == r else set(ALL)
                  for child in CHILDREN}
        out.append(dict(name='4000' if r == 0 else '0005', active=active,
                        public_columns=(), public_leaves=((0, 0),), private=private,
                        fibres=fibres, kind='punctured', active_root=r,
                        cap=(Q(1),Q(1,3),Q(3,8),Q(1,5),Q(1,8),Q(1,8),Q(3,40),Q(1,24),Q(1,40))))
    private = {(2, c): {(0, c)} for c in range(5)}
    private.update({(3, c): {(1, c),(2, c)} for c in range(5)})
    fibres = {child: private[child] if child in private else set(ALL) for child in CHILDREN}
    out.append(dict(name='0055',active=(0,0,5,5),public_columns=(),public_leaves=(),
                    private=private,fibres=fibres,kind='twoactive',
                    cap=(Q(1),Q(2,7),Q(3,7),Q(2,21),Q(1,7),Q(13,105),Q(3,35),Q(1,21),Q(1,35))))
    for whole in (False, True):
        private = {(r,c): {(r,c)} for r in (1,2,3) for c in range(5)}
        fibres = {child: set(ALL) for child in CHILDREN}
        for (r,c), pts in private.items():
            common = {(0,c)} if whole else {(0,h) for h in range(3)}
            fibres[r,c] = common | pts
        out.append(dict(name='0555_whole' if whole else '0555_finite',active=(0,5,5,5),
                        public_columns=(0,) if whole else (),
                        public_leaves=() if whole else tuple((0,h) for h in range(3)),
                        private=private,fibres=fibres,kind='threeactive',
                        cap=(Q(1),Q(145,417),Q(100,417),Q(47,417),Q(100,417),
                             Q(10,139),Q(9,139),Q(20,417),Q(20,417))))
    for item in out:
        item['source'] = {(r,c,g,h) for (r,c), ys in item['fibres'].items() for g,h in ys}
    return out


def literal_checks(item):
    fibres = item['fibres']
    def projection(children):
        return set().union(*(fibres.get(child,set()) for child in children))
    def tree(ys,k):
        return sum(sum(gg==g for gg,h in ys)>=k for g in range(7))>=k
    require(set(fibres)==CHILDREN and all(fibres.values()),'literal4555 occupancy')
    require(tree(projection(fibres),5),'actual standalone five-tree')
    pair_count = 0
    for r,s in combinations(range(4),2):
        for aa in combinations(range(N[r]),N[r]-2):
            for bb in combinations(range(N[s]),N[s]-2):
                require(tree(projection({(r,c) for c in aa}|{(s,c) for c in bb}),3),'pair tree')
                pair_count += 1
    literal_count = 0
    for roots in combinations(range(5),3):
        for choices in product(tuple(combinations(range(5),3)),repeat=3):
            require(tree(projection({(r,c) for r,cs in zip(roots,choices) for c in cs}),3),'full literal tree')
            literal_count += 1
    require((pair_count,literal_count)==(480,10000),'complete literal counts')
    return dict(pair_tests=pair_count,literal_tests=literal_count,standalone=True)


def solve_network(caps, start, finish, target, dinic):
    nodes = sorted({node for uv in caps for node in uv})
    ids = {node:i for i,node in enumerate(nodes)}
    net = dinic(len(nodes))
    refs = {uv:net.add(ids[uv[0]],ids[uv[1]],cap) for uv,cap in caps.items()}
    value = net.flow(ids[start],ids[finish],target)
    flow, balance = {},defaultdict(int)
    for (u,v),(i,j,cap) in refs.items():
        f = cap-net.g[i][j][1]
        require(0<=f<=cap,'every edge capacity')
        flow[u,v]=f
        balance[u]-=f
        balance[v]+=f
    require(balance[start]==-value and balance[finish]==value and
            all(v==0 for u,v in balance.items() if u not in(start,finish)),'every vertex balance')
    reachable={ids[start]}; queue=deque(reachable)
    while queue:
        u=queue.popleft()
        for v,cap,rev in net.g[u]:
            if cap and v not in reachable:
                reachable.add(v);queue.append(v)
    return value,flow,{node for node,i in ids.items() if i in reachable}


def actual_network(item,dinic):
    caps={};start=('source',);finish=('sink',)
    def add(u,v,cap):
        require((u,v) not in caps,'unique arc');caps[u,v]=cap
    for r,n in enumerate(N):
        add(start,('r',r),21)
        for c in range(n):
            add(('r',r),('c',r,c),7)
            for g in range(7):
                add(('c',r,c),('pg',r,c,g),6)
                for h in range(7):
                    add(('pg',r,c,g),('ph',r,c,g,h),2)
    for g in range(7):
        add(('cg',g),finish,21)
        for h in range(7):
            add(('ch',g,h),('cg',g),7)
    for p in sorted(item['source']):
        add(('ph',*p),('ch',*p[2:]),126)
    value,flow,side=solve_network(caps,start,finish,1000,dinic)
    require(value==72,'actual maxflow72')
    mincut=[(u,v,c) for (u,v),c in caps.items() if u in side and v not in side]
    require(sum(c for u,v,c in mincut)==72,'computed mincut72')
    explicit={start}
    for g in item['public_columns']:
        explicit.add(('cg',g));explicit.update(('ch',g,h) for h in range(7))
    explicit.update(('ch',g,h) for g,h in item['public_leaves'])
    for r,a in enumerate(item['active']):
        if a: explicit.add(('r',r))
        for c in range(a):
            explicit.add(('c',r,c))
            for g in range(7):
                explicit.add(('pg',r,c,g))
                explicit.update(('ph',r,c,g,h) for h in range(7) if (g,h) not in item['private'][r,c])
    cut=[(u,v,c) for (u,v),c in caps.items() if u in explicit and v not in explicit]
    require(not any(u[0]=='ph' for u,v,c in cut),'no cut bridge')
    require(sum(c for u,v,c in cut)==72,'explicit cut72')
    require(all(flow[u,v]==c for u,v,c in cut),'forward cut saturation')
    require(all(flow[u,v]==0 for u,v in caps if u not in explicit and v in explicit),'zero backward cut flow')
    atoms=[[*u[1:],f] for (u,v),f in flow.items() if u[0]=='ph' and v[0]=='ch' and f]
    return dict(maximum_flow=value,minimum_cut=72,edge_count=len(caps),
                prescribed_cut=[[list(u),list(v),c] for u,v,c in cut],actual_flow_atoms=atoms)


def coupled_child_law(item,r,dinic):
    # Report443 on actual points outside clean H=0; common tree has capacities1/2,1/6.
    m=N[r];q=m-2;den=30 if m==5 else 12
    caps={};start=('source',);finish=('sink',)
    def add(u,v,cap):
        require(Q(cap).denominator==1,'integral scaled capacity');caps[u,v]=int(cap)
    for c in range(m):
        add(start,('child',c),Q(den,3))
        for g in range(1,7):
            add(('child',c),('private_col',c,g),Q(den*q,2*m))
            for h in range(7):
                add(('private_col',c,g),('private_leaf',c,g,h),Q(den*q,6*m))
    for g in range(1,7):
        add(('common_col',g),finish,Q(den,2))
        for h in range(7):
            add(('common_leaf',g,h),('common_col',g),Q(den,6))
    for c in range(m):
        for g,h in sorted(item['fibres'][r,c]):
            if g!=0:add(('private_leaf',c,g,h),('common_leaf',g,h),den)
    value,flow,side=solve_network(caps,start,finish,den,dinic)
    require(value==den,'one actual local coupling')
    law={(r,*u[1:]):Q(f,den) for (u,v),f in flow.items() if u[0]=='private_leaf' and v[0]=='common_leaf' and f}
    return law


def public_law(item,dinic):
    law=defaultdict(Q);restrictions=tuple(combinations(range(5),3));flows=0
    for choices in product(restrictions,repeat=3):
        caps={};start=('source',);finish=('sink',);owners={}
        for r,cc in zip((1,2,3),choices):
            caps[start,('root',r)]=9
            for h in range(7):
                caps[('root',r),('private_leaf',r,h)]=4
                actual=[(r,c,0,h) for c in cc if (0,h) in item['fibres'][r,c]]
                if actual:
                    owners[r,h]=min(actual)
                    caps[('private_leaf',r,h),('common_leaf',h)]=18
        for h in range(7):caps[('common_leaf',h),finish]=6
        for r,s in combinations((1,2,3),2):
            require(len({h for rr,h in owners if rr in(r,s)})>=3,'each restricted pair has3 common leaves')
        value,flow,side=solve_network(caps,start,finish,18,dinic)
        require(value==18,'one actual joint public coupling')
        for (u,v),f in flow.items():
            if u[0]=='private_leaf' and v[0]=='common_leaf' and f:
                law[owners[u[1:]]]+=Q(f,18000)
        flows+=1
    require(flows==1000 and sum(law.values())==1,'average1000 exact public laws')
    return dict(law)


def construct_law(item,dinic):
    law=defaultdict(Q)
    if item['kind']=='punctured':
        excluded=item['active_root'];removed={(0,0)}
        for r in range(4):
            if r==excluded:continue
            restrictions=tuple(combinations(range(N[r]),N[r]-2))
            for cc in restrictions:
                owners=defaultdict(list)
                for c in cc:
                    for y in item['fibres'][r,c]:owners[y].append((r,c,*y))
                union=set(owners)|removed
                branches=[g for g in range(7) if sum(gg==g for gg,h in union)>=3][:3]
                tree={(g,h) for g in branches for h in sorted(h for gg,h in union if gg==g)[:3]}
                points=tree-removed
                require(len(points)>=8,'punctured witness8')
                for y in points:
                    require(owners[y],'retained witness actual owner')
                    law[min(owners[y])]+=Q(1,3*len(restrictions)*len(points))
    elif item['kind']=='twoactive':
        for c in range(5):law[2,c,0,c]+=Q(1,35)
        for c in range(5):
            for g in (1,2):law[3,c,g,c]+=Q(1,35)
        for r in (0,1):
            for p,w in coupled_child_law(item,r,dinic).items():law[p]+=Q(2,7)*w
    else:
        for p,w in public_law(item,dinic).items():law[p]+=Q(30,139)*w
        for r in (1,2,3):
            for c in range(5):law[r,c,r,c]+=Q(20,417)
        # All5 selected distinct gap leaves deliberately use the SAME actual child.
        for h in range(5):law[0,0,4,h]+=Q(9,695)
    return dict(law)


def check_law(item,law):
    require(set(law)<=item['source'] and all(w>0 for w in law.values()),'every positive atom actual')
    require(sum(law.values())==1,'one normalized law')
    def crt(p):
        r,c,g,h=p;x=r+5*c;y=g+7*h
        return x+25*((y-x)*pow(25,-1,49)%49)
    maxima={};count=0
    for d,cap in zip(DIVS,item['cap']):
        values=defaultdict(Q)
        for p,w in law.items():values[crt(p)%d]+=w
        for a in range(d):
            require(values[a]<=cap,'every original numerical cylinder under universal cap');count+=1
        maxima[d]=max(values.values())
    gamma=sum(maxima[lcm(d,e)] for d,e in product(DIVS,repeat=2))
    capdict=dict(zip(DIVS,item['cap']))
    bound=sum(capdict[lcm(d,e)] for d,e in product(DIVS,repeat=2))
    require(count==1767 and gamma<=bound<9,'all81 LCM terms under one law')
    return dict(atoms=[[*p,str(w)] for p,w in sorted(law.items())],
                cylinder_maxima={str(d):str(v) for d,v in maxima.items()},
                universal_caps={str(d):str(v) for d,v in capdict.items()},
                gamma_envelope=str(gamma),universal_gamma=str(bound),
                cylinders_checked=count,ordered_lcm_pairs=81)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();dinic=load_dinic(args.dinic_module)
    controls=[]
    for item in templates():
        rec=dict(name=item['name'],source=sorted(item['source']),source_points=len(item['source']),
                 active_counts=item['active'],public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*child,sorted(ys)] for child,ys in sorted(item['private'].items())],
                 **literal_checks(item),network=actual_network(item,dinic),law=check_law(item,construct_law(item,dinic)))
        controls.append(rec)
        print(json.dumps({k:rec[k] for k in ('name','source_points')}|{'mincut':72,'gamma':rec['law']['gamma_envelope'],'universal_gamma':rec['law']['universal_gamma']}))
    require(len(controls)==5,'four sparse profile families and both0555 public forms')
    out=dict(scope='Five exact actual-source controls for four sparse cut72 laws, including concentrated gap selection. Ordinary exact arithmetic; no full cut72 classification, Lean verification or unrestricted odd-cover lift.',controls=controls)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
