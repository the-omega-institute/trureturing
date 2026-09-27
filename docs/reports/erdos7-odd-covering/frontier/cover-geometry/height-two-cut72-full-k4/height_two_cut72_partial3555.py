#!/usr/bin/env python3
"""Actual controls for every partial3555/k3/private22 cut72 shape."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import argparse
import importlib.util
import json


def require(ok,message):
    if not ok:raise ValueError(message)


def load(path):
    spec=importlib.util.spec_from_file_location('_cut72_sparse_support',path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


ROWS={'033':((),(0,1,2),(2,3,4)),
      '122':((0,),(1,2),(2,3)),
      '123':((0,),(1,2),(3,4,5)),
      '222':((0,1),(1,2),(2,3)),
      '11111':((0,),(1,),(2,),(3,),(4,)),
      '01222':((),(0,),(1,2),(2,3),(3,4)),
      '11112':((0,),(1,),(2,),(3,),(4,5)),
      '11113':((0,),(1,),(2,),(3,),(4,5,6)),
      '11122':((0,),(1,),(2,),(3,4),(4,5))}
SHAPES=('033/11111/11111/11112','122/01222/11111/11111',
        '122/11111/11111/11113','122/11111/11111/11122',
        '122/11111/11112/11112','123/11111/11111/11112',
        '222/11111/11111/11112')


def templates(base):
    out=[]
    for shape in SHAPES:
        for whole in ((False,True) if '3' in shape else (False,)):
            private={};wholechildren=set();rows=shape.split('/')
            for r,row in enumerate(rows):
                for c,hs in enumerate(ROWS[row]):
                    require(len(hs)==int(row[c]),'exact sorted candidate costs')
                    g=4 if r==0 else r
                    private[r,c]={(g,h) for h in (range(7) if whole and len(hs)==3 else hs)}
                    if whole and len(hs)==3:wholechildren.add((r,c))
            fibres={child:({(0,h) for h in range(7)}|private[child]) if child in private else set(base.ALL)
                    for child in base.CHILDREN}
            full=[]
            for r,row in enumerate(rows[1:],1):
                if row in ('11111','11112'):full.extend((r,c,r,c) for c in range(5))
                elif row=='01222':full.extend((r,c,r,c-1) for c in range(1,5))
                elif row in ('11113','11122'):full.extend((r,c,r,c) for c in range(4))
                else:raise ValueError('unknown full selector')
            uniform=rows[0]=='222';nfull=len(full)
            if uniform:
                caps=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1));gap=[(0,c,4,c) for c in range(3)]
            else:
                if rows[0]=='033':gap=[(0,1,4,h) for h in range(3)]
                else:gap=[(0,0,4,0),(0,1,4,1),(0,1,4,2)]
                original=(Q(1),Q(18,55),Q(13,55),Q(6,55),Q(13,55),Q(13,165),Q(3,55),Q(13,275),Q(13,275))
                factor=Q(275,65+13*nfull+15)
                caps=(Q(1),)+tuple(v*factor for v in original[1:])
            item=dict(name=shape+('_whole' if whole else '_finite'),shape=shape,active=(3,5,5,5),
                      public_columns=(0,),public_leaves=(),private=private,whole_private=wholechildren,
                      fibres=fibres,source={(r,c,g,h) for (r,c),ys in fibres.items() for g,h in ys},
                      cap=caps,full_private=full,gap_private=gap,uniform=uniform)
            out.append(item)
    require(len(out)==10,'seven finite controls and three whole-prefix controls')
    return out


def network(item,base,dinic):
    start=('source',);finish=('sink',);caps={}
    for r,n in enumerate(base.N):
        caps[start,('r',r)]=21
        for c in range(n):
            caps[('r',r),('c',r,c)]=7
            for g in range(7):
                caps[('c',r,c),('pg',r,c,g)]=6
                for h in range(7):caps[('pg',r,c,g),('ph',r,c,g,h)]=2
    for g in range(7):
        caps[('cg',g),finish]=21
        for h in range(7):caps[('ch',g,h),('cg',g)]=7
    for p in item['source']:caps[('ph',*p),('ch',*p[2:])]=126
    value,flow,side=base.solve_network(caps,start,finish,1000,dinic)
    require(value==72,'matching maxflow72')
    require(sum(c for(u,v),c in caps.items() if u in side and v not in side)==72,'computed mincut72')
    explicit={start,('cg',0)}|{('ch',0,h) for h in range(7)}
    for r,a in enumerate(item['active']):
        explicit.add(('r',r))
        for c in range(a):
            explicit.add(('c',r,c))
            for g in range(7):
                if (r,c) in item['whole_private'] and g==(4 if r==0 else r):continue
                explicit.add(('pg',r,c,g))
                explicit.update(('ph',r,c,g,h) for h in range(7) if (g,h) not in item['private'][r,c])
    cut=[(u,v,c) for(u,v),c in caps.items() if u in explicit and v not in explicit]
    require(sum(c for u,v,c in cut)==72 and not any(u[0]=='ph' for u,v,c in cut),'explicit bridge-free cut72')
    require(all(flow[u,v]==c for u,v,c in cut),'forward saturation')
    require(all(flow[u,v]==0 for u,v in caps if u not in explicit and v in explicit),'zero backward cut flow')
    return dict(maximum_flow=72,minimum_cut=72,edge_count=len(caps),
                actual_flow_atoms=[[*u[1:],f] for(u,v),f in flow.items() if u[0]=='ph' and v[0]=='ch' and f],
                prescribed_cut=[[list(u),list(v),c] for u,v,c in cut])


def weighted_checks():
    A=(15,25,25,25);B=(15,39,39,39);slacks=[]
    for n in range(5):
        for aa in combinations(range(4),n):
            top=sum(A[r] for r in range(4) if r not in aa)
            if n<=1:slacks.append(Q(top-65))
            else:
                total=sum(B[r] for r in aa)
                slacks.append(top+Q(total,2)-65)
                slacks.extend(Q(top+total-B[j]-65) for j in aa)
    require(len(slacks)==44 and min(slacks)>=0,'all44 existing weighted cuts')
    return dict(count=44,min_slack=str(min(slacks)))


def construct(item,base,dinic):
    points=item['full_private']+item['gap_private']
    require(len(points)==len(set(points)) and set(points)<=item['source'],'selected points actual')
    require(len({p[:2] for p in item['full_private']})==len(item['full_private']),'full private child distinction')
    require(len({p[2:] for p in points})==len(points),'global private leaf distinction')
    if item['uniform']:
        require(len(points)==len({p[:2] for p in points})==18,'eighteen different private owners')
        return {p:Q(1,18) for p in points},dict(public_couplings=0,private_count=18)
    law=defaultdict(Q);runs=0
    restrictions=tuple(combinations(range(5),3))
    for fullchoices in product(restrictions,repeat=3):
        choices=((0,1),)+fullchoices;caps={};owners={};start=('source',);finish=('sink',)
        for r,cc in enumerate(choices):
            caps[start,('root',r)]=45 if r==0 else 75
            for h in range(7):
                caps[('root',r),('private_leaf',r,h)]=15 if r==0 else 39
                actual=[(r,c,0,h) for c in cc if (0,h) in item['fibres'][r,c]]
                if actual:
                    owners[r,h]=min(actual);caps[('private_leaf',r,h),('common_leaf',h)]=195
        for h in range(7):caps[('common_leaf',h),finish]=65
        for r,s in combinations(range(4),2):
            require(len({h for rr,h in owners if rr in(r,s)})>=3,'actual G pair premise')
        value,flow,side=base.solve_network(caps,start,finish,195,dinic)
        require(value==195,'weighted actual public mass65')
        for(u,v),f in flow.items():
            if u[0]=='private_leaf' and v[0]=='common_leaf' and f:law[owners[u[1:]]]+=Q(f,825000)
        runs+=1
    require(runs==1000 and sum(law.values())==Q(65,275),'all1000 joint restrictions')
    for p in item['full_private']:law[p]+=Q(13,275)
    for p in item['gap_private']:law[p]+=Q(5,275)
    mass=sum(law.values());require(mass in(Q(1),Q(262,275)),'fifteen orfourteen full private total')
    return {p:w/mass for p,w in law.items()},dict(public_couplings=runs,full_private_count=len(item['full_private']),
                                                gap_private_count=3,pre_normalization_mass=str(mass))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module);dinic=base.load_dinic(args.dinic_module)
    controls=[]
    for item in templates(base):
        law,cert=construct(item,base,dinic)
        rec=dict(name=item['name'],shape=item['shape'],source_points=len(item['source']),source=sorted(item['source']),
                 whole_private_children=sorted(item['whole_private']),full_private_selection=item['full_private'],
                 gap_private_selection=item['gap_private'],**base.literal_checks(item),
                 network=network(item,base,dinic),construction=cert,law=base.check_law(item,law))
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],mincut=72,
                              gamma=rec['law']['gamma_envelope'],universal_gamma=rec['law']['universal_gamma'])))
    out=dict(scope='Actual controls for all seven partial3555/k3/private22 cut72 shapes, plus whole-prefix variants. Ordinary exact arithmetic; no Lean verification or unrestricted arithmetic lift.',weighted_cut_checks=weighted_checks(),controls=controls)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
