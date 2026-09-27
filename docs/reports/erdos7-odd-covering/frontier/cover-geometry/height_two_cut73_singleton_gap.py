#!/usr/bin/env python3
"""Actual cut73 controls for seven singleton-gap/cost-three shapes."""
from collections import Counter
from fractions import Fraction as Q
from importlib.util import module_from_spec,spec_from_file_location
from itertools import product
from pathlib import Path
import argparse,json


def require(ok,message):
    if not ok:raise ValueError(message)


def load(path,name):
    spec=spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'support module')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod


SHAPES=('1223/01222/11111/11112','1223/01223/11111/11111',
        '1233/01222/11111/11111','1233/11111/11111/11113',
        '1233/11111/11111/11122','1233/11111/11112/11112',
        '1333/11111/11111/11112')


def templates(base):
    out=[]
    for index,shape in enumerate(SHAPES,1):
        baseline={}
        for r,row in enumerate(shape.split('/')):
            cursor=0
            for c,digit in enumerate(row):
                cost=int(digit);baseline[r,c]={(r+1,(cursor+j)%7) for j in range(cost)};cursor+=cost
        modes=['finite_private','thin_whole_private','finite_public_whole_private']
        if index in(4,5):modes.append('collapsed_gap_full_extension')
        if index==7:modes.append('singleton_inside_anchor')
        for mode in modes:
            private={ch:set(ys) for ch,ys in baseline.items()};actual={ch:set(ys) for ch,ys in baseline.items()};whole=set()
            if mode in('thin_whole_private','finite_public_whole_private'):
                ch=next(ch for ch,ys in sorted(private.items()) if ch[0]==0 and len(ys)==3)
                col=5 if mode=='finite_public_whole_private' else 1
                private[ch]={(col,h) for h in range(7)};whole.add(ch)
                if mode=='finite_public_whole_private':
                    actual[ch]=set(private[ch])
                    if index in(3,4,5,6):
                        other=next(cc for cc,ys in sorted(actual.items()) if cc[0]==0 and cc!=ch and len(ys)==3)
                        actual[other]={(1,h) for h in(3,4,5)};private[other]=set(actual[other])
            elif mode=='collapsed_gap_full_extension':
                for c in(2,3):actual[0,c]={(1,h) for h in(0,1,2)};private[0,c]=set(actual[0,c])
                if index==4:
                    actual[3,4]={(1,3),(1,4),(4,4)};private[3,4]=set(actual[3,4])
                else:
                    actual[3,3]={(4,3),(1,3)};private[3,3]=set(actual[3,3])
                    actual[3,4]={(4,4),(1,4)};private[3,4]=set(actual[3,4])
            elif mode=='singleton_inside_anchor':
                actual[0,0]={(2,0)};private[0,0]=set(actual[0,0])
            public={(0,h) for h in range(3 if mode=='finite_public_whole_private' else 7)}
            fibres={ch:public|actual[ch] for ch in base.CHILDREN}
            if mode=='singleton_inside_anchor':fibres[0,0]=set(actual[0,0])
            require(sum(3 if ch in whole else len(ys) for ch,ys in private.items())==26,'private weighted cost26')
            out.append(dict(name='singleton_gap73_%d_%s'%(index,mode),shape=shape,index=index,mode=mode,
                            active=base.N,public=public,public_columns=() if len(public)==3 else(0,),
                            public_leaves=tuple(sorted(public)) if len(public)==3 else(),private=private,
                            actual_private=actual,whole_private=whole,fibres=fibres,
                            source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},
                            cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1))))
    require(len(out)==24,'twenty-four controls')
    return out


def law_for(item):
    private=item['actual_private'];index=item['index'];mode=item['mode'];rows=item['shape'].split('/');pts=[]
    def one(ch):pts.append((*ch,*next(iter(private[ch]))))
    def reps(children,column=None):
        used={p[2:] for p in pts}
        sets=[{y for y in private[ch]-used if column is None or y[0]==column} for ch in children]
        values=next(v for v in product(*(sorted(ys) for ys in sets)) if len(set(v))==len(v))
        pts.extend((*ch,*leaf) for ch,leaf in zip(children,values))
    if mode=='singleton_inside_anchor':reps([(0,c) for c in(1,2,3)])
    else:
        one((0,0))
        gap_children=([1,2,3] if index in(2,4,5) else [1,2])
        if mode=='collapsed_gap_full_extension':gap_children=[1,2]
        reps([(0,c) for c in gap_children])
    if index in(1,2,3):
        pts.append((1,0,0,0));one((1,1))
        reps([(1,c) for c,digit in enumerate(rows[1]) if digit=='2'])
        roots=(2,3)
    else:roots=(1,2,3)
    for r in roots:
        for c,digit in enumerate(rows[r]):
            if digit=='1':one((r,c))
        if rows[r]=='11112':reps([(r,4)],r+1)
        elif rows[r]=='11122':
            reps([(r,3)],r+1)
            if mode=='collapsed_gap_full_extension':reps([(r,4)],r+1)
        elif rows[r]=='11113' and mode=='collapsed_gap_full_extension':reps([(r,4)],r+1)
    require(len(pts)==len({p[:2] for p in pts})==len({p[2:] for p in pts})==18,'eighteen distinct original owners and labels')
    require(set(pts)<=item['source'] and max(Counter(p[2] for p in pts).values())<=5,'actual common law and column cap5')
    return {p:Q(1,18) for p in pts}


def lower_cut_network(item,base,dinic):
    """Measure the two boundary sources without relabeling their mincut as73."""
    caps={};start=('source',);finish=('sink',)
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
    cut=[(u,v,c) for(u,v),c in caps.items() if u in side and v not in side]
    require(value==72 and sum(c for u,v,c in cut)==72,'boundary source has actual mincut72')
    require(all(flow[u,v]==c for u,v,c in cut),'boundary computed cut saturated')
    return dict(maximum_flow=value,minimum_cut=72,displayed_profile_cut_cost=73,
                computed_minimum_cut=[[list(u),list(v),c] for u,v,c in cut],
                actual_flow_atoms=[[*u[1:],f] for(u,v),f in flow.items() if u[0]=='ph' and v[0]=='ch' and f])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module,'_singleton_gap_base');net=load(args.network_module,'_singleton_gap_net')
    dinic=base.load_dinic(args.dinic_module);controls=[];boundary=[]
    for item in templates(base):
        law=law_for(item)
        rec=dict(name=item['name'],shape=item['shape'],active=item['active'],mode=item['mode'],
                 source_points=len(item['source']),source=sorted(item['source']),
                 public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*ch,sorted(ys)] for ch,ys in sorted(item['private'].items())],
                 whole_private_children=sorted(item['whole_private']),selected_points=sorted(law),
                 **base.literal_checks(item),
                 network=lower_cut_network(item,base,dinic) if item['mode']=='collapsed_gap_full_extension' else net.network(item,base,dinic),
                 law=base.check_law(item,law))
        require(Q(rec['law']['universal_gamma'])==Q(79,9),'uniform18 exact envelope')
        if item['mode']=='thin_whole_private':
            ch=next(iter(item['whole_private']))
            require(len(item['private'][ch])==7 and len(item['fibres'][ch]-item['public'])==3,'whole prefix only3 actual leaves')
        if item['mode']=='collapsed_gap_full_extension':
            gap=set().union(*(item['fibres'][0,c]-item['public'] for c in range(4)))
            require(gap=={(1,h) for h in(0,1,2)},'entire actual gap private collapse to3')
            require(sum(p[0]==0 for p in law)==3 and sum(p[0]==3 for p in law)==5,'joint extension at original exceptional root')
            global_K={h for r,c,g,h in item['source'] if g==1}
            require(len(global_K)==5,'exceptional root also fills the gap column to5')
        if item['mode']=='singleton_inside_anchor':
            require(item['fibres'][0,0]=={(2,0)} and all(p[:2]!=(0,0) for p in law),'actual singleton is in anchor and omitted')
        (boundary if item['mode']=='collapsed_gap_full_extension' else controls).append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],cut=rec['network']['minimum_cut'],bound=rec['law']['universal_gamma'])),flush=True)
    require(len(controls)==22 and len(boundary)==2,'twenty-two actual cut73 and two separate cut72 boundary regressions')
    args.output.write_text(json.dumps(dict(controls=controls,lower_cut_boundary_controls=boundary,
        scope='Twenty-two actual cut73 controls for seven singleton-gap shapes, plus TWO SEPARATE actual-cut72 boundary sources with a displayed nonminimal profile cut73. The latter test a collapsed gap rescued by an exceptional root that fills two columns jointly; they are not counted as cut73 controls. Other cases include finite/whole prefixes, finite-public actual standalone and singleton actual inside an anchor. Not the remaining full-k3 shapes, Lean verification or unrestricted odd covering.'),indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
