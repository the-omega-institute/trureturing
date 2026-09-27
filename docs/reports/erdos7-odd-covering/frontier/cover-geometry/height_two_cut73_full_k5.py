#!/usr/bin/env python3
"""Actual cut73 controls for the six surviving full public5/private19 shapes.

These controls accompany a universal tree/owner proof. They do not prove
cut-profile exhaustiveness, Lean verification or unrestricted odd covering.
"""
from collections import Counter
from fractions import Fraction as Q
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import argparse,json


def require(ok,message):
    if not ok:raise ValueError(message)


def load(path):
    spec=spec_from_file_location('_cut73_k5_support',path)
    require(spec is not None and spec.loader is not None,'support module')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod


SHAPES=(
    '0111/11111/11111/11112',
    '0112/11111/11111/11111',
    '1111/01111/11111/11112',
    '1111/01112/11111/11111',
    '1111/11111/11111/11111',
    '1112/01111/11111/11111')


def templates(base):
    result=[]
    for index,shape in enumerate(SHAPES,1):
        rows=shape.split('/')
        zero_full=next((r for r in range(1,4) if '0' in rows[r]),None)
        extra=((1,6),(zero_full+1,6)) if zero_full is not None else((1,5),(1,6))
        if index==5:extra=((1,6),(2,6))
        public={(0,h) for h in range(7)}|set(extra)
        private={}
        for r,row in enumerate(rows):
            cursor=0
            for c,digit in enumerate(row):
                cost=int(digit)
                private[r,c]={(r+1,cursor+j) for j in range(cost)}
                cursor+=cost
        if index==2:private[0,3]={(1,2),(2,5)}
        require(sum(map(len,private.values()))==19,'nineteen private finite occurrences')
        require(all(not(public&ps) for ps in private.values()),'private/public candidate disjointness in controls')
        fibres={child:public|private[child] for child in base.CHILDREN}
        result.append(dict(name='full73k5_%02d'%index,shape=shape,active=base.N,
                           public_columns=(0,),public_leaves=extra,private=private,whole_private=set(),fibres=fibres,
                           source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},
                           cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1))))
    # The zero owner's only actual point lies outside an initially chosen
    # five-leaf G branch. Record a legal branch replacement containing it.
    thin=dict(result[0]);thin['name']='full73k5_zero_branch_repair'
    thin['fibres']=dict(thin['fibres']);thin['fibres'][0,0]={(0,6)}
    thin['source']={(r,c,g,h) for(r,c),ys in thin['fibres'].items() for g,h in ys}
    original={(0,h) for h in range(5)}|{(1,h) for h in(0,1,2,5,6)}
    original|={(g,h) for g in(2,3,4) for h in range(5)}
    repaired=(original-{(0,4)})|{(0,6)}
    projection={p[2:] for p in thin['source']}
    require((0,6) not in original and (0,6) in repaired,'actual zero point enters repaired tree')
    for tree in(original,repaired):
        require(len(tree)==25 and tree<=projection and sorted(Counter(g for g,h in tree).values())==[5]*5,
                'both original and repaired trees are actual five-trees')
    thin['zero_branch_repair']=dict(zero_owner=[0,0],actual_leaf=[0,6],
                                    original_tree=sorted(original),repaired_tree=sorted(repaired))
    result.append(thin)
    return result


def network(item,base,dinic):
    caps={};start=('source',);finish=('sink',)
    def add(u,v,cap):
        require((u,v) not in caps,'unique network arc');caps[u,v]=cap
    for r,n in enumerate(base.N):
        add(start,('r',r),21)
        for c in range(n):
            add(('r',r),('c',r,c),7)
            for g in range(7):
                add(('c',r,c),('pg',r,c,g),6)
                for h in range(7):add(('pg',r,c,g),('ph',r,c,g,h),2)
    for g in range(7):
        add(('cg',g),finish,21)
        for h in range(7):add(('ch',g,h),('cg',g),7)
    for p in sorted(item['source']):add(('ph',*p),('ch',*p[2:]),126)
    value,flow,side=base.solve_network(caps,start,finish,1000,dinic)
    require(value==73,item['name']+': actual maxflow73, got '+str(value))
    mincut=[(u,v,c) for (u,v),c in caps.items() if u in side and v not in side]
    require(sum(c for u,v,c in mincut)==73,'computed mincut73')
    explicit={start}
    for g in item['public_columns']:
        explicit.add(('cg',g));explicit.update(('ch',g,h) for h in range(7))
    explicit.update(('ch',g,h) for g,h in item['public_leaves'])
    for r,a in enumerate(item['active']):
        if a:explicit.add(('r',r))
        for c in range(a):
            explicit.add(('c',r,c))
            whole_cols={g for g,h in item['private'][r,c]} if (r,c) in item['whole_private'] else set()
            require(len(whole_cols)<=1,'private whole prefix is one column')
            for g in range(7):
                if g in whole_cols:continue
                explicit.add(('pg',r,c,g))
                explicit.update(('ph',r,c,g,h) for h in range(7) if(g,h) not in item['private'][r,c])
    cut=[(u,v,c) for (u,v),c in caps.items() if u in explicit and v not in explicit]
    require(not any(u[0]=='ph' for u,v,c in cut),'no actual bridge crosses prescribed cut')
    require(sum(c for u,v,c in cut)==73,'prescribed cut73')
    require(all(flow[u,v]==c for u,v,c in cut),'forward prescribed cut saturation')
    require(all(flow[u,v]==0 for u,v in caps if u not in explicit and v in explicit),'zero backward prescribed cut flow')
    atoms=[[*u[1:],f] for (u,v),f in flow.items() if u[0]=='ph' and v[0]=='ch' and f]
    return dict(maximum_flow=value,minimum_cut=73,edge_count=len(caps),
                prescribed_cut=[[list(u),list(v),c] for u,v,c in cut],
                computed_minimum_cut=[[list(u),list(v),c] for u,v,c in mincut],actual_flow_atoms=atoms)

def selected_law(item,base,dinic):
    caps={};start=('selector source',);finish=('selector sink',)
    for child in sorted(base.CHILDREN):caps[start,('child',*child)]=1
    for p in sorted(item['source']):caps[('child',*p[:2]),('leaf',*p[2:])]=1
    for g,h in sorted({p[2:] for p in item['source']}):caps[('leaf',g,h),('column',g)]=1
    for g in range(7):caps[('column',g),finish]=5
    value,flow,side=base.solve_network(caps,start,finish,18,dinic)
    require(value==18,'actual owner/leaf/column selector18')
    pts=[(*u[1:],*v[1:]) for(u,v),f in flow.items() if u[0]=='child' and v[0]=='leaf' and f]
    require(len(pts)==len(set(pts))==len({p[:2] for p in pts})==len({p[2:] for p in pts})==18,
            'eighteen distinct actual owners and labels')
    require(set(pts)<=item['source'],'selected points actual at their owners')
    require(max(Counter(p[2] for p in pts).values())<=5,'selected column cap5')
    return {p:Q(1,18) for p in pts}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module);dinic=base.load_dinic(args.dinic_module)
    controls=[]
    for item in templates(base):
        literal=base.literal_checks(item);net=network(item,base,dinic);law=selected_law(item,base,dinic)
        rec=dict(name=item['name'],shape=item['shape'],source_points=len(item['source']),source=sorted(item['source']),
                 public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*child,sorted(ys)] for child,ys in sorted(item['private'].items())],
                 selected_points=sorted(law),**literal,network=net,law=base.check_law(item,law))
        if 'zero_branch_repair' in item:rec['zero_branch_repair']=item['zero_branch_repair']
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],minimum_cut=net['minimum_cut'],
                              gamma=rec['law']['gamma_envelope'],universal_gamma=rec['law']['universal_gamma'])),flush=True)
    require(len(controls)==7 and len({r['shape'] for r in controls})==6,'six shapes and actual zero-branch repair control')
    out=dict(scope='Seven actual full cut73/public5/private19 source controls for all six surviving shapes and one zero-branch repair, all with one public whole column and two public leaves. Each has matching actual maxflow and prescribed cut73, a checked actual eighteen-owner/eighteen-leaf selection with column cap5, and one common law. Not exhaustive source search, Lean verification, or unrestricted odd covering.',controls=controls)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
