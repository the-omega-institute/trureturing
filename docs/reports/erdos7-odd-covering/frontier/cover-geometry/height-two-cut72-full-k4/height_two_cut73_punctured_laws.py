#!/usr/bin/env python3
"""Actual cut73 single-active punctured laws and one partial0555 shape.

All mixture components use original actual owners and numerical labels.
These controls do not settle the remaining cut73 families or odd covering.
"""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from importlib.util import module_from_spec,spec_from_file_location
from itertools import combinations,product
from pathlib import Path
import argparse,json


def require(ok,message):
    if not ok:raise ValueError(message)


def load(path,name):
    spec=spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'support module')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod


CAPS={
 'puncture1':tuple(map(Q,('1','1/3','3/8','1/5','1/8','1/8','3/40','1/24','1/40'))),
 'puncture2':tuple(map(Q,('1','35/111','17/37','7/37','5/37','6/37','3/37','5/111','1/37'))),
 'five_eta':tuple(map(Q,('1','6/23','11/23','18/115','3/23','4/23','9/115','1/23','1/23'))),
 'four_in_H':tuple(map(Q,('1','2/7','3/7','6/35','1/7','1/7','3/35','1/21','1/28'))),
 'uniform25':tuple(Q(x,25) for x in(25,10,10,2,5,2,1,1,1))}
BOUNDS=dict(puncture1=Q(33,4),puncture2=Q(328,37),five_eta=Q(206,23),four_in_H=Q(249,28),uniform25=Q(41,5))


def templates(base):
    out=[];all_leaves=set(product(range(7),repeat=2))
    configurations=[
      ('gap_repeated',0,[(0,0),(0,0),(0,1)]),
      ('gap_distinct',0,[(0,0),(0,1),(0,2)]),
      ('full_three_repeated',3,[(0,0),(0,0),(0,0),(1,0),(2,0)]),
      ('full_two_repeated',3,[(0,0),(0,0),(1,0),(2,0),(3,0)]),
      ('full_M1',3,[(g,0) for g in range(5)]),
      ('full_M2',3,[(0,0),(0,1),(1,0),(1,1),(2,0)]),
      ('full_M3',3,[(0,0),(0,1),(0,2),(1,0),(2,0)]),
      ('full_M4',3,[(0,0),(0,1),(0,2),(0,3),(1,0)]),
      ('full_M5',3,[(0,c) for c in range(5)])]
    for name,r,leaves in configurations:
        private={(r,c):{leaf} for c,leaf in enumerate(leaves)}
        if r==0:private[0,3]={(0,3),(0,4)}
        active=tuple(base.N[j] if j==r else 0 for j in range(4))
        fibres={child:set(private[child]) if child in private else set(all_leaves) for child in base.CHILDREN}
        out.append(dict(name=name,distinguished_root=r,active=active,public_columns=(),public_leaves=(),
                        private=private,whole_private=set(),fibres=fibres,
                        source={(rr,c,g,h) for(rr,c),ys in fibres.items() for g,h in ys}))
    private={(1,c):{(0,c)} for c in range(5)};private[1,4].add((0,5))
    private.update({(2,c):{(1,c),(2,c)} for c in range(5)})
    private.update({(3,c):{(2,c),(3,c)} for c in range(5)})
    fibres={child:set(private[child]) if child in private else set(all_leaves) for child in base.CHILDREN}
    out.append(dict(name='0555_11112_22222_22222',active=(0,5,5,5),public_columns=(),public_leaves=(),
                    private=private,whole_private=set(),fibres=fibres,
                    source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys}))
    return out


def punctured_law(item,base):
    if item['name'].startswith('0555'):
        points=[(1,c,0,c) for c in range(5)]
        points +=[(r,c,g,h) for(r,c),ys in item['private'].items() if r in(2,3) for g,h in ys]
        require(len(points)==len(set(points))==25,'actual uniform25 selection')
        return {p:Q(1,25) for p in points},'uniform25',dict(selected_points=sorted(points))
    r=item['distinguished_root']
    singleton=[(r,c,*next(iter(item['fibres'][r,c]))) for c in range(base.N[r]) if len(item['fibres'][r,c])==1]
    repeated=next(((p,q) for p,q in combinations(singleton,2) if p[2:]==q[2:]),None)
    outside_H=None
    if r==0:
        fixed=list(repeated) if repeated else singleton[:2]
        mode='puncture1' if repeated else'puncture2'
    elif repeated:
        third=next(p for p in singleton if p[:2] not in{repeated[0][:2],repeated[1][:2]})
        fixed=[*repeated,third]
        mode='puncture1' if len({p[2:] for p in fixed})==1 else'puncture2'
    else:
        counts=Counter(p[2] for p in singleton);H=max(counts,key=counts.get);M=counts[H]
        fixed=singleton[:3] if M<=2 else[p for p in singleton if p[2]==H][:3]
        if M>=3:outside_H=H
        mode='four_in_H' if M>=4 else'five_eta'
    removed={p[2:] for p in fixed}
    require(len(fixed)==(2 if r==0 else 3),'fixed legal distinguished restriction')
    if mode=='puncture1':eta=[];t=Q(0)
    elif mode=='puncture2':
        eta=[next(p for p in fixed if p[2:]==leaf) for leaf in sorted(removed)]
        require(len(eta)==2,'two actual eta leaves');t=Q(2,37)
    elif mode=='five_eta':eta=singleton;t=Q(5,23)
    else:eta=[p for p in singleton if p[2]==outside_H][:4];t=Q(1,7)
    psi=defaultdict(Q);tests=0
    for s in range(4):
        if s==r:continue
        choices=list(combinations(range(base.N[s]),2 if s==0 else 3))
        for cs in choices:
            owners=defaultdict(list)
            for c in cs:
                for leaf in item['fibres'][s,c]:owners[leaf].append((s,c,*leaf))
            if outside_H is None:
                union=set(owners)|removed
                branches=[g for g in range(7) if sum(gg==g for gg,h in union)>=3][:3]
                require(len(branches)==3,'combined actual ternary tree')
                tree={(g,h) for g in branches for h in sorted(h for gg,h in union if gg==g)[:3]}
                remaining=tree-removed
                require(len(remaining)>=9-len(removed),'puncture retains required leaves')
            else:
                branches=[g for g in range(7) if g!=outside_H and sum(gg==g for gg,h in owners)>=3][:2]
                require(len(branches)==2,'two actual branches outside H')
                remaining={(g,h) for g in branches for h in sorted(h for gg,h in owners if gg==g)[:3]}
            require(remaining<=set(owners),'all retained leaves have actual other-root owners')
            for leaf in sorted(remaining):psi[min(owners[leaf])]+=Q(1,3*len(choices)*len(remaining))
            tests+=1
    require(sum(psi.values())==1 and all(p[0]!=r for p in psi),'one normalized other-root law')
    if outside_H is not None:require(all(p[2]!=outside_H for p in psi),'psi support avoids H')
    law=defaultdict(Q,{p:(1-t)*v for p,v in psi.items()})
    for p in eta:law[p]+=t/len(eta)
    return {p:v for p,v in law.items() if v},mode,dict(fixed_actual_points=fixed,eta_points=eta,
        eta_weight=str(t),psi_outside_column=outside_H,other_root_restriction_checks=tests)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module,'_literal_caps');net=load(args.network_module,'_network73')
    dinic=base.load_dinic(args.dinic_module);controls=[]
    for item in templates(base):
        law,mode,selection=punctured_law(item,base);item['cap']=CAPS[mode]
        rec=dict(name=item['name'],active=item['active'],source_points=len(item['source']),source=sorted(item['source']),
                 private=[[*child,sorted(ys)] for child,ys in sorted(item['private'].items())],
                 mode=mode,selection=selection,**base.literal_checks(item),
                 network=net.network(item,base,dinic),law=base.check_law(item,law))
        require(Q(rec['law']['universal_gamma'])==BOUNDS[mode],'exact rational cap envelope')
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],minimum_cut=rec['network']['minimum_cut'],
                              gamma=rec['law']['gamma_envelope'],bound=rec['law']['universal_gamma'])),flush=True)
    require(len(controls)==10,'all single-active branches and one0555 shape')
    out=dict(controls=controls,scope='Ten actual cut73 controls: both4000 singleton-pair cases; full0005 triple-repeat, pair-repeat and maximum column counts1 through5; and the single0555 shape11112/22222/22222. All sources retain original owners and have matching actual flow/cut73. Exact tests, not exhaustive source search, complete cut73 classification, Lean verification or unrestricted odd covering.')
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
