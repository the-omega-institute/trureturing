#!/usr/bin/env python3
"""Exact controls for the eight partial public4/private19 cut73 shapes.

The ordinary proof is separate. All laws retain actual numerical labels and
owners. These tests establish no Lean result or unrestricted odd covering.
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


ROWS=(('A','022/11111/11111/11111'),('B','111/11111/11111/11112'),
      ('C','112/11111/11111/11111'),('D','122/01111/11111/11111'),
      ('E','1111/0122/11111/11111'),('F','1111/1111/11111/11112'),
      ('G','1111/1112/11111/11111'),('H','1112/1111/11111/11111'))
UNIFORM18=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1))


def refresh(item):
    item['source']={(r,c,g,h) for(r,c),ys in item['fibres'].items() for g,h in ys}
    return item


def template(base,letter,shape,whole):
    rows=shape.split('/');active=tuple(map(len,rows));private={}
    for r,row in enumerate(rows):
        cursor=0
        for c,digit in enumerate(row):
            cost=int(digit);private[r,c]={(r+1,cursor+j) for j in range(cost)};cursor+=cost
    y=(2,6) if letter=='D' else(1,6)
    public={(0,h) for h in range(7 if whole else 3)}|{y}
    all_leaves=set(product(range(7),repeat=2))
    fibres={child:public|private[child] if child in private else set(all_leaves) for child in base.CHILDREN}
    require(sum(map(len,private.values()))==19,'private occurrence count19')
    require(all(not(public&ys) for ys in private.values()),'private candidates outside public')
    return refresh(dict(name='partial73k4_'+letter+('_whole' if whole else'_finite'),letter=letter,
                        shape=shape,active=active,public_columns=(0,) if whole else(),
                        public_leaves=(y,) if whole else tuple(sorted(public)),private=private,
                        public=public,whole_private=set(),fibres=fibres,kind='uniform18',cap=UNIFORM18))


def templates(base):
    out=[]
    for letter,shape in ROWS:
        for whole in(False,True):out.append(template(base,letter,shape,whole))
    for letter in('C','H'):
        shape=dict(ROWS)[letter]
        for whole in(False,True):
            for swap in(False,True):
                item=template(base,letter,shape,whole)
                d=len(shape.split('/')[0])-1
                for c in range(d):item['fibres'][0,c]=set(item['private'][0,c])
                zs=[next(iter(item['private'][0,c])) for c in range(d)]
                item['private'][0,d]=set(zs[:2]);item['fibres'][0,d]=set(zs[:2])
                item['name']+=('_public_swap' if swap else'_deficient')
                item['gap_double']=d
                if swap:
                    item['fibres'][0,0].add((0,0));item['swap_point']=(0,0,0,0)
                    item['kind']='public_swap'
                else:
                    item['kind']='puncture2';item['fixed_gap_children']=(0,d)
                out.append(refresh(item))
    require(len(out)==24,'sixteen base and eight dichotomy controls')
    return out


def active_selection_size(item,base,dinic):
    caps={};start=('active source',);finish=('active sink',)
    points={p for p in item['source'] if p[1]<item['active'][p[0]]}
    for r,a in enumerate(item['active']):
        for c in range(a):caps[start,('owner',r,c)]=1
    for p in sorted(points):caps[('owner',*p[:2]),('leaf',*p[2:])]=1
    for g,h in sorted({p[2:] for p in points}):caps[('leaf',g,h),('column',g)]=1
    for g in range(7):caps[('column',g),finish]=5
    value,flow,side=base.solve_network(caps,start,finish,100,dinic)
    return value


def fixed_pair_law(item,base,puncture):
    cs=item['fixed_gap_children'];removed=set().union(*(item['fibres'][0,c] for c in cs))
    require(len(cs)==len(set(cs))==2 and len(removed)==2,'entire actual gap-pair projection2')
    i,d=cs;zi=next(iter(item['fibres'][0,i]));zj=next(iter(removed-{zi}))
    eta=[(0,i,*zi),(0,d,*zj)]
    require(len({p[:2] for p in eta})==len({p[2:] for p in eta})==2,'eta original owners and leaves')
    psi=defaultdict(Q);tests=0
    for r in(1,2,3):
        for cc in combinations(range(base.N[r]),3):
            owners=defaultdict(list)
            for c in cc:
                for leaf in item['fibres'][r,c]:owners[leaf].append((r,c,*leaf))
            union=set(owners)|removed
            branches=[g for g in range(7) if sum(gg==g for gg,h in union)>=3][:3]
            require(len(branches)==3,'combined actual ternary tree')
            tree={(g,h) for g in branches for h in sorted(h for gg,h in union if gg==g)[:3]}
            remaining=tree-removed
            require(len(remaining)>=7 and remaining<=set(owners),'punctured points actual at other selected owners')
            for leaf in sorted(remaining):psi[min(owners[leaf])]+=Q(1,30*len(remaining))
            tests+=1
    require(tests==30 and sum(psi.values())==1,'all original full-root triples and one psi')
    law=defaultdict(Q,{p:Q(35,37)*v for p,v in psi.items()})
    for p in eta:law[p]+=Q(1,37)
    item['cap']=puncture.CAPS['puncture2']
    return dict(law),dict(fixed_gap_children=cs,entire_actual_projection=sorted(removed),
                          eta_points=eta,eta_weight='2/37',other_root_restriction_checks=tests)


def public_swap_law(item):
    d=item['gap_double'];points=[]
    for(r,c),ys in item['private'].items():
        if(r,c) in((0,0),(0,d)):continue
        require(len(ys)==1,'all non-double selected owners singleton')
        points.append((r,c,*next(iter(ys))))
    points += [item['swap_point'],(0,d,*next(iter(item['private'][0,0])))]
    require(len(points)==len({p[:2] for p in points})==len({p[2:] for p in points})==18,'public swap actual matching18')
    require(set(points)<=item['source'] and max(Counter(p[2] for p in points).values())<=5,'public swap support and column cap')
    return {p:Q(1,18) for p in points}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    parser.add_argument('--puncture-module',type=Path,default=Path(__file__).with_name('height_two_cut73_punctured_laws.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module,'_partial_k4_base');net=load(args.network_module,'_partial_k4_net')
    puncture=load(args.puncture_module,'_partial_k4_puncture');dinic=base.load_dinic(args.dinic_module);controls=[]
    for item in templates(base):
        literal=base.literal_checks(item);network=net.network(item,base,dinic)
        maximum=active_selection_size(item,base,dinic)
        if item['kind']=='puncture2':
            require(maximum==17,'deficient active support admits exactly17 matching points')
            law,selection=fixed_pair_law(item,base,puncture);bound=Q(328,37)
        elif item['kind']=='public_swap':
            require(maximum==18,'public swap repairs active matching')
            law=public_swap_law(item);selection=dict(selected_points=sorted(law),public_swap_point=item['swap_point']);bound=Q(79,9)
        else:
            require(maximum==18,'active actual matching18')
            restricted=dict(item,source={p for p in item['source'] if p[1]<item['active'][p[0]]})
            law=net.selected_law(restricted,base,dinic);selection=dict(selected_points=sorted(law));bound=Q(79,9)
        check=base.check_law(item,law)
        require(Q(check['universal_gamma'])==bound,'exact rational bound')
        rec=dict(name=item['name'],shape=item['shape'],active=item['active'],kind=item['kind'],
                 source_points=len(item['source']),source=sorted(item['source']),
                 public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*child,sorted(ys)] for child,ys in sorted(item['private'].items())],
                 active_selection_maximum=maximum,selection=selection,**literal,network=network,law=check)
        controls.append(rec)
        print(json.dumps(dict(name=item['name'],minimum_cut=network['minimum_cut'],active_selection=maximum,
                              gamma=check['gamma_envelope'],bound=check['universal_gamma'])),flush=True)
    args.output.write_text(json.dumps(dict(controls=controls,
        scope='Twenty-four actual cut73 controls: both public forms for all eight partial-k4 shapes, plus C/H deficient active matching and public-swap cases. Deficient controls use the entire actual gap projection and all original other-root children. Not exhaustive source enumeration, Lean verification or unrestricted odd covering.'),indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
