#!/usr/bin/env python3
"""Actual cut73 controls for full shape1222/01222/01222/11111.

Finite public support is excluded by the ordinary standalone-tree proof.
These two whole-public controls retain original owners and numerical labels.
"""
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


def templates(base):
    rows=('1222','01222','01222','11111');private={}
    for r,row in enumerate(rows):
        cursor=0
        for c,digit in enumerate(row):
            cost=int(digit);private[r,c]={(r+1,cursor+j) for j in range(cost)};cursor+=cost
    require(sum(map(len,private.values()))==26,'private occurrences26')
    public={(0,h) for h in range(7)};out=[]
    for thin in(False,True):
        fibres={child:public|private[child] for child in base.CHILDREN}
        if thin:
            fibres[1,0]={(0,6)};fibres[2,0]={(0,6)}
        out.append(dict(name='one_clean73_'+('thin_zero' if thin else'whole'),shape='/'.join(rows),
                        active=base.N,public_columns=(0,),public_leaves=(),private=private,
                        whole_private=set(),fibres=fibres,
                        source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},
                        cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1))))
    return out


def law_for(item):
    pts=[]
    for r in range(3):
        single=next(child for child,ys in item['private'].items() if child[0]==r and len(ys)==1)
        pts.append((*single,*next(iter(item['private'][single]))))
        doubles=[child for child,ys in sorted(item['private'].items()) if child[0]==r and len(ys)==2]
        reps=next(v for v in product(*(sorted(item['private'][child]) for child in doubles)) if len(set(v))==3)
        pts.extend((*child,*leaf) for child,leaf in zip(doubles,reps))
    pts.extend((3,c,*next(iter(item['private'][3,c]))) for c in range(5))
    pts.append((1,0,0,6))
    require(len(pts)==len({p[:2] for p in pts})==len({p[2:] for p in pts})==18,'eighteen distinct actual owners/leaves')
    require(set(pts)<=item['source'] and max(Counter(p[2] for p in pts).values())==5,'actual selection and column cap5')
    return {p:Q(1,18) for p in pts}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module,'_one_clean_base');net=load(args.network_module,'_one_clean_net')
    dinic=base.load_dinic(args.dinic_module);controls=[]
    for item in templates(base):
        law=law_for(item)
        rec=dict(name=item['name'],shape=item['shape'],active=item['active'],source_points=len(item['source']),
                 source=sorted(item['source']),public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*child,sorted(ys)] for child,ys in sorted(item['private'].items())],
                 selected_points=sorted(law),**base.literal_checks(item),network=net.network(item,base,dinic),law=base.check_law(item,law))
        require(Q(rec['law']['universal_gamma'])==Q(79,9),'uniform18 exact envelope')
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],cut=rec['network']['minimum_cut'],bound=rec['law']['universal_gamma'])),flush=True)
    args.output.write_text(json.dumps(dict(controls=controls,scope='Two actual whole-public cut73 sources of1222/01222/01222/11111, including coincident thin actual zero-owner fibres. Finite public excluded in the separate ordinary proof. Not the remaining48 full-k3 shapes, Lean verification or unrestricted odd covering.'),indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
