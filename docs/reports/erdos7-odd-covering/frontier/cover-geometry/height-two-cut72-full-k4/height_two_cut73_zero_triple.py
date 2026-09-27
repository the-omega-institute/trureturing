#!/usr/bin/env python3
"""Actual finite/whole-prefix cut73 controls for five zero/triple-owner shapes."""
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


SHAPES=('0333/01222/11111/11111','0333/11111/11111/11113',
        '0333/11111/11111/11122','0333/11111/11112/11112',
        '1222/00333/11111/11111')


def templates(base):
    out=[]
    for index,shape in enumerate(SHAPES,1):
        rows=shape.split('/');baseline={}
        for r,row in enumerate(rows):
            cursor=0
            for c,digit in enumerate(row):
                cost=int(digit);baseline[r,c]={(r+1,(cursor+j)%7) for j in range(cost)};cursor+=cost
        r=1 if index==5 else 0
        triples=[child for child,ys in sorted(baseline.items()) if child[0]==r and len(ys)==3]
        require(len(triples)==3,'three selected cost-three owners')
        for mode in('finite_private','thin_whole_private','finite_public_split_whole'):
            public={(0,h) for h in range(3 if mode=='finite_public_split_whole' else 7)}
            private={child:set(ys) for child,ys in baseline.items()};whole=set()
            actual_private={child:set(ys) for child,ys in baseline.items()}
            if mode=='thin_whole_private':
                child=triples[0];private[child]={(r+1,h) for h in range(7)};whole.add(child)
            elif mode=='finite_public_split_whole':
                for child,col in zip(triples[:2],(r+1,5)):
                    private[child]={(col,h) for h in range(7)};whole.add(child)
                    actual_private[child]=set(private[child])
            require(sum(3 if child in whole else len(ys) for child,ys in private.items())==26,'private weighted cut26')
            fibres={child:public|actual_private[child] for child in base.CHILDREN}
            item=dict(name='zero_triple73_%d_%s'%(index,mode),index=index,shape=shape,mode=mode,
                      active=base.N,public=public,public_columns=() if len(public)==3 else(0,),
                      public_leaves=tuple(sorted(public)) if len(public)==3 else(),private=private,
                      whole_private=whole,actual_private=actual_private,fibres=fibres,triples=triples,
                      source={(rr,c,g,h) for(rr,c),ys in fibres.items() for g,h in ys},
                      cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1)))
            out.append(item)
    return out


def law_for(item):
    pts=[];private=item['actual_private'];index=item['index'];rows=item['shape'].split('/')
    triples=item['triples'];reps=next(v for v in product(*(sorted(private[ch]) for ch in triples)) if len(set(v))==3)
    pts.extend((*ch,*leaf) for ch,leaf in zip(triples,reps))
    if index in(1,5):
        r=1 if index==1 else 0
        one=next(ch for ch,ys in private.items() if ch[0]==r and len(ys)==1)
        pts.append((*one,*next(iter(private[one]))))
        doubles=[ch for ch,ys in sorted(private.items()) if ch[0]==r and len(ys)==2]
        reps=next(v for v in product(*(sorted(private[ch]) for ch in doubles)) if len(set(v))==3)
        pts.extend((*ch,*leaf) for ch,leaf in zip(doubles,reps))
        pts.append((1,0,0,0))
        for rr in(2,3):pts.extend((rr,c,*next(iter(private[rr,c]))) for c in range(5))
    else:
        pts.append((0,0,0,0))
        for r in range(1,4):
            for c,digit in enumerate(rows[r]):
                if digit=='1':pts.append((r,c,*next(iter(private[r,c]))))
        if index in(3,4):
            r=3 if index==3 else 2
            ch=next(ch for ch,ys in sorted(private.items()) if ch[0]==r and len(ys)==2)
            used={p[2:] for p in pts}
            leaf=next(y for y in sorted(private[ch]) if y not in used)
            pts.append((*ch,*leaf))
    require(len(pts)==len({p[:2] for p in pts})==len({p[2:] for p in pts})==18,'eighteen distinct owners and labels')
    require(set(pts)<=item['source'] and max(Counter(p[2] for p in pts).values())<=5,'actual selection column cap5')
    return {p:Q(1,18) for p in pts}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module,'_zero_triple_base');net=load(args.network_module,'_zero_triple_net')
    dinic=base.load_dinic(args.dinic_module);controls=[]
    for item in templates(base):
        law=law_for(item)
        rec=dict(name=item['name'],shape=item['shape'],active=item['active'],mode=item['mode'],
                 source_points=len(item['source']),source=sorted(item['source']),
                 public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*child,sorted(ys)] for child,ys in sorted(item['private'].items())],
                 whole_private_children=sorted(item['whole_private']),
                 selected_points=sorted(law),**base.literal_checks(item),network=net.network(item,base,dinic),law=base.check_law(item,law))
        require(Q(rec['law']['universal_gamma'])==Q(79,9),'uniform18 exact envelope')
        if item['mode']=='thin_whole_private':
            ch=item['triples'][0]
            require(len(item['private'][ch])==7 and len(item['fibres'][ch]-item['public'])==3,'whole cut retains only3 actual private leaves')
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],cut=rec['network']['minimum_cut'],bound=rec['law']['universal_gamma'])),flush=True)
    require(len(controls)==15,'five shapes crossed with three private/public realizations')
    args.output.write_text(json.dumps(dict(controls=controls,scope='Fifteen actual cut73 controls for five zero/triple-owner shapes: finite private triples, thin whole private prefix with only3 actual leaves, and finite public with two distinct whole private columns. All retain actual standalone trees and original owners. Not the remaining full-k3 family, Lean verification or unrestricted odd covering.'),indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
