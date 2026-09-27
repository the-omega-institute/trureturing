#!/usr/bin/env python3
"""Actual cut73 controls for seven shapes using common-column double selection."""
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


SHAPES=('1222/02222/11111/11112','1222/02223/11111/11111',
        '1223/02222/11111/11111','2222/01222/11111/11112',
        '2222/01223/11111/11111','2222/02222/11111/11111',
        '2223/01222/11111/11111')


def templates(base):
    out=[]
    for index,shape in enumerate(SHAPES,1):
        baseline={}
        for r,row in enumerate(shape.split('/')):
            cursor=0
            for c,digit in enumerate(row):
                cost=int(digit);baseline[r,c]={(r+1,(cursor+j)%7) for j in range(cost)};cursor+=cost
        triples=[ch for ch,ys in baseline.items() if len(ys)==3]
        modes=['finite_private']
        if triples:modes += ['thin_whole_private','finite_public_whole_private']
        if index==6:modes.append('cross_double')
        for mode in modes:
            private={ch:set(ys) for ch,ys in baseline.items()};actual={ch:set(ys) for ch,ys in baseline.items()};whole=set()
            if mode in('thin_whole_private','finite_public_whole_private'):
                ch=triples[0];col=5 if mode=='finite_public_whole_private' else ch[0]+1
                private[ch]={(col,h) for h in range(7)};whole.add(ch)
                if mode=='finite_public_whole_private':actual[ch]=set(private[ch])
            elif mode=='cross_double':
                for r,c,h in((0,3,0),(1,4,1)):
                    actual[r,c]={(r+1,6),(5,h)};private[r,c]=set(actual[r,c])
            public={(0,h) for h in range(3 if mode=='finite_public_whole_private' else 7)}
            fibres={ch:public|actual[ch] for ch in base.CHILDREN}
            require(sum(3 if ch in whole else len(ys) for ch,ys in private.items())==26,'private weighted cost26')
            out.append(dict(name='seven_double73_%d_%s'%(index,mode),shape=shape,index=index,mode=mode,
                            active=base.N,public=public,public_columns=() if len(public)==3 else(0,),
                            public_leaves=tuple(sorted(public)) if len(public)==3 else(),private=private,
                            actual_private=actual,whole_private=whole,fibres=fibres,
                            source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},
                            cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1))))
    require(len(out)==16,'sixteen controls')
    return out


def law_for(item):
    private=item['actual_private'];rows=item['shape'].split('/');pts=[];index=item['index']
    def one(ch):pts.append((*ch,*next(iter(private[ch]))))
    def reps(children):
        # The theorem selects the shared column, not a cross-double outlier.
        sets=[{y for y in private[ch] if y[0]==ch[0]+1} for ch in children]
        used={p[2:] for p in pts}
        values=next(v for v in product(*(sorted(ys-used) for ys in sets)) if len(set(v))==len(v))
        pts.extend((*ch,*leaf) for ch,leaf in zip(children,values))
    gap=rows[0]
    if gap.startswith('1'):one((0,0))
    gap_doubles=[(0,c) for c,digit in enumerate(gap) if digit=='2']
    if index==6:gap_doubles=gap_doubles[:3]
    reps(gap_doubles)
    pts.append((1,0,0,0))
    for c,digit in enumerate(rows[1]):
        if digit=='1':one((1,c))
    reps([(1,c) for c,digit in enumerate(rows[1]) if digit=='2'])
    for r in(2,3):
        for c,digit in enumerate(rows[r]):
            if digit=='1':one((r,c))
    require(len(pts)==len({p[:2] for p in pts})==len({p[2:] for p in pts})==18,'eighteen original owners and actual labels')
    require(set(pts)<=item['source'] and max(Counter(p[2] for p in pts).values())<=5,'actual law and column cap5')
    return {p:Q(1,18) for p in pts}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module,'_seven_double_base');net=load(args.network_module,'_seven_double_net')
    dinic=base.load_dinic(args.dinic_module);controls=[]
    for item in templates(base):
        law=law_for(item)
        rec=dict(name=item['name'],shape=item['shape'],active=item['active'],mode=item['mode'],
                 source_points=len(item['source']),source=sorted(item['source']),
                 public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*ch,sorted(ys)] for ch,ys in sorted(item['private'].items())],
                 whole_private_children=sorted(item['whole_private']),selected_points=sorted(law),
                 **base.literal_checks(item),network=net.network(item,base,dinic),law=base.check_law(item,law))
        require(Q(rec['law']['universal_gamma'])==Q(79,9),'uniform18 exact envelope')
        if item['mode']=='thin_whole_private':
            ch=next(iter(item['whole_private']))
            require(len(item['private'][ch])==7 and len(item['fibres'][ch]-item['public'])==3,'whole prefix only3 actual leaves')
        if item['mode']=='cross_double':
            require(all(any(g==5 for g,h in item['actual_private'][ch]) for ch in((0,3),(1,4))),'two actual cross-double fibres')
            require(not any(p[2]==5 for p in law),'common-column selection omits both outliers')
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],cut=rec['network']['minimum_cut'],bound=rec['law']['universal_gamma'])),flush=True)
    args.output.write_text(json.dumps(dict(controls=controls,scope='Sixteen actual cut73 controls for seven common-column double-selection shapes. Includes whole-prefix only3 actual leaves, finite-public valid standalone sources, and two cross-double actual fibres. Original owners and labels retained; not all full-k3 shapes, Lean verification or unrestricted odd covering.'),indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
