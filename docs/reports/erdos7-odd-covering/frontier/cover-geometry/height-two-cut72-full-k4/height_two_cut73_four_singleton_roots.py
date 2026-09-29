#!/usr/bin/env python3
"""Actual cut73 controls for original shapes22,23,31,44 and their 18-point laws."""
from collections import Counter
from fractions import Fraction as Q
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import argparse,json

def require(ok,message):
    if not ok:raise ValueError(message)

def load(path,name):
    spec=spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'support module')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod

SHAPES={22:'1222/11112/11112/11113',23:'1222/11112/11112/11122',
        31:'1223/11112/11112/11112',44:'2222/11112/11112/11112'}

def template(base,index,mode='whole_public'):
    shape=SHAPES[index];private={};actual={};whole=set();rows=shape.split('/')
    public={(0,h) for h in range(3 if mode.startswith('finite_public') else 7)}
    for r,row in enumerate(rows):
        if r==0:
            leaves=([{0},{1,2},{2,3},{3,4}] if index in (22,23) else
                    [{0},{1,2},{3,4},{0,1,2}] if index==31 else
                    [{0,1},{1,2},{2,3},{3,4}])
        elif row=='11112':leaves=[{0},{1},{2},{3},{4,5}]
        elif row=='11113':leaves=[{0},{1},{2},{3},{4,5,6}]
        elif row=='11122':leaves=[{0},{1},{2},{0,3},{1,4}]
        else:raise ValueError(row)
        for c,hs in enumerate(leaves):private[r,c]={(r+1,h) for h in hs}
    actual={ch:set(ys) for ch,ys in private.items()}
    if mode=='thin_ignored_whole':
        require(index==22,'thin ignored triple control')
        private[3,4]={(4,h) for h in range(7)};whole.add((3,4))
    if mode=='finite_public_finite_gap_triple':
        require(index==31,'finite-public source scope')
        private[0,3]={(5,h) for h in (3,4,5)}
        for r in (1,2,3):private[r,4]={(r+1,4),(5,r-1)}
        actual={ch:set(ys) for ch,ys in private.items()}
    if mode=='finite_public_whole_gap_triple':
        require(index==31,'whole-gap source scope')
        private[0,3]={(5,h) for h in range(7)};actual[0,3]={(5,h) for h in range(5)};whole.add((0,3))
    require(sum(3 if ch in whole else len(ys) for ch,ys in private.items())==26,'private cut cost26')
    require(all(not(public&ys) for ys in private.values()),'displayed private/public supports disjoint')
    fibres={ch:public|actual[ch] for ch in base.CHILDREN}
    pts=[]
    if index in (22,23):pts.extend((0,c,1,h) for c,h in enumerate((0,1,2,3)))
    elif index==31:pts.extend((0,c,1,h) for c,h in enumerate((0,1,3)))
    else:pts.extend((0,c,1,c) for c in range(3))
    for r,row in enumerate(rows[1:],1):
        if row=='11112':pts.extend((r,c,r+1,c) for c in range(5))
        elif row=='11113':pts.extend((r,c,r+1,c) for c in range(4))
        elif row=='11122':pts.extend((r,c,r+1,c) for c in range(4))
    source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys}
    require(len(pts)==len({p[:2] for p in pts})==len({p[2:] for p in pts})==18,'one eighteen-owner/eighteen-leaf selection')
    require(set(pts)<=source and max(Counter(p[2] for p in pts).values())<=5,'actual selection and column bound')
    return dict(name='four_singleton73_%d_%s'%(index,mode),index=index,shape=shape,mode=mode,
                active=base.N,public_columns=(0,) if len(public)==7 else(),public_leaves=tuple(sorted(public)) if len(public)==3 else(),
                public=public,private=private,actual_private=actual,whole_private=whole,fibres=fibres,source=source,selected=pts,
                cap=tuple(Q(x,18) for x in (18,5,5,1,5,1,1,1,1)))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module,'_four_singleton_base');net=load(args.network_module,'_four_singleton_net');dinic=base.load_dinic(args.dinic_module)
    items=[template(base,i) for i in SHAPES]
    items.extend([template(base,22,'thin_ignored_whole'),template(base,31,'finite_public_finite_gap_triple'),template(base,31,'finite_public_whole_gap_triple')])
    controls=[]
    for item in items:
        law={p:Q(1,18) for p in item['selected']}
        rec=dict(name=item['name'],original_shape_index=item['index'],shape=item['shape'],mode=item['mode'],
                 source_points=len(item['source']),source=sorted(item['source']),public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*ch,sorted(ys)] for ch,ys in sorted(item['private'].items())],whole_private_children=sorted(item['whole_private']),
                 selected_points=sorted(law),**base.literal_checks(item),network=net.network(item,base,dinic),law=base.check_law(item,law))
        require(Q(rec['law']['universal_gamma'])==Q(79,9),'same common law envelope79/9')
        if item['mode']=='thin_ignored_whole':require(len(item['actual_private'][3,4])==3,'only three actual leaves of ignored whole prefix')
        controls.append(rec)
        print(json.dumps({k:rec[k] for k in ('name','source_points','shape')}|{'cut':rec['network']['minimum_cut'],'gamma':rec['law']['universal_gamma']}),flush=True)
    args.output.write_text(json.dumps({'scope':'Seven actual source controls for four further fully active cut73/public3/private26 shapes. Whole and finite public forms; ignored triple may be a finite set or whole private prefix. Every control retains literal blocking, standalone, a matched actual flow/cut73 and one uniform18 actual law. Not the remaining full family, Lean verification, or unrestricted odd covering.','controls':controls},indent=2)+'\n')

if __name__=='__main__':main()
