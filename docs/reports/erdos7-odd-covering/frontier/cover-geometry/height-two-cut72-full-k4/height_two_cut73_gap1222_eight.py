#!/usr/bin/env python3
"""Actual controls for cut73 gap1222 shapes14-21 and their common18 laws."""
from fractions import Fraction as Q
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import argparse,json

SHAPES={14:'1222/11111/11111/11133',15:'1222/11111/11111/11223',16:'1222/11111/11111/12222',17:'1222/11111/11112/11123',18:'1222/11111/11112/11222',19:'1222/11111/11113/11113',20:'1222/11111/11113/11122',21:'1222/11111/11122/11122'}
ROWS={'11111':[{0},{1},{2},{3},{4}], '11112':[{0},{1},{2},{3},{4,5}], '11113':[{0},{1},{2},{3},{4,5,6}], '11122':[{0},{1},{2},{3,4},{4,5}], '11123':[{0},{1},{2},{3,4},{4,5,6}], '11222':[{0},{1},{2,3},{3,4},{4,5}], '11133':[{0},{1},{2},{3,4,5},{4,5,6}], '11223':[{0},{1},{2,3},{3,4},{4,5,6}], '12222':[{0},{1,2},{2,3},{3,4},{4,5}]}
def require(ok,msg):
    if not ok:raise ValueError(msg)
def load(path,name):
    spec=spec_from_file_location(name,path);require(spec is not None and spec.loader is not None,'support loader')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod

def template(base,index,mode='whole_public'):
    shape=SHAPES[index];private={};whole=set()
    for r,row in enumerate(shape.split('/')):
        sets=[{0},{1,2},{2,3},{3,4}] if r==0 else ROWS[row]
        for c,hs in enumerate(sets):private[r,c]={(r+1,h) for h in hs}
    public={(0,h) for h in range(3 if mode=='finite_public_whole_triples' else 7)}
    if mode=='finite_public_whole_triples':
        require(index==14,'whole triple control shape')
        for c,g in ((3,5),(4,6)):
            private[3,c]={(g,h) for h in range(7)};whole.add((3,c))
    if mode=='one_deficient_root':
        require(index==19,'deficient root control shape')
        private[2,4]={(3,h) for h in (0,1,2)}
        private[3,4]={(3,4),(4,4),(4,5)}
    actual={ch:set(ys) for ch,ys in private.items()}
    if mode=='finite_public_whole_triples':
        for c,g in ((3,5),(4,6)):actual[3,c]={(g,h) for h in range(5)}
    require(sum(3 if ch in whole else len(ys) for ch,ys in private.items())==26,'private26')
    fibres={ch:public|actual[ch] for ch in base.CHILDREN}
    if mode=='one_deficient_root':
        for c in range(5):fibres[2,c]=set(actual[2,c])
        require(len(set().union(*(fibres[2,c] for c in range(5))))==4,'five owners have only four actual leaves')
    source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys}
    return dict(name='gap1222_eight_%d_%s'%(index,mode),index=index,shape=shape,mode=mode,active=base.N,
                public_columns=(0,) if len(public)==7 else(), public_leaves=tuple(sorted(public)) if len(public)==3 else(),
                private=private,whole_private=whole,fibres=fibres,source=source,
                cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1)))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    p.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    p.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    a=p.parse_args();base=load(a.support_module,'_eight_base');net=load(a.network_module,'_eight_net');dinic=base.load_dinic(a.dinic_module)
    items=[template(base,i) for i in SHAPES]+[template(base,14,'finite_public_whole_triples'),template(base,19,'one_deficient_root')]
    controls=[]
    for item in items:
        literal=base.literal_checks(item);network=net.network(item,base,dinic);law=net.selected_law(item,base,dinic)
        rec=dict(name=item['name'],original_shape_index=item['index'],shape=item['shape'],mode=item['mode'],source_points=len(item['source']),source=sorted(item['source']),
                 public_columns=item['public_columns'],public_leaves=item['public_leaves'],private=[[*ch,sorted(ys)] for ch,ys in sorted(item['private'].items())],
                 whole_private_children=sorted(item['whole_private']),selected_points=sorted(law),**literal,network=network,law=base.check_law(item,law))
        require(rec['law']['universal_gamma']=='79/9','one common18 envelope')
        controls.append(rec)
        print(json.dumps({k:rec[k] for k in('name','source_points','shape')}|{'cut':network['minimum_cut'],'gamma':rec['law']['universal_gamma']}),flush=True)
    a.output.write_text(json.dumps({'scope':'Ten actual source controls for original fully active cut73/public3/private26 shapes14-21. Includes finite public plus thin whole triples and a five-owner root with only four actual leaves. Each checks literal pair/product tests, standalone, matched actual maxflow/cut73 and one common18 law. Ordinary finite arithmetic, not Lean or unrestricted odd covering.','controls':controls},indent=2)+'\n')
if __name__=='__main__':main()
