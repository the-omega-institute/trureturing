#!/usr/bin/env python3
"""Actual controls for cut73 gap1223 shapes27-30 and complementary Hall repair."""
from fractions import Fraction as Q
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import argparse,json
SHAPES={27:'1223/11111/11111/11123',28:'1223/11111/11111/11222',29:'1223/11111/11112/11113',30:'1223/11111/11112/11122'}
ROWS={'11111':[{0},{1},{2},{3},{4}], '11112':[{0},{1},{2},{3},{4,5}], '11113':[{0},{1},{2},{3},{4,5,6}], '11122':[{0},{1},{2},{3,4},{4,5}], '11123':[{0},{1},{2},{3,4},{4,5,6}], '11222':[{0},{1},{2,3},{3,4},{4,5}]}
def require(ok,msg):
    if not ok:raise ValueError(msg)
def load(path,name):
    spec=spec_from_file_location(name,path);require(spec is not None and spec.loader is not None,'support loader')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod

def template(base,index,mode='whole_public'):
    shape=SHAPES[index];private={};whole=set();public={(0,h) for h in range(7)}
    for r,row in enumerate(shape.split('/')):
        sets=[{0},{1,2},{2,3},{3,4,5}] if r==0 else ROWS[row]
        for c,hs in enumerate(sets):private[r,c]={(r+1,h) for h in hs}
    if mode=='blocked_singleton':
        require(index==28,'blocked singleton source')
        private[3,0]={(2,6)};private[3,1]={(4,0)}
        for c,hs in ((2,(1,2)),(3,(2,3)),(4,(3,4))):private[3,c]={(4,h) for h in hs}
    if mode=='thin_whole_gap':
        private[0,3]={(1,h) for h in range(7)};whole.add((0,3))
    actual={ch:set(ys) for ch,ys in private.items()}
    if mode=='thin_whole_gap':actual[0,3]={(1,h) for h in(3,4,5)}
    require(sum(3 if ch in whole else len(ys) for ch,ys in private.items())==26,'private26')
    fibres={ch:public|actual[ch] for ch in base.CHILDREN}
    if mode=='blocked_singleton':fibres[3,0]=set(actual[3,0])
    return dict(name='gap1223_four_%d_%s'%(index,mode),index=index,shape=shape,mode=mode,active=base.N,
                public_columns=(0,),public_leaves=(),private=private,whole_private=whole,fibres=fibres,
                source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},
                cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1)))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    p.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    p.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    a=p.parse_args();base=load(a.support_module,'_gapfour_base');net=load(a.network_module,'_gapfour_net');dinic=base.load_dinic(a.dinic_module)
    items=[template(base,i) for i in SHAPES]+[template(base,28,'blocked_singleton'),template(base,29,'thin_whole_gap')]
    controls=[]
    for item in items:
        literal=base.literal_checks(item);network=net.network(item,base,dinic);law=net.selected_law(item,base,dinic)
        rec=dict(name=item['name'],original_shape_index=item['index'],shape=item['shape'],mode=item['mode'],source_points=len(item['source']),source=sorted(item['source']),
                 public_columns=item['public_columns'],public_leaves=item['public_leaves'],private=[[*ch,sorted(ys)] for ch,ys in sorted(item['private'].items())],
                 whole_private_children=sorted(item['whole_private']),selected_points=sorted(law),**literal,network=network,law=base.check_law(item,law))
        require(rec['law']['universal_gamma']=='79/9','one common18 envelope')
        controls.append(rec)
        print(json.dumps({k:rec[k] for k in('name','source_points','shape')}|{'cut':network['minimum_cut'],'gamma':rec['law']['universal_gamma']}),flush=True)
    a.output.write_text(json.dumps({'scope':'Six actual matched cut73/public3/private26 source controls for original shapes27-30. Includes a private singleton blocked by another anchor and an ignored whole gap prefix with only three actual leaves. Each checks literal pair/product tests, standalone, actual flow=cut73 and one common18 law. Ordinary finite arithmetic, not Lean or unrestricted odd covering.','controls':controls},indent=2)+'\n')
if __name__=='__main__':main()
