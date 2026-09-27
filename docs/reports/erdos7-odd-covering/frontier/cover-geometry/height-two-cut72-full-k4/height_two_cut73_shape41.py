#!/usr/bin/env python3
"""Actual source controls for the cut73 shape41 complementary four selections."""
from fractions import Fraction as Q
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import argparse,json

def require(ok,msg):
    if not ok:raise ValueError(msg)
def load(path,name):
    spec=spec_from_file_location(name,path);require(spec is not None and spec.loader is not None,'support loader')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod

def template(base,mixed=False):
    private={}
    for c,hs in enumerate(({0,1},{1,2},{2,3},{3,4})):private[0,c]={(1,h) for h in hs}
    if mixed:
        private[0,0]={(1,0),(5,0)}
        for c,hs in enumerate(({1,2},{2,3},{3,4}),1):private[0,c]={(1,h) for h in hs}
    for r in(1,2):
        for c in range(5):private[r,c]={(r+1,c)}
    for c,hs in enumerate(({0},{1},{2,3},{3,4},{4,5})):private[3,c]={(4,h) for h in hs}
    public={(0,h) for h in range(7)};fibres={ch:public|private[ch] for ch in base.CHILDREN}
    require(sum(map(len,private.values()))==26,'private26')
    return dict(name='shape41_'+('gap_outlier' if mixed else 'whole_public'),active=base.N,public_columns=(0,),public_leaves=(),private=private,whole_private=set(),fibres=fibres,
                source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1)))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    p.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    p.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    a=p.parse_args();base=load(a.support_module,'_shape41_base');net=load(a.network_module,'_shape41_net');dinic=base.load_dinic(a.dinic_module)
    controls=[]
    for mixed in(False,True):
        item=template(base,mixed);literal=base.literal_checks(item);network=net.network(item,base,dinic);law=net.selected_law(item,base,dinic)
        rec=dict(name=item['name'],original_shape_index=41,shape='2222/11111/11111/11222',source_points=len(item['source']),source=sorted(item['source']),public_columns=item['public_columns'],public_leaves=(),
                 private=[[*ch,sorted(ys)] for ch,ys in sorted(item['private'].items())],whole_private_children=[],selected_points=sorted(law),**literal,network=network,law=base.check_law(item,law))
        require(rec['law']['universal_gamma']=='79/9','common18 envelope')
        controls.append(rec);print(json.dumps({'name':rec['name'],'points':rec['source_points'],'cut':network['minimum_cut'],'gamma':rec['law']['universal_gamma']}),flush=True)
    a.output.write_text(json.dumps({'scope':'Two actual matched cut73/public3/private26 controls for original shape41, including an actual gap outlier. Each checks all literal pair/product tests, standalone, actual flow=cut73 and one common18 law. Ordinary finite arithmetic, not Lean or unrestricted odd covering.','controls':controls},indent=2)+'\n')
if __name__=='__main__':main()
