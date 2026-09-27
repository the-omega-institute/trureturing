#!/usr/bin/env python3
"""Seven full cut73 double-gap shapes: actual sources and one common18 law."""
from fractions import Fraction as Q
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import argparse,json

SHAPES={40:'2222/11111/11111/11123',42:'2222/11111/11112/11113',43:'2222/11111/11112/11122',46:'2223/11111/11111/11113',47:'2223/11111/11111/11122',48:'2223/11111/11112/11112',49:'2233/11111/11111/11112'}

def require(ok,msg):
    if not ok:raise ValueError(msg)

def load(path,name):
    spec=spec_from_file_location(name,path);require(spec is not None and spec.loader is not None,'support loader')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod

def templates(base):
    for index,shape in SHAPES.items():
        baseline={}
        for r,row in enumerate(shape.split('/')):
            cursor=0
            for c,digit in enumerate(row):
                cost=int(digit);baseline[r,c]={(r+1,(cursor+j)%7) for j in range(cost)};cursor+=cost
        modes=['finite_private']
        if '3' in shape:modes+=['thin_whole_private','finite_public_whole_private']
        if index in(46,47):modes+=['collapsed_gap_full_extension']
        for mode in modes:
            private={ch:set(ys) for ch,ys in baseline.items()};actual={ch:set(ys) for ch,ys in baseline.items()};whole=set()
            if mode in('thin_whole_private','finite_public_whole_private'):
                ch=next(ch for ch,ys in sorted(private.items()) if len(ys)==3)
                col=5 if mode=='finite_public_whole_private' else ch[0]+1
                private[ch]={(col,h) for h in range(7)};whole.add(ch)
                if mode=='finite_public_whole_private':
                    actual[ch]=set(private[ch])
                    if index==42:private[0,3]=actual[0,3]={(1,6),(4,4)}
                    if index==49:private[0,3]=actual[0,3]={(1,h) for h in(4,5,6)}
            if mode=='collapsed_gap_full_extension':
                for c,hs in enumerate(((0,1),(0,2),(1,2),(0,1,2))):private[0,c]=actual[0,c]={(1,h) for h in hs}
                if index==46:private[3,4]=actual[3,4]={(1,3),(1,4),(4,4)}
                else:
                    private[3,3]=actual[3,3]={(4,3),(1,3)}
                    private[3,4]=actual[3,4]={(4,4),(1,4)}
            public={(0,h) for h in range(3 if mode=='finite_public_whole_private' else 7)}
            fibres={ch:public|actual[ch] for ch in base.CHILDREN}
            require(sum(3 if ch in whole else len(ys) for ch,ys in private.items())==26,'private26')
            yield dict(name='double_gap73_%d_%s'%(index,mode),shape=shape,index=index,mode=mode,active=base.N,
                public=public,public_columns=(0,) if len(public)==7 else(),public_leaves=tuple(sorted(public)) if len(public)==3 else(),
                private=private,whole_private=whole,fibres=fibres,source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},
                cap=tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1)))

def lower_cut_network(item,base,dinic):
    caps={};start=('source',);finish=('sink',)
    for r,n in enumerate(base.N):
        caps[start,('r',r)]=21
        for c in range(n):
            caps[('r',r),('c',r,c)]=7
            for g in range(7):
                caps[('c',r,c),('pg',r,c,g)]=6
                for h in range(7):caps[('pg',r,c,g),('ph',r,c,g,h)]=2
    for g in range(7):
        caps[('cg',g),finish]=21
        for h in range(7):caps[('ch',g,h),('cg',g)]=7
    for p in item['source']:caps[('ph',*p),('ch',*p[2:])]=126
    value,flow,side=base.solve_network(caps,start,finish,1000,dinic)
    cut=[(u,v,c) for(u,v),c in caps.items() if u in side and v not in side]
    require(value==72 and sum(c for u,v,c in cut)==72,'joint extension boundary actual mincut72')
    require(all(flow[u,v]==c for u,v,c in cut),'computed cut saturated')
    return dict(maximum_flow=value,minimum_cut=value,displayed_profile_cut_cost=73,
        computed_minimum_cut=[[list(u),list(v),c] for u,v,c in cut],
        actual_flow_atoms=[[*u[1:],f] for(u,v),f in flow.items() if u[0]=='ph' and v[0]=='ch' and f])

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    p.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    p.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    a=p.parse_args();base=load(a.support_module,'_double_gap_base');net=load(a.network_module,'_double_gap_net');dinic=base.load_dinic(a.dinic_module)
    controls=[];boundary=[]
    for item in templates(base):
        literal=base.literal_checks(item)
        network=lower_cut_network(item,base,dinic) if item['mode']=='collapsed_gap_full_extension' else net.network(item,base,dinic)
        law=net.selected_law(item,base,dinic)
        rec=dict(name=item['name'],original_shape_index=item['index'],shape=item['shape'],mode=item['mode'],source_points=len(item['source']),source=sorted(item['source']),
            public_columns=item['public_columns'],public_leaves=item['public_leaves'],private=[[*ch,sorted(ys)] for ch,ys in sorted(item['private'].items())],
            whole_private_children=sorted(item['whole_private']),selected_points=sorted(law),**literal,network=network,law=base.check_law(item,law))
        require(rec['law']['universal_gamma']=='79/9','common18 envelope')
        if item['mode']=='thin_whole_private':
            ch=next(iter(item['whole_private']));require(len(item['private'][ch])==7 and len(item['fibres'][ch]-item['public'])==3,'whole candidate with only three actual leaves')
        if item['mode']=='collapsed_gap_full_extension':
            require(set().union(*(item['fibres'][0,c]-item['public'] for c in range(4)))=={(1,h) for h in range(3)},'actual gap exactly three private leaves')
            require({h for r,c,g,h in item['source'] if g==1}==set(range(5)),'exceptional root jointly fills gap column')
        (boundary if item['mode']=='collapsed_gap_full_extension' else controls).append(rec)
        print(json.dumps(dict(name=item['name'],points=rec['source_points'],mincut=network['minimum_cut'],actual_gamma=rec['law']['gamma_envelope'],bound=rec['law']['universal_gamma'])),flush=True)
    require(len(controls)==19 and len(boundary)==2,'19 actual73 controls and two separate lower72 controls')
    a.output.write_text(json.dumps(dict(scope='Nineteen actual mincut73 controls for original shapes40,42,43,46-49, plus two separate actual mincut72 boundary sources displaying nonminimal profile cut73. The boundary sources test joint extension after exact gap support collapse; they are not cut73 controls. Every source retains original actual restrictions/owners/numerical labels and one common18 law. Ordinary arithmetic, not Lean or unrestricted #7.',controls=controls,lower_cut_boundary_controls=boundary),indent=2)+'\n')
if __name__=='__main__':main()
