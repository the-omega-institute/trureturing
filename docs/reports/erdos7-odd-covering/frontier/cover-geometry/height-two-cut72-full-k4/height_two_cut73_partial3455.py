#!/usr/bin/env python3
"""Two actual partial3455 cut73 controls using one equal public coupling."""
from collections import defaultdict
from fractions import Fraction as Q
from importlib.util import module_from_spec,spec_from_file_location
from itertools import combinations,product
from pathlib import Path
import argparse,json


def require(ok,message):
    if not ok:raise ValueError(message)


def load(path,name):
    spec=spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'existing support module')
    mod=module_from_spec(spec);spec.loader.exec_module(mod);return mod


CAPS=tuple(map(Q,('1','139/459','35/153','31/306','35/153','2/27','1/18','7/153','7/153')))


def template(base,whole):
    active=(3,4,5,5)
    rowleaves=({0,1},{1,2},{2,3},{3,4}) if whole else({0,1},{1,2},{0,2},{0,1,2})
    private={(0,0):{(4,0)},(0,1):{(4,1),(4,2)},(0,2):{(4,2),(4,3)}}
    private.update({(r,c):{(r,c)} for r in range(1,4) for c in range(active[r])})
    fibres={(r,c):({(0,h) for h in rowleaves[r]}|private[r,c]) if c<active[r]
                      else set(product(range(7),repeat=2)) for r,c in base.CHILDREN}
    return dict(name='3455_public_'+('whole' if whole else'finite'),active=active,
                public_columns=(0,) if whole else(),public_leaves=() if whole else((0,0),(0,1),(0,2)),
                private=private,whole_private=set(),fibres=fibres,rowleaves=rowleaves,cap=CAPS,
                source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys})


def law_for(item,base,dinic):
    caps={};start=('source',);finish=('sink',)
    for r in range(4):
        caps[start,('root',r)]=6
        for h in item['rowleaves'][r]:caps[('root',r),('leaf',h)]=3
    for h in range(7):caps[('leaf',h),finish]=6
    value,flow,side=base.solve_network(caps,start,finish,18,dinic)
    require(value==18,'one actual root/fine/joint public coupling')
    public={(u[1],v[1]):Q(f,18) for(u,v),f in flow.items() if u[0]=='root' and v[0]=='leaf' and f}
    require(sum(public.values())==1,'normalized public probability')
    for r in range(4):require(sum(v for(rr,h),v in public.items() if rr==r)<=Q(1,3),'public root cap')
    for h in range(7):require(sum(v for(r,hh),v in public.items() if hh==h)<=Q(1,3),'public fine cap')
    require(all(v<=Q(1,6) for v in public.values()),'public root/fine cap')
    choices=[tuple(combinations(range(a),2 if r==0 else 3)) for r,a in enumerate(item['active'])]
    combinations_checked=0;pair_checks=0
    for selection in product(*choices):
        actual=[set().union(*({h for g,h in item['fibres'][r,c] if g==0} for c in cs)) for r,cs in enumerate(selection)]
        for r,h in public:require(h in actual[r],'one coupling supported at every complete restriction')
        for r,s in combinations(range(4),2):
            require(len(actual[r]|actual[s])>=3,'actual common-G branch at each selected pair');pair_checks+=1
        combinations_checked+=1
    require((combinations_checked,pair_checks)==(1200,7200),'complete restriction counts')
    law=defaultdict(Q)
    for(r,h),v in public.items():
        for cs in choices[r]:
            p=(r,min(cs),0,h);require(p in item['source'],'actual lifted public owner')
            law[p]+=Q(2,9)*v/len(choices[r])
    private_points=[(0,0,4,0),(0,1,4,1),(0,2,4,2)]
    private_points +=[(r,c,r,c) for r in range(1,4) for c in range(item['active'][r])]
    require(len(private_points)==len({p[:2] for p in private_points})==len({p[2:] for p in private_points})==17,
            'seventeen distinct actual private owners/leaves')
    require(set(private_points)<=item['source'],'actual private selection')
    for p in private_points:law[p]+=Q(7,153)
    require(all(p[1]<item['active'][p[0]] for p in law),'no law mass at inactive children')
    return dict(law),dict(public_flow=[[r,h,str(v)] for(r,h),v in sorted(public.items())],
                          private_selection=private_points,complete_restrictions=combinations_checked,pair_checks=pair_checks)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module,'_sparse_support');net=load(args.network_module,'_network73')
    dinic=base.load_dinic(args.dinic_module);controls=[]
    for whole in(False,True):
        item=template(base,whole);law,selection=law_for(item,base,dinic)
        rec=dict(name=item['name'],active=item['active'],source_points=len(item['source']),source=sorted(item['source']),
                 public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                 private=[[*child,sorted(ys)] for child,ys in sorted(item['private'].items())],
                 selection=selection,**base.literal_checks(item),network=net.network(item,base,dinic),law=base.check_law(item,law))
        require(Q(rec['law']['universal_gamma'])==Q(3761,459),'exact envelope3761/459')
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],minimum_cut=rec['network']['minimum_cut'],
                              gamma=rec['law']['gamma_envelope'],bound=rec['law']['universal_gamma'])),flush=True)
    out=dict(controls=controls,scope='Two actual partial3455 cut73 source controls for both public forms. Matching actual maxflow/cut73; one public flow valid on all1200 complete retained-child restrictions, checked7200 actual G pairs; one common mixed law. Exact construction controls, not exhaustive source search, Lean verification or unrestricted odd covering.')
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
