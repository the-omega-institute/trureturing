#!/usr/bin/env python3
"""Actual partial2555 cut73 controls with one exceptional full-root double.

Reuse the exact weighted coupling and probability checks from the existing
cut71 partial2555 controls. The new actual-support bridge is proved separately.
"""
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


def common_G_checks(item):
    choices=[tuple(combinations(range(a),2 if r==0 else 3)) for r,a in enumerate(item['active'])]
    tests=0
    for selection in product(*choices):
        supports=[set().union(*({h for g,h in item['fibres'][r,c] if g==0} for c in cs))
                  for r,cs in enumerate(selection)]
        for r,s in combinations(range(4),2):
            require(len(supports[r]|supports[s])>=3,'actual common-G branch at every selected pair')
            tests+=1
    require(tests==6000,'all complete retained-restriction pair checks')
    return tests


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--weighted-module',type=Path,default=Path(__file__).with_name('height_two_cut71_partial2555.py'))
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut73_full_k5.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    old=load(args.weighted_module,'_existing_partial2555_weighted_law')
    base=load(args.support_module,'_existing_literal_and_network_solver')
    net=load(args.network_module,'_cut73_actual_network_checks')
    dinic=base.load_dinic(args.dinic_module)
    controls=[]
    for whole_public in(False,True):
        for shape,whole_private in(('03',False),('03',True),('12',False)):
            item=old.template(shape,whole_public,whole_private)
            item['active']=item['active_counts']
            item['private'][3,4].add((3,5));item['fibres'][3,4].add((3,5));item['source'].add((3,4,3,5))
            item['shape']=shape+'/11111/11111/11112'
            law,public=old.law_for(item,dinic)
            rec=dict(name=item['name'],shape=item['shape'],source_points=len(item['source']),source=sorted(item['source']),
                     public_columns=item['public_columns'],public_leaves=item['public_leaves'],
                     private=[[*child,sorted(ys)] for child,ys in sorted(item['private'].items())],
                     whole_private_children=sorted(item['whole_private']),public_flow=public,
                     **base.literal_checks(item),common_G_restriction_pairs=common_G_checks(item),
                     network=net.network(item,base,dinic),law=old.check_law(item,law))
            controls.append(rec)
            print(json.dumps(dict(name=rec['name'],points=rec['source_points'],minimum_cut=rec['network']['minimum_cut'],
                                  gamma=rec['law']['measured_lcm_upper'],bound=rec['law']['theoretical_lcm_upper'])),flush=True)
    require(len(controls)==6,'two public forms crossed with03 finite,03 whole,12')
    out=dict(weighted_cut_checks=old.weighted_cut_checks(),controls=controls,
             scope='Six actual partial2555 cut73 controls with an exceptional11112 full root, both public forms and finite/whole gap cost3. Exact actual common-G restriction checks, matching actual flow/cut73, and one weighted law; not exhaustive source search, Lean verification or unrestricted odd covering.')
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
