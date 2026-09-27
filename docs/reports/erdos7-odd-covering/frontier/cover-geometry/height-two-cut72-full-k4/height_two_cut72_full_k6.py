#!/usr/bin/env python3
"""Actual controls and forced-column contradictions for full cut72 k6/Z15."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import argparse
import importlib.util
import json


def require(ok,message):
    if not ok:raise ValueError(message)


def load(path):
    spec=importlib.util.spec_from_file_location('_cut72_sparse_support',path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod


def forced_column_controls():
    out=[]
    for shape in('0111/01111/01111/01111','1111/00111/01111/01111'):
        rows=shape.split('/')
        labels=[(r,c) for r,row in enumerate(rows) for c,z in enumerate(row) if z=='1']
        require(len(labels)==15,'fifteen private labels')
        parent={p:p for p in labels};tests=[]
        def root(x):
            while parent[x]!=x:x=parent[x]
            return x
        def join(points):
            tests.append(points)
            for p in points[1:]:parent[root(p)]=root(points[0])
        if shape.startswith('0111'):
            for c in range(1,4):
                for r in(1,2,3):
                    for pair in combinations(range(1,5),2):join([(0,c),*( (r,d) for d in pair)])
        else:
            for pair in combinations(range(4),2):
                for c in range(2,5):join([*((0,d) for d in pair),(1,c)])
        groups=defaultdict(list)
        for p in labels:groups[root(p)].append(p)
        sizes=sorted(map(len,groups.values()),reverse=True)
        require(sizes[0]==(15 if shape.startswith('0111') else 7),'forced oversized column')
        require(sizes[0]>5,'contradicts standalone external columncap5')
        out.append(dict(shape=shape,private_labels=labels,exact_three_tests=tests,
                        forced_same_column_components=sorted(groups.values()),
                        largest_forced_component=sizes[0],standalone_column_cap=5,realizable=False))
    public=[]
    for whole in range(3):
        leaves=6-3*whole
        available=leaves+15
        needed=5*(5-whole)
        public.append(dict(whole_columns=whole,finite_public_leaves=leaves,
                           maximum_leaves_outside_whole_columns=available,
                           standalone_required_outside_whole_columns=needed,
                           possible=available>=needed))
    require([p['possible'] for p in public]==[False,False,True],'publicprefix form exhaustion')
    return dict(public_forms=public,impossible_shapes=out)


def templates(base):
    out=[]
    for distributed in(False,True):
        private={(r,c):set() if r==0 else {(r+1,c)} for r,c in base.CHILDREN}
        fibres={}
        for r,c in base.CHILDREN:
            common={(g,c) for g in(0,1)} if distributed else set(product((0,1),range(7)))
            fibres[r,c]=common|private[r,c]
        out.append(dict(name='distributed_public' if distributed else 'full_public',active=base.N,
                        public_columns=(0,1),public_leaves=(),private=private,fibres=fibres,
                        source={(r,c,g,h) for (r,c),ys in fibres.items() for g,h in ys},
                        cap=(Q(1),Q(1,3),Q(1,4),Q(1,10),Q(1,4),Q(1,12),Q(1,20),Q(1,20),Q(1,20))))
    return out


def construct(item,base,dinic):
    restrictions=[tuple(combinations(range(n),n-2)) for n in base.N]
    law=defaultdict(Q);runs=0
    for choices in product(*restrictions):
        caps={};start=('source',);finish=('sink',);owners={}
        for r,cc in enumerate(choices):
            caps[start,('root',r)]=2
            for g,h in product((0,1),range(7)):
                caps[('root',r),('private_leaf',r,g,h)]=1
                actual=[(r,c,g,h) for c in cc if (g,h) in item['fibres'][r,c]]
                if actual:
                    owners[r,g,h]=min(actual)
                    caps[('private_leaf',r,g,h),('common_leaf',g,h)]=6
        for g,h in product((0,1),range(7)):caps[('common_leaf',g,h),finish]=2
        for r,s in combinations(range(4),2):
            require(len({(g,h) for rr,g,h in owners if rr in(r,s)})>=3,'each actual pair hasthree flatpublicleaves')
        value,flow,side=base.solve_network(caps,start,finish,6,dinic)
        require(value==6,'one actual flat14-leaf coupling')
        for(u,v),f in flow.items():
            if u[0]=='private_leaf' and v[0]=='common_leaf' and f:
                law[owners[u[1:]]]+=Q(f,6*6000*4)
        runs+=1
    require(runs==6000 and sum(law.values())==Q(1,4),'all6000 restrictions andpublicmass1/4')
    for r in(1,2,3):
        for c in range(5):law[r,c,r+1,c]+=Q(1,20)
    require(sum(law.values())==1,'one normalized mixture')
    return dict(law),dict(public_couplings=runs,flat_public_leaf_count=14,public_total='1/4',private_point_mass='1/20')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module);dinic=base.load_dinic(args.dinic_module)
    negative=forced_column_controls();controls=[]
    for item in templates(base):
        law,cert=construct(item,base,dinic)
        rec=dict(name=item['name'],source_points=len(item['source']),source=sorted(item['source']),
                 **base.literal_checks(item),network=base.actual_network(item,dinic),construction=cert,
                 law=base.check_law(item,law))
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],mincut=72,
                              gamma=rec['law']['gamma_envelope'],universal_gamma=rec['law']['universal_gamma'])))
    out=dict(scope='Fully active k6/Z15 cut72: two impossible necessary shapes and two actual controls of the surviving shape. Ordinary exact arithmetic, not Lean verification or unrestricted odd covering.',
             necessary_contradiction_checks=negative,controls=controls)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
