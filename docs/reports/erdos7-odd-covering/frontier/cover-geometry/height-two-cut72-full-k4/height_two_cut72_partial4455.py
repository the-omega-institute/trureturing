#!/usr/bin/env python3
"""Exact actual controls for all five partial4455/k3/private22 cut72 shapes."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import argparse
import importlib.util
import json


def require(ok,message):
    if not ok:raise ValueError(message)


def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod


ROWS={'1222':((0,),(1,2),(2,3),(3,4)),
      '1223':((0,),(1,2),(2,3),(4,5,6)),
      '2222':((0,1),(1,2),(2,3),(3,4)),
      '0122':((),(0,),(1,2),(2,3)),
      '1111':((0,),(1,),(2,),(3,)),
      '1112':((0,),(1,),(2,),(3,4)),
      '11111':((0,),(1,),(2,),(3,),(4,)),
      '11112':((0,),(1,),(2,),(3,),(4,5))}
SHAPES=('1222/0122/11111/11111','1222/1111/11111/11112',
        '1222/1112/11111/11111','1223/1111/11111/11111',
        '2222/1111/11111/11111')
A=(Q(5,63),Q(4,63),Q(5,63),Q(5,63))
B=(Q(1,7),Q(5,63),Q(1,9),Q(1,9))
W=Q(2,9)


def weighted_checks():
    slacks=[]
    for n in range(5):
        for ss in combinations(range(4),n):
            top=sum(A[r] for r in range(4) if r not in ss)
            if n<=1:slacks.append(top-W)
            else:
                total=sum(B[r] for r in ss);slacks.append(top+total/2-W)
                slacks.extend(top+total-B[j]-W for j in ss)
    require(len(slacks)==44 and min(slacks)>=0,'all44 exact scaled weighted cuts')
    return dict(inequalities=44,minimum_slack=str(min(slacks)),A=list(map(str,A)),B=list(map(str,B)),W=str(W))


def templates(base):
    out=[]
    for shape in SHAPES:
        for whole in ((False,True) if shape.startswith('1223') else (False,)):
            rows=shape.split('/');private={};wholechildren=set()
            for r,row in enumerate(rows):
                for c,hs in enumerate(ROWS[row]):
                    require(len(hs)==int(row[c]),'exact sorted private cost')
                    g=4 if r==0 else r
                    private[r,c]={(g,h) for h in (range(7) if whole and len(hs)==3 else hs)}
                    if whole and len(hs)==3:wholechildren.add((r,c))
            fibres={child:({(0,h) for h in range(7)}|private[child]) if child in private else set(base.ALL)
                    for child in base.CHILDREN}
            points=[]
            for r,row in enumerate(rows):
                g=4 if r==0 else r
                if row=='0122':points.extend((r,c,g,c-1) for c in range(1,4))
                elif row=='1223':points.extend((r,c,g,h) for c,h in enumerate((0,1,2,4)))
                else:points.extend((r,c,g,c) for c in range(len(row)))
            weighted=rows[1]=='0122'
            caps=(Q(1),Q(19,63),Q(2,9),Q(2,21),Q(2,9),Q(2,27),Q(1,21),Q(1,21),Q(1,21)) if weighted else tuple(Q(x,18) for x in(18,5,5,1,5,1,1,1,1))
            out.append(dict(name=shape+('_whole' if whole else '_finite'),shape=shape,active=(4,4,5,5),
                            public_columns=(0,),public_leaves=(),private=private,whole_private=wholechildren,
                            fibres=fibres,source={(r,c,g,h) for(r,c),ys in fibres.items() for g,h in ys},
                            cap=caps,points=points,weighted=weighted))
    require(len(out)==6,'five finite and one whole-prefix control')
    return out


def construct(item,base,dinic):
    pts=item['points']
    require(set(pts)<=item['source'],'every selected private point actual')
    require(len(pts)==len({p[:2] for p in pts})==len({p[2:] for p in pts}),'distinct private children and leaves')
    if not item['weighted']:
        require(len(pts)==18,'uniform18 selector')
        return {p:Q(1,18) for p in pts},dict(public_couplings=0,private_count=18)
    require(len(pts)==17,'weighted17 private selector')
    law=defaultdict(Q);runs=0
    restrictions=[tuple(combinations(range(a),base.N[r]-2)) for r,a in enumerate(item['active'])]
    count=1
    for rr in restrictions:count*=len(rr)
    require(count==2400,'all2400 actual active restrictions')
    # Scale actual masses by189: target42, root15/12, joint9/5/7/7, publicfine14.
    den=189;target=int(den*W)
    for choices in product(*restrictions):
        caps={};start=('source',);finish=('sink',);owners={}
        for r,cc in enumerate(choices):
            caps[start,('root',r)]=int(den*A[r])
            for h in range(7):
                caps[('root',r),('private_leaf',r,h)]=int(den*B[r]/3)
                actual=[(r,c,0,h) for c in cc if (0,h) in item['fibres'][r,c]]
                if actual:
                    owners[r,h]=min(actual);caps[('private_leaf',r,h),('common_leaf',h)]=target
        for h in range(7):caps[('common_leaf',h),finish]=int(den*W/3)
        for r,s in combinations(range(4),2):
            require(len({h for rr,h in owners if rr in(r,s)})>=3,'actual G pair premise')
        value,flow,side=base.solve_network(caps,start,finish,target,dinic)
        require(value==target,'one scaled weighted public law')
        for(u,v),f in flow.items():
            if u[0]=='private_leaf' and v[0]=='common_leaf' and f:law[owners[u[1:]]]+=Q(f,den*count)
        runs+=1
    require(sum(law.values())==W and runs==2400,'public total and complete restrictions')
    for p in pts:law[p]+=Q(1,21) if p[0] in(0,1) else Q(2,45)
    require(sum(law.values())==1,'one normalized actual law')
    return dict(law),dict(public_couplings=runs,private_count=17)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--network-module',type=Path,default=Path(__file__).with_name('height_two_cut72_partial3555.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load(args.support_module,'_cut72_sparse_base');netmod=load(args.network_module,'_cut72_partial_network')
    dinic=base.load_dinic(args.dinic_module);checks=weighted_checks();controls=[]
    for item in templates(base):
        law,cert=construct(item,base,dinic)
        rec=dict(name=item['name'],shape=item['shape'],source_points=len(item['source']),source=sorted(item['source']),
                 whole_private_children=sorted(item['whole_private']),private_selection=item['points'],
                 **base.literal_checks(item),network=netmod.network(item,base,dinic),construction=cert,
                 law=base.check_law(item,law))
        controls.append(rec)
        print(json.dumps(dict(name=rec['name'],points=rec['source_points'],mincut=72,
                              gamma=rec['law']['gamma_envelope'],universal_gamma=rec['law']['universal_gamma'])))
    out=dict(scope='Actual controls for all five partial4455/k3/private22 cut72 shapes, including a whole-prefix variant. Ordinary exact arithmetic; no Lean verification or unrestricted arithmetic lift.',weighted_cut_checks=checks,controls=controls)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
