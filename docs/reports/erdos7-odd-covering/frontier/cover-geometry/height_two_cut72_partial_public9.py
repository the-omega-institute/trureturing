#!/usr/bin/env python3
"""Exact actual controls for all five partial public9/private1 cut72 placements."""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import argparse
import importlib.util
import json


def require(ok,message):
    if not ok:raise ValueError(message)


def load_module(path):
    spec=importlib.util.spec_from_file_location('_cut72_sparse_support',path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod


def weighted_checks():
    alpha=(Q(3,13),)+(Q(5,13),)*3
    beta=(Q(1,3),)+(Q(5,9),)*3
    slacks=[]
    for n in range(5):
        for aa in combinations(range(4),n):
            top=sum(alpha[r] for r in range(4) if r not in aa)
            if n<=1:slacks.append(top-1)
            else:
                total=sum(beta[r] for r in aa)
                slacks.append(top+total/2-1)
                slacks.extend(top+total-beta[j]-1 for j in aa)
    require(len(slacks)==44 and min(slacks)>=0,'all44 sufficient weighted inequalities')
    return dict(alpha=[str(x) for x in alpha],beta=[str(x) for x in beta],
                inequalities=len(slacks),minimum_slack=str(min(slacks)))


def templates(base):
    specs=[('3555_gap',(3,5,5,5),(0,2),True),
           ('3555_full',(3,5,5,5),(1,4),False),
           ('4455_gap',(4,4,5,5),(0,3),False),
           ('4455_partialfull',(4,4,5,5),(1,3),True),
           ('4455_full',(4,4,5,5),(2,4),False)]
    out=[]
    public=set(product(range(3),range(7)))
    for name,active,e,weighted in specs:
        private={(r,c): {(3,0)} if (r,c)==e else set()
                 for r in range(4) for c in range(active[r])}
        inactive=next(child for child in base.CHILDREN if child not in private)
        fibres={child:public|private[child] if child in private else set(base.ALL) for child in base.CHILDREN}
        retained={r:tuple(c for c in range(active[r]) if (r,c)!=e) for r in range(4)}
        require(all(len(retained[r])>=base.N[r]-2 for r in range(4)),'legal retained restrictions')
        caps=(Q(1),Q(9,26),Q(3,10),Q(27,130),Q(3,26),Q(1,10),Q(9,130),Q(1,18),Q(1,30)) if weighted else (
             Q(1),Q(1,3),Q(1,3),Q(1,4),Q(1,9),Q(1,9),Q(1,12),Q(1,18),Q(1,24))
        out.append(dict(name=name,active=active,public_columns=(0,1,2),public_leaves=(),private=private,
                        fibres=fibres,source={(r,c,g,h) for (r,c),ys in fibres.items() for g,h in ys},
                        cap=caps,weighted=weighted,exception=e,inactive=inactive,retained=retained))
    return out


def construct(item,base,dinic):
    law=defaultdict(Q)
    weighted=item['weighted'];bad=item['inactive'][0]
    if weighted:
        alpha={r:Q(3 if r==bad else 5,13) for r in range(4)}
        beta={r:Q(3 if r==bad else 5,9) for r in range(4)}
        den=351;weight=Q(9,10)
    else:
        alpha={r:Q(1,3) for r in range(4)};beta={r:Q(1,2) for r in range(4)}
        den=6;weight=Q(1)
    restrictions=[tuple(combinations(item['retained'][r],base.N[r]-2)) for r in range(4)]
    count=1
    for rr in restrictions:count*=len(rr)
    runs=0
    for choices in product(*restrictions):
        for g in range(3):
            caps={};start=('source',);finish=('sink',);owners={}
            for r,cc in enumerate(choices):
                require((den*alpha[r]).denominator==1 and (den*beta[r]/3).denominator==1,'integer coupling scale')
                caps[start,('root',r)]=int(den*alpha[r])
                for h in range(7):
                    caps[('root',r),('private_leaf',r,h)]=int(den*beta[r]/3)
                    actual=[(r,c,g,h) for c in cc if (g,h) in item['fibres'][r,c]]
                    if actual:
                        owners[r,h]=min(actual)
                        caps[('private_leaf',r,h),('common_leaf',h)]=den
            for h in range(7):caps[('common_leaf',h),finish]=den//3
            for r,s in combinations(range(4),2):
                require(len({h for rr,h in owners if rr in(r,s)})>=3,'actual pair premise each branch')
            value,flow,side=base.solve_network(caps,start,finish,den,dinic)
            require(value==den,'actual public coupling')
            for (u,v),f in flow.items():
                if u[0]=='private_leaf' and v[0]=='common_leaf' and f:
                    law[owners[u[1:]]]+=weight*Q(f,3*count*den)
            runs+=1
    require(runs==3*count,'every retained profile and branch coupled')
    extra=[]
    if weighted:
        r,c=item['inactive']
        # Candidate(3,0) is excluded; the other4 plus a full5 give9 guaranteed actual leaves.
        extra=[(r,c,3,h) for h in range(1,5)]+[(r,c,4,h) for h in range(5)]
        require(len(set(extra))==9 and all(p in item['source'] for p in extra),'nine external atoms at actual inactivechild')
        for p in extra:law[p]+=Q(1,90)
    return dict(law),dict(coupling_runs=runs,complete_restriction_profiles=count,
                          external_atoms=extra,alpha={str(r):str(v) for r,v in alpha.items()},
                          beta={str(r):str(v) for r,v in beta.items()})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support-module',type=Path,default=Path(__file__).with_name('height_two_cut72_sparse_laws.py'))
    parser.add_argument('--dinic-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();base=load_module(args.support_module);dinic=base.load_dinic(args.dinic_module)
    checks=weighted_checks();controls=[]
    for item in templates(base):
        law,certificate=construct(item,base,dinic)
        rec=dict(name=item['name'],source_points=len(item['source']),source=sorted(item['source']),
                 active_counts=item['active'],exceptional_private_child=item['exception'],
                 original_inactive_child=item['inactive'],weighted=item['weighted'],
                 **base.literal_checks(item),network=base.actual_network(item,dinic),
                 construction=certificate,law=base.check_law(item,law))
        controls.append(rec)
        print(json.dumps(dict(name=item['name'],points=rec['source_points'],mincut=72,
                              gamma=rec['law']['gamma_envelope'],universal_gamma=rec['law']['universal_gamma'])))
    out=dict(scope='Exact controls for all five partial public9/private1 cut72 placements. Ordinary rational arithmetic; no full cut72 classification, Lean verification or unrestricted arithmetic lift.',
             weighted_cut_checks=checks,controls=controls)
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':main()
