#!/usr/bin/env python3
"""Actual maximum74 control with two genuine maximal mass18 entries."""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import json
import runpy


def req(ok,msg):
    if not ok:raise ValueError(msg)


def margins(atom):
    root=defaultdict(Q);block=defaultdict(Q);row=defaultdict(Q)
    col=defaultdict(Q);fine=defaultdict(Q);cell=defaultdict(Q)
    for (r,c,g,h),m in atom.items():
        root[r]+=m;block[r,g]+=m;row[r,c,g]+=m
        col[g]+=m;fine[g,h]+=m;cell[r,g,h]+=m
    return root,block,row,col,fine,cell


def charge(atom,c,h):
    root,block,row,col,fine,cell=margins(atom)
    a=root[0];b=col[0];d=block[0,0]
    r=row[0,c,0];cc=cell[0,0,h];x=atom.get((0,c,0,h),Q())
    z=sum(m for (rr,child,g,hh),m in atom.items() if rr==0 and child==c and g!=0)
    y=fine[0,h]-cc
    return 3*a+3*b+9*d+20*r+20*cc+25*x+5*z+5*y,dict(
        a=str(a),b=str(b),d=str(d),r=str(r),c=str(cc),x=str(x),z=str(z),y=str(y))


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--base-helper',type=Path,required=True)
    p.add_argument('--network-helper',type=Path,required=True)
    p.add_argument('--source-helper',type=Path,required=True)
    args=p.parse_args()
    base=runpy.run_path(str(args.base_helper))
    network=runpy.run_path(str(args.network_helper))
    checker=runpy.run_path(str(args.source_helper))['source_checks']
    source,template=base['fixture']()
    for c in (0,1):source[0,c]={(g,h) for g,h in source[0,c] if g!=0 or h in (0,1)}
    old={point:Q(m) for point,m in template.items() if point[0]!=0 and point[2]!=0}
    for c,entries in enumerate((((0,2),(1,2)),((0,2),(1,2)),
                               ((0,2),(1,2),(2,2)),((0,1),(1,1),(3,2)))):
        for h,m in entries:old[0,c,0,h]=Q(m)
    old[0,2,1,0]=Q(1,2)
    for c in range(5):old[1,c,0,2]=Q(1,2)
    old[2,0,0,3]=Q(1,2)
    flat={(r,c,g,h) for (r,c),labels in source.items() for g,h in labels}
    children,pairs,mono=checker(flat)
    edges,trails=network['paths'](source)
    edgeA=(('P',0,2,0),('L',0,2,0,0))
    edgeB=(('P',0,2,0),('L',0,2,0,1))

    def check(atom,lowered):
        load=defaultdict(Q)
        for point,m in atom.items():
            req(point in flat and m>=0 and 2*m==int(2*m),'same actual half-integral atom')
            for e in trails[point]:load[e]+=m
        for e,cap in edges.items():
            bound=Q(37,2) if e[0]==('S',) else Q(3,2) if e in lowered else cap
            req(0<=load[e]<=bound,'every live original or lowered capacity')
        req(sum(atom.values())==74,'same value74')
        req(all(load[(('S',),('R',r))]==Q(37,2) for r in range(4)),'balanced roots')
        return load

    oldload=check(old,set())
    cut=[e for e in edges if base['original_cut_side'](e[0]) and not base['original_cut_side'](e[1])]
    req(sum(edges[e] for e in cut)==74,'matching original cut74')
    req(all(oldload[e]==edges[e] for e in cut),'original forward equality')
    req(all(oldload[e]==0 for e in edges if not base['original_cut_side'](e[0]) and base['original_cut_side'](e[1])),
        'original zero backward flow')
    for h in (0,1):
        K,read=charge(old,2,h)
        req(K==593 and read==dict(a='37/2',b='21',d='18',r='6',c='7',x='2',z='1/2',y='0'),
            'two genuine GE1 maximal entries')
    one=dict(old)
    for point,delta in (((0,2,1,0),Q(1,2)),((1,0,0,0),Q(1,2)),
                        ((1,0,1,0),-Q(1,2)),((0,2,0,0),-Q(1,2))):
        one[point]=one.get(point,Q())+delta
    check(one,{edgeA})
    both=dict(one)
    for point,delta in (((0,2,1,0),Q(1,2)),((1,1,0,1),Q(1,2)),
                        ((1,1,1,1),-Q(1,2)),((0,2,0,1),-Q(1,2))):
        both[point]=both.get(point,Q())+delta
    check(both,{edgeA,edgeB})
    req(margins(old)[3]==margins(one)[3]==margins(both)[3],'same public coarse column totals')
    req(one[0,2,0,0]==Q(3,2) and both[0,2,0,0]==both[0,2,0,1]==Q(3,2),
        'actual entry cap reduction')
    queries={name:[dict(fine=h,K=str(charge(atom,2,h)[0]),readings=charge(atom,2,h)[1]) for h in(0,1)]
             for name,atom in (('initial',old),('one_entry',one),('both_entries',both))}
    req([q['K'] for q in queries['initial']]==['593','593'],'initial actual coherent charges')
    req([q['K'] for q in queries['one_entry']]==['561','581'],'individual reduction actual charges')
    req([q['K'] for q in queries['both_entries']]==['549','549'],'joint reduction actual charges')
    out=dict(status='PASS',scope='One complete actual original-maximum74 source with two genuine GE1 entries; explicit individual and joint reductions. No universal common-law closure.',
             actual_points=len(flat),live_edges=len(edges),pair_checks=pairs,
             original_maximum=74,balanced_total=74,genuine_bad_entries=[[0,2,0,0],[0,2,0,1]],
             query_checks=queries,
             source=[dict(root=r,child=c,whole_fibre=sorted(labels))for(r,c),labels in sorted(source.items())],
             initial_flow=[dict(point=p,mass=str(m))for p,m in sorted(old.items())if m],
             one_entry_flow=[dict(point=p,mass=str(m))for p,m in sorted(one.items())if m],
             both_entries_flow=[dict(point=p,mass=str(m))for p,m in sorted(both.items())if m])
    args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in('source','initial_flow','one_entry_flow','both_entries_flow')}))


if __name__=='__main__':main()
