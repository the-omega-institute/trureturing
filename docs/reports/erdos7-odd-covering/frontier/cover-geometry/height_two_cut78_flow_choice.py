#!/usr/bin/env python3
"""Exact literal4555 source with mincut78 and both a bad and a good maxflow.
All masses/capacities are integer units1/63. No optimizer or Lean used.
"""
from itertools import combinations
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
from math import lcm
import argparse
import json
T=((2,2,2,0,0,0,0),(2,2,1,1,0,0,0),(2,0,0,0,0,0,0),(1,2,1,1,0,0,0),(0,1,1,0,0,0,0))
DIVS=(1,5,7,25,35,49,175,245,1225)
AXES=((1,1),(5,1),(1,7),(25,1),(5,7),(1,49),(25,7),(5,49),(25,49))
CAPS=(78,21,21,7,21,7,6,7,2)


def verify():
    checks=0
    def ck(p,m):
     nonlocal checks
     checks+=1
     if not p:raise ArithmeticError(m)
    source=set();bad={}
    for r in range(3):
     for c,row in enumerate(T):
      for h,z in enumerate(row):
       if z:source.add((r,c,r+1,h));bad[r,c,r+1,h]=z
      source.add((r,c,0,c))
     source.add((r,0,r+1,4))
    for c,z in enumerate((2,2,2,1)):
     source.add((3,c,4,0));source.add((3,c,4,c+1));bad[3,c,4,0]=z;bad[3,c,4,c+1]=2
    # Literal tree/blocking predicates directly from the actual support.
    def tree(proj,k):return sum(len({h for gg,h in proj if gg==g})>=k for g in range(7))>=k
    occupancy=[sorted({c for rr,c,g,h in source if rr==r}) for r in range(5)]
    ck(list(map(len,occupancy))==[5,5,5,4,0],'literal occupied children55540')
    projection={(g,h) for r,c,g,h in source};ck(tree(projection,5),'standalone five-ary height-two tree')
    blocking=0
    for r,s in combinations(range(4),2):
     for A in combinations(range(5),3):
      for B in combinations(range(5),3):
       proj={(g,h) for rr,c,g,h in source if (rr==r and c in A) or (rr==s and c in B)}
       ck(tree(proj,3),'literal pair/subset ternary-seven witness');blocking+=1
    ck(blocking==600,'all literal pair/triple tests')
    # Actual child network of447, integer units1/63.
    caps={}
    def edge(a,b,z):ck((a,b) not in caps,'one edge');caps[a,b]=z
    S=('source',);sink=('sink',)
    for r in range(4):
     edge(S,('r',r),21)
     for c in occupancy[r]:
      edge(('r',r),('c',r,c),7)
      for g in range(7):
       edge(('c',r,c),('pg',r,c,g),6)
       for h in range(7):edge(('pg',r,c,g),('ph',r,c,g,h),2)
    for g in range(7):
     edge(('cg',g),sink,21)
     for h in range(7):edge(('ch',g,h),('cg',g),7)
    for r,c,g,h in source:edge(('ph',r,c,g,h),('ch',g,h),126)
    cut={S,('r',3),('ch',4,0)}
    for c in occupancy[3]:
     cut.add(('c',3,c))
     for g in range(7):
      cut.add(('pg',3,c,g))
      for h in range(7):
       if not (g==4 and h==c+1):cut.add(('ph',3,c,g,h))
    cutedges=[(u,v,z) for (u,v),z in caps.items() if u in cut and v not in cut]
    ck(sum(z for u,v,z in cutedges)==78,'explicit cut78')
    ck(sorted(z for u,v,z in cutedges)==[2,2,2,2,7,21,21,21],'exact cut edge inventory')
    def verify_flow(atoms,name):
     ck(sum(atoms.values())==78,name+' value78');ck(set(atoms)<=source,name+' actual support')
     flow=defaultdict(int)
     for (r,c,g,h),z in atoms.items():
      ck(type(z)is int and z>=0,name+' nonnegative integral atom')
      path=(S,('r',r),('c',r,c),('pg',r,c,g),('ph',r,c,g,h),('ch',g,h),('cg',g),sink)
      for a,b in zip(path,path[1:]):flow[a,b]+=z
     balance=defaultdict(int)
     for uv,z in flow.items():
      ck(uv in caps and z<=caps[uv],name+' path capacity');a,b=uv;balance[a]-=z;balance[b]+=z
     ck(balance[S]==-78 and balance[sink]==78 and all(z==0 for v,z in balance.items() if v not in(S,sink)),name+' conservation')
     maxima=[];literal=0
     for d,(px,py),cap in zip(DIVS,AXES,CAPS):
      sums=defaultdict(int)
      for (r,c,g,h),z in atoms.items():sums[(r+5*c)%px,(g+7*h)%py]+=z
      for a in range(px):
       for b in range(py):ck(sums[a,b]<=cap,name+' all literal cylinder caps');literal+=1
      maxima.append(max(sums.values()))
     ck(literal==1767,name+' all1767 cylinders')
     capmap=dict(zip(DIVS,maxima));raw_lcm=sum(capmap[lcm(d,e)] for d in DIVS for e in DIVS)-78
     coherent=[]
     for x in range(25):
      for y in range(49):
       value=0
       for (r,c,g,h),z in atoms.items():
        n=sum((r+5*c-x)%px==0 and (g+7*h-y)%py==0 for px,py in AXES[1:]);value+=z*(n*n+2*n)
       coherent.append((value,x,y))
     attained=max(v for v,x,y in coherent);ck(raw_lcm==attained,name+' full orderedLCM envelope is attained by one coherent layout')
     return {'raw_nonunit_ordered_lcm_envelope':raw_lcm,'normalized_gamma_exact':str(1+F(raw_lcm,78)),'mass':'78/63','positive_atoms':sum(z>0 for z in atoms.values()),'max_cylinder_units':dict(zip(map(str,DIVS),maxima)),'coherent_raw_max_units':max(v for v,x,y in coherent),'coherent_maximizers':[[x,y] for v,x,y in coherent if v==max(t[0] for t in coherent)],'literal_cylinders_checked':literal,'atoms':[[*p,z] for p,z in sorted(atoms.items()) if z]}
    badresult=verify_flow(bad,'bad');ck(badresult['coherent_raw_max_units']==625,'bad attained625')
    good=dict(bad)
    for r in range(3):good[r,0,r+1,0]-=1;good[r,0,0,0]=1
    goodresult=verify_flow(good,'good');ck(goodresult['normalized_gamma_exact']=='691/78','good exact Gamma691/78');ck(goodresult['max_cylinder_units']['35']==20,'good root/column max20')
    coherent_upper=8*21+3*21+4*20+5*7+20*6+15*7+25*2
    ck(coherent_upper==621,'uniform coherent conic upper')
    noncoherent_upper=622
    ck(goodresult['coherent_raw_max_units']<=coherent_upper,'all coherent layouts below conic upper')
    bound=1+F(max(coherent_upper,noncoherent_upper),78);ck(bound==F(350,39) and bound<9,'all-layout normalized bound from449 analytic argument')
    out={'status':'PASS','checks':checks,'scope':'One literal source realizes cut78, a bad maxflow attaining625/63, and a rerouted good maxflow. This refutes arbitrary-maxflow success, not existence of a good law for the uniform source class. Each exact Gamma uses its full81-pair orderedLCM envelope and a matching coherent layout; no general phase theorem or optimizer is needed.','source_points':len(source),'source':list(map(list,sorted(source))),'occupied_children':occupancy,'literal_blocking_checks':blocking,'standalone_tree':True,'network_edges':len(caps),'cut_numerator':78,'cut_denominator':63,'cut_edges':[[list(u),list(v),z] for u,v,z in cutedges],'bad_flow':badresult,'good_flow':goodresult,'bad_normalized_gamma':'703/78','good_normalized_gamma_exact':goodresult['normalized_gamma_exact'],'good_normalized_gamma_general_cap_upper':str(bound),'good_coherent_upper_units':coherent_upper,'all_layout_noncoherent_upper_units':noncoherent_upper}
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'),
                        help='exact result path (default: sibling .json)')
    args=parser.parse_args()
    payload=json.dumps(verify(),indent=2)+'\n'
    args.output.write_text(payload,encoding='utf-8')
    print(payload,end='')


if __name__=='__main__':
    main()
