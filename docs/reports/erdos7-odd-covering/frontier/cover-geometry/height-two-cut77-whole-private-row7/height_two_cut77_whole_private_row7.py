#!/usr/bin/env python3
"""Actual253-point controls for the last whole-private k0 cut77 shape.
Ordinary exact controls, not Lean or unrestricted cut77 closure.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations,product,combinations_with_replacement
from math import lcm
from pathlib import Path
import json

def req(p,message):
    if not p:raise ValueError(message)

def row2_vectors():
    cols=range(7);found=[]
    for vv in combinations_with_replacement(cols,4):
        v=[vv.count(g)for g in cols]
        for uu in combinations_with_replacement(cols,2):
            u=[uu.count(g)for g in cols]
            for w in cols:
                total=[v[g]+2*u[g]+int(g==w)for g in cols]
                if sorted(x for x in total if x)==[3,3,3]:
                    req(sorted(x for x in v if x) in ([1,3],[1,1,2]),'two fixed-gap column vector shapes')
                    req(sorted(x for x in u if x)==[1,1],'one leaf in each full-double column')
                    found.append({'gap_vector':v,'full_double_vector':u,'singleton_column':w})
    req(len(found)==315,'315 labelled vector solutions')
    return found

def construct(same_column):
    n=(5,5,5,4,0);J=5;K=4;W=4 if same_column else 6
    fixed={(1,c,g,c)for c in range(5)for g in(0,1)}|{(2,c,g,c)for c in range(5)for g in(2,3)}
    fixed|={(3,0,K,0),(3,1,K,1),(3,1,K,2),(3,2,K,3),(3,2,K,4)}
    whole={(3,3,W,h)for h in range(7)}
    E={(0,0):2,(0,1):2,(0,2):2,(1,0):2,(1,1):2,(2,0):2,(2,1):2,(4,0):1,(4,1):1,(4,3):2,(4,4):2}
    source=fixed|whole|{(0,c,g,h)for c in range(5)for g in range(7)if g!=J for h in range(7)}|{(0,c,J,h)for c,h in E}
    req(len(source)==253,'253 actual points')
    old={p:2 for p in fixed};old.update({(3,3,W,h):2 for h in range(3)})
    old.update({(0,c,J,h):v for(c,h),v in E.items()});old[0,0,0,0]=1
    good=dict(old);good[0,0,J,0]-=1;good[0,0,0,0]+=1
    fibres=defaultdict(set)
    for r,c,g,h in source:fibres[r,c].add((g,h))
    req(tuple(sum(rr==r for rr,c in fibres)for r in range(5))==n,'occupancy4555')
    def tree(ps,k):return sum(len({h for gg,h in ps if gg==g})>=k for g in range(7))>=k
    pairs=literal=0
    for r,s in combinations(range(4),2):
      for aa in combinations(range(n[r]),n[r]-2):
       for bb in combinations(range(n[s]),n[s]-2):
        req(tree(set().union(*(fibres[r,c]for c in aa),*(fibres[s,c]for c in bb)),3),'selected literal pair');pairs+=1
    for rr in combinations(range(5),3):
      for picks in product(tuple(combinations(range(5),3)),repeat=3):
        req(tree(set().union(*(fibres[r,c]for r,cs in zip(rr,picks)for c in cs)),3),'complete literal blocker');literal+=1
    req((pairs,literal)==(480,10000) and tree({(g,h)for r,c,g,h in source},5),'literal and standalone inventory')
    robust=[r for r in range(4)if all(tree(set().union(*(fibres[r,c]for c in cs)),3)for cs in combinations(range(5),3))]
    req(robust==[0],'one individually robust root')
    badtriples=[list(cs)for cs in combinations(range(5),3)if len({h for r,c,g,h in source if r==0 and c in cs and g==J})<3]
    req([1,2,3]in badtriples,'actual target fails T3')
    S,T=('source',),('sink',);caps={}
    def edge(u,v,c):
        req((u,v)not in caps,'unique arc');caps[u,v]=c
    for r in range(4):
      edge(S,('r',r),21)
      for c in range(n[r]):
        edge(('r',r),('c',r,c),7)
        for g in range(7):
          edge(('c',r,c),('pg',r,c,g),6)
          for h in range(7):edge(('pg',r,c,g),('ph',r,c,g,h),2)
    for g in range(7):
      edge(('cg',g),T,21)
      for h in range(7):edge(('ch',g,h),('cg',g),7)
    for r,c,g,h in source:edge(('ph',r,c,g,h),('ch',g,h),126)
    inside={S}
    for r in(1,2,3):
      inside.add(('r',r))
      for c in range(n[r]):
        inside.add(('c',r,c))
        for g in range(7):
          if(r,c,g)==(3,3,W):continue
          inside.add(('pg',r,c,g))
          inside.update(('ph',r,c,g,h)for h in range(7)if(r,c,g,h)not in fixed)
    cut={uv:c for uv,c in caps.items()if uv[0]in inside and uv[1]not in inside}
    req(sorted(cut.values())==[2]*25+[6,21]and sum(cut.values())==77,'inactive21 plus25leaves2 pluswhole6 cut')
    def check(atoms):
      req(set(atoms)<=source and all(type(v)is int and v>0 for v in atoms.values())and sum(atoms.values())==77,'actual integral flow77')
      flow=defaultdict(int);bal=defaultdict(int);roots=defaultdict(int);blocks=defaultdict(int);external=defaultdict(int)
      for(r,c,g,h),v in atoms.items():
        roots[r]+=v;blocks[r,g]+=v
        if r:external[g,h]+=v
        path=(S,('r',r),('c',r,c),('pg',r,c,g),('ph',r,c,g,h),('ch',g,h),('cg',g),T)
        for u,w in zip(path,path[1:]):flow[u,w]+=v
      for(u,v),cap in caps.items():
        req(0<=flow[u,v]<=cap,'all capacities');bal[u]-=flow[u,v];bal[v]+=flow[u,v]
      req(bal[S]==-77 and bal[T]==77 and all(v==0 for u,v in bal.items()if u not in(S,T)),'conservation')
      req(all(flow[uv]==c for uv,c in cut.items()),'forward cut saturation')
      req(all(flow[u,v]==0 for u,v in caps if u not in inside and v in inside),'zero backward cut flow')
      req(all(v<=6 for v in external.values()),'no saturated fine leaf after subtracting inactive root')
      req(dict(roots)=={1:20,2:20,3:16,0:21},'forced root totals')
      danger=sorted([r,g]for(r,g),v in blocks.items()if roots[r]==21 and v==20)
      def crt(p):
        r,c,g,h=p;x=r+5*c;y=g+7*h;return x+25*((y-x)*2%49)
      mods=(1,5,7,25,35,49,175,245,1225)
      maxima={m:max(sum(v for p,v in atoms.items()if crt(p)%m==a)for a in range(m))for m in mods}
      env=Fraction(sum(maxima[lcm(a,b)]for a,b in product(mods,repeat=2)),77)
      return {'atoms':[[*p,v]for p,v in sorted(atoms.items())],'root_totals':dict(roots),'joint_blocks':[[*p,v]for p,v in sorted(blocks.items())],'external_fine_max':max(external.values()),'dangerous_blocks':danger,'lcm_envelope':str(env)}
    before,after=check(old),check(good)
    req(before['dangerous_blocks']==[[0,J]]and after['dangerous_blocks']==[],'actual two-unit repair removes danger')
    after['SH1_all_layout_bound']='691/77'
    return {'scope':'Actual row7 whole-private source for one-inactive-full-root cut77. Ordinary exact finite control, not Lean.','whole_equals_gap_finite_column':same_column,'whole_column':W,'gap_finite_column':K,'source_points':len(source),'source':sorted(source),'private_shape':[[2]*5,[2]*5,[1,2,2,3]],'pair_tests':pairs,'literal_tests':literal,'robust_roots':robust,'bad_T3_triples':badtriples,'network_edges':len(caps),'minimum_cut':77,'cut':[[list(u),list(v),c]for(u,v),c in sorted(cut.items())],'old_flow':before,'repaired_flow':after}

def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();out={'row2_column_vectors':row2_vectors(),'controls':[construct(True),construct(False)]}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'row2_vectors':len(out['row2_column_vectors']),'controls':[{'whole_equals_K':d['whole_equals_gap_finite_column'],'points':d['source_points'],'old_envelope':d['old_flow']['lcm_envelope'],'new_envelope':d['repaired_flow']['lcm_envelope']}for d in out['controls']]}))
if __name__=='__main__':main()
