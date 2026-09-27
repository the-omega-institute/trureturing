#!/usr/bin/env python3
"""Actual68-point cut77 source with a bad-neighborhood near20 block.
An explicit one-unit cross-block transfer repairs the same actual flow.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from importlib.util import spec_from_file_location,module_from_spec
from math import lcm
from pathlib import Path
import argparse,json

def require(ok,message):
    if not ok:raise ValueError(message)

def verify(base_module):
    occupancy=(5,5,5,4,0);owner=(0,2,3,4,5)
    E={(0,0):2,(0,1):2,(0,2):2,(1,0):2,(1,1):2,
       (2,0):2,(2,1):2,(4,0):1,(4,1):1,(4,3):2,(4,4):2}
    source={(0,c,1,h) for c,h in E}|{(0,0,0,0)}
    source|={(0,c,owner[c],h) for c in range(1,5) for h in range(3)}
    source|={(r,c,owner[c],h) for r in (1,2) for c in range(5) for h in range(3)}
    source|={(1,c,owner[c],h) for c in range(3) for h in (3,4)}
    source.add((1,0,1,5))
    gap={(3,c,6,h) for c,hs in enumerate(((0,),(1,2),(3,4),(5,6))) for h in hs}
    source|=gap
    require(len(source)==68,'68 actual points')
    require(tuple(len({c for rr,c,g,h in source if rr==r}) for r in range(5))==occupancy,'literal4555 occupancy')
    fibres={(r,c):{(g,h) for rr,cc,g,h in source if (rr,cc)==(r,c)} for r in range(5) for c in range(5)}
    def tree(ys,k):return sum(len({h for g,h in ys if g==j})>=k for j in range(7))>=k
    require(tree({(g,h) for r,c,g,h in source},5),'standalone five-tree')
    robust=[]
    for r in range(4):
        if all(tree(set().union(*(fibres[r,c] for c in cs)),3) for cs in combinations(range(5),3)):
            robust.append(r)
    require(robust==[0,1,2],'three full roots individually robust')
    pair_tests=0
    for r,s in combinations(range(4),2):
        for aa in combinations(range(occupancy[r]),occupancy[r]-2):
            for bb in combinations(range(occupancy[s]),occupancy[s]-2):
                require(tree(set().union(*(fibres[r,c] for c in aa),*(fibres[s,c] for c in bb)),3),'selected pair literal tree')
                pair_tests+=1
    full_tests=0
    for rr in combinations(range(5),3):
        for choices in product(tuple(combinations(range(5),3)),repeat=3):
            require(tree(set().union(*(fibres[r,c] for r,cs in zip(rr,choices) for c in cs)),3),'full literal product')
            full_tests+=1
    require((pair_tests,full_tests)==(480,10000),'literal test counts')
    actualE={(c,h) for r,c,g,h in source if (r,g)==(0,1)}
    require(actualE==set(E),'bad block is entire actual support, not just chosen positives')
    require({h for c,h in actualE if c in (1,2,3)}=={0,1},'actual three-row condition fails')
    S,T=('source',),('sink',);caps={}
    def edge(u,v,cap):
        require((u,v) not in caps,'unique network edge');caps[u,v]=cap
    for r in range(4):
        edge(S,('r',r),21)
        for c in range(occupancy[r]):
            edge(('r',r),('c',r,c),7)
            for g in range(7):
                edge(('c',r,c),('pg',r,c,g),6)
                for h in range(7):edge(('pg',r,c,g),('ph',r,c,g,h),2)
    for g in range(7):
        edge(('cg',g),T,21)
        for h in range(7):edge(('ch',g,h),('cg',g),7)
    for r,c,g,h in sorted(source):edge(('ph',r,c,g,h),('ch',g,h),126)
    inside={S,('r',3)}
    for c in range(4):
        inside.add(('c',3,c))
        for g in range(7):
            inside.add(('pg',3,c,g))
            for h in range(7):
                if (3,c,g,h) not in gap:inside.add(('ph',3,c,g,h))
    cut=[(u,v,cap) for (u,v),cap in caps.items() if u in inside and v not in inside]
    require(sorted(cap for u,v,cap in cut)==[2]*7+[21]*3,'exact cut77')
    spec=spec_from_file_location('_existing_dinic',base_module);module=module_from_spec(spec);spec.loader.exec_module(module)
    ids={u:i for i,u in enumerate(sorted({u for uv in caps for u in uv}))};graph=module.Dinic(len(ids))
    for (u,v),cap in caps.items():graph.add(ids[u],ids[v],cap)
    require(graph.flow(ids[S],ids[T],1000)==77,'maximum flow77')
    bad={(0,c,1,h):v for (c,h),v in E.items()}
    bad[0,0,0,0]=1
    for r in (1,2):
        for c in range(5):
            for h in range(3):bad[r,c,owner[c],h]=2 if c<2 else 1
    bad[1,0,0,0]-=1;bad[1,0,1,5]=1
    bad.update({p:2 for p in gap})
    good=dict(bad);good[0,0,1,0]-=1;good[0,0,0,0]+=1
    cycle=dict(good);cycle[1,0,0,1]-=1;cycle[1,0,1,5]+=1
    axes=((1,1),(5,1),(1,7),(25,1),(5,7),(1,49),(25,7),(5,49),(25,49))
    divisors=tuple(a*b for a,b in axes);coeff=(3,3,5,9,5,15,15,25)
    caplist=(77,21,21,7,21,7,6,7,2)
    def check_flow(atoms):
        require(set(atoms)<=source and all(type(v) is int and v>0 for v in atoms.values()),'positive actual integer law')
        require(sum(atoms.values())==77,'unchanged total77')
        flow=defaultdict(int)
        for (r,c,g,h),v in atoms.items():
            path=(S,('r',r),('c',r,c),('pg',r,c,g),('ph',r,c,g,h),('ch',g,h),('cg',g),T)
            for u,w in zip(path,path[1:]):flow[u,w]+=v
        balance=defaultdict(int)
        for (u,v),cap in caps.items():
            require(0<=flow[u,v]<=cap,'all edge capacities')
            balance[u]-=flow[u,v];balance[v]+=flow[u,v]
        require(balance[S]==-77 and balance[T]==77 and all(v==0 for u,v in balance.items() if u not in (S,T)),'all-node conservation')
        require(all(flow[u,v]==cap for u,v,cap in cut),'all forward cut arcs saturated')
        require(all(flow[u,v]==0 for u,v in caps if u not in inside and v in inside),'all backward cut arcs zero')
        tables=[];maxima=[];count=0
        for (a,b),cap in zip(axes,caplist):
            vals=defaultdict(int)
            for (r,c,g,h),v in atoms.items():vals[(r+5*c)%a,(g+7*h)%b]+=v
            for x,y in product(range(a),range(b)):
                require(vals[x,y]<=cap,'literal cylinder capacity');count+=1
            tables.append(vals);maxima.append(max(vals.values()))
        centres=[]
        for x,y in product(range(25),range(49)):
            masses=[vals[x%a,y%b] for vals,(a,b) in zip(tables[1:],axes[1:])]
            K=sum(co*v for co,v in zip(coeff,masses));centres.append((K,x,y,masses))
        maximum=max(K for K,x,y,ms in centres);maxmap=dict(zip(divisors,maxima))
        envelope=sum(maxmap[lcm(d,e)] for d,e in product(divisors,repeat=2))-77
        return {'atoms':[[*p,v] for p,v in sorted(atoms.items())], 'coarse_masses':{
                  'root0':sum(v for (r,c,g,h),v in atoms.items() if r==0),
                  'column1':sum(v for (r,c,g,h),v in atoms.items() if g==1),
                  'root0_column1':sum(v for (r,c,g,h),v in atoms.items() if (r,g)==(0,1))},
                'cylinder_maxima':dict(zip(map(str,divisors),maxima)),'cylinders_checked':count,
                'maximum_coherent_charge':maximum,'maximizers':[[x,y,ms] for K,x,y,ms in centres if K==maximum],
                'coherent_gamma_lower':str(1+Q(maximum,77)),'nonunit_lcm_upper':envelope,
                'all_layout_lcm_upper':str(1+Q(envelope,77))}
    bad_result=check_flow(bad);good_result=check_flow(good);cycle_result=check_flow(cycle)
    require(bad_result['coarse_masses']=={'root0':21,'column1':21,'root0_column1':20},'bad dangerous block')
    require(bad_result['maximum_coherent_charge']==621 and Q(bad_result['coherent_gamma_lower'])>9,'bad flow has Gamma>9')
    require(good_result['coarse_masses']=={'root0':21,'column1':20,'root0_column1':19},'one-unit cross-block repair')
    require(good_result['nonunit_lcm_upper']==609 and Q(good_result['all_layout_lcm_upper'])==Q(686,77)<9,'good complete-LCM certificate')
    require(set(bad)==set(good)==set(cycle),'both repairs preserve exact positive support')
    require(cycle_result['coarse_masses']=={'root0':21,'column1':21,'root0_column1':19},'four-atom block change')
    require(cycle_result['nonunit_lcm_upper']==612 and Q(cycle_result['all_layout_lcm_upper'])==Q(689,77)<9,'four-atom complete-LCM certificate')
    for r in range(5):
        for c in range(5):
            require(sum(v for (rr,cc,g,h),v in bad.items() if (rr,cc)==(r,c))==sum(v for (rr,cc,g,h),v in cycle.items() if (rr,cc)==(r,c)),'cycle preserves every child and therefore root mass')
    for g in range(7):
        require(sum(v for (r,c,gg,h),v in bad.items() if gg==g)==sum(v for (r,c,gg,h),v in cycle.items() if gg==g),'cycle preserves every public column mass')
    # Exact uniqueness certificate for the original isolated mass20 block.
    forced={e for e in E if e[0]!=4}
    require(len(forced)==7 and all(E[e]==2 for e in forced),'local row4+7cell cut20')
    room={h:min(2,7-sum(E.get((c,h),0) for c in range(4))) for h in (0,1,3,4)}
    require(room=={0:1,1:1,3:2,4:2} and sum(room.values())==6,'local unique rational completion')
    require(not any(h==5 for c,h in actualE),'external public unit flags unused fine column5')
    return {'source_points':len(source),'source':sorted(source),'occupancy':occupancy,'robust_roots':robust,
            'standalone_five_tree':True,'pair_tests':pair_tests,'full_literal_tests':full_tests,
            'network_edges':len(caps),'minimum_cut':77,'cut_edges':[[list(u),list(v),cap] for u,v,cap in cut],
            'actual_bad_block':{'root':0,'column':1,'rows':[1,2,3],'neighbor_union':[0,1],
                 'unique_mass20_law':[[c,h,v] for (c,h),v in sorted(E.items())],
                 'forced_local_score':310,'flagged_column':5},
            'fixed_coarse_obstruction':{'a':21,'d':20,'b':21,'forced_local_score':310,'coherent_raw_lower':616,'gamma_lower':'9','reason':'The actual20 matrix is unique. At its row0/leaf0 cell S=310; every77 law with these coarse masses has K=306+S+5z+5y>=616, with z,y>=0.'},
            'bad_flow':bad_result,'repaired_flow':good_result,'cycle_repaired_flow':cycle_result,
            'scope':'Literal4555 plus standalone and mincut77 do not make every dangerous actual block satisfy the three-row property. The example has three individually robust roots, so existing good-law theorems already apply. A displayed same-positive-support cross-block move also gives a good law. No counterexample to good-law existence, original odd covering, or outside-cofactor lift.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();out=verify(args.base_module)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ('source_points','pair_tests','full_literal_tests','network_edges','minimum_cut','robust_roots')}))
    print(json.dumps({'bad_coherent_charge':out['bad_flow']['maximum_coherent_charge'],'repaired_lcm_upper':out['repaired_flow']['all_layout_lcm_upper'],'cycle_lcm_upper':out['cycle_repaired_flow']['all_layout_lcm_upper']}))
if __name__=='__main__':main()
