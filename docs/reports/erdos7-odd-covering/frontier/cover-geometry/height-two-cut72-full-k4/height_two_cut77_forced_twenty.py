#!/usr/bin/env python3
"""Literal4555 source of mincut77 forces a root/column block to remain20.
Its positive support still permits a good fractional redistribution.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from importlib.util import spec_from_file_location,module_from_spec
from math import lcm
from pathlib import Path
import argparse,json

def require(ok,msg):
    if not ok:raise ValueError(msg)

def verify(base):
    n=(5,5,5,4,0)
    source={(r,c,0,h) for r in range(4) for c in range(n[r]) for h in range(7)}
    block={(0,c,1,h) for c in range(5) for h in (0,1)}|{(0,c,1,c+2) for c in range(3)}
    private={(1,c,2,c) for c in range(5)}|{(1,0,2,5)}|{(2,c,3,c) for c in range(5)}
    private|={(3,c,4,h) for c,hs in enumerate(((0,),(1,2),(3,4),(5,6))) for h in hs}
    source|=block|private
    require(len(source)==164 and len(block)==13 and len(private)==18,'source sizes')
    fibres={(r,c):{(g,h) for rr,cc,g,h in source if (rr,cc)==(r,c)} for r in range(5) for c in range(5)}
    def tree(ys,k):return sum(len({h for g,h in ys if g==a})>=k for a in range(7))>=k
    require(tree({(g,h) for r,c,g,h in source},5),'standalone5-tree')
    pair_tests=0
    for r,s in combinations(range(4),2):
        for aa in combinations(range(n[r]),n[r]-2):
            for bb in combinations(range(n[s]),n[s]-2):
                require(tree(set().union(*(fibres[r,c] for c in aa),*(fibres[s,c] for c in bb)),3),'selected pair tree')
                pair_tests+=1
    literal_tests=0
    for rr in combinations(range(5),3):
        for choices in product(tuple(combinations(range(5),3)),repeat=3):
            require(tree(set().union(*(fibres[r,c] for r,cs in zip(rr,choices) for c in cs)),3),'complete literal product blocking')
            literal_tests+=1
    require((pair_tests,literal_tests)==(480,10000),'all literal counts')
    for cs in combinations(range(5),3):
        require(len({h for r,c,g,h in block if c in cs})>=3,'root0 internal triple property')
    S,T=('source',),('sink',)
    caps={}
    def edge(u,v,cap):
        require((u,v) not in caps,'unique edge');caps[u,v]=cap
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
    private_cut=private|{(0,c,1,c+2) for c in range(3)}
    inside={S,('cg',0)}|{('ch',0,h) for h in range(7)}|{('ch',1,0),('ch',1,1)}
    for r in range(4):
        inside.add(('r',r))
        for c in range(n[r]):
            inside.add(('c',r,c))
            for g in range(7):
                inside.add(('pg',r,c,g))
                for h in range(7):
                    if (r,c,g,h) not in private_cut:inside.add(('ph',r,c,g,h))
    cut=[(u,v,cap) for (u,v),cap in caps.items() if u in inside and v not in inside]
    require(sorted(cap for u,v,cap in cut)==[2]*21+[7]*2+[21],'cut21+14+42=77')
    require(not any(u[0]=='ph' for u,v,cap in cut),'no actual bridge crosses')
    spec=spec_from_file_location('existing_dinic',base);module=module_from_spec(spec);spec.loader.exec_module(module)
    ids={u:i for i,u in enumerate(sorted({u for uv in caps for u in uv}))}
    graph=module.Dinic(len(ids))
    for (u,v),cap in caps.items():graph.add(ids[u],ids[v],cap)
    require(graph.flow(ids[S],ids[T],1000)==77,'exact maximum77')
    bad={p:2 for p in private}
    for c,amount in enumerate((2,2,1,1,1)):
        for h in (0,1):bad[0,c,1,h]=amount
    for c in range(3):bad[0,c,1,c+2]=2
    common={(0,0,0,0):1,(1,0,0,0):1,(3,0,0,5):2}
    common.update({(1,c,0,c):2 for c in range(1,5)})
    common.update({(2,c,0,c):2 if c<4 else 1 for c in range(5)})
    require(sum(common.values())==21,'common total21')
    bad.update(common)
    good={p:Q(v) for p,v in bad.items() if p not in block}
    for c in range(5):
        for h in (0,1):good[0,c,1,h]=Q(7,5)
    for c in range(3):good[0,c,1,c+2]=Q(2)
    axes=((1,1),(5,1),(1,7),(25,1),(5,7),(1,49),(25,7),(5,49),(25,49))
    ds=tuple(a*b for a,b in axes);coeff=(3,3,5,9,5,15,15,25)
    def law_check(atoms):
        require(set(atoms)<=source and sum(atoms.values())==77,'actual total77 law')
        flow=defaultdict(Q)
        for (r,c,g,h),v in atoms.items():
            path=(S,('r',r),('c',r,c),('pg',r,c,g),('ph',r,c,g,h),('ch',g,h),('cg',g),T)
            for u,w in zip(path,path[1:]):flow[u,w]+=v
        balance=defaultdict(Q)
        for (u,v),cap in caps.items():
            require(0<=flow[u,v]<=cap,'all edge capacities')
            balance[u]-=flow[u,v];balance[v]+=flow[u,v]
        require(balance[S]==-77 and balance[T]==77 and all(v==0 for u,v in balance.items() if u not in (S,T)),'all conservation')
        require(all(flow[u,v]==cap for u,v,cap in cut),'forward cut saturated')
        require(all(flow[u,v]==0 for u,v in caps if u not in inside and v in inside),'backward cut zero')
        matrices=[];maxima=[];cylinders=0
        for a,b in axes:
            vals=defaultdict(Q)
            for (r,c,g,h),v in atoms.items():vals[(r+5*c)%a,(g+7*h)%b]+=v
            matrices.append(vals);maxima.append(max(vals.values()))
            cylinders+=a*b
        coherent=[]
        for x,y in product(range(25),range(49)):
            masses=[vals[x%a,y%b] for vals,(a,b) in zip(matrices[1:],axes[1:])]
            coherent.append((sum(co*v for co,v in zip(coeff,masses)),x,y,masses))
        maxcoherent=max(row[0] for row in coherent)
        maxmap=dict(zip(ds,maxima))
        envelope=sum(maxmap[lcm(a,b)] for a,b in product(ds,repeat=2))-77
        return {'atoms':[[*p,str(v)] for p,v in sorted(atoms.items())], 'maximum_coherent_charge':str(maxcoherent),
                'maximizers':[[x,y,list(map(str,ms))] for k,x,y,ms in coherent if k==maxcoherent],
                'cylinder_maxima':dict(zip(map(str,ds),map(str,maxima))), 'cylinders_checked':cylinders,
                'nonunit_lcm_upper':str(envelope),'normalized_lcm_upper':str(1+envelope/77)}
    badinfo=law_check(bad);goodinfo=law_check(good)
    require(set(good)==set(bad) and all(v>0 for v in good.values()),
            'fractional repair preserves exact positive support')
    # The fixed internal block can also coexist with a successful external
    # reroute: lowering its root mass removes the a21,d20 obstruction.
    rerouted=dict(bad)
    rerouted[0,0,0,0]-=1
    rerouted[2,4,0,4]+=1
    rerouted={p:v for p,v in rerouted.items() if v}
    reroutedinfo=law_check(rerouted)
    root_mass={r:sum(v for (rr,c,g,h),v in rerouted.items() if rr==r) for r in range(5)}
    block_mass={(r,g):sum(v for (rr,c,gg,h),v in rerouted.items() if (rr,gg)==(r,g))
                for r in range(5) for g in range(7)}
    require(root_mass[0]==20 and block_mass[0,1]==20,'reroute keeps internal20 but lowers root')
    require(not any(root_mass[r]==21 and v==20 for (r,g),v in block_mass.items()),
            'existing SH1 premise holds after the external reroute')
    reroutedinfo['all_layout_upper_from_SH1']='691/77'
    require(badinfo['maximum_coherent_charge']=='618','bad near20 has coherent618')
    require(Q(goodinfo['nonunit_lcm_upper'])==597,'good full LCM upper597')
    require(Q(goodinfo['normalized_lcm_upper'])==Q(674,77)<9,'same-source good law')
    # The fixed minimum cut forces both G public leaves to7 and each of its three other points to2.
    require({p for p in source if p[2]==1}==block,'G is exclusive to root0')
    require(all((('ch',1,h),('cg',1),7) in cut for h in (0,1)),'both G public leaves are cut')
    require(all((('pg',0,c,1),('ph',0,c,1,c+2),2) in cut for c in range(3)),'three G private leaves are cut')
    return {'source_points':len(source),'source':sorted(source),'occupancy':n,'pair_tests':pair_tests,'literal_tests':literal_tests,
            'standalone5_tree':True,'network_edges':len(caps),'minimum_cut':77,'cut':[[list(u),list(v),cap] for u,v,cap in cut],
            'root0_G_forced_mass':20,'all_internal_triples_union_at_least3':True,'internal_leaf_union_size':5,
            'bad_flow':badinfo,'good_flow':goodinfo,'externally_rerouted_flow':reroutedinfo,
            'scope':'Actual literal4555/mincut77 counterexample to raising the internal20 block to21. Every maximum flow keeps this block at20. A good law exists by fractional redistribution; an external integral reroute also satisfies the existing SH1 condition; this is not a counterexample to general77 good-law existence or an original odd covering.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-module',type=Path,default=Path(__file__).with_name('height_two_saturated_block_transport.py'))
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();out=verify(args.base_module)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ('source_points','pair_tests','literal_tests','network_edges','minimum_cut','root0_G_forced_mass')}))
    print('good law bound',out['good_flow']['normalized_lcm_upper'])
if __name__=='__main__':main()
