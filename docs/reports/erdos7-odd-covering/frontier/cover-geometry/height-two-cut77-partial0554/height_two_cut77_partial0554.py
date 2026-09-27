#!/usr/bin/env python3
"""Exact controls for three cut77 strata with one inactive full root.
Ordinary finite controls, not Lean verification or general cut77 closure.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import lcm
from pathlib import Path
import json

def req(p,message):
    if not p: raise ValueError(message)

def private_shapes(budget=14,pair_min=5):
    # No artificial cost3 truncation: every nonnegative sorted cost of total<=budget.
    choices={n:[z for z in combinations_with_replacement(range(budget+1),n) if sum(z)<=budget] for n in (4,5)}
    bysum={n:defaultdict(list) for n in choices}
    for n,zs in choices.items():
        for z in zs:bysum[n][sum(z)].append(z)
    found=[];tested=0
    for a in choices[5]:
        for b in choices[5]:
            left=budget-sum(a)-sum(b)
            if left<0:continue
            for c in bysum[4][left]:
                tested+=1;p=(sum(a[:3]),sum(b[:3]),sum(c[:2]))
                if all(p[i]+p[j]>=pair_min for i,j in combinations(range(3),2)):found.append([list(a),list(b),list(c)])
    if (budget,pair_min)==(14,5):
        expected=[[[1]*5,[1]*5,[1]*4]]
    else:
        req((budget,pair_min)==(21,7),'declared second profile')
        expected=[[[1]*5,e,[2]*4] for e in ([0,2,2,2,2],[1,1,2,2,2])]
        expected += [[b,a,c] for a,b,c in expected[:]]
    req(sorted(found)==sorted(expected),'exact private shape inventory')
    return {'private_budget':budget,'full_lengths':[5,5],'gap_length':4,'pair_lower_bound':pair_min,'sorted_cost_triples_tested':tested,'survivors':found}

def construct(public_whole):
    private_only=public_whole is None
    n=(5,5,5,4,0);G,K,H1,H2,J=0,2,3,4,(5 if private_only else 1)
    E={(0,0):2,(0,1):2,(0,2):2,(1,0):2,(1,1):2,(2,0):2,(2,1):2,(4,0):1,(4,1):1,(4,3):2,(4,4):2}
    pubs=range(7) if public_whole else range(3)
    if private_only:
        private={(1,c,g,c) for c in range(5) for g in (0,1)}|{(2,c,g,c) for c in range(5) for g in (2,3)}|{(3,c,4,h) for c in range(4) for h in (c,c+1)}
        source=set(private)
    else:
        source={(r,c,G,h) for r in (1,2,3) for c in range(n[r]) for h in pubs}
        source|={(r,c,K,0) for r in (1,2,3) for c in range(n[r])}
        private={(1,c,H1,c) for c in range(5)}|{(2,c,H2,c) for c in range(5)}|{(3,c,K,c+1) for c in range(4)}
    source|=private
    source|={(0,c,g,h) for c in range(5) for g in range(7) if g!=J for h in range(7)}
    source|={(0,c,J,h) for c,h in E}
    req(len(source)==(249 if private_only else (347 if public_whole else 291)),'point count')
    outside=(0,0,0,0) if private_only else (0,0,K,1)
    old={(0,c,J,h):v for (c,h),v in E.items()};old[outside]=1
    for p in private:old[p]=2
    if not private_only:
        for r,last in ((1,0),(2,1)):
            for c,h in enumerate((0,1,2,last)):old[r,c,G,h]=2
            for c in range(3):old[r,c,K,0]=1
        for c,h,v in ((0,0,1),(1,1,1),(2,2,2),(3,2,1)):old[3,c,G,h]=v
        old[3,0,K,0]=1
    good=dict(old);good[0,0,J,0]-=1;good[outside]+=1
    fibres=defaultdict(set)
    for r,c,g,h in source:fibres[r,c].add((g,h))
    req(tuple(sum(rr==r for rr,c in fibres) for r in range(5))==n,'occupancy')
    def tree(ps,k):return sum(len({h for g,h in ps if g==j})>=k for j in range(7))>=k
    pairs=literal=0
    for r,s in combinations(range(4),2):
        for aa in combinations(range(n[r]),n[r]-2):
            for bb in combinations(range(n[s]),n[s]-2):
                req(tree(set().union(*(fibres[r,c] for c in aa),*(fibres[s,c] for c in bb)),3),'literal pair');pairs+=1
    for rr in combinations(range(5),3):
        for picks in product(tuple(combinations(range(5),3)),repeat=3):
            req(tree(set().union(*(fibres[r,c] for r,cs in zip(rr,picks) for c in cs)),3),'full literal blocker');literal+=1
    req((pairs,literal)==(480,10000),'literal inventory')
    req(tree({(g,h) for r,c,g,h in source},5),'standalone5')
    robust=[r for r in range(4) if all(tree(set().union(*(fibres[r,c] for c in cs)),3) for cs in combinations(range(5),3))]
    req(robust==[0],'exactly one individually robust root')
    badtriples=[list(cs) for cs in combinations(range(5),3) if len({h for r,c,g,h in source if r==0 and c in cs and g==J})<3]
    req([1,2,3] in badtriples,'selected block fails literal-row T3')
    owners={g:len({(r,c) for r,c,gg,h in source if gg==g}) for g in range(7)}
    req(all(v>3 for v in owners.values()),'all seven columns violate nonpublic WC1 owner budget')
    S,T=('source',),('sink',);caps={}
    def edge(u,v,cap):
        req((u,v) not in caps,'unique edge');caps[u,v]=cap
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
    if not private_only:
        inside.add(('ch',K,0))
        if public_whole:inside|={('cg',G)}|{('ch',G,h) for h in range(7)}
        else:inside|={('ch',G,h) for h in range(3)}
    for r in (1,2,3):
        inside.add(('r',r))
        for c in range(n[r]):
            inside.add(('c',r,c))
            for g in range(7):
                inside.add(('pg',r,c,g))
                inside.update(('ph',r,c,g,h) for h in range(7) if (r,c,g,h)not in private)
    cut={uv:cap for uv,cap in caps.items() if uv[0]in inside and uv[1]not in inside}
    expected=[2]*28+[21] if private_only else [2]*14+([7,21,21] if public_whole else [7]*4+[21])
    req(sorted(cut.values())==sorted(expected) and sum(cut.values())==77,'exact77 cut')
    def check(atoms):
        req(set(atoms)<=source and all(type(v)is int and v>0 for v in atoms.values()) and sum(atoms.values())==77,'actual integral77')
        flow=defaultdict(int);bal=defaultdict(int);roots=defaultdict(int);blocks=defaultdict(int)
        fine=defaultdict(int);cols=defaultdict(int);otherfine=defaultdict(int);othercols=defaultdict(int)
        for (r,c,g,h),v in atoms.items():
            roots[r]+=v;blocks[r,g]+=v;fine[g,h]+=v;cols[g]+=v
            if r!=0:otherfine[g,h]+=v;othercols[g]+=v
            path=(S,('r',r),('c',r,c),('pg',r,c,g),('ph',r,c,g,h),('ch',g,h),('cg',g),T)
            for u,w in zip(path,path[1:]):flow[u,w]+=v
        for(u,v),cap in caps.items():
            req(0<=flow[u,v]<=cap,'all network capacities');bal[u]-=flow[u,v];bal[v]+=flow[u,v]
        req(bal[S]==-77 and bal[T]==77 and all(v==0 for u,v in bal.items() if u not in (S,T)),'flow conservation')
        req(all(flow[uv]==cap for uv,cap in cut.items()),'cut forward saturation')
        req(all(flow[u,v]==0 for u,v in caps if u not in inside and v in inside),'no backward cut flow')
        if private_only:
            req(dict(othercols)=={0:10,1:10,2:10,3:10,4:16},'private-only external coarse masses')
            req(all(v%2==0 for v in otherfine.values()) and all(atoms[p]==2 for p in private),'finite private points carry2; even public projection')
        else:
            req(dict(othercols)=={H1:10,H2:10,K:15,G:21},'forced external coarse masses')
            req(otherfine[K,0]==7 and all(v==2 for(g,h),v in otherfine.items() if g!=G and(g,h)!=(K,0)),'external fine masses outside public')
        mods=(1,5,7,25,35,49,175,245,1225)
        def crt(p):
            r,c,g,h=p;x=r+5*c;y=g+7*h;return x+25*((y-x)*2%49)
        maxima={m:max(sum(v for p,v in atoms.items() if crt(p)%m==a) for a in range(m)) for m in mods}
        env=Fraction(sum(maxima[lcm(m,k)] for m,k in product(mods,repeat=2)),77)
        danger=sorted([r,g] for(r,g),v in blocks.items() if roots[r]==21 and v==20)
        return {'atoms':[[*p,v] for p,v in sorted(atoms.items())],'roots':dict(roots),'blocks':[[*p,v] for p,v in sorted(blocks.items())],'dangerous_blocks':danger,'other_root_columns':dict(othercols),'lcm_envelope':str(env)}
    before,after=check(old),check(good)
    req(before['dangerous_blocks']==[[0,J]] and after['dangerous_blocks']==[],'danger repaired without a new danger')
    after['SH1_all_layout_bound']='691/77'
    return {'scope':'Actual source in a proved inactive-full-root cut77 stratum. Ordinary exact control; no general cut77 or Lean claim.','public_form':'none_finite_private' if private_only else ('whole_column_plus_leaf' if public_whole else 'four_leaves'),'source_points':len(source),'source':sorted(source),'occupancy':n,'active_counts':[0,5,5,4,0],'private_costs':[[2]*5,[2]*5,[2]*4] if private_only else [[1]*5,[1]*5,[1]*4],'pair_tests':pairs,'literal_tests':literal,'standalone5_tree':True,'robust_roots':robust,'target_bad_triples':badtriples,'column_owner_counts':owners,'minimum_cut':77,'network_edges':len(caps),'cut':[[list(u),list(v),c]for(u,v),c in sorted(cut.items())],'old_flow':before,'repaired_flow':after,'repair_changes':[[0,0,J,0,-1],[*outside,1]]}

def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    out={'scope':'Restricted cut77 stratum only; ordinary finite controls, not Lean.','private_classification':private_shapes(),'impossible_public2_private_classification':private_shapes(21,7),'controls':[construct(False),construct(True),construct(None)]}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'shape_triples':out['private_classification']['sorted_cost_triples_tested'],'public2_shape_triples':out['impossible_public2_private_classification']['sorted_cost_triples_tested'],'controls':[{k:c[k] for k in('public_form','source_points','minimum_cut','robust_roots')}|{'old_envelope':c['old_flow']['lcm_envelope'],'repaired_envelope':c['repaired_flow']['lcm_envelope']}for c in out['controls']]}))
if __name__=='__main__':main()
