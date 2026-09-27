#!/usr/bin/env python3
"""Exact controls for the fixed-other-roots two-unit complement bridge.
No literal-source theorem is inferred from these controls; all arithmetic is exact.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations_with_replacement, combinations, product
from pathlib import Path
from math import lcm
import json

def req(p,msg):
    if not p:raise ValueError(msg)

def check_flow(source,atoms,total=77):
    req(set(atoms)<=source and all(type(v) is int and v>=0 for v in atoms.values()),'actual nonnegative integer flow')
    req(sum(atoms.values())==total,'flow value')
    roots=defaultdict(int);children=defaultdict(int);private=defaultdict(int);fine=defaultdict(int);cols=defaultdict(int)
    for (r,c,g,h),v in atoms.items():
        req(v<=2,'entry cap2');roots[r]+=v;children[r,c]+=v;private[r,c,g]+=v;fine[g,h]+=v;cols[g]+=v
    req(all(v<=21 for v in roots.values()),'roots21');req(all(v<=7 for v in children.values()),'children7')
    req(all(v<=6 for v in private.values()),'private columns6');req(all(v<=7 for v in fine.values()),'public leaves7');req(all(v<=21 for v in cols.values()),'public columns21')
    return roots,children,private,fine,cols

def complement(source,old,r,G):
    roots,children,private,fine,cols=check_flow(source,old)
    req(roots[r]==21 and sum(v for (rr,c,g,h),v in old.items() if (rr,g)==(r,G))==20,'danger a21 d20')
    othercols={g:sum(v for (rr,c,gg,h),v in old.items() if rr!=r and gg==g) for g in range(7)}
    otherfine={(g,h):sum(v for (rr,c,gg,hh),v in old.items() if rr!=r and (gg,hh)==(g,h)) for g,h in product(range(7),repeat=2)}
    Rg={g:21-v for g,v in othercols.items()};Rh={p:7-v for p,v in otherfine.items()}
    A={g:sorted({h for rr,c,gg,h in source if (rr,gg)==(r,g)}) for g in range(7) if g!=G}
    colcap={g:min(Rg[g],sum(Rh[g,h] for h in hs)) for g,hs in A.items()}
    C=sum(colcap.values());req(C>=1,'old outside unit feasible')
    if C>=2:
        return {'C':C,'column_available':colcap,'R_column':Rg,'R_leaf':Rh,'kind':'repairable'}
    used=[g for g,v in colcap.items() if v]
    req(len(used)==1 and colcap[used[0]]==1,'unique positive complement column');g=used[0]
    if Rg[g]==1:critical=('column',g)
    else:
        hs=[h for h in A[g] if Rh[g,h]]
        req(len(hs)==1 and Rh[g,hs[0]]==1,'unique residual-one leaf');critical=('leaf',g,hs[0])
    zeros=[]
    for gg,hs in A.items():
        if not hs:continue
        if critical==('column',gg):continue
        if Rg[gg]==0:zeros.append(('column',gg));continue
        for h in hs:
            if critical==('leaf',gg,h):continue
            req(Rh[gg,h]==0,'all remaining actual off-G leaves saturated');zeros.append(('leaf',gg,h))
    def covers(prefix,p):
        rr,c,gg,h=p;return gg==prefix[1] and (prefix[0]=='column' or h==prefix[2])
    req(all(any(covers(p,x) for p in [critical,*zeros]) for x in source if x[0]==r and x[2]!=G),'whole actual complement covered')
    Czero=sum(p[0]=='column' for p in zeros);Lzero=len(zeros)-Czero
    e=othercols[G];req(e in (0,1),'near-full public external0or1')
    demand=(20 if critical[0]=='column' else 6)+21*Czero+7*Lzero+e
    req(demand<=56,'other-root mass budget56')
    req(3*Czero+Lzero<=(5 if critical[0]=='column' else 7),'weighted prefix bound')
    return {'C':C,'column_available':colcap,'R_column':Rg,'R_leaf':Rh,'kind':'blocked','critical':critical,'zero_prefixes':zeros,'zero_prefix_counts':[Czero,Lzero],'disjoint_other_mass_lower':demand,'external_G':e}

def repair(source,old,r,G,outside):
    req(sum(outside.values())==2 and all(type(v)is int and v>0 for v in outside.values()),'two integer outside units')
    req(set(outside)<=source and all(rr==r and g!=G for rr,c,g,h in outside),'actual complement support')
    info=complement(source,old,r,G);Rg,Rh=info['R_column'],info['R_leaf']
    req(all(sum(v for (rr,c,gg,h),v in outside.items() if gg==g)<=Rg[g] for g in range(7)),'complement column feasibility')
    req(all(sum(v for (rr,c,gg,hh),v in outside.items() if (gg,hh)==(g,h))<=Rh[g,h] for g,h in product(range(7),repeat=2)),'complement leaf feasibility')
    block={p:v for p,v in old.items() if p[0]==r and p[2]==G and v}
    rowmass={c:sum(v for (rr,cc,g,h),v in block.items() if cc==c) for c in range(5)}
    outside_row={c:sum(v for (rr,cc,g,h),v in outside.items() if cc==c) for c in range(5)}
    over=[c for c in range(5) if rowmass[c]+outside_row[c]>7]
    req(len(over)<=1,'at most one child conflict')
    candidates=[p for p,v in block.items() if v and (not over or p[1]==over[0])]
    req(bool(candidates),'removable old block atom');removed=min(candidates)
    new={p:v for p,v in old.items() if p[0]!=r or p[2]==G}
    new[removed]-=1
    for p,v in outside.items():new[p]=v
    new={p:v for p,v in new.items() if v}
    check_flow(source,new)
    req({p:v for p,v in new.items() if p[0]!=r}=={p:v for p,v in old.items() if p[0]!=r and v},'all other-root atoms fixed')
    req(sum(v for p,v in new.items() if p[0]==r)==21 and sum(v for p,v in new.items() if p[0]==r and p[2]==G)==19,'a21 d19')
    return new,{'removed_block_atom':removed,'child_conflict':over}

def envelope(atoms):
    mods=(1,5,7,25,35,49,175,245,1225)
    def crt(p):
        r,c,g,h=p;x=r+5*c;y=g+7*h;return x+25*((y-x)*2%49)
    maxima={m:max(sum(v for p,v in atoms.items() if crt(p)%m==a) for a in range(m)) for m in mods}
    return str(Q(sum(maxima[lcm(a,b)] for a,b in product(mods,repeat=2)),77))

def source_fixture(data):
    d=data;source=set(map(tuple,d['source']))
    atoms={tuple(row[:4]):Q(row[4]) for row in d['bad_flow']['atoms']}
    req(all(v.denominator==1 for v in atoms.values()),'input integral');atoms={p:int(v) for p,v in atoms.items() if v}
    check_flow(source,atoms)
    # Exact source assumptions, recomputed without invoking producer or a flow solver.
    n=(5,5,5,4,0);fibres=defaultdict(set)
    for r,c,g,h in source:fibres[r,c].add((g,h))
    req(tuple(sum(rr==r for rr,c in fibres) for r in range(5))==n,'source occupancy')
    def tree(points,k):return sum(len({h for g,h in points if g==j})>=k for j in range(7))>=k
    req(tree({(g,h) for r,c,g,h in source},5),'standalone tree')
    pairs=0
    for r,s in combinations(range(4),2):
        for aa in combinations(range(n[r]),n[r]-2):
            for bb in combinations(range(n[s]),n[s]-2):
                req(tree(set().union(*(fibres[r,c] for c in aa),*(fibres[s,c] for c in bb)),3),'literal pair criterion');pairs+=1
    req(pairs==480,'pair checks')
    return d,source,atoms

def release_cycles(source,old,r,G):
    roots,children,private,fine,cols=check_flow(source,old)
    req(roots[r]==21 and sum(v for (rr,c,g,h),v in old.items() if (rr,g)==(r,G))==20,'danger a21 d20')
    outside=[(p,v) for p,v in old.items() if p[0]==r and p[2]!=G and v]
    req(len(outside)==1 and outside[0][1]==1,'unique outside atom')
    p=outside[0][0];_,rho,H,k=p
    needs_row=children[r,rho]==7
    forbidden={j for j in range(7) if needs_row and fine[G,j]==7 and old.get((r,rho,G,j),0)==0}
    req(len(forbidden)<=2,'at most two blocked fine leaves')
    donors=[q for q,v in old.items() if v and q[0]!=r and q[2]==H and (q[3]==k or fine[H,k]<7)]
    out=[]
    for donor in sorted(donors):
        ss,cc,HH,ll=donor
        dests=[x for x in source if x[:3]==(ss,cc,G) and x[3]not in forbidden]
        for dest in sorted(dests):
            j=dest[3]
            choices=[q for q,v in old.items() if v and q[0]==r and q[2]==G
                     and (not needs_row or q[1]==rho) and (fine[G,j]<7 or q[3]==j)]
            req(choices,'old G removal fits row and public leaf')
            removed=min(choices)
            change={removed:-1,p:1,donor:-1,dest:1}
            req(len(change)==4,'four distinct actual atoms')
            flow=dict(old)
            for q,v in change.items():flow[q]=flow.get(q,0)+v
            flow={q:v for q,v in flow.items() if v}
            rr,ch,pr,ff,co=check_flow(source,flow)
            req(dict(rr)==dict(roots) and dict(co)==dict(cols),'all root and public-column totals fixed')
            req(sum(v for q,v in flow.items() if q[0]==r and q[2]==G)==19,'cross-root lowers d')
            out.append((change,flow))
    if not out:
        req(all({q[3] for q in source if q[:3]==(ss,cc,G)}<=forbidden for ss,cc,HH,ll in donors),'no release forces entire donor-child G neighborhoods into common two-leaf set')
    donor_children={(ss,cc) for ss,cc,HH,ll in donors}
    result={'old_outside_point':p,'old_outside_child_full':needs_row,'forbidden_G_fine_leaves':sorted(forbidden),'eligible_donor_children':len(donor_children),'actual_four_atom_releases':len(out)}
    if out:
        change,flow=out[0];result['first_release']={'changes':[[*q,v] for q,v in change.items()],'atoms':[[*q,v] for q,v in sorted(flow.items())],'lcm_envelope':envelope(flow)}
    return result

def construct_nonrobust192():
    n=(5,5,5,4,0)
    local={(0,0):2,(0,1):2,(0,2):2,(1,0):2,(1,1):2,(2,0):2,(2,1):2,(4,0):1,(4,1):1,(4,3):2,(4,4):2}
    source={(r,c,0,h) for r in range(4) for c in range(n[r]) for h in range(7)}
    source|={(0,c,1,h) for c,h in local}
    source|={(r,c,1,2) for r in (1,2,3) for c in range(n[r])}|{(2,0,1,5)}
    source|={(r,c,2,0) for r in range(4) for c in range(n[r])}
    source|={(1,c,3,c) for c in range(5)}|{(2,c,4,c) for c in range(5)}|{(3,c,2,c+1) for c in range(4)}
    req(len(source)==192,'192 points')
    bad={(0,c,1,h):v for (c,h),v in local.items()};bad[0,0,2,0]=1
    for r,g in ((1,3),(2,4)):
        for c in range(5):bad[r,c,g,c]=2;bad[r,c,0,c]=2
    bad[2,0,1,5]=1
    for c in range(4):bad[3,c,2,c+1]=2
    for c in range(3):bad[3,c,2,0]=2
    bad[3,0,0,5]=1
    good=dict(bad)
    changes={(0,0,1,0):-1,(0,0,2,0):1,(3,0,2,0):-1,(3,0,1,2):1}
    for p,v in changes.items():
        req(p in source,'actual cross-root cycle');good[p]=good.get(p,0)+v
    n=(5,5,5,4,0);fibres=defaultdict(set)
    for r,c,g,h in source:fibres[r,c].add((g,h))
    def tree(ps,k):return sum(len({h for g,h in ps if g==j})>=k for j in range(7))>=k
    robust=[r for r in range(4) if all(tree(set().union(*(fibres[r,c] for c in cs)),3) for cs in combinations(range(5),3))]
    req(robust==[],'zero individually robust roots')
    pairs=literal=0
    for r,s in combinations(range(4),2):
        for aa in combinations(range(n[r]),n[r]-2):
            for bb in combinations(range(n[s]),n[s]-2):
                req(tree(set().union(*(fibres[r,c] for c in aa),*(fibres[s,c] for c in bb)),3),'pair blocking');pairs+=1
    for rr in combinations(range(5),3):
        for picks in product(tuple(combinations(range(5),3)),repeat=3):
            req(tree(set().union(*(fibres[r,c] for r,cs in zip(rr,picks) for c in cs)),3),'literal blocking');literal+=1
    req((pairs,literal)==(480,10000) and tree({(g,h) for r,c,g,h in source},5),'tree inventory')
    colowners={g:sorted({(r,c) for r,c,gg,h in source if gg==g}) for g in range(7)}
    req(sum(len(owners)>3 for owners in colowners.values())==5,'five columns each need public placement under WC1')
    rootcols={r:sorted({g for rr,c,g,h in source if rr==r}) for r in range(4)}
    req(all(len(gs)>2 for gs in rootcols.values()),'outside two-column-per-root class')
    S,T=('source',),('sink',);caps={}
    def edge(u,v,c):
        req((u,v)not in caps,'unique edge');caps[u,v]=c
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
    private={(1,c,3,c) for c in range(5)}|{(2,c,4,c) for c in range(5)}|{(3,c,2,c+1) for c in range(4)}
    inside={S,('cg',0),('cg',1),('ch',2,0)}|{('ch',g,h) for g in (0,1) for h in range(7)}
    for r in range(4):
        inside.add(('r',r))
        for c in range(n[r]):
            inside.add(('c',r,c))
            for g in range(7):
                inside.add(('pg',r,c,g))
                inside.update(('ph',r,c,g,h) for h in range(7) if (r,c,g,h)not in private)
    cut={uv:c for uv,c in caps.items() if uv[0] in inside and uv[1]not in inside}
    req(sorted(cut.values())==[2]*14+[7]+[21]*2 and sum(cut.values())==77,'old exact77 cut retained')
    mods=(1,5,7,25,35,49,175,245,1225)
    def check(atoms):
        req(set(atoms)<=source and all(v>0 for v in atoms.values()) and sum(atoms.values())==77,'actual law77')
        flow=defaultdict(int);bal=defaultdict(int)
        for (r,c,g,h),v in atoms.items():
            path=(S,('r',r),('c',r,c),('pg',r,c,g),('ph',r,c,g,h),('ch',g,h),('cg',g),T)
            for u,w in zip(path,path[1:]):flow[u,w]+=v
        for (u,v),cap in caps.items():
            req(0<=flow[u,v]<=cap,'all network caps');bal[u]-=flow[u,v];bal[v]+=flow[u,v]
        req(bal[S]==-77 and bal[T]==77 and all(v==0 for u,v in bal.items() if u not in (S,T)),'flow conservation')
        req(all(flow[uv]==cap for uv,cap in cut.items()),'cut saturation')
        def crt(p):
            r,c,g,h=p;x=r+5*c;y=g+7*h;return x+25*((y-x)*2%49)
        maxima={m:max(sum(v for p,v in atoms.items() if crt(p)%m==a) for a in range(m)) for m in mods}
        env=sum(maxima[lcm(m,k)] for m,k in product(mods,repeat=2))
        return {'atoms':[[*p,str(v)] for p,v in sorted(atoms.items())],'cylinder_maxima':{str(m):v for m,v in maxima.items()},'lcm_upper':str(Q(env,77))}
    bi,gi=check(bad),check(good)
    req(gi['lcm_upper']=='689/77','global cycle succeeds')
    out={'source_points':len(source),'source':sorted(source),'occupancy':n,'robust_roots':robust,'pair_tests':pairs,'literal_tests':literal,'standalone5_tree':True,'network_edges':len(caps),'minimum_cut':77,'cut':[[list(u),list(v),c] for(u,v),c in cut.items()],'bad_flow':bi,'global_cycle_flow':gi,'cycle':[[*p,v] for p,v in changes.items()],'column_owner_counts':{g:len(owners) for g,owners in colowners.items()},'root_columns':rootcols,'scope':'Literal192-point source with fixed-other-root complement C1 but a successful cross-root cycle. Zero individually robust roots, outside two-column-per-root source class, and no WC1 cut because five columns each occur at more than three distinct child owners. Does not refute the genuine no-global-cycle dichotomy or original odd noncoverage.'}
    return out

def capacity_boundary_controls():
    # These controls check capacity logic only; they are not asserted literal blockers.
    old={(0,0,1,j):2 for j in (2,3,4)}
    for c in (1,2,3):
        for j in (0,1):old[0,c,1,j]=2
    for j in (0,1):old[0,4,1,j]=1
    old[0,0,0,0]=1
    for c in range(3):old[1,c,0,0]=2
    for c in range(5):old[1,c,2,c]=2;old[1,c,2,(c+1)%5]=1
    for c in range(3):
        for h in range(3):old[2,c,3,h]=2
    for h in (3,4,5):old[2,3,3,h]=1
    for c in range(3):
        for h in (0,1):old[3,c,4,h]=2
    old[3,3,4,2]=2
    base=set(old)|{(1,0,1,0),(1,0,1,1)}
    check_flow(base,old)
    before=release_cycles(base,old,0,1)
    req(before['forbidden_G_fine_leaves']==[0,1] and before['actual_four_atom_releases']==0,'two forbidden leaves can both occur')
    augmented=base|{(1,0,1,2)}
    after=release_cycles(augmented,old,0,1)
    req(after['forbidden_G_fine_leaves']==[0,1] and after['actual_four_atom_releases']==1,'third actual neighbor forces release')
    nonfull=dict(old);nonfull[0,0,1,2]-=1;nonfull[0,4,1,2]=1
    nonfull_source=base|{(0,4,1,2)}
    check_flow(nonfull_source,nonfull)
    loose=release_cycles(nonfull_source,nonfull,0,1)
    req(loose['old_outside_child_full']==False and loose['forbidden_G_fine_leaves']==[] and loose['actual_four_atom_releases']==2,'nonfull recipient child permits a different removal row')
    return {'scope':'Capacity-only controls, not asserted literal4555 blockers or mincut77 sources.','two_forbidden_leaves':before,'third_actual_neighbor':after,'nonfull_recipient_child':loose}

def verify(fixtures_dir):
    constructed=construct_nonrobust192()
    fixtures=(('actual68',json.loads((fixtures_dir/'height_two_cut77_actual_bad_neighborhood.json').read_text())),('forced164',json.loads((fixtures_dir/'height_two_cut77_forced_twenty.json').read_text())),('nonrobust192',constructed))
    results={}
    for name,data in fixtures:
        raw,source,old=source_fixture(data);r=0;G=1;info=complement(source,old,r,G)
        off=sorted(p for p in source if p[0]==r and p[2]!=G)
        witnesses=[]
        for p,q in combinations_with_replacement(off,2):
            out={p:2} if p==q else {p:1,q:1}
            Rg,Rh=info['R_column'],info['R_leaf']
            if any(sum(v for pp,v in out.items() if pp[2]==g)>Rg[g] for g in range(7)):continue
            if any(sum(v for pp,v in out.items() if pp[2:]==(g,h))>Rh[g,h] for g,h in product(range(7),repeat=2)):continue
            new,certificate=repair(source,old,r,G,out);witnesses.append((out,new,certificate))
        req(bool(witnesses)==(info['C']>=2),'formula iff exact two-unit multiset enumeration')
        serial={k:v for k,v in info.items() if k not in ('R_column','R_leaf')}
        serial.update({'source_points':len(source),'literal_pair_checks':480,'two_unit_multisets_tested':len(off)*(len(off)+1)//2,'feasible_two_unit_lifts':len(witnesses)})
        if name=='actual68':
            # Deliberately use a child with no actual G point: same-child rerouting cannot implement this witness.
            out={(0,3,4,0):2};new,certificate=repair(source,old,r,G,out)
            req(not any(p[0]==0 and p[1]==3 and p[2]==1 for p in source),'destination child has no target-block support')
            serial['different_child_repair']={'outside':[[*p,v] for p,v in out.items()],**certificate,'atoms':[[*p,v] for p,v in sorted(new.items())],'lcm_envelope':envelope(new)}
        if name=='forced164':req(info['kind']=='blocked' and info['critical']==('column',0),'164 critical common column')
        if name=='nonrobust192':req(info['kind']=='blocked' and info['critical']==('leaf',2,0),'192 critical public leaf')
        serial['cross_root_release']=release_cycles(source,old,r,G)
        results[name]=serial
    return {'scope':'Ordinary exact controls for the fixed-other-roots two-unit criterion and four-atom cross-root release. C is only a threshold2 public bound, not general root throughput. No general cut77 or Lean claim.','actual_nonrobust192_source':constructed,'fixtures':results,'capacity_boundary_controls':capacity_boundary_controls()}

def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures-dir',type=Path,default=Path(__file__).parent)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args();out=verify(args.fixtures_dir)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({name:{'C':value['C'],'feasible_two_unit_lifts':value['feasible_two_unit_lifts'],'cross_root_releases':value['cross_root_release']['actual_four_atom_releases']} for name,value in out['fixtures'].items()}))
if __name__=='__main__':main()
