#!/usr/bin/env python3
"""Exact cut-profile controls using the published164/68 actual-source fixtures.

Checks the new local supplier and a165-point extension; it does not rerun the
published global literal suites, enumerate all mincuts, or claim Lean validation.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from pathlib import Path
from hashlib import sha256
import argparse
import json

def need(p,msg):
    if not p:raise ValueError(msg)

def read_fixture(directory,name):
    p=directory/name
    return json.loads(p.read_text()),sha256(p.read_bytes()).hexdigest()

def fixture_values(data,cutkey):
    source={tuple(p) for p in data['source']}
    atoms={tuple(row[:4]):Fraction(row[4]) for row in data['bad_flow']['atoms']}
    cut={(tuple(u),tuple(v)):cap for u,v,cap in data[cutkey]}
    need(len(source)==data['source_points'] and len(atoms)==len(data['bad_flow']['atoms']),'unique fixture coordinates')
    need(set(atoms)<=source and all(w.denominator==1 and w>0 for w in atoms.values()),'actual integral fixture flow')
    need(sum(atoms.values())==77 and sum(cut.values())==77,'fixture flow and cut value77')
    return source,atoms,cut

def validate_positive(source,atoms,cut):
    S,T=('source',),('sink',);P,G,r,u,v=0,1,0,0,1
    pubcol={(('cg',P),T):21}
    pubfine={(('ch',G,h),('cg',G)):7 for h in (u,v)}
    need(all(cut.get(edge)==cap for edge,cap in (pubcol|pubfine).items()),'exact public boundary')
    private={edge:cap for edge,cap in cut.items() if edge not in pubcol and edge not in pubfine}
    need(all(a[0]=='pg' and b[0]=='ph' and cap==2 for (a,b),cap in private.items()),'fixture private leaves only')
    need(sum(cap for (a,b),cap in private.items() if a[1]==r)==6,'distinguished private6')
    need(all(a[3]==G for a,b in private if a[1]==r),'distinguished private column')
    need(sum(cap for (a,b),cap in private.items() if a[1]!=r)==36,'other private36')
    occ={s:sorted({c for rr,c,g,h in source if rr==s}) for s in range(5)}
    need([len(occ[s]) for s in range(5)]==[5,5,5,4,0],'literal occupied sizes')
    caps={}
    def add(a,b,cap):
        need((a,b) not in caps,'network edge uniqueness');caps[a,b]=cap
    for s in range(4):
        add(S,('r',s),21)
        for c in occ[s]:
            add(('r',s),('c',s,c),7)
            for g in range(7):
                add(('c',s,c),('pg',s,c,g),6)
                for h in range(7):add(('pg',s,c,g),('ph',s,c,g,h),2)
    for g in range(7):
        add(('cg',g),T,21)
        for h in range(7):add(('ch',g,h),('cg',g),7)
    for s,c,g,h in source:add(('ph',s,c,g,h),('ch',g,h),126)
    private_points={tuple(b[1:]) for a,b in private}
    inside={S,('cg',P)}|{('ch',P,h) for h in range(7)}|{('ch',G,h) for h in (u,v)}
    for edge in caps:
        for node in edge:
            if node[0] in ('r','c','pg'):inside.add(node)
            if node[0]=='ph' and tuple(node[1:]) not in private_points:inside.add(node)
    boundary={edge:cap for edge,cap in caps.items() if edge[0] in inside and edge[1] not in inside}
    need(boundary==cut,'complete reconstructed boundary')
    edge_flow=Counter();balance=Counter();blocks=Counter();roots=Counter()
    for (s,c,g,h),w in atoms.items():
        path=[S,('r',s),('c',s,c),('pg',s,c,g),('ph',s,c,g,h),('ch',g,h),('cg',g),T]
        roots[s]+=w;blocks[s,g]+=w
        for a,b in zip(path,path[1:]):edge_flow[a,b]+=w
    for (a,b),cap in caps.items():
        flow=edge_flow[a,b];need(0<=flow<=cap,'every network capacity');balance[a]-=flow;balance[b]+=flow
    need(balance[S]==-77 and balance[T]==77 and all(w==0 for node,w in balance.items() if node not in (S,T)),'all vertex balances')
    need(all(edge_flow[edge]==cap for edge,cap in boundary.items()),'all forward cut arcs saturated')
    need(all(edge_flow[a,b]==0 for a,b in caps if a not in inside and b in inside),'zero backwards cut flow')
    need(blocks[r,G]==20 and roots[r]==21,'fixture dangerous block')
    leaf_masses={h:sum(w for (s,c,g,hh),w in atoms.items() if (s,g,hh)==(r,G,h)) for h in (u,v)}
    need(leaf_masses=={u:7,v:7},'root alone supplies public7+7')
    private_atoms=[(p,w) for p,w in atoms.items() if p in private_points and p[0]==r]
    need(sum(w for p,w in private_atoms)==6 and all(p[3] not in (u,v) for p,w in private_atoms),'private6 disjoint from public pair')
    owners={h:sorted({c for rr,c,g,hh in source if (rr,g,hh)==(r,G,h)}) for h in (u,v)}
    need(all(len(cs)>=4 for cs in owners.values()),'four actual owners per public fine leaf')
    neighborhoods=[len({h for rr,c,g,h in source if rr==r and g==G and c in cs}) for cs in combinations(occ[r],3)]
    need(min(neighborhoods)>=3,'actual T3')
    private_costs={s:[sum(cap//2 for (a,b),cap in private.items() if (a[1],a[2])==(s,c)) for c in occ[s]] for s in range(4)}
    return {'source_points':len(source),'network_edges':len(caps),'cut_capacity':77,'flow_value':77,
            'distinguished_block':{'root':r,'column':G,'root_mass':21,'block_mass':20},
            'public_boundary_capacity':35,'distinguished_private_capacity':6,'other_private_capacity':36,
            'public_leaf_owners':owners,'minimum_actual_three_row_neighborhood':min(neighborhoods),
            'private_child_token_costs':private_costs,
            'root_actual_column_counts':{s:len({g for rr,c,g,h in source if rr==s}) for s in range(4)}}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures-dir',type=Path,default=Path(__file__).parent)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    good,good_hash=read_fixture(args.fixtures_dir,'height_two_cut77_forced_twenty.json')
    bad,bad_hash=read_fixture(args.fixtures_dir,'height_two_cut77_actual_bad_neighborhood.json')
    source,atoms,cut=fixture_values(good,'cut')
    positive=validate_positive(source,atoms,cut)
    added=(1,0,1,0)
    need(added not in source,'one new actual incidence')
    enlarged=source|{added}
    extension=validate_positive(enlarged,atoms,cut)
    need(len(enlarged)==165 and extension['root_actual_column_counts'][1]==3,'strict extension of all-root two-column premise')
    bs,ba,bc=fixture_values(bad,'cut_edges')
    top=[list(a)+list(b)+[cap] for (a,b),cap in bc.items() if a==('source',)]
    need(len(top)==3 and sum(row[-1] for row in top)==63,'negative displayed top-cut profile')
    need(not any(a[0] in ('cg','ch') for a,b in bc),'negative has no public boundary')
    triple=(1,2,3)
    neighbor=sorted({h for r,c,g,h in bs if r==0 and g==1 and c in triple})
    need(len(neighbor)<3 and sum(w for (r,c,g,h),w in ba.items() if (r,g)==(0,1))==20,'negative actual bad-T3 mass20')
    # Independent sharp sorted-cost minima supporting the contradiction budget.
    minima={}
    for n,q in ((5,3),(4,2)):
        feasible=[sum(z) for z in combinations_with_replacement(range(9),n) if sum(z[:q])>=4]
        minima[f'{n},{q}']=min(feasible)
    need(set(minima.values())=={8},'both other-root token minima8')
    out={'scope':'Exact local supplier controls; published full literal suites reused, not rerun. Ordinary mathematics, no Lean or general cut77 claim.',
         'fixture_sha256':{'forced164':good_hash,'bad68':bad_hash},'positive164':positive,
         'extension165':dict(extension,added_actual_point=added,old_source_is_subset=source<=enlarged),
         'negative68':{'source_points':len(bs),'displayed_source_root_cut_edges':top,'public_cut_capacity':0,
                       'fails_supplier_boundary':True,'bad_child_triple':triple,'actual_G_neighbors':neighbor},
         'sorted_token_minima':minima,'hypothetical_other_private_requirement':48,'available_other_private_capacity':36}
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'positive_points':positive['source_points'],'extension_points':extension['source_points'],
                      'extension_root1_columns':extension['root_actual_column_counts'][1],
                      'negative_top_capacity':63,'required_other_private_capacity':48}))

if __name__=='__main__':main()
