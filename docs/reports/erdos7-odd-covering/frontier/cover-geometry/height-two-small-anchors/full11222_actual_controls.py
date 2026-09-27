#!/usr/bin/env python3
"""Complete nonrobust actual4555 controls for the full11222 common law.

Reuses the neighboring canonical small-anchor numerical/source helpers.
Tests actual positive mass on repeated R labels after normalization.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import json
import runpy

HELP=runpy.run_path(str(Path(__file__).with_name('small_anchor_actual_controls.py')))
N=HELP['N']
SELECT=HELP['SELECT']
D=HELP['DIVISORS']
require=HELP['require']
tree_exists=HELP['tree_exists']
numerical_caps=HELP['numerical_caps']
original_integer=HELP['original_integer']
R=1
BASE=(Q(1),Q(1,3),Q(3,5),Q(1,5),Q(1,5),Q(1,5),Q(3,25),Q(1,15),Q(1,25))
OTHER={5:Q(1,4),25:Q(3,20),35:Q(3,20),175:Q(9,100),245:Q(1,20),1225:Q(3,100)}


def fixtures():
    singles=[{(0,0)},{(0,1)}]
    return [
        dict(name='matching8',fibres=singles+[{(0,2),(1,0)},{(0,3),(1,1)},{(0,4),(1,2)}],n=8,m=5),
        dict(name='path6',fibres=singles+[{(0,2),(1,0)},{(0,3),(1,0)},{(0,3),(1,1)}],n=6,m=4),
        dict(name='adjacent7',fibres=singles+[{(0,2),(1,0)},{(0,3),(1,0)},{(0,4),(1,1)}],n=7,m=5),
    ]


def make_source(rec):
    source={(R,c):frozenset(f) for c,f in enumerate(rec['fibres'])}
    outside_pairs=((2,3),(2,4),(3,4))
    extra_J=(3,4,3) if rec['name']=='matching8' else (2,3,4)
    for index,r in enumerate((0,2,3)):
        labels={(g,h) for g in outside_pairs[index] for h in range(5)}
        labels.update(((1,0),(1,extra_J[index])))
        if rec['name']=='path6':
            labels.add((0,4))
        for c in range(N[r]):
            source[r,c]=frozenset(labels)
    return source


def fine_masses(law):
    out=Counter()
    for (r,c,g,h),mass in law.items():
        out[g,h]+=mass
    return out


def normalize_puncture(source):
    A=source[R,0]|source[R,1]
    root_labels=frozenset().union(*(source[R,c] for c in range(5)))
    psi=defaultdict(Q)
    rows=[]
    for double_owner in (2,3,4):
        anchor=(0,1,double_owner)
        F=frozenset().union(*(source[R,c] for c in anchor))
        require(len(F)<=4 and all(sum(g==G for g,h in F)<=3 for G in range(7)), 'normalizable whole original F')
        part=defaultdict(Q)
        deletes=Counter()
        restrictions_count=0
        for q in (0,2,3):
            restrictions=list(combinations(range(N[q]),SELECT[q]))
            included=Counter()
            for index,chosen in enumerate(restrictions):
                included.update(chosen)
                B=frozenset().union(*(source[q,c] for c in chosen))
                actual_union=F|B
                columns=[g for g in range(7) if sum(G==g for G,h in actual_union)>=3][:3]
                require(len(columns)==3,'original legal-pair tree exists')
                old={label for g in columns for label in sorted(p for p in actual_union if p[0]==g)[:3]}
                require(len(old)==9 and tree_exists(old,3,3),'old actual ternary tree')
                tree=set()
                for g in columns:
                    required={p for p in F if p[0]==g}
                    keep=sorted(p for p in old if p[0]==g and p not in required)[:3-len(required)]
                    branch=required|set(keep)
                    require(len(branch)==3 and branch<=actual_union,'actual normalized branch')
                    require(required<=branch,'whole F column inserted')
                    tree.update(branch)
                require(len(tree)==9 and tree_exists(tree,3,3),'normalized ternary tree')
                surviving=tree-F
                require(len(surviving)>=5 and surviving<=B,'five leaves have original other-root owners')
                selected=sorted(surviving,key=lambda p:(p not in root_labels,p))[:5]
                for g in range(7):
                    require(sum(G==g for G,h in selected)<=3-sum(G==g for G,h in F),'per-column normalized deletion bound')
                owner=chosen[(index+q+double_owner)%len(chosen)]
                require(set(selected)<=source[q,owner],'actual owner lift')
                mass=Q(1,3*3*len(restrictions)*5)
                for g,h in selected:
                    part[q,owner,g,h]+=mass
                deletes[9-len(surviving)]+=1
                restrictions_count+=1
            require(all(Q(included[c],len(restrictions))<=Q(3,5) for c in range(N[q])),'original full/gap inclusion bound')
        require(sum(part.values())==Q(1,3),'one third weight on this original anchor')
        partial_fine=fine_masses(part)
        require(all(partial_fine[y]==0 for y in F),'complete F globally removed in its component')
        for p,mass in part.items():psi[p]+=mass
        rows.append(dict(anchor=list(anchor),complete_projection=sorted(F),paired_trees=restrictions_count,
                         deletion_counts=dict(deletes),deleted_anchor_mass='0'))
    require(sum(psi.values())==1,'one psi probability')
    require(all(r!=R and (g,h) in source[r,c] for r,c,g,h in psi),'same actual source and other-root support')
    fine=fine_masses(psi)
    require(all(fine[y]==0 for y in A),'both singleton labels always deleted')
    column_mass=Counter()
    for (g,h),mass in fine.items():column_mass[g]+=mass
    for g in range(7):
        a=sum(G==g for G,h in A)
        d=sum(sum(G==g for G,h in source[R,c]-A) for c in (2,3,4))
        require(column_mass[g]<=Q(3-a,5)-Q(d,15),'column expectation bound with repeated labels')
    degrees={y:sum(y in source[R,c] for c in (2,3,4)) for y in root_labels-A}
    for y,t in degrees.items():
        require(fine[y]<=Q(3-t,15),'label deletion frequency bound')
    require(fine[(1,0)]==Q(3-degrees[(1,0)],15)>0,'positive R-label reaches its exact deletion-frequency cap')
    numeric_marked=sum(mass for point,mass in psi.items() if original_integer(point)%49==1)
    require(numeric_marked==fine[(1,0)],'marked shared point is the original numerical49 residue1')
    measured,seen=numerical_caps(psi)
    require(all(x<=b for x,b in zip(measured,BASE)),'all original psi cylinder caps')
    return dict(psi),dict(anchors=rows,paired_trees=sum(r['paired_trees'] for r in rows),
                         psi_caps=list(map(str,measured)),numerical_cylinders=seen,
                         positive_R_fine_masses={str(y):str(fine[y]) for y in sorted(root_labels) if fine[y]>0},
                         marked_label=[1,0],marked_numerical49_residue=1,marked_degree=degrees[(1,0)],marked_mass=str(fine[(1,0)]))


def validate(rec):
    source=make_source(rec)
    require(len(source)==19 and all(source.values()),'all complete occupied children')
    require([len(source[R,c]) for c in range(5)]==[1,1,2,2,2],'actual full11222 fibres')
    labels=frozenset().union(*(source[R,c] for c in range(5)))
    n=len(labels)
    m=max(Counter(g for g,h in labels).values())
    require((n,m)==(rec['n'],rec['m']),'actual distinct-label/column parameters')
    projections={r:[frozenset().union(*(source[r,c] for c in chosen))
                    for chosen in combinations(range(N[r]),SELECT[r])] for r in range(4)}
    pairs=0
    for r,s in combinations(range(4),2):
        for F,G in product(projections[r],projections[s]):
            require(tree_exists(F|G,3,3),'every original complete legal pair')
            pairs+=1
    require(pairs==480,'all480 original pair restrictions')
    robust=[r for r in range(4) if all(tree_exists(F,3,3) for F in projections[r])]
    require(not robust,'no individually robust root')
    require(tree_exists(frozenset().union(*source.values()),5,5),'standalone actual five-tree')
    psi,puncture=normalize_puncture(source)
    eta={}
    for y in sorted(labels):
        owner=next(c for c in range(5) if y in source[R,c])
        eta[R,owner,*y]=Q(1,n)
    require(sum(eta.values())==1,'uniform distinct-label eta')
    eta_owners=Counter()
    for (r,c,g,h),mass in eta.items():eta_owners[c]+=mass
    require(max(eta_owners.values())<=Q(2,n),'at most two selected labels per owner')
    lam={p:Q(3,4)*mass for p,mass in psi.items()}
    pi={p:Q(1,4)*mass for p,mass in eta.items()}
    nu=defaultdict(Q)
    for law in (lam,pi):
        for p,mass in law.items():nu[p]+=mass
    require(sum(nu.values())==1 and all((g,h) in source[r,c] for r,c,g,h in nu),'one same-source common law')
    lcap,ln=numerical_caps(lam)
    pcap,pn=numerical_caps(pi)
    ncap,nn=numerical_caps(nu)
    special={5:Q(1,4),25:Q(1,2*n),35:Q(m,4*n),175:Q(1,2*n),245:Q(1,4*n),1225:Q(1,4*n)}
    lc=dict(zip(D,lcap));pc=dict(zip(D,pcap));nc=dict(zip(D,ncap))
    require(all(lc[d]<=OTHER[d] and pc[d]<=special[d] for d in OTHER),'actual root-sensitive component cap tables')
    require(nc[7]<=Q(9,20) and nc[49]<=Q(3,20),'whole SAME law pure7/49 bounds')
    # One queried R label genuinely has positive mass under both components.
    marked=(1,0)
    shared_mass=sum(mass for (r,c,g,h),mass in lam.items() if (g,h)==marked)
    require(shared_mass>0 and sum(mass for (r,c,g,h),mass in pi.items() if (g,h)==marked)>0,'fine supports actually overlap')
    return dict(name=rec['name'],distinct_labels=n,maximum_column=m,actual_points=sum(map(len,source.values())),
                original_pair_tests=pairs,individually_robust_roots=robust,standalone=True,
                explicit_private_entry_cut=63+2*sum(len(source[R,c]) for c in range(5)),cut_not_claimed_minimum=True,
                puncture=puncture,eta_owner_max=str(max(eta_owners.values())),
                lambda_caps=list(map(str,lcap)),pi_caps=list(map(str,pcap)),nu_caps=list(map(str,ncap)),
                common_root_query_bound='44/5',lambda_positive_marked_fine=str(shared_mass),
                numerical_cylinders=puncture['numerical_cylinders']+ln+pn+nn)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    controls=[validate(rec) for rec in fixtures()]
    result=dict(result='PASS',source_count=len(controls),original_pair_tests=sum(c['original_pair_tests'] for c in controls),
                paired_trees=sum(c['puncture']['paired_trees'] for c in controls),
                numerical_cylinders=sum(c['numerical_cylinders'] for c in controls),controls=controls,
                scope='Complete nonrobust matching8/path6/adjacent7 actual sources, original pair tests and one common normalized law with positive shared fine support. Query bound uses separately verified root64 certificate; not exhaustive source enumeration, minimum-cut certification or Lean verification.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='controls'},sort_keys=True))
if __name__=='__main__':main()
