#!/usr/bin/env python3
"""Actual nonrobust-source controls for the gap four-double common laws."""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import argparse
import importlib.util
import json


def require(ok,message):
    if not ok:
        raise ValueError(message)


def load(path):
    spec=importlib.util.spec_from_file_location('small_anchor_actual_controls',path)
    require(spec is not None and spec.loader is not None,'anchor control import')
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def two_sets(labels):
    return list(combinations(labels,2))[:3]


def sources():
    return [
        ('cross4','cross',[{(0,i),(1,i)} for i in range(4)]),
        ('cross2_pure_H_pure_J','cross',[
            {(0,0),(1,0)},{(0,1),(1,1)},{(0,2),(0,3)},{(1,2),(1,3)}]),
        ('cross3_pure_H','cross',[
            {(0,0),(1,0)},{(0,1),(1,1)},{(0,2),(1,2)},{(0,3),(0,4)}]),
        ('pure_four_columns','pure',[
            {(g,0),(g,1)} for g in range(4)]),
        ('pure_overlap_and_two_singles','pure',[
            {(0,0),(0,1)},{(0,0),(0,2)},{(1,0),(1,1)},{(2,0),(2,1)}]),
        ('pure_two_overlap_pairs','pure',[
            {(0,0),(0,1)},{(0,0),(0,2)},{(1,0),(1,1)},{(1,0),(1,2)}]),
        ('cross4_shared_gap_label','cross',[{(0,i),(1,i)} for i in range(4)],True),
    ]


def complete_source(fibres,mode):
    labels=set().union(*fibres)
    occupied=sorted({g for g,h in labels})
    outside=[g for g in range(7) if g not in occupied]
    complements={g:[h for h in range(7) if (g,h) not in labels] for g in occupied}
    source={(0,c):frozenset(f) for c,f in enumerate(fibres)}
    for r in range(1,4):
        S=set()
        if mode=='cross':
            for g in occupied:
                if len(complements[g])>=3:
                    S.update((g,h) for h in two_sets(complements[g])[r-1])
                else:
                    S.add((g,complements[g][(r-1)%len(complements[g])]))
            S.update((outside[r-1],h) for h in range(5))
        else:
            for g in occupied:
                S.add((g,complements[g][r-1]))
            branch_pair=((0,1),(0,2),(1,2))[r-1]
            S.update((outside[j],h) for j in branch_pair for h in range(5))
        for c in range(5):
            source[r,c]=frozenset(S)
    return source


def eta_measure(fibres,mode):
    eta={}
    if mode=='cross':
        require(len(set().union(*fibres))==8,'cross eight distinct original labels')
        return {(0,c,g,h):Q(1,8) for c,f in enumerate(fibres) for g,h in f}
    grouped=defaultdict(list)
    for c,f in enumerate(fibres):
        cols={g for g,h in f}
        require(len(cols)==1,'pure original fibre')
        grouped[next(iter(cols))].append(c)
    for g,owners in grouped.items():
        require(len(owners)<=2,'at most two pure owners per column')
        if len(owners)==1:
            c=owners[0]
            for gg,h in fibres[c]: eta[0,c,gg,h]=Q(1,8)
        else:
            a,b=owners
            common=fibres[a]&fibres[b]
            require(len(common)==1,'two pure fibres overlap in exactly one label')
            for c in owners:
                for gg,h in fibres[c]:
                    eta[0,c,gg,h]=Q(1,10) if (gg,h) in common else Q(3,20)
    return eta


def psi_measure(source,helper):
    law=defaultdict(Q)
    gap_pairs=list(combinations(range(4),2))
    puncture_checks=0; replacements=0; pair_fine_masses=[]
    for gap_pair in gap_pairs:
        F=set().union(*(source[0,c] for c in gap_pair))
        Fcols=Counter(g for g,h in F)
        require(max(Fcols.values())<=3,'actual F per column at most3')
        conditional=defaultdict(Q)
        for r in range(1,4):
            full_triples=list(combinations(range(5),3))
            for index,full_triple in enumerate(full_triples):
                other=set().union(*(source[r,c] for c in full_triple))
                union=other|F
                available=[g for g in range(7) if sum(gg==g for gg,h in union)>=3]
                require(len(available)>=3,'original actual paired tree exists')
                shift=(index+sum(gap_pair)+r)%len(available)
                cols=(available[shift:]+available[:shift])[:3]
                tree=set()
                for g in cols:
                    selected={p for p in F if p[0]==g}
                    initial=set(sorted(p for p in union if p[0]==g)[-3:])
                    if not selected<=initial: replacements+=1
                    branch=set(selected)
                    for label in sorted(p for p in union if p[0]==g):
                        if len(branch)<3: branch.add(label)
                    require(len(branch)==3 and selected<=branch,'complete F column forced into actual branch')
                    tree.update(branch)
                require(helper.tree_exists(tree,3,3) and tree<=union,'same actual9leaf tree')
                remaining=sorted(tree-F)
                require(len(remaining)>=5 and set(remaining)<=other,'all surviving leaves actually from other restriction')
                # Rotate the five chosen leaves to vary owners/columns across original tests.
                offset=(index+r)%len(remaining)
                leaves=(remaining[offset:]+remaining[:offset])[:5]
                owner=full_triple[index%len(full_triple)]
                require(set(leaves)<=source[r,owner],'actual chosen other owner')
                mass=Q(1,3*len(full_triples)*5)
                for g,h in leaves: conditional[r,owner,g,h]+=mass
                for g,count in Fcols.items():
                    require(sum(gg==g for gg,h in leaves)<=3-count,'conditional forced-column survivor bound')
                puncture_checks+=1
        require(sum(conditional.values())==1,'conditional common probability')
        require(sum(m for (r,c,g,h),m in conditional.items() if (g,h) in F)==0,'entire F globally excluded')
        pair_fine_masses.append('0')
        for p,m in conditional.items():law[p]+=m/Q(len(gap_pairs))
    return dict(law),puncture_checks,replacements,pair_fine_masses


def all_actual_tree_replacements(source,helper):
    """Exhaust every tree on each distinct actual gap-pair/full-root union.

    All five fibres at a tested full root are equal in these fixtures, so
    this covers every original full triple without repeating identical trees.
    """
    count=0
    for gap_pair in combinations(range(4),2):
        F=set().union(*(source[0,c] for c in gap_pair))
        for r in range(1,4):
            require(all(source[r,c]==source[r,0] for c in range(5)), 'same full projection for exhaustive quotient')
            other=set(source[r,0]); union=other|F
            available=[g for g in range(7) if sum(gg==g for gg,h in union)>=3]
            for cols in combinations(available,3):
                branches=[list(combinations(sorted(p for p in union if p[0]==g),3)) for g in cols]
                for original in product(*branches):
                    normalized=set()
                    for g,old in zip(cols,original):
                        required={p for p in F if p[0]==g}
                        branch=set(required)
                        for label in old:
                            if len(branch)<3:branch.add(label)
                        require(len(branch)==3 and required<=branch,'every actual branch admits F-preserving replacement')
                        normalized.update(branch)
                    remaining=normalized-F
                    require(helper.tree_exists(normalized,3,3) and normalized<=union,'every normalized tree remains actual')
                    require(len(remaining)>=5 and remaining<=other,'every normalized tree leaves actual other-root points')
                    for g in range(7):
                        require(sum(gg==g for gg,h in remaining)<=3-sum(gg==g for gg,h in F),
                                'every tree obeys whole F-column survivor inequality')
                    count+=1
    return count


def validate(helper,name,mode,rawfibres,overlap=False):
    fibres=[frozenset(f) for f in rawfibres]
    source=complete_source(fibres,mode)
    if overlap:
        require(mode=='cross','shared-label control is a cross source')
        for c in range(5):
            source[1,c]=source[1,c]|{(0,0)}
    projected={r:[set().union(*(source[r,c] for c in chosen))
                  for chosen in combinations(range(helper.N[r]),helper.SELECT[r])] for r in range(4)}
    pair_count=0
    for r,s in combinations(range(4),2):
        for a,b in product(projected[r],projected[s]):
            require(helper.tree_exists(a|b,3,3),'all original legal pair conditions')
            pair_count+=1
    require(pair_count==480,'480 original complete-fibre pairs')
    require(helper.tree_exists(set().union(*source.values()),5,5),'actual standalone five-tree')
    robust=[r for r in range(4) if all(helper.tree_exists(F,3,3) for F in projected[r])]
    require(robust==[],'controls must have no individually robust root')
    exhaustive_replacements=all_actual_tree_replacements(source,helper)
    psi,checks,replacements,puncture_zero=psi_measure(source,helper)
    eta=eta_measure(fibres,mode)
    actual_gap=set().union(*fibres)
    occupied={g for g,h in actual_gap}
    psi_columns=Counter(); psi_fine=Counter(); eta_child=Counter(); eta_fine=Counter(); eta_columns=Counter()
    for (r,c,g,h),m in psi.items():psi_columns[g]+=m;psi_fine[g,h]+=m
    for (r,c,g,h),m in eta.items():eta_child[c]+=m;eta_fine[g,h]+=m;eta_columns[g]+=m
    require(sum(psi.values())==sum(eta.values())==1,'two actual probability measures')
    require(all((g,h) in source[r,c] and m>0 for law in (psi,eta) for (r,c,g,h),m in law.items()),'same-source actual support')
    require(all(psi_fine[label]<=Q(1,10) for label in actual_gap),'global fine-label inclusion averaging')
    overlap_mass=sum(psi_fine[label] for label in actual_gap)
    if overlap:
        require(psi_fine[0,0]>0,'shared original gap label must receive positive psi mass')
        require(overlap_mass>0,'nonzero gap-label overlap exercises the averaging bound')
    if mode=='cross':
        count=Counter(g for g,h in actual_gap)
        require(all(psi_columns[g]<=Q(6-count[g],10) for g in occupied),'cross pair-averaged column caps')
        require(max(eta_child.values())==Q(1,4) and max(eta_fine.values())==Q(1,8),'cross actual eta')
        weight=Q(25,33)
        caps=(Q(1),Q(25,99),Q(5,11),Q(5,33),Q(5,33),Q(5,33),Q(1,11),Q(5,99),Q(1,33))
        bound=Q(293,33)
    else:
        require(all(psi_columns[g]<=Q(2,5) for g in occupied),'pure pair-averaged column caps')
        require(max(eta_child.values())==Q(1,4) and max(eta_fine.values())<=Q(1,5) and max(eta.values())<=Q(3,20),'pure weighted eta')
        require(max(eta_columns.values())<=Q(1,2),'pure actual column cap')
        weight=Q(3,4)
        caps=(Q(1),Q(1,4),Q(9,20),Q(3,20),Q(3,20),Q(3,20),Q(9,100),Q(1,20),Q(3,80))
        bound=Q(719,80)
    nu=defaultdict(Q)
    for p,m in psi.items():nu[p]+=weight*m
    for p,m in eta.items():nu[p]+=(1-weight)*m
    measured,cylinders=helper.numerical_caps(nu)
    require(all(a<=b for a,b in zip(measured,caps)),'all1767 original numerical cylinders')
    require(sum(a*b for a,b in zip(helper.COEFF,caps))==bound<9,'strict uniform same-law envelope')
    return dict(name=name,mode=mode,complete_actual_points=sum(map(len,source.values())),
                original_legal_pair_tests=pair_count,standalone=True,individually_robust_roots=robust,
                explicit_private2222_cut=79,cut_is_not_claimed_minimum=True,
                actual_paired_tree_controls=checks,nontrivial_forced_replacements=replacements,
                exhaustive_original_tree_replacement_checks=exhaustive_replacements,
                complete_anchor_puncture_masses=puncture_zero,gap_fine_label_cap=str(max(psi_fine[p] for p in actual_gap)),
                actual_gap_projection_psi_mass=str(overlap_mass),
                shared_gap_label_control=overlap,
                original_numerical_cylinders=cylinders,measured_caps=list(map(str,measured)),
                measured_envelope=str(sum(a*b for a,b in zip(helper.COEFF,measured))),
                uniform_bound=str(bound),actual_law_points=len(nu))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--anchor-module',type=Path,default=Path(__file__).with_name('small_anchor_actual_controls.py'))
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();helper=load(args.anchor_module)
    controls=[validate(helper,*item) for item in sources()]
    require(sum(c['nontrivial_forced_replacements'] for c in controls)>0,'actual branch replacements exercised')
    out=dict(result='PASS',controls=controls,
             scope='Complete actual sources with no individually robust root, including positive psi mass on an original gap label; exact common laws and all original numerical caps. Not an enumeration, minimum-cut certification, Lean proof or unrestricted covering result.')
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(result='PASS',complete_sources=len(controls),
                          original_pair_tests=sum(c['original_legal_pair_tests'] for c in controls),
                          paired_tree_controls=sum(c['actual_paired_tree_controls'] for c in controls),
                          exhaustive_tree_replacements=sum(c['exhaustive_original_tree_replacement_checks'] for c in controls),
                          numerical_cylinders=sum(c['original_numerical_cylinders'] for c in controls))))


if __name__=='__main__':
    main()
