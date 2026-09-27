#!/usr/bin/env python3
"""Complete actual-source controls for full/public1/private11111.

All original pairs and numerical cylinders; explicit simultaneous punctures.
Exact arithmetic, including under -O. Not an exhaustive source enumeration.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import argparse
import json

N=(4,5,5,5)
SELECT=(2,3,3,3)
D=(1,5,7,25,35,49,175,245,1225)
COEFF=(1,3,3,5,9,5,15,15,25)
P=(Q(1),Q(1,3),Q(3,5),Q(1,5),Q(1,5),Q(1,5),Q(3,25),Q(1,15),Q(1,25))
R=1
Y=(0,0)

def require(condition,message):
    if not condition:
        raise ValueError(message)

def has_tree(labels,branches,leaves):
    count=Counter(g for g,h in labels)
    return sum(n>=leaves for n in count.values())>=branches

def integer(point):
    r,c,g,h=point
    five=r+5*c
    seven=g+7*h
    return (five+25*((2*(seven-five))%49))%1225

def caps(law):
    out=[]
    for d in D:
        sums=[Q(0)]*d
        for p,m in law.items():
            sums[integer(p)%d]+=m
        out.append(max(sums))
    return tuple(out),sum(D)

def source_for(a,omitted):
    private=[(0,i+1) for i in range(a)]+[(1,i) for i in range(5-a)]
    fibres=[{z} if i in omitted else {Y,z} for i,z in enumerate(private)]
    b=5-a
    j_pairs=([(4,5),(5,6),(4,6)] if b==5 else
             [(4,5),(5,6),(4,6)] if b==4 else
             [(3,4),(4,5),(5,6)])
    source={}
    for index,r in enumerate((0,2,3)):
        labels={(0,2*index+1),(0,2*index+2)}
        labels.update((1,h) for h in j_pairs[index])
        labels.update((2,h) for h in (2*index,2*index+1,2*index+2))
        labels.update((g,h) for g in (3,4) for h in (2*index,2*index+1))
        for c in range(N[r]):
            source[r,c]=frozenset(labels)
    for c,f in enumerate(fibres):
        source[R,c]=frozenset(f)
    return source,private

def puncture(source,private,which):
    if which=='J':
        anchor=tuple(i for i,z in enumerate(private) if z[0]==1)[:3]
        removed_column=1
        removed_label=Y
    else:
        anchor=tuple(i for i,z in enumerate(private) if z[0]==0)+(next(i for i,z in enumerate(private) if z[0]==1),)
        removed_column=0
        removed_label=private[anchor[-1]]
    require(len(anchor)==3,'one original legal full restriction')
    F=set().union(*(source[R,c] for c in anchor))
    require(len(F)==4 and Y in F,'entire original four-label anchor')
    require(all(g==removed_column or (g,h)==removed_label for g,h in F),'entire F lies in global deletion')
    law=defaultdict(Q)
    count=0
    root_counts={}
    deletions=Counter()
    inclusion_counts={}
    for q in (0,2,3):
        restrictions=list(combinations(range(N[q]),SELECT[q]))
        require(len(restrictions)==(6 if q==0 else 10),'original gap/full restriction count')
        includes=Counter()
        for index,chosen in enumerate(restrictions):
            includes.update(chosen)
            other=set().union(*(source[q,c] for c in chosen))
            original=other|F
            # Force the maximal four-leaf deletion, preserving literal labels.
            deleted_branch=sorted(p for p in F if p[0]==removed_column)
            require(len(deleted_branch)==3,'three anchor leaves in deleted column')
            remaining_column=1-removed_column
            other_two=sorted(p for p in other if p[0]==remaining_column and p!=removed_label)[:2]
            require(len(other_two)==2,'two actual other-root leaves in surviving column')
            surviving_branch=[removed_label]+other_two
            outside_branch=sorted(p for p in other if p[0]==2)
            require(len(outside_branch)==3,'three actual outside leaves')
            tree=set(deleted_branch+surviving_branch+outside_branch)
            require(len(tree)==9 and has_tree(tree,3,3) and tree<=original,'original paired actual ternary tree')
            surviving=sorted(p for p in tree if p[0]!=removed_column and p!=removed_label)
            removed=len(tree)-len(surviving)
            deletions[removed]+=1
            require(removed<=4 and len(surviving)>=5,'at most four deletions')
            selected=surviving[:5]
            require(not (set(selected)&F),'complete original F deleted globally')
            require(set(selected)<=other,'actual lift exists in original other-root restriction')
            owner=chosen[(index+q)%len(chosen)]
            require(set(selected)<=source[q,owner],'selected owner is actual')
            mass=Q(1,3*len(restrictions)*5)
            for g,h in selected:
                law[q,owner,g,h]+=mass
            count+=1
        require(all(Q(includes[c],len(restrictions))<=Q(3,5) for c in range(N[q])),'original child inclusion at most three fifths')
        root_counts[str(q)]=len(restrictions)
        inclusion_counts[str(q)]=[str(Q(includes[c],len(restrictions))) for c in range(N[q])]
    require(sum(law.values())==1,'one probability law')
    require(all(r!=R and g!=removed_column and (g,h)!=removed_label for r,c,g,h in law),'global root and column and fine zero support')
    for p,m in law.items():
        r,c,g,h=p
        require(m>0 and (g,h) in source[r,c],'same complete actual source')
    measured,n=caps(law)
    require(all(x<=y for x,y in zip(measured,P)),'every original numerical cylinder obeys common P')
    return dict(law),dict(which=which,anchor=list(anchor),complete_anchor=sorted(F),original_restrictions=root_counts,child_inclusion_probabilities=inclusion_counts,paired_trees=count,deletion_counts=dict(deletions),whole_anchor_mass='0',removed_column_mass='0',removed_fine_mass='0',measured_caps=list(map(str,measured)),numerical_cylinders=n)

def validate(a,omitted):
    source,private=source_for(a,omitted)
    require(len(source)==19 and all(source.values()),'nineteen complete occupied children')
    require(all(source[R,c]<={Y,private[c]} for c in range(5)),'full public1 private11111 containment')
    require(3*21+7+2*len(private)==80,'complete-fibre public/private cut witness')
    require(sum(Y in source[R,c] for c in range(5))>=3,'every legal full triple contains y')
    projected={r:[set().union(*(source[r,c] for c in chosen)) for chosen in combinations(range(N[r]),SELECT[r])] for r in range(4)}
    pairs=0
    for r,s in combinations(range(4),2):
        for left,right in product(projected[r],projected[s]):
            require(has_tree(left|right,3,3),'all original complete legal pairs')
            pairs+=1
    require(pairs==480,'all480 original pairs')
    robust=[r for r in range(4) if all(has_tree(F,3,3) for F in projected[r])]
    require(not robust,'no individually robust root')
    require(has_tree(set().union(*source.values()),5,5),'standalone actual five-tree')
    psi_J,control_J=puncture(source,private,'J')
    controls=[control_J]
    if a==2:
        psi_H,control_H=puncture(source,private,'H')
        controls.append(control_H)
        eta={(R,c,*z):Q(1,5) for c,z in enumerate(private)}
        components=[(Q(104,217),psi_J),(Q(50,217),psi_H),(Q(63,217),eta)]
        target=Q(1299,155)
    else:
        b=5-a
        eta={(R,c,*z):Q(1,b) for c,z in enumerate(private) if z[0]==1}
        alpha=Q(35,48) if b==5 else Q(625,833)
        components=[(alpha,psi_J),(1-alpha,eta)]
        target=Q(103,12) if b==5 else Q(7333,833)
    require(sum(eta.values())==1,'eta actual probability')
    require(all(r==R and (g,h) in source[r,c] for r,c,g,h in eta),'eta complete actual incidences')
    eta_caps,eta_n=caps(eta)
    if a==2:
        require(eta_caps==(Q(1),Q(1),Q(3,5),Q(1,5),Q(3,5),Q(1,5),Q(1,5),Q(1,5),Q(1,5)),'eta exact global cap vector')
        columns=Counter()
        for (r,c,g,h),m in eta.items():columns[g]+=m
        require(columns=={0:Q(2,5),1:Q(3,5)},'eta exact two-column masses')
    else:
        require(eta_caps==tuple(Q(1) if d in (1,5,7,35) else Q(1,5-a) for d in D),'eta exact J cap vector')
    nu=defaultdict(Q)
    for weight,law in components:
        for p,m in law.items():nu[p]+=weight*m
    require(sum(nu.values())==1,'single fixed mixture')
    require(all((g,h) in source[r,c] for r,c,g,h in nu),'mixture actual source support')
    mixed,mixed_n=caps(nu)
    require(target<9,'strict certified common-query target')
    # These fixtures need not attain the uniform support/cap certificate.
    return dict(name=f'a{a}_omit_'+('none' if not omitted else '_'.join(map(str,omitted))),private_H=a,private_J=5-a,y_omitted_owners=list(omitted),complete_actual_points=sum(map(len,source.values())),original_pair_tests=pairs,individually_robust_roots=robust,standalone=True,explicit_complete_fibre_cut=80,cut_is_not_claimed_minimum=True,punctures=controls,eta_caps=list(map(str,eta_caps)),mixture_weights=list(str(w) for w,law in components),mixture_caps=list(map(str,mixed)),measured_independent_cap_envelope=str(sum(c*m for c,m in zip(COEFF,mixed))),uniform_joint_query_bound=str(target),numerical_cylinders=sum(c['numerical_cylinders'] for c in controls)+eta_n+mixed_n)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    controls=[validate(a,omitted) for a in range(3) for n in range(3) for omitted in combinations(range(5),n)]
    result=dict(result='PASS',source_count=len(controls),original_pair_tests=sum(c['original_pair_tests'] for c in controls),paired_tree_controls=sum(p['paired_trees'] for c in controls for p in c['punctures']),original_numerical_cylinders=sum(c['numerical_cylinders'] for c in controls),controls=controls,scope='Forty-eight complete nonrobust original sources, all choices omitting y at zero/one/two original owners, actual punctures and one common mixture. Query bounds use the separately verified complete finite partition/coarse-layout certificates. Not exhaustive source enumeration, a minimum-cut certificate, Lean verification or unrestricted covering result.')
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='controls'},indent=2))

if __name__=='__main__':main()
