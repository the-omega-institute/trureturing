#!/usr/bin/env python3
"""Exact public/private coupling for fully active R=1 cut75/77 shapes.

Construct one actual law with all eight numerical cylinder caps across
every owner placement and the extra private leaf. Reuses the existing
weighted row/tree and restriction constructors. The general source theorem
is the ordinary proof in Report449; controls are not odd-cover residuals.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json
import runpy

W=F(9,11)
N=(4,5,5,5)
Q=(2,3,3,3)
MODULI=(5,7,25,35,49,175,245,1225)
GOAL=tuple(map(F,('2/5','3/11','1/5','1/6','1/11','1/11','1/18','1/33')))
CASES={
 'same_gap_child':(((0,0),(0,0)),('12/55','1/3','1/3','1/3'),('9/22',)*4),
 'same_full_child':(((1,0),(1,0)),('2/5','12/55','1/3','1/3'),('1/2','4/11','17/44','17/44')),
 'two_gap_children':(((0,0),(0,1)),('1/5','1/3','1/3','1/3'),('3/11','5/11','5/11','5/11')),
 'two_children_same_full':(((1,0),(1,1)),('2/5','1/5','1/3','1/3'),('1/2','3/11','19/44','19/44')),
 'gap_and_full':(((0,0),(1,0)),('3/10','4/15','1/3','1/3'),('9/22','4/11','19/44','19/44')),
 'two_full_roots':(((1,0),(2,0)),('2/5','4/15','4/15','1/3'),('1/2','4/11','4/11','9/22')),
}

def check(v,message):
    if not v: raise ValueError(message)


def budgets(name):
    owners,aa,bb=CASES[name]
    A,B=tuple(map(F,aa)),tuple(map(F,bb))
    deleted=set(owners)
    remaining=[tuple(c for c in range(n) if (r,c) not in deleted) for r,n in enumerate(N)]
    delta=tuple(F(q,len(cs)) for q,cs in zip(Q,remaining))
    rho=tuple(F(sum(owner[0]==r for owner in owners),11) for r in range(4))
    private_child=F(2 if owners[0]==owners[1] else 1,11)
    slacks=[[],[],[]]
    for mask in range(16):
        S=[r for r in range(4) if mask>>r&1]
        top=sum((A[r] for r in range(4) if r not in S),F())
        if len(S)<=1: slacks[0].append(top-W)
        else:
            slacks[1].append(top+sum((B[r] for r in S),F())/2-W)
            slacks[2].extend(top+sum((B[r] for r in S if r!=j),F())-W for j in S)
    check(all(min(row)>=0 for row in slacks),'weighted cut inequalities')
    caps=(max(A[r]+rho[r] for r in range(4)),W/3,
          max(private_child,max(d*a for d,a in zip(delta,A))),
          max(F(1,11),max(B)/3), W/9,
          max(F(1,11),max(d*b for d,b in zip(delta,B))/3),
          max(F(1,44),max(B)/9),
          max(F(1,44),max(d*b for d,b in zip(delta,B))/9))
    check(all(c<=g for c,g in zip(caps,GOAL)),'universal caps')
    return owners,A,B,remaining,{'delta':list(map(str,delta)),
        'A':list(map(str,A)),'B':list(map(str,B)),'private_root_masses':list(map(str,rho)),
        'cut_inequalities':sum(map(len,slacks)),'minimum_slacks':list(map(str,map(min,slacks))),
        'caps':dict(zip(map(str,MODULI),map(str,caps)))}


def fixture(owners,extra,irregular=False):
    deleted=set(owners)
    source={}
    for r,n in enumerate(N):
        for c in range(n):
            digits={(c+j)%7 for j in range(5)} if irregular else set(range(5))
            source[r,c]=set() if (r,c) in deleted else {g+7*h for g in range(3) for h in digits}
    for i,owner in enumerate(owners):
        source[owner].update(3+i+7*h for h in range(4 if extra and i==0 else 5))
    star_owner=next(c for c in sorted(source) if c not in deleted)
    if extra: source[star_owner].add(3+7*4)
    return source,star_owner


def has_tree(leaves,arity):
    return sum(sum(y%7==g for y in leaves)>=arity for g in range(7))>=arity


def construct_control(name,extra,core,couple,irregular=False):
    owners,A,B,remaining,info=budgets(name)
    source,star_owner=fixture(owners,extra,irregular)
    check(all(source.values()),'every literal child actual')
    projection=set().union(*source.values())
    check(has_tree(projection,5),'standalone five-ary tree')
    pair_tests=0
    for r,s in combinations(range(4),2):
        for rr in combinations(range(N[r]),Q[r]):
            for ss in combinations(range(N[s]),Q[s]):
                pair_tests+=1
                leaves=set().union(*(source[r,c] for c in rr),*(source[s,c] for c in ss))
                check(has_tree(leaves,3),'literal selected pair tree')
    literal_tests=0
    for roots in combinations(range(5),3):
        for cs in product(tuple(combinations(range(5),3)),repeat=3):
            literal_tests+=1
            leaves=set().union(*(source.get((r,c),set()) for r,cc in zip(roots,cs) for c in cc))
            check(has_tree(leaves,3),'full original ternary five-tree test')
    # Check the chosen cut's containment, not a minimum-cut assertion.
    for child,leaves in source.items():
        allowed={y for y in range(49) if y%7<3}
        for i,owner in enumerate(owners):
            if child==owner: allowed.update(3+i+7*h for h in range(7))
        if extra and child==star_owner: allowed.add(3+7*4)
        check(leaves<=allowed,'actual cut containment')
    public=[(r,c,y) for (r,c),ys in source.items() if (r,c) not in set(owners)
            for y in sorted(ys) if y%7<3]
    selections=[tuple(combinations(cs,q)) for cs,q in zip(remaining,Q)]
    caps={(b,v):F(1,3**b) for b in (1,2) for v in range(7**b)}
    alpha,beta=tuple(a/W for a in A),tuple(b/W for b in B)
    def conditional(m,q,radix,depth,projected,prefix_caps):
        return couple(m,q,radix,depth,projected,prefix_caps,
                      row_caps=alpha,joint_coefficients=beta)
    public_law,coupling=core(4,2,5,7,2,public,caps,conditional,selections,
                              root_caps=alpha,joint_coefficients=beta)
    law=defaultdict(F)
    for point,mass in public_law.items(): law[point]+=W*mass
    private_points=[]
    for i,(r,c) in enumerate(owners):
        available=sorted(y for y in source[r,c] if y%7==3+i)
        check(len(available)>=4,'four actual owner leaves')
        for y in available[:4]:
            law[r,c,y]+=F(1,44)
            private_points.append((r,c,y))
    check(len(set(private_points))==8,'eight distinct actual private points')
    check(sum(law.values(),F())==1,'one probability')
    check(all(y in source[r,c] for r,c,y in law),'all law atoms actual')
    literal={r+5*c+25*((y-(r+5*c))*pow(25,-1,49)%49):mass for (r,c,y),mass in law.items()}
    check(len(literal)==len(law),'injective literal CRT')
    maxima={1:F(1)}
    cylinder_tests=1
    for d,cap in zip(MODULI,GOAL):
        masses=[sum((mass for x,mass in literal.items() if x%d==a),F()) for a in range(d)]
        maxima[d]=max(masses)
        cylinder_tests+=d
        check(maxima[d]<=cap,('same-law cylinder bound',name,extra,d,maxima[d],cap))
    envelope=sum(maxima[lcm(d,e)] for d in maxima for e in maxima)
    check(envelope<=F(491,55)<9,'full independent-phase upper')
    return {'owner_configuration':name,'extra_leaf':extra,'irregular_public_fibres':irregular,
            'source_points':sum(map(len,source.values())),'witness_cut_numerator_over63':75+2*extra,
            'minimum_cut_claimed':False,'selected_pair_tests':pair_tests,'literal_five_tree_tests':literal_tests,
            'public_coupling':coupling,'private_points':private_points,'law_atoms':len(law),
            'numerical_cylinder_tests':cylinder_tests,'ordered_lcm_pairs':81,
            'actual_caps':{str(d):str(v) for d,v in maxima.items()},'actual_lcm_envelope':str(envelope),
            'law':[{'residue':x,'mass':str(mass)} for x,mass in sorted(literal.items())]}


def verify(directory):
    core=runpy.run_path(str(directory/'subtree_restriction_coupling.py'))['couple_child_restriction_caps']
    couple=runpy.run_path(str(directory/'tree_cap_coupling.py'))['couple_tree_caps']
    controls=[construct_control(name,extra,core,couple) for name in CASES for extra in (False,True)]
    controls.append(construct_control('gap_and_full',True,core,couple,irregular=True))
    envelope=F(1)+sum(w*c for w,c in zip((3,3,5,9,5,15,15,25),GOAL))
    check(envelope==F(491,55),'exact universal bound')
    return {'budgets':{name:budgets(name)[-1] for name in CASES},
            'universal_caps':dict(zip(map(str,MODULI),map(str,GOAL))),
            'universal_lcm_bound':str(envelope),'controls':controls,
            'scope':'One common actual law for fully active R=1 whole-column cut shapes. Witness cut capacities are not claimed minimum; other75/77 shapes, outside-cofactor lifting and original odd-covering realization remain separate.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--library',type=Path,default=Path(__file__).parent,
                        help='directory of existing coupling programs (default: sibling directory)')
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=parser.parse_args()
    payload=json.dumps(verify(args.library),indent=2)+'\n'
    args.output.write_text(payload,encoding='utf-8')
    print(payload,end='')


if __name__=='__main__':main()
