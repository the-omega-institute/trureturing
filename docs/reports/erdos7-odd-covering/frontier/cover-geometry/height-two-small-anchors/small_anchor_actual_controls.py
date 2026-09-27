#!/usr/bin/env python3
"""Complete actual4555 source controls for small-anchor common laws.

Checks all480 original legal pairs, standalone, whole-fibre cut witnesses,
actual common measures, global puncture exclusion and all1767 ORIGINAL
numerical cylinders. Ordinary finite controls, not exhaustive source proofs.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import argparse
import json

N = (4, 5, 5, 5)
SELECT = (2, 3, 3, 3)
DIVISORS = (1, 5, 7, 25, 35, 49, 175, 245, 1225)
COEFF = (1, 3, 3, 5, 9, 5, 15, 15, 25)
SPACE = frozenset(product(range(7), repeat=2))
TARGET = {
    'B3': (Q(1), Q(25,84), Q(3,7), Q(5,28), Q(5,42), Q(5,28), Q(1,14), Q(5,84), Q(1,28)),
    'B4': (Q(1), Q(25,87), Q(12,29), Q(5,29), Q(10,87), Q(5,29), Q(2,29), Q(5,87), Q(1,29)),
    'H4-two': (Q(1), Q(2,7), Q(3,7), Q(6,35), Q(1,7), Q(1,7), Q(3,35), Q(1,21), Q(1,28)),
    'H4': (Q(1), Q(2,7), Q(3,7), Q(6,35), Q(1,7), Q(1,7), Q(3,35), Q(3,56), Q(1,28)),
    'H3+2': (Q(1), Q(6,23), Q(11,23), Q(18,115), Q(3,23), Q(4,23), Q(9,115), Q(1,23), Q(1,23)),
}
WEIGHTS = {'B3': Q(25,28), 'B4': Q(25,29), 'H4-two': Q(6,7), 'H4': Q(6,7), 'H3+2': Q(18,23)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def column(g):
    return frozenset((g,h) for h in range(7))


def tree_exists(labels, branches, leaves):
    return sum(sum(g == c for g,h in labels) >= leaves for c in range(7)) >= branches


def original_integer(point):
    r,c,g,h = point
    five = r + 5*c
    seven = g + 7*h
    return (five + 25*((2*(seven-five)) % 49)) % 1225


def numerical_caps(law):
    caps, seen = [], 0
    for d in DIVISORS:
        values = [Q(0)] * d
        for point, mass in law.items():
            values[original_integer(point) % d] += mass
        seen += len(values)
        caps.append(max(values))
    require(seen == 1767, 'all1767 numerical cylinders')
    return tuple(caps), seen


def uniform_eta(points):
    return {point: Q(1,len(points)) for point in points}


def case(name, root, fibres, anchor, mode, eta=None, public=(), inactive=(), cut=None):
    return dict(name=name, root=root, fibres=[frozenset(f) for f in fibres],
                anchor=tuple(anchor), mode=mode, eta=eta, public=frozenset(public),
                inactive=frozenset(inactive), expected_cut=cut)


def fixtures():
    u,v,w = (0,0),(0,1),(0,2)
    balanced = [{u},{v},{(1,0)}]
    mono = [{u},{v},{w}]
    eta4 = uniform_eta([(0,u),(1,v),(2,w),(3,(0,3))])
    out = [
        case('full11123_balanced',1,balanced+[{(1,1),(2,0)},column(2)],(0,1,2),'B3',cut=79),
        case('full11123_new_H',1,mono+[{(0,3),(1,0)},column(2)],(0,1,2),'H4',eta4,cut=79),
        case('full11133_balanced_whole_columns',1,balanced+[column(2),column(3)],(0,1,2),'B3',cut=81),
        case('partial_full1112_balanced',1,balanced+[{(2,0),(2,1)},SPACE],(0,1,2),'B3',inactive=(4,),cut=80),
        case('partial_full1112_inactive_H_owner',1,mono+[{u,(1,0)},SPACE],(0,1,2),'H4',
             uniform_eta([(0,u),(1,v),(2,w),(4,(0,3))]),inactive=(4,),cut=80),
        case('full_three_singletons_two_H_split',1,mono+[{u,v,(1,0),(1,1),(2,0)},{w,(3,0)}],(0,1,2),'H4',
             {(0,u):Q(1,4),(1,v):Q(1,4),(2,w):Q(1,4),(3,u):Q(1,8),(3,v):Q(1,8)}),
        case('full_three_singletons_shared_outside',1,mono+[{u,(4,0)},{v,(4,0)}],(0,1,2),'H4',
             {(2,w):Q(1,4),(0,u):Q(3,16),(3,u):Q(3,16),(1,v):Q(3,16),(4,v):Q(3,16)},cut=77),
        case('full11133_two_outside',1,mono+[{u,(1,0),(2,0)},{v,(3,0),(4,0)}],(0,1,2),'H3+2',
             uniform_eta([(0,u),(1,v),(2,w),(3,(1,0)),(4,(3,0))]),cut=81),
    ]
    for partial in (False,True):
        fourth = SPACE if partial else column(3)
        options = dict(inactive=(3,),cut=80) if partial else dict(cut=79)
        prefix = 'partial_gap122' if partial else 'gap1223'
        out.append(case(prefix+'_balanced',0,[{u},{v,(1,0)},{(1,1),(2,0)},fourth],(0,1),'B3',**options))
        out.append(case(prefix+'_repeated_H_owner',0,[{u},{v,w},{w,(0,3)},fourth],(0,1),'H4-two',
                        uniform_eta([(0,u),(1,v),(1,w),(2,(0,3))]),**options))
    for root in (0,1):
        for spread in (False,True):
            z = [(0,1),(1,0),(2,0)] if spread else [(0,1),(0,2),(0,3)]
            private = [{u,a} for a in z]
            if root == 1:
                fibres = [{u}]+private+[{u,(3,0),(3,1)}]
                anchor = (0,1,2)
                eta = uniform_eta([(0,u)]+[(i+1,z[i]) for i in range(3)])
            else:
                fibres = private+[{u,(3,0),(3,1)}]
                if not spread:
                    fibres[2] = {z[2]}
                anchor = (0,1)
                eta = uniform_eta([(0,u)]+[(i,z[i]) for i in range(3)])
            out.append(case(('gap' if root==0 else 'full')+'_public1_'+('spread' if spread else 'mono'),
                            root,fibres,anchor,'B3' if spread else 'H4-two',
                            None if spread else eta,public=(u,),cut=80))
    out += [
        case('balanced3_capacity_two_owner',0,[{u,v,(1,0)},{u},SPACE,SPACE],(0,1),'B3'),
        case('spread4_211_capacity_three_owner',1,[{u,v,(1,0)},{(2,0)},{u},SPACE,SPACE],(0,1,2),'B4'),
        case('spread4_1111_gap',0,[{u,(1,0)},{(2,0),(3,0)},SPACE,SPACE],(0,1),'B4'),
        case('spread4_full_public1',1,[{u,(1,0)},{u,(2,0)},{u,(0,1)},
                                     {u,(3,0)},{u,(4,0)}],(0,1,2),'B4',public=(u,),cut=80),
    ]
    return out


def make_psi(source, root, anchor, mode):
    F = frozenset().union(*(source[root,c] for c in anchor))
    mono = mode.startswith('H')
    if mono:
        require(len({g for g,h in F})==1, 'complete mono anchor')
        H = next(iter(F))[0]
    else:
        require(len(F)==(3 if mode=='B3' else 4), 'whole balanced anchor size')
        mult = sorted(Counter(g for g,h in F).values(),reverse=True)
        require(mult[0]<=2 and (mode!='B4' or mult in ([2,1,1],[1,1,1,1])), 'allowed deletion pattern')
    psi = defaultdict(Q)
    choices = 0
    for other in range(4):
        if other == root:
            continue
        restrictions = list(combinations(range(N[other]),SELECT[other]))
        for index, chosen in enumerate(restrictions):
            labels = frozenset().union(*(source[other,c] for c in chosen))
            shift = (index+other) % 7
            columns = [(shift+j)%7 for j in range(7)]
            if mono:
                columns = [g for g in columns if g != H][:2]
                leaves = [(g,(shift+h)%7) for g in columns for h in range(3)]
                require(not any(g==H for g,h in leaves), 'monochromatic column exclusion')
            else:
                # A genuine paired ternary tree with source-dependent literal labels.
                tree = [(g,(shift+h)%7) for g in columns[:3] for h in range(3)]
                require(tree_exists(set(tree),3,3), 'actual ternary tree')
                require(set(tree) <= (labels|F), 'tree outside paired actual union')
                remaining = [label for label in tree if label not in F]
                leaves, counts = [], Counter()
                for label in remaining:
                    if counts[label[0]] < 2 and len(leaves) < 5:
                        leaves.append(label); counts[label[0]] += 1
                require(len(leaves)==5, 'five actual puncture leaves')
            require(set(leaves)<=labels, 'lift leaves not supplied by other restriction')
            owner = chosen[0]
            require(set(leaves)<=source[other,owner], 'chosen actual owner')
            mass = Q(1,3*len(restrictions)*len(leaves))
            for g,h in leaves:
                psi[other,owner,g,h] += mass
            choices += 1
    return dict(psi),F,choices


def make_eta(source, rec, F):
    root = rec['root']
    if rec['eta'] is not None:
        return {(root,c,g,h):mass for (c,(g,h)),mass in rec['eta'].items()}
    labels = sorted(F)
    candidates = [[c for c in rec['anchor'] if label in source[root,c]] for label in labels]
    cap = len(labels)-1
    owners = next(ch for ch in product(*candidates) if max(Counter(ch).values())<=cap)
    return {(root,c,g,h):Q(1,len(labels)) for c,(g,h) in zip(owners,labels)}


def validate(rec):
    root = rec['root']
    require(len(rec['fibres'])==N[root], 'original occupied children retained')
    source = {(r,c):(rec['fibres'][c] if r==root else SPACE) for r in range(4) for c in range(N[r])}
    require(all(source.values()), 'complete nonempty actual fibres')
    projected = {r:[frozenset().union(*(source[r,c] for c in chosen))
                    for chosen in combinations(range(N[r]),SELECT[r])] for r in range(4)}
    pair_count = 0
    for r,s in combinations(range(4),2):
        for a,b in product(projected[r],projected[s]):
            require(tree_exists(a|b,3,3), 'original complete legal pair condition')
            pair_count += 1
    require(pair_count==480, '480 original pairs')
    require(tree_exists(frozenset().union(*source.values()),5,5), 'standalone five-tree')
    cut = None
    if rec['expected_cut'] is not None:
        private = 0
        for c in range(N[root]):
            if c in rec['inactive']:
                continue
            remaining = source[root,c]-rec['public']
            private += sum(min(3,sum(g==col for g,h in remaining)) for col in range(7))
        cut = 63+7*(len(rec['inactive'])+len(rec['public']))+2*private
        require(cut==rec['expected_cut'], 'complete fibre private/public cut witness')
    psi,F,choices = make_psi(source,root,rec['anchor'],rec['mode'])
    eta = make_eta(source,rec,F)
    for label,law in [('psi',psi),('eta',eta)]:
        require(sum(law.values())==1, label+' probability')
        require(all(m>0 and (g,h) in source[r,c] for (r,c,g,h),m in law.items()),label+' actual support')
    excluded = sum(m for (r,c,g,h),m in psi.items() if (g,h) in F)
    require(excluded==0, 'global49 puncture exclusion')
    pure49 = defaultdict(Q)
    for p,m in psi.items():
        pure49[original_integer(p)%49] += m
    require(all(pure49[g+7*h]==0 for g,h in F), 'original numerical49 F cylinders zero')
    weight = WEIGHTS[rec['mode']]
    nu = defaultdict(Q)
    for p,m in psi.items(): nu[p] += weight*m
    for p,m in eta.items(): nu[p] += (1-weight)*m
    caps,count = numerical_caps(nu)
    require(all(a<=b for a,b in zip(caps,TARGET[rec['mode']])), 'one-law numerical caps')
    envelope = sum(a*b for a,b in zip(COEFF,caps))
    require(envelope<9, 'strict original independent-LCM envelope')
    eta_children = Counter()
    for (r,c,g,h),mass in eta.items(): eta_children[c] += mass
    return dict(name=rec['name'],mode=rec['mode'],actual_points=sum(map(len,source.values())),
                complete_pair_tests=pair_count,standalone=True,explicit_cut=cut,
                cut_is_not_claimed_minimum=True,actual_anchor_size=len(F),
                averaged_original_restrictions=choices,global49_puncture_mass=str(excluded),
                eta_owner_max=str(max(eta_children.values())),law_points=len(nu),
                numerical_cylinders=count,caps=list(map(str,caps)),
                envelope=str(envelope),uniform_bound=str(sum(a*b for a,b in zip(COEFF,TARGET[rec['mode']]))))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    controls=[validate(rec) for rec in fixtures()]
    result=dict(result='PASS',controls=controls,
                scope='Complete actual sources and exact shared-law controls; no source enumeration, minimum-cut, Lean, higher-height or unrestricted covering conclusion.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(result='PASS',source_controls=len(controls),
                          original_pair_checks=sum(c['complete_pair_tests'] for c in controls),
                          numerical_cylinders=sum(c['numerical_cylinders'] for c in controls))))


if __name__=='__main__':
    main()
