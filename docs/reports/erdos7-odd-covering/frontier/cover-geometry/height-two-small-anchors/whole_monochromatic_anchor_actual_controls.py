#!/usr/bin/env python3
"""Complete nonrobust source controls for the whole monochromatic anchor.

All original fibres, owners and numerical CRT cylinders are retained.
These two fixtures test constructions, not exhaustive source classification.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
import json
from pathlib import Path
import runpy

_helper = runpy.run_path(str(Path(__file__).with_name('small_anchor_actual_controls.py')))
N, SELECT, D = (_helper[k] for k in ('N', 'SELECT', 'DIVISORS'))
require, tree_exists, numerical_caps, original_integer = (
    _helper[k] for k in ('require', 'tree_exists', 'numerical_caps', 'original_integer'))
P = (Q(1), Q(1,3), Q(1,2), Q(1,5), Q(1,6), Q(1,6), Q(1,10), Q(1,18), Q(1,30))
E = (Q(1), Q(1), Q(1), Q(1,2), Q(1), Q(1,2), Q(1,2), Q(1,2), Q(1,2))


def five_column(g):
    return frozenset((g,h) for h in range(5))


def validate(root):
    if root == 0:
        fibres = [frozenset({(0,0)}), frozenset({(0,1)}), five_column(4), five_column(5)]
        anchor = (0,1)
        eta_points = ((root,0,0,0), (root,1,0,1))
    else:
        fibres = [frozenset({(0,0),(0,1)}), frozenset({(0,0)}),
                  frozenset({(0,0)}), five_column(4), five_column(5)]
        anchor = (0,1,2)
        # The distinct labels must be matched to distinct actual owners.
        eta_points = ((root,0,0,1), (root,1,0,0))
    source = {(root,c):f for c,f in enumerate(fibres)}
    other_roots = [r for r in range(4) if r != root]
    outside = {}
    for index,(r,columns) in enumerate(zip(other_roots, ((1,2),(1,3),(2,3)))):
        f = five_column(columns[0]) | five_column(columns[1]) | {(0,index+2)}
        for c in range(N[r]):
            source[r,c] = frozenset(f)
        outside[r] = columns
    require(len(source) == 19 and all(source.values()), 'all original nonempty fibres')
    restrictions = {r:list(combinations(range(N[r]),SELECT[r])) for r in range(4)}
    projections = {r:[frozenset().union(*(source[r,c] for c in cs))
                       for cs in restrictions[r]] for r in range(4)}
    pairs = 0
    for r,s in combinations(range(4),2):
        for f,g in product(projections[r],projections[s]):
            require(tree_exists(f|g,3,3), 'original legal-pair ternary tree')
            pairs += 1
    require(pairs == 480, 'all480 original pairs')
    require(tree_exists(frozenset().union(*source.values()),5,5), 'actual standalone five-tree')
    require(all(not all(tree_exists(f,3,3) for f in projections[r]) for r in range(4)),
            'no individually robust root')
    F = frozenset().union(*(source[root,c] for c in anchor))
    require(F == {(0,0),(0,1)}, 'complete original two-label monochromatic anchor')
    psi = defaultdict(Q)
    trees = 0
    for index,r in enumerate(other_roots):
        leaves = [(g,h) for g in outside[r] for h in range(3)]
        for j,cs in enumerate(restrictions[r]):
            other = frozenset().union(*(source[r,c] for c in cs))
            tree = F | {(0,index+2)} | set(leaves)
            require(len(tree) == 9 and tree_exists(tree,3,3), 'chosen actual ternary tree')
            require(tree <= F|other, 'tree in original paired union')
            require(set(leaves) <= other, 'outside leaves belong to original other restriction')
            owner = cs[j % len(cs)]
            require(set(leaves) <= source[r,owner], 'all six leaves have actual owner')
            for g,h in leaves:
                psi[r,owner,g,h] += Q(1,3*len(restrictions[r])*6)
            trees += 1
    eta = {p:Q(1,2) for p in eta_points}
    require(len({p[1] for p in eta}) == len({p[2:] for p in eta}) == 2,
            'two distinct labels at two actual owners')
    nu = defaultdict(Q)
    for p,m in psi.items(): nu[p] += Q(95,113)*m
    for p,m in eta.items(): nu[p] += Q(18,113)*m
    cap_readouts = {}
    cylinders = 0
    for name,law in [('psi',psi),('eta',eta),('nu',nu)]:
        require(sum(law.values()) == 1, name+' probability')
        require(all(m > 0 and (g,h) in source[r,c] for (r,c,g,h),m in law.items()),
                name+' actual support')
        caps,count = numerical_caps(law)
        cylinders += count
        cap_readouts[name] = list(map(str,caps))
        if name != 'nu':
            bound = P if name == 'psi' else E
            require(all(v <= b for v,b in zip(caps,bound)), name+' simultaneous numerical caps')
    require(all(r != root and g != 0 for r,c,g,h in psi), 'whole-root and whole-column exclusion')
    separated = 0
    for d in D[1:]:
        left,right = [Q(0)]*d,[Q(0)]*d
        for p,m in psi.items(): left[original_integer(p)%d] += m
        for p,m in eta.items(): right[original_integer(p)%d] += m
        for a in range(d):
            require(left[a] == 0 or right[a] == 0, 'every nonunit cylinder meets at most one component')
            separated += 1
    require(separated == 1766, 'all original nonunit numerical cylinders separated')
    return {'name':'gap_two_label_anchor' if root == 0 else 'full_two_label_owner_matching',
            'root':root,'actual_points':sum(map(len,source.values())),
            'original_owners':len(source),'original_pair_checks':pairs,'standalone':True,
            'no_individually_robust_root':True,'paired_trees':trees,
            'actual_anchor':sorted(F),'eta_original_points':list(eta),
            'numerical_cylinders':cylinders,'separated_nonunit_cylinders':separated,
            'caps':cap_readouts,'fixed_psi_weight':'95/113',
            'universal_query_bound_from_separate_256_certificate':'968/113'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    controls = [validate(0),validate(1)]
    result = {'status':'PASS','controls':controls,
              'scope':'Actual constructions and numerical caps. No source enumeration, minimum-cut, Lean or height-lift claim.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','sources':len(controls),
                      **{k:sum(c[k] for c in controls) for k in
                         ('original_pair_checks','paired_trees','numerical_cylinders','separated_nonunit_cylinders')}}))


if __name__ == '__main__':
    main()
