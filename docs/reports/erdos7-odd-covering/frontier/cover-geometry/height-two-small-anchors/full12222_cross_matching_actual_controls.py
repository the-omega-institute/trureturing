#!/usr/bin/env python3
"""A complete nonrobust H5/J4 matching source with off-anchor J fine mass1/4.

All owners and complete fibres are retained. Reads only the named sibling
helper, writes only --output, and uses no directory traversal.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
import json
from pathlib import Path
import runpy

_helper = runpy.run_path(str(Path(__file__).with_name('small_anchor_actual_controls.py')))
N, SELECT, D = (_helper[k] for k in ('N','SELECT','DIVISORS'))
require, tree_exists, numerical_caps, original_integer = (
    _helper[k] for k in ('require','tree_exists','numerical_caps','original_integer'))
R,H,J = 1,0,1
W,WH,WJ = Q(3,5),Q(1,4),Q(3,20)


def category(residue):
    col = residue % 7
    return 'H' if col == H else ('J' if col == J else 'other')


def table_cap(d,cat,component):
    if component == 'lambda':
        if d == 5: return W/3
        if d == 25: return W/5
        if cat == 'H': return Q(0)
        if d == 35: return W/12 if cat == 'J' else W/4
        if d == 175: return W/20 if cat == 'J' else 3*W/20
        if d == 245: return W/12
        if d == 1225: return W/20
    if component == 'pi':
        if d == 5: return WH+WJ
        if d == 25: return WH/5+WJ/4
        if cat == 'other': return Q(0)
        if d == 35: return WH if cat == 'H' else WJ
        if d in (175,245,1225): return WH/5 if cat == 'H' else WJ/4
    if component == 'nu':
        if d == 7: return {'H':WH,'J':W/4+WJ,'other':3*W/4}[cat]
        if d == 49: return {'H':WH/5,'J':W/4+WJ/4,'other':W/4}[cat]
    raise ValueError('unexpected cap-table input')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    source = {(R,0):frozenset({(H,0)})}
    for i in range(1,5):
        source[R,i] = frozenset({(H,i),(J,i-1)})
    outside_columns = {0:(2,3),2:(2,4),3:(3,4)}
    marker = (J,4)
    for r,cols in outside_columns.items():
        fibre = frozenset({(g,h) for g in cols for h in range(5)}|{marker})
        for c in range(N[r]):
            source[r,c] = fibre
    require(len(source) == 19 and all(source.values()),'19 original nonempty fibres')
    restrictions = {r:list(combinations(range(N[r]),SELECT[r])) for r in range(4)}
    projections = {r:[frozenset().union(*(source[r,c] for c in cs))
                     for cs in restrictions[r]] for r in range(4)}
    pair_count = 0
    for r,s in combinations(range(4),2):
        for f,g in product(projections[r],projections[s]):
            require(tree_exists(f|g,3,3),'every original paired ternary-tree premise')
            pair_count += 1
    require(pair_count == 480,'all480 original legal pairs')
    require(tree_exists(frozenset().union(*source.values()),5,5),'actual standalone five-tree')
    require(all(not all(tree_exists(f,3,3) for f in projections[r]) for r in range(4)),
            'no individually robust root')
    anchors = [(0,i,j) for i,j in combinations(range(1,5),2)]
    psi = defaultdict(Q)
    trees = 0
    for anchor_index,anchor in enumerate(anchors):
        F = frozenset().union(*(source[R,c] for c in anchor))
        require(len(F) == 5 and sum(g == H for g,h in F) == 3,'complete original3+2 anchor')
        component = defaultdict(Q)
        for r,cols in outside_columns.items():
            for index,cs in enumerate(restrictions[r]):
                outer_col = cols[(anchor_index+index)%2]
                outside = {(outer_col,h) for h in range(3)}
                tree = F | {marker} | outside
                actual_other = frozenset().union(*(source[r,c] for c in cs))
                require(len(tree) == 9 and tree_exists(tree,3,3),'selected ternary tree')
                require(tree <= F|actual_other,'tree in original complete paired union')
                leaves = tree-F
                require(len(leaves) == 4 and leaves <= actual_other,'four actual puncture survivors')
                require(not any(g == H for g,h in leaves),'whole-H puncture')
                owner = cs[index%len(cs)]
                require(leaves <= source[r,owner],'original owner lift')
                for g,h in leaves:
                    component[r,owner,g,h] += Q(1,3*len(restrictions[r])*4)
                trees += 1
        require(sum(component.values()) == 1,'each original-anchor puncture probability')
        require(all((g,h) not in F for r,c,g,h in component),'complete-F global fine exclusion')
        for p,m in component.items():
            psi[p] += m/len(anchors)
    require(trees == 156,'six anchors times26 original other-root restrictions')
    eta_h = {(R,c,H,c):Q(1,5) for c in range(5)}
    eta_j = {(R,c,J,c-1):Q(1,4) for c in range(1,5)}
    lam = {p:W*m for p,m in psi.items()}
    pi = defaultdict(Q)
    for p,m in eta_h.items(): pi[p] += WH*m
    for p,m in eta_j.items(): pi[p] += WJ*m
    nu = defaultdict(Q,lam)
    for p,m in pi.items(): nu[p] += m
    readouts = {}
    cylinder_count = 0
    laws = [('psi',psi,Q(1)),('eta_H',eta_h,Q(1)),('eta_J',eta_j,Q(1)),
            ('lambda',lam,W),('pi',pi,WH+WJ),('nu',nu,Q(1))]
    for name,law,total in laws:
        require(sum(law.values()) == total,name+' fixed total mass')
        require(all(m > 0 and (g,h) in source[r,c] for (r,c,g,h),m in law.items()),
                name+' original actual support')
        caps,count = numerical_caps(law)
        cylinder_count += count
        readouts[name] = list(map(str,caps))
    require(all(r != R and g != H for r,c,g,h in psi),'psi entire R and H exclusion')
    marker_mass = sum(m for (r,c,g,h),m in psi.items() if (g,h) == marker)
    require(marker not in frozenset().union(*(source[R,c] for c in range(5))),
            'marked original J fine label is absent at R')
    require(marker_mass == Q(1,4) and marker_mass > Q(1,8),
            'safe full-J1/4 cap is necessary in this actual source')
    original_marker_residue = J+7*marker[1]
    require(sum(m for p,m in psi.items() if original_integer(p)%49 == original_marker_residue)
            == marker_mass,'marked mass in original numerical49 cylinder')
    table_checks = 0
    for name,law in [('lambda',lam),('pi',pi),('nu',nu)]:
        for d in (tuple(d for d in D if d%5 == 0) if name != 'nu' else (7,49)):
            values = [Q(0)]*d
            for p,m in law.items(): values[original_integer(p)%d] += m
            for residue,mass in enumerate(values):
                if name == 'lambda' and residue%5 == R:
                    require(mass == 0,'lambda original R cylinders zero')
                elif name == 'pi' and residue%5 != R:
                    require(mass == 0,'pi other-root cylinders zero')
                else:
                    require(mass <= table_cap(d,category(residue),name),name+' root/category numerical cap')
                table_checks += 1
    result = {'status':'PASS','source_name':'four_cross_doubles_with_off_R_J_label',
              'actual_points':sum(map(len,source.values())),'original_owners':len(source),
              'original_pair_checks':pair_count,'standalone':True,'no_individually_robust_root':True,
              'original_anchors':len(anchors),'paired_tree_constructions':trees,
              'numerical_cylinders':cylinder_count,'root_category_table_checks':table_checks,
              'marker_original49_residue':original_marker_residue,'psi_marker_mass':str(marker_mass),
              'marker_is_not_one_of_four_R_J_labels':True,'global_J_1_over_8_cap_fails':True,
              'safe_global_J_fine_cap':'1/4','caps':readouts,
              'query_bound_from_separate46656_certificate':'691/80',
              'scope':'Complete source construction controls; not exhaustive sources, minimum cut, Lean or arbitrary height.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in
                     ('status','actual_points','original_pair_checks','paired_tree_constructions',
                      'numerical_cylinders','root_category_table_checks','psi_marker_mass')}))


if __name__ == '__main__':
    main()
