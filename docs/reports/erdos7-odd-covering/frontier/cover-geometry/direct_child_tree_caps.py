#!/usr/bin/env python3
"""Exact ordinary direct child-tree coupling; no Lean or minimax certification.

The finite-flow primitives are supplied from tree_cap_coupling.py so that this
constructor reuses the existing exact flow and projected-capacity algorithms.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json
import runpy


def require(condition, message):
    if not condition:
        raise ValueError(message)


def contains_complete_seven_tree(leaves, depth, branching):
    """Literal lowest-digit-first subtree existence, not fractional capacity."""
    require(type(depth) is int and depth>=1 and type(branching) is int
            and 1<=branching<=7,"exact finite seven-tree parameters")
    level=set(leaves)
    require(all(type(y) is int and 0<=y<7**depth for y in level),
            "literal leaves in the complete seven-tree carrier")
    for b in range(depth-1,-1,-1):
        level={v for v in range(7**b)
               if sum(v+d*7**b in level for d in range(7))>=branching}
    return 0 in level


def full_six_root_fiveary_projection(depth):
    """The exact seven projection of the displayed source controls."""
    require(type(depth) is int and depth>=1,"positive seven projection height")
    tails=[0]
    for b in range(depth-1):
        tails=[v+d*7**b for v in tails for d in range(5)]
    return {g+7*v for g in range(1,7) for v in tails}


def tree_existence_controls(coupling):
    """Two countercontrols distinguish fractional capacity from literal trees."""
    examples=((3,{g+7*v for g in range(7) for v in range(2)}),
              (5,{g+7*v for g in range(4) for v in range(5)}
                 |{4+7*v for v in range(3)}|{5+7*v for v in range(2)}))
    for branching,leaves in examples:
        caps={(b,v):F(1,branching**b) for b in (1,2) for v in range(7**b)}
        require(coupling['projected_capacity'](7,2,leaves,caps)==1,
                "countercontrol has feasible fractional prefix capacity")
        require(not contains_complete_seven_tree(leaves,2,branching),
                "countercontrol has no complete requested-branching tree")
    return {"fractional_capacity_does_not_certify_tree_controls":len(examples)}


def weighted_child_cut_check(gammas, *, occupancies=None):
    """Sufficient weighted cuts on all declared active-child count profiles.

    The default is the original five-child, three-selected interface. Actual
    occupancies use n_r children and q_r=n_r-2 selected actual children.
    """
    require(type(gammas) in (tuple, list) and len(gammas) == 4
            and all(type(g) in (int, F) and g >= 0 for g in gammas),
            "four exact nonnegative child joint coefficients")
    gammas=tuple(map(F,gammas))
    if occupancies is None:
        occupancies=(5,)*4
    require(type(occupancies) in (tuple,list) and len(occupancies)==4
            and all(type(n) is int and 3<=n<=5 for n in occupancies),
            "four exact actual child counts between three and five")
    selections=tuple(n-2 for n in occupancies)
    minimum,checked=None,0
    for active in product(*(range(n+1) for n in occupancies)):
        top=sum((min(F(1,3),F(n-a,9)) for n,a in zip(occupancies,active)),F())
        weights=[a*g/q for a,g,q in zip(active,gammas,selections) if a>=q]
        private=F()
        if len(weights)>=2:
            total=sum(weights,F())
            private=min(total/2,total-max(weights))
        value=top+min(F(1),private)
        require(value>=1,f"weighted child cut fails at active counts {active}: {value}")
        minimum=value if minimum is None else min(minimum,value)
        checked+=1
    return {"child_cut_checks":checked,"minimum_child_cut_bound":str(minimum)}


def couple_direct_child_caps(source, depth, caps, gammas, coupling, *, actual_occupancy=False):
    """Return one law on literal (five root, five child, seven leaf) triples.

    Exactly four literal roots occur, with their sorted order matching gammas.
    By default all 600 original pair/triple premises and all five child nodes
    per root are retained. With actual_occupancy=True, n_r>=3 actual children
    are used and every pair of q_r=n_r-2 actual-child selections is checked.
    A successful call does not assert an arithmetic source realization.
    """
    require(type(depth) is int and depth >= 1, "positive exact seven height")
    require(type(actual_occupancy) is bool, "explicit actual-occupancy mode")
    points = list(source)
    require(points and all(type(z) in (tuple, list) and len(z) == 3
                           and all(type(a) is int for a in z) for z in points),
            "nonempty literal integer triples")
    points = [tuple(z) for z in points]
    require(len(points) == len(set(points)), "distinct literal source triples")
    require(all(0 <= r < 5 and 0 <= c < 5 and 0 <= y < 7**depth for r,c,y in points),
            "source inside the declared literal carrier")
    roots = sorted({r for r,c,y in points})
    require(len(roots) == 4, "exactly four occupied first-five roots")
    expected = {(b,v) for b in range(1,depth+1) for v in range(7**b)}
    require(type(caps) is dict and set(caps) == expected
            and all(type(b) is int and type(v) is int for b,v in caps)
            and all(type(w) in (int,F) and w >= 0 for w in caps.values()),
            "complete exact nonnegative seven-prefix capacities")
    caps = {key:F(w) for key,w in caps.items()}
    occupied={r:sorted({c for rr,c,y in points if rr==r}) for r in roots}
    if actual_occupancy:
        require(all(3<=len(occupied[r])<=5 for r in roots),
                "actual-occupancy direct flow requires three to five children per root")
        carriers=occupied
        sizes={r:len(occupied[r])-2 for r in roots}
        cut_info=weighted_child_cut_check(gammas,occupancies=[len(occupied[r]) for r in roots])
        mode_info={"actual_occupancy":True,
                   "occupied_child_counts":[len(occupied[r]) for r in roots],
                   "local_subset_sizes":[sizes[r] for r in roots]}
    else:
        carriers={r:tuple(range(5)) for r in roots}
        sizes={r:3 for r in roots}
        cut_info=weighted_child_cut_check(gammas)
        mode_info={}
    gamma=dict(zip(roots,map(F,gammas)))
    choices={r:tuple(combinations(carriers[r],sizes[r])) for r in roots}
    columns={(r,c):{y for rr,cc,y in points if (rr,cc)==(r,c)}
             for r in roots for c in carriers[r]}
    projections={(r,choice):set().union(*(columns[(r,c)] for c in choice))
                 for r in roots for choice in choices[r]}
    projected_checks=0
    for r,s in combinations(roots,2):
        for left,right in product(choices[r],choices[s]):
            leaves=projections[(r,left)]|projections[(s,right)]
            require(coupling['projected_capacity'](7,depth,leaves,caps)==1,
                    f"restricted pair projection fails: {r},{left}; {s},{right}")
            projected_checks+=1

    start, finish = ('source',), ('public',0,0)
    edges = []
    for r in roots:
        edges.append((start,('root',r),F(1,3)))
        for c in carriers[r]:
            edges.append((('root',r),('private',r,c,0,0),F(1,9)))
            for b,v in sorted(expected):
                edges.append((('private',r,c,b-1,v % 7**(b-1)),
                              ('private',r,c,b,v),gamma[r]*caps[(b,v)]))
    for b,v in sorted(expected):
        edges.append((('public',b,v),('public',b-1,v % 7**(b-1)),caps[(b,v)]))
    for r,c,y in sorted(points):
        edges.append((('private',r,c,depth,y),('public',depth,y),F(1)))
    denominator = lcm(*(w.denominator for _,_,w in edges))
    flow, augmentations = coupling['_unit_flow'](edges,start,finish,denominator)
    law = {(r,c,y):flow[(('private',r,c,depth,y),('public',depth,y))]
           for r,c,y in sorted(points)}
    law = {point:w for point,w in law.items() if w > 0}
    require(set(law) <= set(points) and sum(law.values(),F()) == 1,
            "one actual supported probability")
    for r in roots:
        require(sum((w for (rr,c,y),w in law.items() if rr==r),F()) <= F(1,3),
                "same-law first-five root cap")
        for c in range(5):
            require(sum((w for (rr,cc,y),w in law.items() if (rr,cc)==(r,c)),F()) <= F(1,9),
                    "same-law second-five prefix cap")
    multiplicities = {r:max(len({c for rr,c,y in points if rr==r and y%7==u})
                           for u in range(7)) for r in roots}
    for (b,v),cap in sorted(caps.items()):
        require(sum((w for (r,c,y),w in law.items() if y%7**b==v),F()) <= cap,
                "same-law pure seven-prefix cap")
        for r in roots:
            for c in range(5):
                joint = sum((w for (rr,cc,y),w in law.items()
                             if (rr,cc)==(r,c) and y%7**b==v),F())
                require(joint <= gamma[r]*cap, "same-law child/seven-prefix cap")
            joint = sum((w for (rr,c,y),w in law.items() if rr==r and y%7**b==v),F())
            require(joint <= multiplicities[r]*gamma[r]*cap,
                    "same-law root/seven cap from actual child incidence")
    return law, {**cut_info, **mode_info, "source_points":len(points), "selected_points":len(law),
                 "literal_roots":roots, "restricted_pair_checks":projected_checks,
                 "network_edges":len(edges), "flow_denominator":denominator,
                 "augmentations":augmentations,
                 "child_joint_coefficients":[str(gamma[r]) for r in roots],
                 "root_seven_child_multiplicities":[multiplicities[r] for r in roots],
                 "inferred_root_joint_coefficients":[str(multiplicities[r]*gamma[r]) for r in roots]}


def couple_incidence_caps(source, depth, coupling, *, weighted=False, special_root=None,
                          actual_occupancy=False):
    """Use the original incidence rules or occupancy-dependent uniform caps.

    Actual-occupancy mode allows incidence multiplicity two in every root.
    Its coefficient is selected from the measured original child counts;
    weighted and special_root belong to the original interface only.
    """
    # Core validates literal inputs; these preliminary checks only select weights.
    points = list(source)
    require(points and all(type(z) in (tuple,list) and len(z)==3
                           and all(type(a) is int for a in z) for z in points),
            "nonempty literal integer triples")
    roots = sorted({r for r,c,y in points})
    require(len(roots)==4, "exactly four occupied first-five roots")
    multiplicities = {r:max(len({c for rr,c,y in points if rr==r and y%7==u})
                           for u in range(7)) for r in roots}
    require(type(depth) is int and depth>=1, "positive exact seven height")
    require(type(actual_occupancy) is bool,"explicit actual-occupancy mode")
    consumer_info={}
    if actual_occupancy:
        require(not weighted and special_root is None,
                "actual-occupancy mode selects its own uniform coefficient")
        occupancies=[len({c for rr,c,y in points if rr==r}) for r in roots]
        require(all(3<=n<=5 for n in occupancies),
                "actual-occupancy consumer requires three to five children per root")
        require(max(multiplicities.values())<=2,
                "actual-occupancy consumer permits at most two children per root/seven-root pair")
        if min(occupancies)<=3:
            coefficient,rule=F(4,15),"one-root-with-at-most-three-children"
        elif sum(n<=4 for n in occupancies)>=2:
            coefficient,rule=F(3,11),"at-least-two-roots-with-at-most-four-children"
        elif min(occupancies)==4:
            coefficient,rule=F(2,7),"exactly-one-missing-child-nonstrict-threshold"
        else:
            raise ValueError("the actual-occupancy incidence consumer requires a missing actual child; use the original interface for all-full roots")
        gammas=[coefficient]*4
        designated_roots=[]
        consumer_info={"occupancy_coefficient_rule":rule}
    elif weighted:
        doubled = [r for r in roots if multiplicities[r] > 1]
        require(len(doubled)<=2 and max(multiplicities.values())<=2,
                "at most two roots with multiplicity two; all others at most one")
        if len(doubled)==2:
            require(special_root is None, "two doubled roots are selected from their actual incidences")
            designated_roots=doubled
            gammas=[F(1,5) if r in doubled else F(2,5) for r in roots]
        else:
            if special_root is None:
                special_root = doubled[0] if doubled else roots[0]
            require(type(special_root) is int and special_root in roots
                    and all(multiplicities[r]<=1 for r in roots if r!=special_root),
                    "designated actual root contains every doubled incidence")
            designated_roots=[special_root]
            gammas = [F(1,5) if r==special_root else F(1,3) for r in roots]
    else:
        require(max(multiplicities.values())<=1, "at most one actual child per root/seven-root pair")
        gammas = [F(3,10)]*4
        designated_roots=[]
    caps = {(b,v):F(1,3**b) for b in range(1,depth+1) for v in range(7**b)}
    law,info = couple_direct_child_caps(points,depth,caps,gammas,coupling,
                                      actual_occupancy=actual_occupancy)
    root_beta = max(map(F,info['inferred_root_joint_coefficients']))
    child_beta = max(gammas)
    numerical_caps = {}
    for a,b in product(range(3),range(depth+1)):
        # Every cap below belongs to the same constructed law. Intersecting the
        # marginal and mixed caps is necessary for the two-doubled-root result.
        value=min(F(1,3**a),F(1,3**b))
        if a and b:
            value=min(value,(root_beta if a==1 else child_beta)/3**b)
        numerical_caps[5**a*7**b] = value
    literal = {}
    period = 25*7**depth
    for (r,c,y),w in law.items():
        x5=r+5*c
        x=x5+25*((y-x5)*pow(25,-1,7**depth) % 7**depth)
        require((x%5,(x//5)%5,x%7**depth)==(r,c,y) and 0<=x<period,
                "literal CRT transport")
        literal[x]=w
    require(len(literal)==len(law) and sum(literal.values(),F())==1,
            "one normalized actual numerical-period law")
    maxima={}
    for d,cap in numerical_caps.items():
        masses=defaultdict(F)
        for x,w in literal.items():masses[x%d]+=w
        maxima[d]=max(masses.values())
        require(maxima[d]<=cap,"same-law original numerical cylinder caps")
    labels=tuple(sorted(numerical_caps))
    theorem=sum((numerical_caps[lcm(d,e)] for d,e in product(labels,repeat=2)),F())
    actual=sum((maxima[lcm(d,e)] for d,e in product(labels,repeat=2)),F())
    require(actual<=theorem,"same-law full independent-phase LCM upper")
    if actual_occupancy:
        consumer_info["theorem_LCM_strictly_below_nine"]=theorem<9
    return literal,{**info,**consumer_info,"weighted":weighted,"designated_literal_root":special_root,
                    "designated_literal_roots":designated_roots,
                    "original_labels":labels,"ordered_pairs":len(labels)**2,
                    "theorem_LCM_upper":str(theorem),"actual_LCM_upper":str(actual),
                    "cylinder_caps":{str(d):str(v) for d,v in numerical_caps.items()},
                    "actual_law":[{"residue":x,"mass":str(w)} for x,w in sorted(literal.items())]}


def irregular_incidence_source(depth=2, *, extra_incidence=False, double_roots=()):
    """A missing-child four-root family, with all roots individually nonrobust.

    Root one uses child/first-seven incidences (0,1),(1,6),(2,2),(2,3),
    (3,4),(3,5), so literal child four and original mod25 residue21 are absent.
    Its second-seven digits are all0,...,4. In roots two through four, child c
    uses first-seven digit c+1; child zero has second digits {r-1,r}, the other
    children have digits0,...,4. All subsequent seven digits range over0,...,4.
    An optional added incidence at root four doubles only that root's maximum
    number of actual children meeting one first-seven prefix.
    """
    require(type(depth) is int and depth>=2, "source family starts at seven height two")
    tails=[0]
    for j in range(depth-2):
        tails=[z+d*7**j for z in tails for d in range(5)]
    first_incidence=((0,1),(1,6),(2,2),(2,3),(3,4),(3,5))
    source=[(1,c,g+7*v+49*t) for c,g in first_incidence
            for v in range(5) for t in tails]
    source += [(r,c,c+1+7*v+49*t) for r in range(2,5) for c in range(5)
               for v in ((r-1,r) if c==0 else range(5)) for t in tails]
    require(type(double_roots) in (tuple,list) and len(double_roots)<=2
            and all(type(r) is int and r in (2,3,4) for r in double_roots)
            and len(double_roots)==len(set(double_roots)), "distinct designated full literal roots")
    if extra_incidence:
        require(not double_roots, "use one form of the incidence-addition argument")
        double_roots=(4,)
    source += [(r,0,2+7*v+49*t) for r in double_roots for v in range(5) for t in tails]
    require(len(source)==(96+5*len(double_roots))*5**(depth-2),
            "exact size of the missing-child source family")
    return source


def incidence_family_controls(source, depth, coupling, *, expected_failed_deletions=15):
    """Exact source boundaries for the displayed missing-child family."""
    points=set(source)
    roots=sorted({r for r,c,y in points})
    require(roots==[1,2,3,4], "four literal roots in the source family")
    occupied={r:{c for rr,c,y in points if rr==r} for r in roots}
    require(occupied[1]=={0,1,2,3} and all(occupied[r]==set(range(5)) for r in (2,3,4)),
            "root one misses child four; exactly three roots have all five children")
    require(all(r+5*c!=21 for r,c,y in points), "original mod25 residue21 is missing")
    require({y%7 for r,c,y in points}==set(range(1,7)), "original first-seven digit zero is missing")
    caps={(b,v):F(1,3**b) for b in range(1,depth+1) for v in range(7**b)}
    fivecaps={(b,v):F(1,5**b) for b in range(1,depth+1) for v in range(7**b)}
    projection={y for r,c,y in points}
    require(projection==full_six_root_fiveary_projection(depth)
            and contains_complete_seven_tree(projection,depth,5),
            "literal standalone full five-ary seven projection")
    require(coupling['projected_capacity'](7,depth,projection,fivecaps)==1,
            "standalone projection also supports its pure prefix caps")
    choices=tuple(combinations(range(5),3))
    original_projections={(r,T):{y for rr,c,y in points if rr==r and c in T}
                          for r in roots for T in choices}
    original_checks=0
    for r,ss in combinations(roots,2):
        for left,right in product(choices,repeat=2):
            require(contains_complete_seven_tree(
                    original_projections[(r,left)]|original_projections[(ss,right)],depth,3),
                    "literal original pair/triple product-blocking condition")
            original_checks+=1
    nonrobust=[]
    for r in roots:
        choice=(0,1,4) if r==1 else (0,1,2)
        expected=F(2,3) if r==1 else F(8,9)
        value=coupling['projected_capacity'](7,depth,
              {y for rr,c,y in points if rr==r and c in choice},caps)
        require(value==expected and not contains_complete_seven_tree(
                {y for rr,c,y in points if rr==r and c in choice},depth,3),
                "explicit failed single-root triple projection")
        nonrobust.append(str(value))
    full_roots=[r for r in roots if len(occupied[r])==5]
    deletions=0
    preserving=[]
    for r,c in product(full_roots,range(5)):
        other=next(s for s in full_roots if s!=r)
        if c==0:
            left=right=(0,1,2)
        else:
            d,e=[a for a in range(1,5) if a!=c][:2]
            left=(c,d,e)
            right=(0,d,e)
        leaves={y for rr,cc,y in points if (rr,cc)!=(r,c)
                and ((rr==r and cc in left) or (rr==other and cc in right))}
        value=coupling['projected_capacity'](7,depth,leaves,caps)
        if contains_complete_seven_tree(leaves,depth,3):
            # Added incidences can repair this particular obstruction. Check
            # literal trees on every pair/triple before declaring preservation.
            remaining={z for z in points if z[:2]!=(r,c)}
            choices=tuple(combinations(range(5),3))
            projections={(rr,T):{y for rrr,cc,y in remaining if rrr==rr and cc in T}
                         for rr in roots for T in choices}
            found=None
            for rr,ss in combinations(roots,2):
                for ll,qq in product(choices,repeat=2):
                    projected=projections[(rr,ll)]|projections[(ss,qq)]
                    trial=coupling['projected_capacity'](7,depth,projected,caps)
                    if not contains_complete_seven_tree(projected,depth,3):
                        found=trial
                        break
                if found is not None:
                    break
            if found is None:
                preserving.append([r,c])
                continue
            value=found
        require(value==F(8,9), "failed full-child deletion has a checked pair-projection obstruction")
        deletions+=1
    require(deletions+len(preserving)==15 and deletions==expected_failed_deletions,
            "all fifteen full-child deletion outcomes agree with the declared control")
    for c in sorted(occupied[1]):
        surviving=next(a for a in (2,3) if a!=c)
        columns=(2,3) if surviving==2 else (4,5)
        left=(c,4,surviving)
        right=(0,columns[0]-1,columns[1]-1)
        leaves={y for rr,cc,y in points if (rr,cc)!=(1,c)
                and ((rr==1 and cc in left) or (rr==2 and cc in right))}
        value=coupling['projected_capacity'](7,depth,leaves,caps)
        require(value==F(8,9) and not contains_complete_seven_tree(leaves,depth,3),
                "each sparse-root occupied-child deletion has a failed pair projection")
    occupied_deletions=deletions+len(occupied[1])
    return {"occupied_child_counts":[len(occupied[r]) for r in roots],
            "missing_child_under_occupied_root":{"root":1,"child":4,"modulus":25,"residue":21},
            "missing_seven_root_digits":[0],"standalone_fiveary_projection":True,
            "original_pair_triple_tree_checks":original_checks,
            "nonrobust_root_projection_capacities":nonrobust,
            "failed_full_child_deletions":deletions,
            "failed_occupied_child_deletions":occupied_deletions,
            "full_child_deletions_preserving_product_blocking":preserving,
            "deletion_obstruction_capacity":"8/9"}


def actual_occupancy_source(depth=2):
    """A 121*5**(depth-2)-point source with n=(4,4,5,5), m=(2,2,2,2).

    This is an abstract actual source, not a claimed covering-system residual.
    It lies outside the earlier at-most-two-doubled-root consumer by its four
    measured doubled incidences; no comparison with all earlier selectors is
    asserted.
    """
    source=set(irregular_incidence_source(depth))
    source={z for z in source if z[:2]!=(2,1)}
    tails=[0]
    for j in range(depth-2):
        tails=[z+d*7**j for z in tails for d in range(5)]
    additions=((1,0,6),(2,0,6),(2,2,2),(2,3,6),(3,0,2),(4,0,2))
    source.update((r,c,g+7*v+49*t) for r,c,g in additions
                  for v in range(5) for t in tails)
    require(len(source)==121*5**(depth-2),"exact actual-occupancy source size")
    return sorted(source)


def occupancy_branch_sources(depth=2):
    """Controls of the one-missing-child and three-child coefficient branches."""
    base=set(irregular_incidence_source(depth))
    tails=[0]
    for j in range(depth-2):
        tails=[z+d*7**j for z in tails for d in range(5)]
    later=base | {(r,0,2+7*v+49*t) for r in (2,3,4)
                  for v in range(5) for t in tails}
    one_gap=later | {(1,0,6+7*v+49*t) for v in range(5) for t in tails}
    one_three={z for z in later if z[0]!=1}
    one_three.update((1,c,g+7*v+49*t) for c,g in ((0,1),(0,2),(1,1),(1,6),(2,6),(2,3))
                     for v in range(5) for t in tails)
    require(len(one_gap)==116*5**(depth-2) and len(one_three)==111*5**(depth-2),
            "exact coefficient-branch source sizes")
    return sorted(one_gap),sorted(one_three)


def occupancy_branch_source_controls(source, depth):
    """Literal tree-premise checks for the two coefficient-branch controls."""
    points=set(source)
    roots=tuple(sorted({r for r,c,y in points}))
    require(roots==(1,2,3,4),"the displayed coefficient branches retain the missing five root")
    projection={y for r,c,y in points}
    require(projection==full_six_root_fiveary_projection(depth)
            and contains_complete_seven_tree(projection,depth,5),
            "exact standalone five-ary projection of the coefficient branches")
    choices=tuple(combinations(range(5),3))
    projections={(r,T):{y for rr,c,y in points if rr==r and c in T}
                 for r in roots for T in choices}
    checked=0
    for r,ss in combinations(roots,2):
        for left,right in product(choices,repeat=2):
            require(contains_complete_seven_tree(
                    projections[(r,left)]|projections[(ss,right)],depth,3),
                    "literal coefficient-branch pair/triple product-blocking condition")
            checked+=1
    return {"standalone_fiveary_projection":True,"original_pair_triple_tree_checks":checked,
            "missing_first_five_digits":[0],"missing_first_seven_digits":[0],
            "scope":"Source controls of the coefficient branches, not a covering-residual realization or comparison with every earlier source theorem."}


def actual_occupancy_source_controls(source, depth, coupling):
    """Check the literal source facts and all original pair/triple premises."""
    points=set(source)
    roots=(1,2,3,4)
    occupied=[sorted({c for r,c,y in points if r==rr}) for rr in roots]
    require(occupied==[[0,1,2,3],[0,2,3,4],[0,1,2,3,4],[0,1,2,3,4]],
            "actual occupied child digits are retained")
    multiplicities=[max(len({c for r,c,y in points if r==rr and y%7==u})
                        for u in range(7)) for rr in roots]
    require(multiplicities==[2]*4,"all four roots have a doubled actual incidence")
    require({r for r,c,y in points}==set(roots) and {y%7 for r,c,y in points}==set(range(1,7)),
            "the original first-five and first-seven digit zero are missing")
    require(all(r+5*c not in (7,21) for r,c,y in points),
            "the original mod25 residues7 and21 are missing")
    caps={(b,v):F(1,3**b) for b in range(1,depth+1) for v in range(7**b)}
    fivecaps={(b,v):F(1,5**b) for b in range(1,depth+1) for v in range(7**b)}
    projection={y for r,c,y in points}
    require(projection==full_six_root_fiveary_projection(depth)
            and contains_complete_seven_tree(projection,depth,5),
            "literal standalone complete five-ary seven projection")
    require(coupling['projected_capacity'](7,depth,projection,fivecaps)==1,
            "standalone projection also supports its pure prefix caps")
    choices=tuple(combinations(range(5),3))
    projections={(r,T):{y for rr,c,y in points if rr==r and c in T}
                 for r in roots for T in choices}
    original_checks=0
    for r,ss in combinations(roots,2):
        for left,right in product(choices,repeat=2):
            projected=projections[(r,left)]|projections[(ss,right)]
            require(contains_complete_seven_tree(projected,depth,3),
                    "literal full original pair/triple product-blocking premise")
            require(coupling['projected_capacity'](7,depth,projected,caps)==1,
                    "the projected literal tree supports its prefix caps")
            original_checks+=1
    failed_triples=((0,1,4),(0,1,3),(0,1,2),(0,1,2))
    nonrobust=[]
    for r,T in zip(roots,failed_triples):
        value=coupling['projected_capacity'](7,depth,projections[(r,T)],caps)
        require(value==(F(2,3) if r==1 else F(8,9))
                and not contains_complete_seven_tree(projections[(r,T)],depth,3),
                "explicit nonrobust individual-root projection")
        nonrobust.append(str(value))
    try:
        couple_incidence_caps(source,depth,coupling,weighted=True)
    except ValueError as error:
        require(str(error)=="at most two roots with multiplicity two; all others at most one",
                "the old incidence consumer rejects precisely its multiplicity premise")
    else:
        raise ValueError("the old at-most-two-doubled-root consumer unexpectedly accepted")
    return {"occupied_child_counts":[4,4,5,5],
            "root_seven_child_multiplicities":multiplicities,
            "missing_first_five_digits":[0],"missing_first_seven_digits":[0],
            "missing_mod25_children_under_occupied_roots":[7,21],
            "standalone_fiveary_projection":True,
            "original_pair_triple_checks":original_checks,
            "nonrobust_root_projection_capacities":nonrobust,
            "original_incidence_consumer_rejected":True,
            "scope":"Outside the previous incidence premise; no escape from every earlier selector or covering-residual realization is asserted."}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--coupling-script',type=Path,default=Path(__file__).with_name('tree_cap_coupling.py'))
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    coupling=runpy.run_path(str(args.coupling_script))
    source=irregular_incidence_source(2)
    _,plain=couple_incidence_caps(source,2,coupling)
    plain['source_boundary_controls']=incidence_family_controls(source,2,coupling)
    plain['actual_source']=sorted(source)
    require(F(plain['theorem_LCM_upper'])==F(353,45)<9,"multiplicity-one target")
    third_source=irregular_incidence_source(3)
    _,third=couple_incidence_caps(third_source,3,coupling)
    third['source_boundary_controls']=incidence_family_controls(third_source,3,coupling)
    third['actual_source']=sorted(third_source)
    require(F(third['theorem_LCM_upper'])==F(1178,135)<9,"third seven-height target")
    weighted_source=irregular_incidence_source(2,extra_incidence=True)
    _,weighted=couple_incidence_caps(weighted_source,2,coupling,weighted=True)
    weighted['source_boundary_controls']=incidence_family_controls(weighted_source,2,coupling)
    weighted['actual_source']=sorted(weighted_source)
    require(F(weighted['theorem_LCM_upper'])==F(1157,135)<9,"one-double target")
    two_source=irregular_incidence_source(2,double_roots=(3,4))
    _,two_weighted=couple_incidence_caps(two_source,2,coupling,weighted=True)
    two_weighted['actual_source']=sorted(two_source)
    two_weighted['source_boundary_controls']=incidence_family_controls(
        two_source,2,coupling,expected_failed_deletions=14)
    require(F(two_weighted['theorem_LCM_upper'])==F(394,45)<9,"two-double target after same-law cap intersection")
    require(F(two_weighted['cylinder_caps']['175'])==F(1,9),"pure child cap clips the depth-(2,1) joint cap")
    occupied_source=actual_occupancy_source(2)
    _,occupied=couple_incidence_caps(occupied_source,2,coupling,actual_occupancy=True)
    occupied['actual_source']=occupied_source
    occupied['source_boundary_controls']=actual_occupancy_source_controls(occupied_source,2,coupling)
    require(F(occupied['theorem_LCM_upper'])==F(79,9)<9,"actual-occupancy all-four-doubled target")
    require(occupied['restricted_pair_checks']==376 and occupied['child_cut_checks']==900,
            "actual-child projection and cut carriers")
    one_gap_source,one_three_source=occupancy_branch_sources(2)
    _,one_gap=couple_incidence_caps(one_gap_source,2,coupling,actual_occupancy=True)
    _,one_three=couple_incidence_caps(one_three_source,2,coupling,actual_occupancy=True)
    one_gap['actual_source']=one_gap_source
    one_three['actual_source']=one_three_source
    one_gap['source_boundary_controls']=occupancy_branch_source_controls(one_gap_source,2)
    one_three['source_boundary_controls']=occupancy_branch_source_controls(one_three_source,2)
    require(F(one_gap['theorem_LCM_upper'])==9 and not one_gap['theorem_LCM_strictly_below_nine'],
            "one missing child reaches the non-strict threshold only")
    require(F(one_three['theorem_LCM_upper'])==F(1171,135)<9,
            "one three-child root coefficient target")
    result={'tree_existence_controls':tree_existence_controls(coupling),
            'plain':plain,'third_height':third,'weighted':weighted,'two_weighted':two_weighted,
            'actual_occupancy':occupied,'actual_occupancy_one_gap':one_gap,
            'actual_occupancy_one_three':one_three,
            'scope':'One actual law; exact ordinary finite controls, not Lean, optimized Gamma, or odd-cover realization.'}
    payload=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload,end='')


if __name__=='__main__':
    main()
