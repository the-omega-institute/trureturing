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


def weighted_child_cut_check(gammas):
    """Sufficient weighted cut conditions on all 6**4 active-child patterns."""
    require(type(gammas) in (tuple, list) and len(gammas) == 4
            and all(type(g) in (int, F) and g >= 0 for g in gammas),
            "four exact nonnegative child joint coefficients")
    gammas = tuple(map(F, gammas))
    minimum, checked = None, 0
    for active in product(range(6), repeat=4):
        top = sum((min(F(1, 3), F(5-a, 9)) for a in active), F())
        weights = [a*g/3 for a, g in zip(active, gammas) if a >= 3]
        private = F()
        if len(weights) >= 2:
            total = sum(weights, F())
            private = min(total/2, total-max(weights))
        value = top + min(F(1), private)
        require(value >= 1, f"weighted child cut fails at active counts {active}: {value}")
        minimum = value if minimum is None else min(minimum, value)
        checked += 1
    return {"child_cut_checks": checked, "minimum_child_cut_bound": str(minimum)}


def couple_direct_child_caps(source, depth, caps, gammas, coupling):
    """Return one law on literal (five root, five child, seven leaf) triples.

    Exactly four literal roots occur, with their sorted order matching gammas.
    All 600 pair-of-roots and pair-of-child-triples projected-cap premises are
    checked. A successful call does not assert an arithmetic source realization.
    """
    require(type(depth) is int and depth >= 1, "positive exact seven height")
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
    cut_info = weighted_child_cut_check(gammas)
    gamma = dict(zip(roots, map(F,gammas)))
    choices = tuple(combinations(range(5),3))
    columns = {(r,c):{y for rr,cc,y in points if (rr,cc)==(r,c)}
               for r in roots for c in range(5)}
    projections = {(r,choice):set().union(*(columns[(r,c)] for c in choice))
                   for r in roots for choice in choices}
    projected_checks = 0
    for r,s in combinations(roots,2):
        for left,right in product(choices,repeat=2):
            leaves = projections[(r,left)] | projections[(s,right)]
            require(coupling['projected_capacity'](7,depth,leaves,caps) == 1,
                    f"restricted pair projection fails: {r},{left}; {s},{right}")
            projected_checks += 1

    start, finish = ('source',), ('public',0,0)
    edges = []
    for r in roots:
        edges.append((start,('root',r),F(1,3)))
        for c in range(5):
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
    return law, {**cut_info, "source_points":len(points), "selected_points":len(law),
                 "literal_roots":roots, "restricted_pair_checks":projected_checks,
                 "network_edges":len(edges), "flow_denominator":denominator,
                 "augmentations":augmentations,
                 "child_joint_coefficients":[str(gamma[r]) for r in roots],
                 "root_seven_child_multiplicities":[multiplicities[r] for r in roots],
                 "inferred_root_joint_coefficients":[str(multiplicities[r]*gamma[r]) for r in roots]}


def couple_incidence_caps(source, depth, coupling, *, weighted=False, special_root=None):
    """Apply incidence caps with zero, one, or two doubled roots."""
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
    if weighted:
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
    law,info = couple_direct_child_caps(points,depth,caps,gammas,coupling)
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
    return literal,{**info,"weighted":weighted,"designated_literal_root":special_root,
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
    require(coupling['projected_capacity'](7,depth,{y for r,c,y in points},fivecaps)==1,
            "standalone full five-ary seven projection")
    nonrobust=[]
    for r in roots:
        choice=(0,1,4) if r==1 else (0,1,2)
        expected=F(2,3) if r==1 else F(8,9)
        value=coupling['projected_capacity'](7,depth,
              {y for rr,c,y in points if rr==r and c in choice},caps)
        require(value==expected, "explicit failed single-root triple projection")
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
        if value==1:
            # Added incidences can repair this particular obstruction. Check
            # every pair/triple before classifying the deletion as preserving.
            remaining={z for z in points if z[:2]!=(r,c)}
            choices=tuple(combinations(range(5),3))
            projections={(rr,T):{y for rrr,cc,y in remaining if rrr==rr and cc in T}
                         for rr in roots for T in choices}
            found=None
            for rr,ss in combinations(roots,2):
                for ll,qq in product(choices,repeat=2):
                    trial=coupling['projected_capacity'](7,depth,
                          projections[(rr,ll)]|projections[(ss,qq)],caps)
                    if trial<1:
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
        require(value==F(8,9), "each sparse-root occupied-child deletion has a failed pair projection")
    occupied_deletions=deletions+len(occupied[1])
    return {"occupied_child_counts":[len(occupied[r]) for r in roots],
            "missing_child_under_occupied_root":{"root":1,"child":4,"modulus":25,"residue":21},
            "missing_seven_root_digits":[0],"standalone_fiveary_projection":True,
            "nonrobust_root_projection_capacities":nonrobust,
            "failed_full_child_deletions":deletions,
            "failed_occupied_child_deletions":occupied_deletions,
            "full_child_deletions_preserving_product_blocking":preserving,
            "deletion_obstruction_capacity":"8/9"}


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
    result={'plain':plain,'third_height':third,'weighted':weighted,'two_weighted':two_weighted,
            'scope':'One actual law; exact ordinary finite controls, not Lean, optimized Gamma, or odd-cover realization.'}
    payload=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload,end='')


if __name__=='__main__':
    main()
