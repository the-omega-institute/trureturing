#!/usr/bin/env python3
"""One actual four-root law from occupancy-aware child restrictions.

The general finite-tree proof is in report445. This implements five-height
two with arbitrary finite seven-height; all arithmetic uses Fraction and
the original numerical modulus labels. No Lean certification is claimed.
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


def series(k):
    return 3-F(k+2,3**k)


def couple_occupied_children(source, depth, core, couple, *, weighted=False):
    """Retain literal (first-five root, second-five child, seven leaf) points.

    The constructor checks the restricted pair-cap premises. The caller's
    full product-tree premise implies them by report445; it is not inferred
    merely from constructor success. Weighted mode allows at most one root
    with all five occupied children and uses the report445 rational caps.
    """
    require(type(depth) is int and depth >= 1, "positive seven height")
    points = list(source)
    require(points and all(type(z) in (tuple,list) and len(z)==3
                           and all(type(a) is int for a in z) for z in points),
            "literal integer triples")
    points = [tuple(z) for z in points]
    require(len(points)==len(set(points)), "distinct source triples")
    require(all(0<=r<5 and 0<=c<5 and 0<=y<7**depth for r,c,y in points),
            "literal source inside five-by-five-by-seven carrier")
    roots = sorted({r for r,c,y in points})
    require(len(roots)==4, "exactly four occupied first-five roots")
    row = {r:i for i,r in enumerate(roots)}
    normalized = [(row[r],c,y) for r,c,y in points]
    active = [sorted({c for rr,c,y in normalized if rr==r}) for r in range(4)]
    restrictions = [tuple(combinations(children,len(children)-2))
                    if len(children)>=3 else ((),) for children in active]
    delta = [F(max(len(children)-2,0),len(children)) for children in active]
    caps = {(b,c):F(1,3**b) for b in range(1,depth+1) for c in range(7**b)}
    alpha, beta = [F(1,3)]*4, [F(1,2)]*4
    if weighted:
        full = [r for r in range(4) if len(active[r])==5]
        require(len(full)<=1, "weighted theorem permits at most one full child fibre")
        special = full[0] if full else 0
        alpha = [F(5 if r==special else 6,17) for r in range(4)]
        beta = [F(10 if r==special else 12,23) for r in range(4)]
        def conditional(m,q,radix,height,projected,prefix_caps):
            return couple(m,q,radix,height,projected,prefix_caps,
                          row_caps=alpha,joint_coefficients=beta)
    else:
        conditional = couple
    law,info = core(4,2,5,7,depth,normalized,caps,conditional,restrictions,
                    root_caps=alpha,joint_coefficients=beta)
    literal = {}
    modulus = 25*7**depth
    for (r,c,y),mass in law.items():
        x5=roots[r]+5*c
        x=x5+25*((y-x5)*pow(25,-1,7**depth) % 7**depth)
        require((roots[r],c,y) in points and 0<=x<modulus, "actual unique CRT lift")
        literal[x]=mass
    require(len(literal)==len(law) and sum(literal.values(),F())==1,
            "one actual probability on the original period")
    cap = {(0,b):F(1,3**b) for b in range(depth+1)}
    cap[(1,0)] = max(alpha)
    cap[(2,0)] = max(a*d for a,d in zip(alpha,delta))
    for b in range(1,depth+1):
        cap[(1,b)]=max(beta)/3**b
        cap[(2,b)]=max(z*d for z,d in zip(beta,delta))/3**b
    numerical_caps={5**a*7**b:value for (a,b),value in cap.items()}
    maxima={}
    for d,value in numerical_caps.items():
        masses=defaultdict(F)
        for x,mass in literal.items():
            masses[x%d]+=mass
        maxima[d]=max(masses.values())
        require(maxima[d]<=value, "same-law original-label cylinder cap")
    labels=tuple(sorted(numerical_caps))
    bound=sum((numerical_caps[lcm(d,e)] for d,e in product(labels,repeat=2)),F())
    actual=sum((maxima[lcm(d,e)] for d,e in product(labels,repeat=2)),F())
    require(actual<=bound, "same-law full independent-phase LCM upper")
    return literal,{**info,"literal_roots":roots,"occupied_children":active,
                   "survival_probabilities":list(map(str,delta)),"weighted":weighted,
                   "original_labels":labels,"ordered_pairs":len(labels)**2,
                   "theorem_LCM_upper":str(bound),"actual_LCM_upper":str(actual),
                   "cylinder_caps":{str(d):str(v) for d,v in numerical_caps.items()},
                   "actual_law":[{"residue":x,"mass":str(w)} for x,w in sorted(literal.items())]}


def irregular_source(depth, *, extra_child=False):
    """Report432's 21-point source, lifted through all actual seven tails.

    Its occupied child counts are (3,4,3,4). Optional extra child makes them
    (3,5,3,4) by copying an existing actual neighborhood into an empty slot;
    adding points preserves the product blocking premise.
    """
    neighborhoods={1:{1:(0,3),2:(0,2),4:(0,4,6)},
                   2:{0:(3,),1:(3,5),3:(5,),4:(1,)},
                   3:{0:(6,),2:(6,),3:(4,)},
                   4:{0:(2,6),2:(1,),3:(0,),4:(0,1)}}
    if extra_child:
        neighborhoods[2][2]=neighborhoods[2][1]
    # At height (2,1) pairwise disjoint bad-pair sets are the full product test.
    bad=[]
    for children in neighborhoods.values():
        bad.append({pair for pair in combinations(range(7),2)
                    if sum(bool(set(cols)-set(pair)) for cols in children.values())<=2})
    require(all(not(bad[r]&bad[s]) for r,s in combinations(range(4),2)),
            "reused source's full height-(2,1) product blocking")
    return [(r,c,y+7*t) for r,children in neighborhoods.items()
            for c,cols in children.items() for y in cols for t in range(7**(depth-1))]


def height_controls():
    checked,bounds=0,{}
    for occupancy in (3,4,5):
        delta=F(occupancy-2,occupancy)
        for h,k in product(range(1,16),repeat=2):
            v=sum((F(2*a+1)*delta**(a-1) for a in range(1,h+1)),F())
            bound=series(k)+(series(k)/2-F(1,6))*v
            caps={(0,b):F(1,3**b) for b in range(k+1)}
            for a in range(1,h+1):
                caps[(a,0)]=delta**(a-1)/3
                for b in range(1,k+1):
                    caps[(a,b)]=delta**(a-1)/2/3**b
            literal=sum((F((2*a+1)*(2*b+1))*caps[(a,b)]
                         for a,b in product(range(h+1),range(k+1))),F())
            require(bound==literal, "all original labels retained in height formula")
            if occupancy==3:
                require(bound==series(h)*series(k)+(series(h)-1)*(series(k)-1)/2,
                        "ternary occupied-prefix simplification")
            if (occupancy,h,k) in ((4,2,2),(3,2,2),(3,3,2),(3,4,2)):
                bounds[f"max{occupancy}_H{h}K{k}"]=str(bound)
            checked+=1
    require(bounds=={"max4_H2K2":"26/3","max3_H2K2":"209/27",
                     "max3_H3K2":"697/81","max3_H4K2":"727/81"},
            "new source-class height bounds")
    return {"exact_height_pairs":checked,**bounds}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    directory=Path(__file__).parent
    restrictions=runpy.run_path(str(directory/"subtree_restriction_coupling.py"))
    coupling=runpy.run_path(str(directory/"tree_cap_coupling.py"))
    core=restrictions["couple_child_restriction_caps"]
    couple=coupling["couple_tree_caps"]
    _,plain=couple_occupied_children(irregular_source(2),2,core,couple)
    require(F(plain["theorem_LCM_upper"])==F(26,3)<9, "max-four target")
    _,weighted=couple_occupied_children(irregular_source(2,extra_child=True),2,
                                       core,couple,weighted=True)
    require(F(weighted["theorem_LCM_upper"])==F(31532,3519)<9,
            "one-full-root weighted target")
    payload=json.dumps({"height_controls":height_controls(),
                        "weighted_pair_controls":coupling["weighted_pair_controls"](),
                        "irregular_source":plain,
                        "one_full_root_source":weighted,
                        "scope":"Exact common-law construction and controls; ordinary source theorem, not Lean certification or an odd-cover realization."},indent=2)+"\n"
    if args.output:
        args.output.write_text(payload,encoding="utf-8")
    else:
        print(payload,end="")


if __name__=="__main__":
    main()
