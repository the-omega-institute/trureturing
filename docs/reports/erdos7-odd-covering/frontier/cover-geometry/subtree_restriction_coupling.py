#!/usr/bin/env python3
"""Exact depth-two restriction averaging on one actual supported law.

Requires the existing report443 row/tree coupling and report442 fixtures.
The ordinary universal proof is separate; no numerical optimizer or Lean
certification is used here. Original divisor phases are never identified.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, lcm, prod
from pathlib import Path
import argparse
import json
import runpy


def require(condition, message):
    if not condition:
        raise ValueError(message)


def couple_depth_two_caps(m, q, p, t, radix, depth, source, caps, couple):
    """Return one law on literal (root, child, column_leaf) triples.

    Each q-root/t-child restricted column projection must support the caps.
    Equivalent per-root column signatures are grouped; all original choices
    retain their exact multiplicity. The supplied couple is report443's
    couple_tree_caps, which checks every q-row projection before each flow.
    """
    require(all(type(z) is int for z in (m,q,p,t,radix,depth))
            and 1 <= q <= m and 1 <= t <= p and radix >= 2 and depth >= 1,
            "exact positive carrier and selection sizes")
    points = list(source)
    require(points and all(type(z) in (tuple,list) and len(z) == 3
                           and all(type(a) is int for a in z) for z in points),
            "nonempty literal integer triples")
    points = [tuple(z) for z in points]
    require(len(points) == len(set(points)), "distinct actual source triples")
    require(all(0 <= r < m and 0 <= c < p and 0 <= y < radix**depth
                for r,c,y in points), "actual triples inside declared carrier")
    expected = {(b,c) for b in range(1,depth+1) for c in range(radix**b)}
    require(type(caps) is dict and set(caps) == expected
            and all(type(v) in (int,F) and v >= 0 for v in caps.values()),
            "complete nonnegative exact prefix caps")
    caps = {key:F(v) for key,v in caps.items()}
    children = [defaultdict(set) for _ in range(m)]
    for r,c,y in points:
        children[r][y].add(c)
    selections = tuple(combinations(range(p), t))
    root_groups = []
    for r in range(m):
        buckets = defaultdict(list)
        for choice in selections:
            selected = set(choice)
            signature = tuple(y for y in sorted(children[r]) if children[r][y] & selected)
            buckets[signature].append(choice)
        groups = []
        for signature, choices in sorted(buckets.items()):
            lift = {y:defaultdict(F) for y in signature}
            for choice in choices:
                selected = set(choice)
                for y in signature:
                    available = children[r][y] & selected
                    require(available, "signature retains actual children for every column")
                    for c in available:
                        lift[y][c] += F(1,len(choices)*len(available))
            require(all(sum(weights.values(),F()) == 1 for weights in lift.values()),
                    "conditional actual-child lifts are probabilities")
            groups.append((signature,len(choices),lift))
        root_groups.append(groups)
    law = defaultdict(F)
    flow_count = subset_checks = 0
    profile_weight = F()
    for profile in product(*root_groups):
        projected = [(r,y) for r,(signature,_,_) in enumerate(profile) for y in signature]
        conditional, info = couple(m,q,radix,depth,projected,caps)
        weight = prod((F(size,len(selections)) for _,size,_ in profile),start=F(1))
        profile_weight += weight
        flow_count += 1
        subset_checks += info["q_subset_checks"]
        for (r,y),mass in conditional.items():
            for c,lift_mass in profile[r][2][y].items():
                law[(r,c,y)] += weight*mass*lift_mass
    law = dict(law)
    require(profile_weight == 1 and sum(law.values(),F()) == 1,
            "all restriction profiles form one unit probability")
    require(set(law) <= set(points) and all(mass > 0 for mass in law.values()),
            "final probability has literal actual support")
    root_cap, beta, delta = F(1,m-q+1), F(q,m), F(t,p)
    root_mass = [sum((w for (rr,c,y),w in law.items() if rr == r),F()) for r in range(m)]
    child_mass = {(r,c):sum((w for (rr,cc,y),w in law.items() if (rr,cc)==(r,c)),F())
                  for r,c in product(range(m),range(p))}
    require(all(w <= root_cap for w in root_mass), "same-law root marginals")
    require(all(w <= delta*root_cap for w in child_mass.values()), "same-law child marginals")
    for (b,v),cap in sorted(caps.items()):
        pure = sum((w for (r,c,y),w in law.items() if y % radix**b == v),F())
        require(pure <= cap, "same-law pure column prefix")
        for r in range(m):
            joint = sum((w for (rr,c,y),w in law.items() if rr == r and y % radix**b == v),F())
            require(joint <= beta*cap, "same-law root/column prefix")
            for c in range(p):
                leaf = sum((w for (rr,cc,y),w in law.items()
                            if (rr,cc)==(r,c) and y % radix**b == v),F())
                require(leaf <= beta*delta*cap, "same-law child/column prefix")
    return law, {"source_points":len(points), "selected_points":len(law),
                 "original_restriction_choices":comb(p,t)**m,
                 "root_signature_counts":[len(groups) for groups in root_groups],
                 "grouped_profiles":flow_count, "q_subset_checks":subset_checks,
                 "root_cap":str(root_cap), "child_cap":str(delta*root_cap),
                 "joint_root_coefficient":str(beta), "joint_child_coefficient":str(beta*delta)}


def height_controls():
    def series(k):
        return 3-F(k+2,3**k)
    def extra(h):
        return sum((F(2*a+1,9)*F(3,5)**(a-2) for a in range(2,h+1)),F())
    results = {}
    for h in range(2,21):
        u = extra(h)
        require(u == (20-5*(h+3)*F(3,5)**(h-1))/9, "closed row-tail sum")
        for k in range(1,21):
            sk = series(k)
            bound = 2*sk+(9*sk-4)*u/5
            caps = {(0,b):F(1,3**b) for b in range(k+1)}
            caps.update({(1,b):F(1,3**(b+1)) for b in range(k+1)})
            for a in range(2,h+1):
                caps[(a,0)] = F(1,9)*F(3,5)**(a-2)
                for b in range(1,k+1):
                    caps[(a,b)] = F(1,3)*F(3,5)**(a-1)*F(1,3**b)
            literal = sum((F((2*a+1)*(2*b+1))*caps[(a,b)]
                           for a,b in product(range(h+1),range(k+1))),F())
            require(bound == literal, "all-original-label ordered-pair count")
            strict = h==2 or (h==3 and k<=2) or (h in (4,5) and k==1)
            require((bound < 9) == strict, "finite height-domain controls")
            if (h,k) in ((3,2),(3,3),(4,1),(5,1),(6,1),(4,2)):
                results[f"H{h}K{k}"] = str(bound)
    require(results["H3K2"] == "2024/225" and results["H3K3"] == "2248/225",
            "new target and excluded larger-seven-height certificate")
    return {"checked_height_pairs":380, "bounds":results,
            "H3_all_K_formula":"(96/25)*S_K-184/225", "H3_K_limit":"2408/225",
            "strict_height_domain":"H=2 all K; H=3 K<=2; H=4 or5 K=1 (H>=2,K>=1)",
            "scope":"An exact bound formula; non-strict bounds are not actual minimax obstructions."}


def input_controls(couple):
    caps = {(b,c):F(1,2**b) for b in (1,2) for c in range(3**b)}
    diagonal = [(r,c,r+3*c) for r,c in product(range(3),repeat=2)]
    law,info = couple_depth_two_caps(3,2,3,2,3,2,diagonal,caps,couple)
    require(len(law)==9 and all(w==F(1,9) for w in law.values()), "small diagonal exact uniformity")
    require(max(law.values()) == F(2,3)**2*F(1,4), "iterated mixed leaf cap is attained")
    rejected=[]
    bad_caps=dict(caps)
    bad_caps[(1,0)]=0.5
    for name,source,cc in (("duplicate",diagonal+[diagonal[0]],caps),
                           ("outside carrier",diagonal+[(3,0,0)],caps),
                           ("inexact cap",diagonal,bad_caps),
                           ("failed restricted projection",[(0,0,0)],caps)):
        try:
            couple_depth_two_caps(3,2,3,2,3,2,source,cc,couple)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError(f"failed to reject {name}")
    return {"small_diagonal":info,"uniform_atom":"1/9","rejected_inputs":rejected}


def actual_consumer(source, fixture, couple):
    actual=set(source)
    require(len(actual)==len(source),"distinct reused fixture source")
    fibres=defaultdict(set)
    for x in source:
        x5,y=x%125,x%49
        fibres[x5%5].add(((x5//5)%5,x5//25,y))
    require(len(fibres)==3,"exactly three occupied first-five roots")
    caps={(b,c):F(1,3**b) for b in (1,2) for c in range(7**b)}
    cache,law,records={}, {}, []
    for root,points in sorted(fibres.items()):
        key=tuple(sorted(points))
        if key not in cache:
            cache[key]=couple_depth_two_caps(5,3,5,3,7,2,key,caps,couple)
        conditional,info=cache[key]
        records.append({"first_five_root":root,**info})
        for (a,u,y),mass in conditional.items():
            x=fixture["fine_crt"](root+5*a+25*u,y)
            require(x in actual and x not in law,"one actual CRT lift")
            law[x]=mass/3
    require(sum(law.values(),F())==1,"one supported consumer law")
    boundcaps={}
    for a,b in product(range(4),range(3)):
        if a<=1:
            value=F(1,3**(a+b))
        elif b==0:
            value=F(1,9)*F(3,5)**(a-2)
        else:
            value=F(1,3)*F(3,5)**(a-1)*F(1,3**b)
        boundcaps[5**a*7**b]=value
    labels=tuple(sorted(boundcaps))
    maxima={d:fixture["cylinder_max"](law,d) for d in labels}
    require(all(maxima[d]<=boundcaps[d] for d in labels),"all twelve same-law cylinder maxima")
    bound=sum((boundcaps[lcm(d,e)] for d,e in product(labels,repeat=2)),F())
    actual_upper=sum((maxima[lcm(d,e)] for d,e in product(labels,repeat=2)),F())
    require(actual_upper<=bound==F(2024,225)<9,"all144 independent original-phase pairs")
    return {"source_points":len(actual),"selected_actual_points":len(law),
            "distinct_local_source_constructions":len(cache),"local_couplings":records,
            "original_labels":labels,"ordered_pairs":len(labels)**2,
            "theorem_bound":str(bound),"actual_LCM_upper":str(actual_upper),
            "cylinder_maxima":{str(d):str(maxima[d]) for d in labels},
            "actual_law":[{"residue":x,"mass":str(w)} for x,w in sorted(law.items())],
            "scope":"One exact law on the reused actual source, selected before all original phases; no odd-cover realization claim."}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coupling-script",type=Path,
                        default=Path(__file__).with_name("tree_cap_coupling.py"))
    parser.add_argument("--fixture-script",type=Path,
                        default=Path(__file__).with_name("minimum_source_fibre_lift.py"))
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    ctx=runpy.run_path(str(args.coupling_script))
    fixture=runpy.run_path(str(args.fixture_script))
    couple=ctx["couple_tree_caps"]
    result={"height_bounds":height_controls(),"input_controls":input_controls(couple)}
    obstruction=ctx["simultaneous_selector_obstruction"](args.fixture_script)
    result["actual_450_consumer"]=actual_consumer(obstruction["actual_residues"],fixture,couple)
    old=fixture["empty_good_fibre_countercontrol"]()
    result["actual_540_consumer"]=actual_consumer(old["actual_residues"],fixture,couple)
    result["scope"]="Ordinary general proof and exact rational controls; no Lean certification or unrestricted Erdős7 resolution."
    payload=json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.write_text(payload,encoding="utf-8")
    else:
        print(payload,end="")


if __name__=="__main__":
    main()
