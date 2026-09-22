#!/usr/bin/env python3
"""Exact controls of report447's strict cut surplus; ordinary, not Lean.

The same actual source can support both a law saturating the old bound nine
and a new law satisfying all the scaled caps. The experiment keeps the law
fixed before every independently phased original-label test.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import argparse
import json
import runpy


def require(condition, message):
    if not condition:
        raise ValueError(message)


def profile_controls():
    """Check the numerical cut profiles, not all cuts of a source network."""
    occupancies=(4,5,5,5)
    selections=(2,3,3,3)
    minima={}
    equalities={}
    full=[]
    checks=0
    for active in product(*(range(n+1) for n in occupancies)):
        top=sum((min(F(1,3),F(n-a,9)) for n,a in zip(occupancies,active)),F())
        weights=[F(2*a,7*q) for a,q in zip(active,selections) if a>=q]
        size=len(weights)
        cost=top
        if size>=2:
            total=sum(weights,F())
            cost+=min(F(1),total/2,total-max(weights))
        require(cost>=1,"unscaled numerical cut lower bound")
        minima[size]=min(minima.get(size,cost),cost)
        if cost==1:
            equalities[size]=equalities.get(size,0)+1
            if size==4:
                full.append(active)
        checks+=1
    require(minima=={0:F(4,3),1:F(1),2:F(8,7),3:F(22,21),4:F(1)},
            "eligible-root-count minima")
    require(checks==1080 and equalities=={1:81,4:1} and full==[occupancies],
            "only the two analytically excluded equality classes remain")
    return {"profiles":checks,"minima_by_eligible_count":{str(k):str(v) for k,v in sorted(minima.items())},
            "equality_counts":{str(k):v for k,v in sorted(equalities.items())},
            "fully_active_equality_profile":list(occupancies)}


def integer_cut_controls():
    """Exact integer minima in the all-active cut reduction of report447."""
    def f2(p):
        return p+2*((p+1)//2)

    def f3(p):
        return p+2*((p+2)//3)

    rows=[]
    checked=0
    expected=[70,71,72,65,66,67,72,73,74]
    for k in range(9):
        u=9-k
        one_dimensional=min(min(f2(p)+3*f3(max(p,u-p)),
                                f3(p)+f2(max(p,u-p))+2*f3(max(p,u-p)))
                            for p in range((u+1)//2+1))
        exact=None
        # Clipping any p_r>u down to u preserves every pair constraint.
        for values in product(range(u+1),repeat=4):
            checked+=1
            if any(values[i]+values[j]<u for i,j in combinations(range(4),2)):
                continue
            total=f2(values[0])+sum(f3(p) for p in values[1:])
            exact=total if exact is None else min(exact,total)
        require(exact==one_dimensional,"sorting/minimum-coordinate formula")
        numerator=7*k+2*exact
        require(numerator==expected[k],"all-active integer cut table")
        rows.append({"public_numerator_over_nine":k,"remaining_numerator":u,
                     "minimum_private_integer_sum":exact,
                     "cut_numerator_over_63":numerator})
    require(min(expected)==65,"quantitative integer margin")
    return {"four_coordinate_candidates":checked,"all_active_table":rows,
            "minimum_cut_lower":"65/63"}


def rejection_controls(direct, coupling, source):
    caps={(b,v):F(1,3**b) for b in (1,2) for v in range(7**b)}
    gamma=[F(2,7)]*4
    core=direct['couple_direct_child_caps']
    carrier=[(r,c) for r in range(1,5) for c in range(4 if r==1 else 5)]
    ternary=[(r,c,g+7*h) for r,c in carrier for g,h in product(range(3),repeat=2)]
    failed_pairs=sorted({(r,c,0) for r,c in carrier}
                        |{(1,0,g+7*h) for g,h in product(range(5),repeat=2)})
    bad_caps=dict(caps)
    bad_caps[(1,0)]=F(1,2)
    cases=[
        ("requires_actual_occupancy",lambda: core(source,2,caps,gamma,coupling,strict_one_gap=True),
         "strict one-gap mode requires actual occupancy"),
        ("height",lambda: core(direct['occupancy_branch_sources'](3)[0],3,
             {(b,v):F(1,3**b) for b in (1,2,3) for v in range(7**b)},gamma,coupling,
             actual_occupancy=True,strict_one_gap=True),
         "strict one-gap mode requires height two and occupancy 4555"),
        ("occupancy",lambda: core(direct['actual_occupancy_source'](),2,caps,gamma,coupling,
             actual_occupancy=True,strict_one_gap=True),
         "strict one-gap mode requires height two and occupancy 4555"),
        ("coefficient",lambda: core(source,2,caps,[F(1,3)]*4,coupling,
             actual_occupancy=True,strict_one_gap=True),
         "strict one-gap mode requires gamma 2/7 and ternary prefix caps"),
        ("prefix_caps",lambda: core(source,2,bad_caps,gamma,coupling,
             actual_occupancy=True,strict_one_gap=True),
         "strict one-gap mode requires gamma 2/7 and ternary prefix caps"),
        ("standalone_tree",lambda: core(ternary,2,caps,gamma,coupling,
             actual_occupancy=True,strict_one_gap=True),
         "strict one-gap mode requires a literal standalone five-ary projection"),
        ("pair_projection",lambda: core(failed_pairs,2,caps,gamma,coupling,
             actual_occupancy=True,strict_one_gap=True),"restricted pair projection fails:"),
        ("incidence",lambda: direct['couple_incidence_caps'](ternary,2,coupling,
             actual_occupancy=True,strict_one_gap=True),
         "actual-occupancy consumer permits at most two children per root/seven-root pair"),
    ]
    rejected=[]
    for name,call,expected in cases:
        try:
            call()
        except ValueError as error:
            require(str(error).startswith(expected),f"wrong rejection for {name}: {error}")
            rejected.append({"premise":name,"reason":str(error)})
        else:
            raise ValueError(f"unsupported strict premise accepted: {name}")
    return rejected


def translated_source(source):
    """One common CRT translation; no cross-prime-dependent relabelling."""
    points=[]
    for r,c,y in source:
        x5=(r+5*c+3)%25
        points.append((x5%5,x5//5,(y+8)%49))
    return sorted(points)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    directory=Path(__file__).parent
    direct=runpy.run_path(str(directory/'direct_child_tree_caps.py'))
    coupling=runpy.run_path(str(directory/'tree_cap_coupling.py'))
    saturation=runpy.run_path(str(directory/'child_cut_saturation.py'))
    sources={"one_gap":direct['occupancy_branch_sources'](2)[0],
             "old_cap_saturation":saturation['saturation_source']()}
    sources['translated_saturation']=translated_source(sources['old_cap_saturation'])
    controls={}
    for name,source in sources.items():
        law,info=direct['couple_incidence_caps'](source,2,coupling,
                         actual_occupancy=True,strict_one_gap=True)
        require(F(info['theorem_LCM_upper'])==F(569,65) and F(info['actual_LCM_upper'])<9,
                "strict common-law original-label bound")
        require(info['flow_denominator']==65 and info['restricted_pair_checks']==480,
                "exact scaled flow and actual-subset carriers")
        require(info['cylinder_caps']['1']=='1' and info['ordered_pairs']==81,
                "unit cylinder and all original-label pairs retained")
        require(sum(law.values(),F())==1,"normalization after strict flow")
        info['actual_source']=source
        # Check literal product blocking separately from fractional feasibility.
        choices=list(combinations(range(5),3))
        roots=sorted({r for r,c,y in source})
        checks=0
        for i,r in enumerate(roots):
            for s in roots[i+1:]:
                for left,right in product(choices,repeat=2):
                    leaves={y for rr,c,y in source if (rr==r and c in left) or (rr==s and c in right)}
                    require(direct['contains_complete_seven_tree'](leaves,2,3),
                            "literal pair/triple product-blocking premise")
                    checks+=1
        info['original_pair_triple_tree_checks']=checks
        controls[name]=info
    result={"profile_controls":profile_controls(),"integer_cut_controls":integer_cut_controls(),
            "laws":controls,
            "rejection_controls":rejection_controls(direct,coupling,sources['one_gap']),
            "scope":"One better actual law for height two and occupancy 4555, not every old-cap law, a minimax computation, Lean certification, or a covering-system realization."}
    payload=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload,end='')


if __name__=='__main__':
    main()
