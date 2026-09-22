#!/usr/bin/env python3
"""Exact controls for literal projected trees excluding the 65/63 equality.

These are finite construction and premise controls, not Lean certification,
an optimized layout game, or a covering-system realization.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from pathlib import Path
import argparse
import json
import runpy


def require(condition, message):
    if not condition:
        raise ValueError(message)


def equality_classification():
    """Check the unique integer shape left at the generic 65/63 boundary."""
    minimizers=[]
    for p in product(range(7),repeat=4):
        if any(p[i]+p[j]<6 for i in range(4) for j in range(i)):
            continue
        total=p[0]+2*((p[0]+1)//2)+sum(v+2*((v+2)//3) for v in p[1:])
        require(total>=22,"u=6 integer minimum")
        if total==22:
            minimizers.append(p)
    require(minimizers==[(3,3,3,3)],"unique root-subset cost profile")
    full=[v for v in combinations_with_replacement(range(6),5)
          if sum(v)==5 and sum(v[:3])==3]
    sparse=[v for v in combinations_with_replacement(range(8),4)
            if sum(v)==7 and sum(v[:2])==3]
    require(full==[(1,1,1,1,1)] and sparse==[(1,2,2,2)],
            "unique individual child-cost profiles")
    require(F(3,5)+F(1,25)==F(16,25)<1,
            "R=1 and one private leaf cannot cover the standalone five-ary tree")
    return {"u6_candidates":7**4,"root_subset_minimizer":list(minimizers[0]),
            "full_root_child_costs":list(full[0]),"sparse_root_child_costs":list(sparse[0]),
            "public_cost_one_projection_mass_upper":"16/25"}


def fractional_nonliteral_source(saturation):
    """118 actual points: all fractional premises hold, literal blocking fails."""
    removed={(4,4,y) for y in (5,19,26)}
    return sorted(set(saturation['saturation_source']())-removed)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    directory=Path(__file__).parent
    direct=runpy.run_path(str(directory/'direct_child_tree_caps.py'))
    coupling=runpy.run_path(str(directory/'tree_cap_coupling.py'))
    saturation=runpy.run_path(str(directory/'child_cut_saturation.py'))
    strict=runpy.run_path(str(directory/'strict_child_cut_surplus.py'))
    boundary=runpy.run_path(str(directory/'literal_child_cut_boundary.py'))
    sources={"one_gap":direct['occupancy_branch_sources']()[0],
             "old_cap_saturation":saturation['saturation_source']()}
    sources['translated_saturation']=strict['translated_source'](sources['old_cap_saturation'])
    laws={}
    for name,source in sources.items():
        law,info=direct['couple_incidence_caps'](source,2,coupling,
                          actual_occupancy=True,literal_one_gap=True)
        require(F(info['theorem_LCM_upper'])==F(95,11)
                and F(info['actual_LCM_upper'])<=F(95,11)<9,
                "one law for the complete original-label inventory")
        require(info['flow_denominator']==66 and info['literal_pair_subset_checks']==480,
                "scaled network and literal actual-subset checks")
        require(F(info['unscaled_mincut_lower'])==F(66,63)
                and info['capacity_scale']=='21/22' and info['cylinder_caps']['1']=='1',
                "quantitative cut surplus leaves unit mass unscaled")
        require(sum(law.values(),F())==1 and info['ordered_pairs']==81,
                "normalization and all original pairs")
        info['actual_source']=source
        laws[name]=info

    # A genuinely fractional-only source must still use the older theorem.
    fractional=fractional_nonliteral_source(saturation)
    _,old=direct['couple_incidence_caps'](fractional,2,coupling,
                              actual_occupancy=True,strict_one_gap=True)
    require(old['restricted_pair_checks']==480 and len(fractional)==118,
            "all actual-subset fractional projection premises remain valid")
    leaves={y for r,c,y in fractional if (r==2 and c in (0,1,2))
                                       or (r==4 and c in (1,2,4))}
    counts=[sum(y%7==g for y in leaves) for g in range(7)]
    require(counts==[0,2,5,5,0,2,0] and sum(min(3,n) for n in counts)>=9
            and not direct['contains_complete_seven_tree'](leaves,2,3),
            "explicit fractional-feasible, literal-infeasible pair")
    rejections=[]
    try:
        direct['couple_incidence_caps'](fractional,2,coupling,
                           actual_occupancy=True,literal_one_gap=True)
    except ValueError as error:
        require(str(error).startswith('literal pair projection fails:'),
                "the missing literal premise is rejected")
        rejections.append({"premise":"literal tree","reason":str(error)})
    else:
        raise ValueError("fractional-only source accepted under the literal theorem")

    caps={(b,v):F(1,3**b) for b in (1,2) for v in range(7**b)}
    sharp=boundary['boundary_source']()
    _,sharp_old=direct['couple_direct_child_caps'](sharp,2,caps,[F(2,7)]*4,coupling,
                             actual_occupancy=True,strict_one_gap=True)
    require(sharp_old['root_seven_child_multiplicities']==[4,5,5,5],
            "sharp old-network example exceeds the new incidence premise")
    try:
        direct['couple_direct_child_caps'](sharp,2,caps,[F(2,7)]*4,coupling,
                             actual_occupancy=True,literal_one_gap=True)
    except ValueError as error:
        require(str(error)=='literal one-gap mode requires a five-child root with incidence below five',
                "the missing incidence premise is rejected")
        rejections.append({"premise":"incidence","reason":str(error)})
    else:
        raise ValueError("sharp 65/63 network accepted under the 66/63 theorem")
    # The core cut theorem has a weaker incidence premise than its moment
    # consumer. Preserve that distinction on one common actual source.
    weak_source=sorted(set(sources['one_gap'])|{(2,2,2)})
    weak_law,weak_info=direct['couple_direct_child_caps'](
        weak_source,2,caps,[F(2,7)]*4,coupling,
        actual_occupancy=True,literal_one_gap=True)
    require(weak_info['root_seven_child_multiplicities']==[2,3,2,2]
            and sum(weak_law.values(),F())==1,"weaker core incidence contract")
    try:
        direct['couple_incidence_caps'](weak_source,2,coupling,
                           actual_occupancy=True,literal_one_gap=True)
    except ValueError as error:
        require(str(error)=='actual-occupancy consumer permits at most two children per root/seven-root pair',
                "the moment consumer keeps its stronger incidence premise")
        rejections.append({"premise":"moment consumer incidence","reason":str(error)})
    else:
        raise ValueError("weaker core premise incorrectly accepted by the moment consumer")
    for actual,old_flag in ((False,False),(True,True)):
        try:
            direct['couple_incidence_caps'](sources['one_gap'],2,coupling,
                        actual_occupancy=actual,strict_one_gap=old_flag,literal_one_gap=True)
        except ValueError as error:
            require(str(error)=='literal one-gap mode requires actual occupancy and excludes strict mode',
                    "explicit mode selection")
            rejections.append({"premise":"mode","reason":str(error)})
        else:
            raise ValueError("invalid literal mode combination accepted")
    result={"equality_classification":equality_classification(),"laws":laws,
            "fractional_nonliteral_boundary":{"source_points":len(fractional),
              "removed_from_saturation":[[4,4,y] for y in (5,19,26)],
              "fractional_subset_checks":old['restricted_pair_checks'],
              "failed_pair_leaf_counts":counts,"old_theorem_upper":old['theorem_LCM_upper']},
            "weak_core_boundary":{**weak_info,"added_to_one_gap":[2,2,2],
              "actual_law":[{"point":list(p),"mass":str(w)} for p,w in sorted(weak_law.items())]},
            "rejection_controls":rejections,
            "scope":"Extra literal and incidence premises exclude equality; one law precedes all phases. No claim of arithmetic residual realization or unrestricted noncoverage."}
    payload=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload,end='')


if __name__=='__main__':
    main()
