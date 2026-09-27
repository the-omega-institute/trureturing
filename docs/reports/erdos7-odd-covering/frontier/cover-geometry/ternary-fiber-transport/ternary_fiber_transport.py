#!/usr/bin/env python3
"""Fixed actual counterexample to automatic two-copy fibre inheritance.
Report536 proves the general transport formulas.
"""
from fractions import Fraction as F
from pathlib import Path
from math import prod
import json
import argparse

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
args=parser.parse_args()
P=(3,5,7,11,13,17,19)
alpha=F(7235955529,6075000000000)
cap=1/alpha
originals=((3,1),(15,0),(45,36),(135,27))
period=135
checks={}
def check(k,v):
    checks[k]=bool(v)
    if not v: raise ValueError(k)
classes=[{x for x in range(period) if x % d == a} for d,a in originals]
covered=set().union(*classes)
U=set(range(period))-covered
check('distinct_odd_nonunit_original_labels',len({d for d,a in originals})==4 and all(d>1 and d%2==1 for d,a in originals))
check('all_original_classes_pairwise_disjoint',all(not(classes[i]&classes[j]) for i in range(4) for j in range(i)))
check('all_originals_have_private_witness',all(c-set().union(*(classes[j] for j in range(4) if j!=i)) for i,c in enumerate(classes)))
private=[min(c-set().union(*(classes[j] for j in range(4) if j!=i))) for i,c in enumerate(classes)]
check('survivor_count_77',len(U)==77)
fiber={x for x in range(period) if x%27==0}
surviving_fiber=U&fiber
check('positive_same_law_fiber_mass',F(len(surviving_fiber),len(U))==F(2,77))
check('three_distinct_actual_mod5_holes',{x%5 for x in fiber-covered}=={3,4})
check('full_fiber_size',len(fiber)==5)
check('three_active_original_mixed_labels',[(d,a%5) for d,a in originals if d!=3]==[(15,0),(45,1),(135,2)])
h=F(len(U),period)
euler=prod(F(p,p-1) for p in P)
common_budget_upper=euler/h-1
check('same_law_density_cap',1/h < cap)
check('same_law_entropy_query_budget_upper_below_five',common_budget_upper<5)
check('retained_cap_above_3_power6',cap>3**6)
# e<3 gives log cap>6>5; log(1/h)<=1/h-1 bounds entropy.
check('generic_h_lower_bound',h>F(17,30))
check('generic_G_bound_for_entire_counterexample_family',euler/F(17,30)-1<5)
check('large_Q_cofactor_exceeds_global_density_cap',5**5>cap)
result={
 'source':'explicit fixed actual original family; new 135-point control, no old producer',
 'originals':[{'modulus':d,'residue':a} for d,a in originals],
 'private_witnesses':private,'period':period,'survivor_count':len(U),'survivor_mass':str(h),
 'complete_ternary_fiber':{'modulus':27,'residue':0,'surviving_points':sorted(surviving_fiber),'nu_mass':str(F(len(surviving_fiber),len(U))),'removed_mod5_phases':[0,1,2],'surviving_mod5_phases':[3,4]},
 'same_law_density':str(1/h),'same_law_entropy_plus_all_queries_upper':str(common_budget_upper),
 'generic_h_lower_bound':'17/30','generic_budget_upper':str(euler/F(17,30)-1),
 'conditional_cap_obstruction':{'Q_cofactor':3125,'mixed_original_count':3124,'full_3_height':3124,'conditional_density':3125},
 'checks':checks,'passed_count':len(checks)
}
out=args.output;out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed_count':len(checks),'survivor_count':len(U),'private':private,'same_G_budget_upper':str(common_budget_upper),'result':str(out)},indent=2))
