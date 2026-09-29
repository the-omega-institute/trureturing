#!/usr/bin/env python3
"""Fixed actual prefix-rectangle counterexample; no full-period enumeration."""
from fractions import Fraction as F
from pathlib import Path
import json
from itertools import combinations

height5=height7=4
query_depth5=query_depth7=6
checks={}
def check(name,value):
 checks[name]=bool(value)
 if not value: raise ValueError(name)
def compatible(p,a,r,b,s):
 return (r-s)%p**min(a,b)==0

def rectangle_mass(rect):
 a,r,b,s=rect
 return F(1,5**a*7**b)

def intersect_mass(left,right):
 a,r,b,s=left;c,u,d,v=right
 if not compatible(5,a,r,c,u) or not compatible(7,b,s,d,v):return F()
 return F(1,5**max(a,c)*7**max(b,d))

pure5=[(e,k*5**(e-1),0,0) for e in range(1,height5+1) for k in (1,2)]
pure7=[(0,0,e,k*7**(e-1)) for e in range(1,height7+1) for k in (1,2)]
mixed=[(a,3*5**(a-1),b,k*7**(b-1)) for a in range(1,height5+1) for b in range(1,height7+1) for k in (3,4)]
queries=[(a,4 if a else 0,b,5 if b else 0) for a in range(query_depth5+1) for b in range(query_depth7+1) if a or b]
check('pure5_pairwise_disjoint',all(not intersect_mass(a,b) for a,b in combinations(pure5,2)))
check('pure7_pairwise_disjoint',all(not intersect_mass(a,b) for a,b in combinations(pure7,2)))
check('mixed_pairwise_disjoint',all(not intersect_mass(a,b) for a,b in combinations(mixed,2)))
check('all_mixed_rectangles_in_complete_pure_survivor',all(not intersect_mass(m,p) for m in mixed for p in pure5+pure7))
check('all_positive_query_cylinders_disjoint_from_mixed_union',all(not intersect_mass(m,q) for m in mixed for q in queries))
check('pure5_query_cylinders_avoid_pure5',all(not intersect_mass((a,4,0,0),p) for a in range(1,query_depth5+1) for p in pure5))
check('pure7_query_cylinders_avoid_pure7',all(not intersect_mass((0,0,b,5),p) for b in range(1,query_depth7+1) for p in pure7))
label_counts={}
for a,r,b,s in pure5+pure7+mixed:
 d=5**a*7**b
 label_counts[d]=label_counts.get(d,0)+1
check('exactly_two_classes_per_numerical_original_label',all(v==2 for v in label_counts.values()))
check('two_pure25_in_root0',all(r%5==0 for a,r,b,s in pure5 if a==2))
check('two_pure125_in_live_cell0mod25',all(r%25==0 for a,r,b,s in pure5 if a==3))
check('roots3and4_have_no_pure5_deletion',all(r%5 not in (3,4) for a,r,b,s in pure5))
w5=1-sum(map(rectangle_mass,pure5),F())
w7=1-sum(map(rectangle_mass,pure7),F())
u=sum(map(rectangle_mass,mixed),F())
check('raw_packing_closed_formula',u==F(1,12)*(1-F(1,5**height5))*(1-F(1,7**height7)))
source_mass=w5*w7
survivor_mass=source_mass-u
check('survivor_mass_positive',survivor_mass>0)

# Exact coordinate law of the finite nested positive query count, including
# the unit label, under each raw pure-survivor Haar restriction.
def count_law(p,w,depth):
 law={1:w-F(1,p)}
 law.update({n:F(p-1,p**n) for n in range(2,depth+1)})
 law[depth+1]=F(1,p**depth)
 check('count_law_mass_p'+str(p),sum(law.values(),F())==w)
 return law
l5=count_law(5,w5,query_depth5)
l7=count_law(7,w7,query_depth7)
load={}
for n,x in l5.items():
 for m,y in l7.items():load[n*m]=load.get(n*m,F())+x*y
# Every removed mixed point is in load atom1, by the preceding exact tests.
actual=load.copy();actual[1]-=u
check('enough_mass_in_load1_to_pay_all_mixed_deletion',actual[1]>=0)
check('actual_pushforward_mass',sum(actual.values(),F())==survivor_mass)
hinges={}
for t in (1,2,3,4,6):
 before=sum((max(v-t,0)*mass for v,mass in load.items()),F())
 after=sum((max(v-t,0)*mass for v,mass in actual.items()),F())
 check('zero_anchor_hinge_saving_t'+str(t),before==after)
 hinges[t]={'pure_source_hinge':str(before),'actual_survivor_hinge':str(after),'saving':'0'}
all_query_numerator=w7/F(4)+w5/F(6)+F(1,24)
all_query_value=all_query_numerator/survivor_mass
source_query_value=all_query_numerator/source_mass
check('normalization_strictly_increases_anchor_query_norm',all_query_value>source_query_value)
check('limiting_anchor_query_norm',F(7,24)/F(1,4)==F(7,6))
result={
 'scope':'new transposed two-copy prefix packing, fixed exact prefix checks; not a full-period or old-grid computation',
 'heights':[height5,height7],'query_depths':[query_depth5,query_depth7],
 'pure5_classes':pure5,'pure7_classes':pure7,'mixed_rectangles':mixed,
 'label_count':len(label_counts),'original_class_count':len(pure5+pure7+mixed),
 'mixed_pair_checks':len(mixed)*(len(mixed)-1)//2,
 'mixed_pure_checks':len(mixed)*(len(pure5)+len(pure7)),
 'mixed_query_checks':len(mixed)*len(queries),
 'pure5_mass':str(w5),'pure7_mass':str(w7),'mixed_union_mass':str(u),
 'source_mass':str(source_mass),'actual_survivor_mass':str(survivor_mass),
 'finite_query_hinges':hinges,
 'complete_anchor_query_numerator':str(all_query_numerator),
 'complete_anchor_query_norm':str(all_query_value),
 'pure_source_query_norm':str(source_query_value),
 'limiting_complete_anchor_query_norm':'7/6',
 'checks':checks,'passed_count':len(checks)
}
out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed_count':len(checks),'original_class_count':result['original_class_count'],'mixed_union_mass':str(u),'actual_survivor_mass':str(survivor_mass),'all_query_norm':str(all_query_value),'mixed_query_intersections_checked':result['mixed_query_checks'],'result':str(out)},indent=2))
