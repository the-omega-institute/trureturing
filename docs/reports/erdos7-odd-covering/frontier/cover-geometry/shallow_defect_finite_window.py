#!/usr/bin/env python3
"""Exact numeric reduction for a general shallow-defect continuation bound."""
from fractions import Fraction as F
from pathlib import Path
from math import prod
from argparse import ArgumentParser
import hashlib,heapq,json

parser=ArgumentParser(description=__doc__)
parser.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
SOURCE=args.source_dir/'normalized_joint_hinge_transfer.json'
data=json.loads(SOURCE.read_text())
def frac(x):
    return F(*x) if isinstance(x,list) else F(x)
B,K2,K3,G,delta,alpha=[frac(data[k]) for k in
    ('B','K2','K3','G','source_only_gate','raw_Q_mass_lower')]
Q=(5,7,11,13,17,19)
D=200000000

def smooth_recursive(bound):
    out=[]
    def visit(i,n):
        if i==len(Q):out.append(n);return
        while n<=bound:
            visit(i+1,n)
            n*=Q[i]
    visit(0,1)
    return sorted(out)

def smooth_heap(bound):
    todo=[1];seen={1};out=[]
    while todo:
        n=heapq.heappop(todo);out.append(n)
        for p in Q:
            m=n*p
            if m<=bound and m not in seen:
                seen.add(m);heapq.heappush(todo,m)
    return out

values=smooth_recursive(D)
total=prod(F(p,p-1) for p in Q)
tail=total-sum((F(1,d) for d in values),F(0))
rho_crit=27*delta/G
epsilon_crit=rho_crit/2
tail_crit=alpha*rho_crit/72
rho=72*tail/alpha
gate=delta-G*rho/27
haar=49*alpha*gate/11088
single_e3_reciprocal_crit=alpha*epsilon_crit/9

# Exact local weights 12 u_A(cylinder)+18 u_B(cylinder).
def ternary_weight(e,t):
    if e==0:return F(30)
    if e==1:return (F(12),F(0),F(18))[t%3]
    if t%3==1 or t%9==3:return F(0)
    return F(54,3**e)

checks={
 'source_pin':hashlib.sha256(SOURCE.read_bytes()).hexdigest()=='4b99d5aa933ef0722ce2b4bf2efca94055ef9310753e0eba9b8b79ad9efd796d',
 'source_margin_identity':delta==G-1-2*B-(3*K2-3+(G-3)*K3)/27,
 'positive_hinge_and_mass_contracts':0<alpha<1 and 0<K3<K2<B and G>3,
 'original_gate_positive':delta>0,
 'smooth_inventory_independent_agreement':values==smooth_heap(D),
 'inventory_unique_complete_recursion':len(values)==len(set(values)) and values[0]==1 and max(values)<=D,
 'nonunit_inventory_count':len(values)-1==2654,
 'full_euler_mass':total==F(323323,165888),
 'positive_complete_tail':tail>0,
 'max_e2_weight_six':max(ternary_weight(2,t) for t in range(9))==6,
 'max_e3_weight_two':max(ternary_weight(3,t) for t in range(27))==2,
 'unselected_e2_e3_budget_eight':max(ternary_weight(2,t) for t in range(9))+max(ternary_weight(3,t) for t in range(27))==8,
 'tail_below_uniform_gate':tail<tail_crit,
 'rho_below_uniform_gate':0<rho<rho_crit,
 'window_gate_positive':gate>0,
 'haar_lower_above_one_in_three_million':haar>F(1,3000000),
 'single_e3_5pow7_qualifies':F(1,5**7)<single_e3_reciprocal_crit,
 'defect_coefficient_identity':F(3,27)+F(1,27)*(G-3)==G/27,
}
if not all(checks.values()):raise RuntimeError(checks)
def ex(v):return {'exact':str(v),'decimal':float(v)}
result={
 'scope':'General same-law shallow-defect theorem; finite cofactor window with fixed pure3 originals and nine-prime support. Ordinary proof, no new Lean.',
 'source':SOURCE.name,'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
 'D':D,'nonunit_cofactor_count':len(values)-1,
 'checks':checks,'check_count':len(checks),
 'rho_critical':ex(rho_crit),'e3_incidence_critical':ex(epsilon_crit),
 'full_reciprocal_tail':ex(tail),'tail_critical':ex(tail_crit),
 'shallow_defect_upper':ex(rho),'continuation_gate_lower':ex(gate),
 'haar_survivor_lower':ex(haar),
 'exceptional_e3_reciprocal_sum_critical':ex(single_e3_reciprocal_crit)}
# Additional pure classes are charged by their actual ternary union.
# For c in [0,1], integer-valued query loads give an exact interpolation
# of the two hinge FUNCTIONS, hence an upper envelope from K2 and K3.
pure_slope=(3+(G-3)*(K2-K3))/27
pure_start=9
pure_budget=F(3)**(4-pure_start)
checks['pure_geometric_tail']=pure_budget==F(1,243)
checks['positive_pure_slope']=pure_slope>0
checks['pure_tail_alone_positive']=delta-pure_slope*pure_budget>0
checks['shallower_uniform_pure_budget_fails_this_bound']=delta-pure_slope*(3*pure_budget)<0
extended_D=1000000000
extended_values=smooth_recursive(extended_D)
checks['extended_inventory_independent_agreement']=extended_values==smooth_heap(extended_D)
checks['extended_nonunit_inventory_count']=len(extended_values)-1==3821
extended_tail=total-sum((F(1,d) for d in extended_values),F())
extended_rho=72*extended_tail/alpha
extended_gate=delta-pure_slope*pure_budget-G*extended_rho/27
extended_haar=49*alpha*extended_gate/11088
checks['extended_tail_positive']=extended_tail>0
checks['joint_pure_and_shallow_margin_positive']=extended_gate>0
checks['joint_haar_above_one_in_23_million']=extended_haar>F(1,23000000)
checks['original_zero_defect_margin_recovered']=delta-pure_slope*0-G*0/27==delta
if not all(checks.values()):raise RuntimeError(checks)
result['scope']='Same-law shallow-defect and pure-union sensitivity, finite cofactor windows, and arbitrary pure tails from exponent9, within the stated nine-prime support. Ordinary mathematics; no Lean claim.'
result['pure_damage_slope']=ex(pure_slope)
result['pure_damage_critical_without_shallow_defect']=ex(delta/pure_slope)
result['pure_tail_alone_margin']=ex(delta-pure_slope*pure_budget)
result['pure_tail_window']={
 'pure_tail_start':pure_start,'pure_union_weight_upper':ex(pure_budget),
 'D':extended_D,'nonunit_cofactor_count':len(extended_values)-1,
 'full_reciprocal_tail':ex(extended_tail),
 'shallow_defect_upper':ex(extended_rho),
 'continuation_gate_lower':ex(extended_gate),
 'haar_survivor_lower':ex(extended_haar)}
# Report578's existing scalar clip also consumes the new source contract.
# If 3 is absent, or 9 is absent/redundant under 3, all higher pure
# originals are included in the actual pure survivor before clipping.
pure_mass=F(11,18)
pure_density=1/pure_mass
pure_query=F(1,2)/pure_mass
deep_weight=F(1,54)/pure_mass
clip=1-3*deep_weight
raw_mass=1-deep_weight*K3/clip
raw_query=B+pure_query*(1+B)/clip
raw_density=9*pure_density/(alpha*clip)
pure_gate=G*raw_mass-raw_query
pure_mass_critical=(3+(G*K3+27*(1+B))/(G-B))/54
simple_D=100000
simple_values=smooth_recursive(simple_D)
simple_tail=total-sum((F(1,d) for d in simple_values),F())
simple_defect=pure_density*(F(1,9)+F(1,27))*9*simple_tail/alpha
simple_mass=raw_mass-simple_defect/clip
simple_gate=G*simple_mass-raw_query
simple_haar=49*simple_gate/(616*raw_density)
old_B=F(432040125182653876501,86355045355449035400)
old_K3=F(12019840537595758779003,5715264751774801992890)
old_pure_gate=G*(1-old_K3/30)-(F(19,10)*old_B+F(9,10))
checks.update({
 'no_effective9_complete_pure_tail':pure_mass==1-F(1,3)-F(1,18),
 'no_mod3_included':1-F(1,6)>=pure_mass,
 'pure_mass_gate_denominator':G>B and F(1,2)<pure_mass_critical<pure_mass,
 'no_effective9_clip':clip==F(10,11) and 0<clip<1,
 'no_effective9_complete_deep_weight':deep_weight==F(1,33),
 'no_effective9_raw_mass':raw_mass==1-K3/30 and raw_mass>0,
 'no_effective9_raw_query':raw_query==F(19,10)*B+F(9,10),
 'no_effective9_raw_density':raw_density==F(81,5)/alpha,
 'no_effective9_global_gate':pure_gate>0,
 'no_effective9_old_supplier_already_passes':old_pure_gate>0,
 'no_effective9_inventory_independent_agreement':simple_values==smooth_heap(simple_D),
 'no_effective9_inventory_count':len(simple_values)-1==317,
 'no_effective9_complete_tail_positive':simple_tail>0,
 'no_effective9_defect_weight':pure_density*(F(1,9)+F(1,27))==F(8,33),
 'no_effective9_combined_gate_identity':simple_gate==pure_gate-F(12,5)*G*simple_tail/alpha,
 'no_effective9_window_mass_positive':simple_mass>0,
 'no_effective9_window_gate_positive':simple_gate>0,
 'no_effective9_density_conversion':simple_haar==245*alpha*simple_gate/49896,
 'no_effective9_haar_above_one_in_7500':simple_haar>F(1,7500),
})
if not all(checks.values()):raise RuntimeError(checks)
result['scope']='Same-law shallow-defect bounds and finite cofactor windows: fixed pure3 with deep pure tails, and the no-effective9 class with arbitrary higher pure originals. Ordinary mathematics; no Lean claim.'
result['no_effective9_window']={
 'pure_survivor_mass_lower':ex(pure_mass),
 'pure_mass_critical_for_global_scalar_clip':ex(pure_mass_critical),
 'clip_threshold':ex(clip),'complete_deep_weight':ex(deep_weight),
 'global_raw_mass_lower':ex(raw_mass),'raw_query_upper':ex(raw_query),
 'raw_density_upper':ex(raw_density),'global_gate':ex(pure_gate),
 'old_supplier_global_gate':ex(old_pure_gate),
 'D':simple_D,'nonunit_cofactor_count':len(simple_values)-1,
 'full_reciprocal_tail':ex(simple_tail),
 'actual_shallow_defect_upper':ex(simple_defect),
 'window_raw_mass_lower':ex(simple_mass),
 'continuation_gate_lower':ex(simple_gate),
 'haar_survivor_lower':ex(simple_haar)}
result['check_count']=len(checks)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'window_gate':float(gate),
                 'pure_tail_window_gate':float(extended_gate),
                 'pure_tail_window_haar_lower':float(extended_haar),
                 'no_effective9_window_gate':float(simple_gate),
                 'no_effective9_window_haar_lower':float(simple_haar)},indent=2))
