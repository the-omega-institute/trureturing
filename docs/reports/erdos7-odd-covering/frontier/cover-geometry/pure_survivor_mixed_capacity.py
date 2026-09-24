#!/usr/bin/env python3
"""Fixed rational constants for the same-law mixed capacity criterion.
Consumes a pinned existing tail result; performs no original-family scan,
no label-inventory generation, no old producer rerun, and no Lean build.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
import argparse
import hashlib
import json

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--input',type=Path,default=Path(__file__).with_name('phase_resampling_arithmetic.json'))
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=p.parse_args()
raw=a.input.read_bytes()
pin='da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f'
if hashlib.sha256(raw).hexdigest()!=pin: raise ValueError('retained tail pin mismatch')
data=json.loads(raw)
P=(3,5,7,11,13,17,19)
EP=prod(F(q,q-1) for q in P)
Dmax=prod(F(q-1,q-2) for q in P)
A=EP-1
alpha=F(data['alpha']); cap=1/alpha; tail=F(data['tail'])
delta=F(51863873,25500000)
checks={}
def req(k,b):
 checks[k]=bool(b)
 if not b: raise ValueError(k)
req('retained_cutoff',data['cutoff']==10**9)
req('haar_euler_A',A==F(212731,110592))
req('pure_survivor_density_envelope',Dmax==F(4096,935))
req('density_envelope_below_nine_halves',Dmax<F(9,2))
req('nonternary_affine_slope_strict_negative',Dmax*F(3,16)-1==F(-167,935))
req('remaining_ternary_slope_strict_negative',EP/3-1==F(-8453,331776))
# e>8/3 and this rational inequality give log(27/2)<8/3.
req('entropy_log_envelope',F(8,3)**8>F(27,2)**3)
req('same_G_budget_below_thirteen_halves',3*A-2+F(8,3)<F(13,2))
# e<11/4, the following inequality and cap>800 give log(cap)>13/2.
req('cap_above_eight_hundred',cap>800)
req('log_cap_above_thirteen_halves',F(11,4)**13<F(800)**2)
req('new_density_below_original_cap',3*Dmax<cap)
req('all_mixed_query_bound_meets_residual',F(2)<delta)
req('direct_all_query_bound',3*(Dmax-1)==F(9483,935) and F(9483,935)<F(565,51))
req('retained_tail_below_one_over_two_hundred_thousand',tail<F(1,200000))
req('deep_mixed_capacity_below_one_over_ten_thousand',Dmax*tail<F(1,10000))
max_mixed=F(2,3)*F(4,15)
req('single_mixed_capacity_envelope',max_mixed==F(8,45))
three=3*max_mixed+Dmax*tail
req('three_shallow_labels_meet_capacity',three<F(2,3))
req('three_shallow_query_upper',3*max_mixed/(1-three)<F(7,6))
eight_shallow=F(8,45)+F(4,35)+F(20,297)+5*F(8,135)
req('eight_shallow_capacity_classification_sum',eight_shallow==F(2272,3465))
req('eight_shallow_labels_meet_capacity',eight_shallow+Dmax*tail<F(2,3))
result={
 'input_name':a.input.name,'input_sha256':pin,
 'scope':'fixed constants for general same-law mixed capacity theorem; analytic proof handles all families and heights',
 'A':str(A),'Dmax':str(Dmax),'Wmin':str(1/Dmax),
 'nonternary_affine_slope_upper':str(Dmax*F(3,16)-1),
 'last_ternary_slope':str(EP/3-1),
 'mixed_capacity_threshold':'2/3','all_mixed_query_upper':'2',
 'density_upper':str(3*Dmax),'unused_upper':str(3*A-2),
 'entropy_upper':'8/3','entropy_unused_upper':str(3*A-2+F(8,3)),
 'cap_log_lower':'13/2','direct_all_query_upper':str(3*(Dmax-1)),
 'retained_tail':str(tail),'deep_capacity_upper':str(Dmax*tail),
 'three_shallow_capacity_upper':str(three),
 'three_shallow_query_upper':str(3*max_mixed/(1-three)),
 'eight_shallow_capacity_upper':str(eight_shallow),
 'eight_with_deep_capacity_upper':str(eight_shallow+Dmax*tail),
 'checks':checks,'passed_count':len(checks)
}
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed_count':len(checks),'Dmax':str(Dmax),'same_G_budget_upper':result['entropy_unused_upper'],'three_shallow_bound_below':'7/6','result':str(a.output)},indent=2))
