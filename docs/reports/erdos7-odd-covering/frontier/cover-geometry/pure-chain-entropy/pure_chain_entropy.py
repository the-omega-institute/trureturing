#!/usr/bin/env python3
"""Independent rational consumer of the retained reciprocal-tail data.
No producer, label scan, LP, full-period enumeration, or Lean invocation.
Report534 gives the positivity and exponential remainder formulas.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import math

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input', type=Path, default=Path(__file__).with_name('phase_resampling_arithmetic.json'))
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
SOURCE = args.input
PIN = 'da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f'
raw = SOURCE.read_bytes()
if hashlib.sha256(raw).hexdigest() != PIN:
    raise ValueError('retained input pin mismatch')
data = json.loads(raw)
P = (3, 5, 7, 11, 13, 17, 19)
N = (18, 12, 10, 8, 8, 7, 7)
n = (8, 7, 7, 7, 7, 7, 7)
B = 10**9
alpha = F(data['alpha'])
cap = 1 / alpha
tail = F(data['tail'])
checks = {}
def check(name, value):
    checks[name] = bool(value)
    if not value:
        raise ValueError(name)

def exp_lower(x, degree):
    if not (x > 0 and degree >= 0):
        raise ValueError("invalid positive Taylor input")
    return sum((x**k / math.factorial(k) for k in range(degree + 1)), F())

def exp_upper(x, degree):
    if not (0 < x < degree + 2):
        raise ValueError("invalid exponential tail ratio")
    return exp_lower(x, degree) + (x**(degree+1) / math.factorial(degree+1)) / (1-x/F(degree+2))

def moment(p, depth, e_bound):
    return sum((F(p-1,p**(k+1))*e_bound**k for k in range(depth)), F()) + e_bound**depth/F(p**depth) - sum((F(1,p**j) for j in range(1,depth+1)), F())

check('cutoff_matches', data['cutoff'] == B)
check('alpha_matches', alpha == F(7235955529,6075000000000))
for p, height, head in zip(P,N,n):
    check('max_shallow_height_p'+str(p), p**height <= B < p**(height+1))
    check('chosen_head_is_shallow_p'+str(p), 1 <= head <= height)
e_upper = F(2718281828459045236,10**18)
check('exp_one_upper_via_positive_tail', exp_upper(F(1),36) < e_upper)
check('exp_one_exceeds_two', exp_lower(F(1),2) > 2)
m_upper = [moment(p,head,e_upper) for p,head in zip(P,n)]
for p,head,bound in zip(P,n,m_upper):
    check('moment_positive_p'+str(p), moment(p,head,exp_lower(F(1),36)) > 0)
product_upper = math.prod(m_upper)
log_cap_bound = F(53863,8000)
log_moments_bound = F(2240699,10**6)
check('log_cap_bound_via_exp_lower', alpha*exp_lower(log_cap_bound,50) > 1)
check('sum_log_moments_bound_via_exp_lower', product_upper < exp_lower(log_moments_bound,50))
pure_above_B = sum((F(1,p**height*(p-1)) for p,height in zip(P,N)),F())
mixed_tail = tail-pure_above_B
pure_above_head = sum((F(1,p**head*(p-1)) for p,head in zip(P,n)),F())
check('mixed_tail_positive', mixed_tail > 0)
density_cost = cap*(mixed_tail+pure_above_head)
density_bound = F(70979023,10**9)
check('density_tail_bound', density_cost < density_bound)
three_bounds = log_cap_bound+log_moments_bound+density_bound
controlled_bound = F(4522277,500000)
check('three_bounds_below_controlled_bound', three_bounds < controlled_bound)
threshold=F(565,51)
delta=F(51863873,25500000)
check('exact_residual_budget', threshold-controlled_bound == delta)
check('residual_exceeds_two', delta > 2)
epsilon=F(1,10**7)
old_query_cap=F(70871,3375)
mix_upper=(1-epsilon)*controlled_bound+epsilon*old_query_cap
mix_bound=F(9044556,10**6)
check('mixture_bound', mix_upper < mix_bound)
check('mixture_lower_density', epsilon*F(1,5) == F(1,50000000))
check('mixture_residual_budget', threshold-mix_bound == F(25931911,12750000))
first = alpha*delta
second = alpha*(2*delta-3)
third = alpha*(delta-2)
check('positive_first_moment', first>0)
check('positive_second_moment', second>0)
check('positive_third_moment', third>0)

# Exact display intervals are derived from the rational values, without floats.
def interval(value, places=24):
    scale=10**places
    low=value.numerator*scale//value.denominator
    def show(integer):
        whole,frac=divmod(integer,scale)
        return str(whole)+'.'+str(frac).zfill(places)
    return [show(low),show(low+1)]

result={
 'input_name':SOURCE.name,'input_sha256':PIN,
 'scope':'new exact rational consequences of retained alpha and reciprocal tail; no old producer or label enumeration',
 'primes':P,'cutoff':B,'max_shallow_heights':N,'pure_head_depths':n,
 'e_upper':str(e_upper),'e_upper_taylor_degree':36,
 'exp_lower_log_bound_degree':50,
 'log_cap_upper':str(log_cap_bound),'sum_log_moments_upper':str(log_moments_bound),
 'moment_upper_by_prime':{str(p):str(value) for p,value in zip(P,m_upper)},
 'product_moment_upper':str(product_upper),
 'mixed_reciprocal_tail':str(mixed_tail),
 'pure_reciprocal_tail_above_heads':str(pure_above_head),
 'density_cost_exact':str(density_cost),'density_cost_interval':interval(density_cost),
 'density_cost_upper':str(density_bound),'three_component_upper_sum':str(three_bounds),
 'controlled_upper':str(controlled_bound),'residual_budget':str(delta),
 'mixture_exact_bound':str(mix_upper),'mixture_upper':str(mix_bound),
 'full_support_lower_density':str(epsilon/5),
 'moment_thresholds':{'first':str(first),'second':str(second),'third':str(third)},
 'moment_threshold_intervals':{'first':interval(first),'second':interval(second),'third':interval(third)},
 'checks':checks,'passed_count':len(checks)
}
out=args.output
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed_count':len(checks),'all_passed':all(checks.values()),'result':str(out),'density_cost_interval':interval(density_cost),'moment_threshold_intervals':result['moment_threshold_intervals']},indent=2))
