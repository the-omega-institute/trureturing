#!/usr/bin/env python3
"""Fixed Taylor/rational certificates for three mixed-pivot profiles.
Consumes retained pure-chain and reciprocal-tail data. No old producer,
phase scan, prime-order scan, original-family enumeration or Lean build.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import math

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input',type=Path,default=Path(__file__).with_name('pure_chain_entropy.json'))
parser.add_argument('--tail-input',type=Path,default=Path(__file__).with_name('phase_resampling_arithmetic.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
def read_pin(path,pin):
 raw=path.read_bytes()
 if hashlib.sha256(raw).hexdigest()!=pin: raise ValueError('retained input pin mismatch: '+path.name)
 return json.loads(raw)
chain_pin='9e360070f26a86af520088623c32c49a35693f372d1be24f44a3fc05e078d356'
tail_pin='da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f'
chain=read_pin(args.input,chain_pin)
source=read_pin(args.tail_input,tail_pin)
checks={}
def req(name,value):
 checks[name]=bool(value)
 if not value: raise ValueError(name)
def exp_lower(x,n):
 if x<=0 or n<0: raise ValueError('invalid lower Taylor input')
 return sum((x**k/math.factorial(k) for k in range(n+1)),F())
def exp_upper(x,n):
 if not 0<x<n+2: raise ValueError('invalid upper Taylor input')
 return exp_lower(x,n)+x**(n+1)/math.factorial(n+1)/(1-x/F(n+2))
def moment(p,profile,base):
 n=len(profile);prefix=0;total=F()
 for k in range(n):
  total+=F(p-1,p**(k+1))*base**(k+prefix)
  prefix+=profile[k]
 return total+base**(n+prefix)/p**n-sum((F(1,p**j) for j in range(1,n+1)),F())
def interval(x,places=18):
 scale=10**places;k=x.numerator*scale//x.denominator
 def show(z):
  whole,frac=divmod(z,scale)
  return str(whole)+'.'+str(frac).zfill(places)
 return [show(k),show(k+1)]

P=tuple(chain['primes']);heads=tuple(chain['pure_head_depths']);B=source['cutoff']
alpha=F(source['alpha']);cap=1/alpha;eup=F(chain['e_upper']);elow=exp_lower(F(1),36)
req('reference_primes',P==(3,5,7,11,13,17,19))
req('head_depths',heads==(8,7,7,7,7,7,7))
req('retained_input_chain',chain['input_sha256']==tail_pin)
req('cutoff',B==10**9 and chain['cutoff']==B)
req('e_upper_via_Taylor_tail',exp_upper(F(1),36)<eup)
req('e_lower_above_two',elow>2)
base_bounds={3:F(1342392,10**6),5:F(400451,10**6),7:F(210347,10**6),11:F(102076,10**6)}
profile_specs={
 'pure3':(3,[0]*8,base_bounds[3]),
 'pure5':(5,[0]*7,base_bounds[5]),
 'pure7':(7,[0]*7,base_bounds[7]),
 'pure11':(11,[0]*7,base_bounds[11]),
 'sparse13':(13,[1]*7,F(709769,10**6)),
 'sparse17':(17,[1]*7,F(470204,10**6)),
 'sparse19':(19,[1]*7,F(401435,10**6)),
 'two11heads':(11,[1,1,0,0,0,0,0],F(675246,10**6)),
 'one7head':(7,[1,0,0,0,0,0,0],F(773905,10**6)),
}
profiles={}
for name,(p,prof,logbound) in profile_specs.items():
 upper=moment(p,prof,eup)
 req(name+'_positive',moment(p,prof,elow)>0)
 req(name+'_log_upper',upper<exp_lower(logbound,50))
 profiles[name]={'prime':p,'multiplicities':prof,'moment_upper':str(upper),'log_upper':str(logbound)}
for p,n in zip(P,heads):
 req('zero_profile_recovers_retained_pure_'+str(p),moment(p,[0]*n,eup)==F(chain['moment_upper_by_prime'][str(p)]))

logcap=F(chain['log_cap_upper']);density_bound=F(chain['density_cost_upper'])
req('retained_log_cap_contract',cap<exp_lower(logcap,50))
mixed_tail=F(source['tail'])-sum((F(1,p**N*(p-1)) for p,N in zip(P,chain['max_shallow_heights'])),F())
pure_tail=sum((F(1,p**n*(p-1)) for p,n in zip(P,heads)),F())
base_density=cap*(mixed_tail+pure_tail)
req('mixed_tail_matches_retained',mixed_tail==F(chain['mixed_reciprocal_tail']))
req('base_density_matches_retained',base_density==F(chain['density_cost_exact']))
req('retained_base_density_upper',base_density<density_bound)

cofactor11=F(3,2)*F(5,4)*F(7,6)-1
cofactor7=F(3,2)*F(5,4)-1
tail11=cofactor11/F(10*11**7)
tail7=cofactor7/F(6*7**7)
req('complete_11_pivot_tail',tail11==F(19,160*11**7))
req('complete_7_pivot_tail',tail7==F(1,48*7**6))
cost11=cap*tail11;cost711=cap*(tail7+tail11)
cost11bound=F(5117,10**9);cost711bound=F(153786,10**9)
req('11_pivot_tail_density_cost',cost11<cost11bound)
req('7_and_11_pivot_tail_density_cost',cost711<cost711bound)
for p in (13,17,19):req('no_shallow_high_pivot_above_head_'+str(p),3*p**8>B)
req('actual_13_pivot_maximum_depth',3*13**7<=B<3*13**8)
req('actual_17_pivot_maximum_depth',3*17**6<=B<3*17**7)
req('actual_19_pivot_maximum_depth',3*19**6<=B<3*19**7)

base_names=['pure3','pure5','pure7','pure11','sparse13','sparse17','sparse19']
base_sum=sum((F(profiles[name]['log_upper']) for name in base_names),F())
second_sum=base_sum-base_bounds[11]+F(profiles['two11heads']['log_upper'])
third_sum=base_sum-base_bounds[7]+F(profiles['one7head']['log_upper'])
req('sparse_high_log_sum',base_sum==F(1818337,500000))
T=F(565,51)
final_specs={
 'sparse_high':(base_sum,F(),F(10440528023,10**9)),
 'two_11_heads':(second_sum,cost11bound,F(550685157,50000000)),
 'one_7_head':(third_sum,cost711bound,F(11004239809,10**9))
}
final={}
for name,(logs,extra,bound) in final_specs.items():
 req(name+'_assembled_upper',logcap+logs+density_bound+extra==bound)
 req(name+'_below_target',bound<T)
 final[name]={'log_profile_sum_upper':str(logs),'extra_tail_cost_upper':str(extra),'all_query_upper':str(bound),'all_query_decimal_interval':interval(bound),'strict_margin':str(T-bound)}

# These finite profile classes already satisfy the earlier existential capacity
# criterion. This check prevents their every-G result being sold as first existence.
Dmax=F(4096,935)
high_capacity=sum((F(2,3*(p-2)) for p in (13,17,19)),F())
capacity_cases={
 'sparse_high':high_capacity+Dmax*F(source['tail']),
 'two_11_heads':high_capacity+F(2,3)*F(10,9)*(F(1,11)+F(1,121))+Dmax*(F(source['tail'])+tail11),
 'one_7_head':high_capacity+F(4,35)+Dmax*(F(source['tail'])+tail7+tail11)
}
for name,value in capacity_cases.items():req(name+'_already_in_mixed_capacity_region',value<F(2,3))

result={
 'input_names':[args.input.name,args.tail_input.name],'input_sha256':[chain_pin,tail_pin],
 'scope':'three fixed every-G-law pivot profiles; exact exponential upper and logarithm certificates; complete analytic pivot tails',
 'e_upper':str(eup),'e_upper_Taylor_degree':36,'log_lower_Taylor_degree':50,
 'profiles':profiles,'log_cap_upper':str(logcap),'base_density_cost_exact':str(base_density),'base_density_cost_upper':str(density_bound),
 'pivot_tails':{'11_reciprocal':str(tail11),'7_reciprocal':str(tail7),'11_density_cost':str(cost11),'7_and_11_density_cost':str(cost711),'11_density_cost_interval':interval(cost11),'7_and_11_density_cost_interval':interval(cost711)},
 'actual_high_pivot_shallow_label_maximum':{'13':7,'17':6,'19':6,'total':19},
 'final_bounds':final,'prior_existential_mixed_capacity_upper':{k:str(v) for k,v in capacity_cases.items()},
 'checks':checks,'passed_count':len(checks)
}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed_count':len(checks),'bounds':{k:v['all_query_upper'] for k,v in final.items()},'tail11':str(tail11),'tail7':str(tail7),'result':str(args.output)},indent=2))
