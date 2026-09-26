#!/usr/bin/env python3
"""Exact positive-layer certificates for moved-threshold owner rows.

Only stdlib. Finite grid uses exact integer probabilities; the discarded
infinite positive tail is bounded analytically. No candidate producer import,
no floating-point decisions, no new Lean verification.
"""
from pathlib import Path
from fractions import Fraction as F
from math import prod,comb,isqrt,lcm
from heapq import heappop,heappush
from hashlib import sha256
from collections import Counter
import json,time
START=time.monotonic()
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=Path(__file__).with_name('arbitrary_pure_network_extensions.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
SOURCE=args.source
old=json.loads(SOURCE.read_text())
checks=Counter()
def ck(name,p):
 if not p:raise ArithmeticError(name)
 checks[name]+=1
ps=(3,5,7);ds=(F(2),F(4,3),F(7,5));K=28;LENGTH=958
heap=[(1,(0,0,0))];seen={(0,0,0)};labels=[]
while len(labels)<LENGTH:
 value,e=heappop(heap);labels.append((value,e))
 for j,p in enumerate(ps):
  ee=tuple(v+(i==j) for i,v in enumerate(e))
  if ee not in seen:seen.add(ee);heappush(heap,(value*p,ee))
ck('prefix_matches_complete625_list',labels==[(v,tuple(e)) for v,e in old['moment_table']['prefix'][:LENGTH]])
ck('all_selected_exponents_below_grid',all(max(e)<K for _,e in labels))
# Independent bounded Cartesian enumeration checks no smooth number omitted.
max_value=labels[-1][0]
power_lists=[]
for p in ps:
 row=[];v=1
 while v<=max_value:row.append(v);v*=p
 power_lists.append(row)
rebuilt=sorted((a*b*c,(i,j,k)) for i,a in enumerate(power_lists[0]) for j,b in enumerate(power_lists[1])
               for k,c in enumerate(power_lists[2]) if a*b*c<=max_value)
ck('prefix_complete_by_cartesian_enumeration',rebuilt==labels)
nums=[];dens=[]
for p,d in zip(ps,ds):
 a,b=d.numerator,d.denominator;den=b*p**K
 row=[den-a*p**(K-1)]+[a*(p-1)*p**(K-l-1) for l in range(1,K)]
 ck('positive_layer_integer_weights',min(row)>0)
 ck('discarded_probability_exact',F(sum(row),den)==1-d/F(p**K))
 nums.append(row);dens.append(den)
DEN=prod(dens)
weights=[nums[0][i]*nums[1][j]*nums[2][k] for i in range(K) for j in range(K) for k in range(K)]
counts=[(i+1)*(j+1)*(k+1) for i in range(K) for j in range(K) for k in range(K)]
# Positive truncated all-volume moments factor coordinatewise.
current={r:prod(sum(nums[i][l]*(l+1)**r for l in range(K)) for i in range(3)) for r in (3,4)}
raw={3:[],4:[]}
delta3=[3*c*c-3*c+1 for c in range(K**3+1)]
delta4=[4*c*c*c-6*c*c+4*c-1 for c in range(K**3+1)]
for n,(_,e) in enumerate(labels):
 a,b,c=e;drop3=0;drop4=0
 for i in range(a,K):
  for j in range(b,K):
   start=(i*K+j)*K
   for k in range(c,K):
    h=start+k;C=counts[h]
    if C<1:raise ArithmeticError('selected prefix not in remaining orthant')
    W=weights[h];drop3+=W*delta3[C];drop4+=W*delta4[C];counts[h]=C-1
 current[3]-=drop3;current[4]-=drop4
 for r in (3,4):
  ck('positive_and_monotone_truncated_moment',current[r]>0 and (not raw[r] or current[r]<=raw[r][-1]))
  raw[r].append(current[r])
# Direct positive summation at the final prefix checks update recurrences.
for r in (3,4):
 ck('final_direct_positive_layer_sum_order'+str(r),raw[r][-1]==sum(w*c**r for w,c in zip(weights,counts)))
def geom(p):
 return [F(1),F(1,p-1),F(p+1,(p-1)**2),F(p*p+4*p+1,(p-1)**3),F(p**3+11*p*p+11*p+1,(p-1)**4)]
def tail_moment(p,d,start,r):
 return d/F(p**start)*sum((F(comb(r,j)*(start+1)**(r-j))*geom(p)[j] for j in range(r+1)),F())
def full_moment(p,d,r):return 1-d/p+tail_moment(p,d,1,r)
TAIL={};TOT={};num_upper={};common_den={}
for r in (3,4):
 total=[full_moment(p,d,r) for p,d in zip(ps,ds)]
 tails=[tail_moment(p,d,K,r) for p,d in zip(ps,ds)]
 error=sum((tails[i]*prod(total[j] for j in range(3) if j!=i) for i in range(3)),F())
 # The complement count is <=total box volume, so this SAME bound works everyN.
 TAIL[r]=error;TOT[r]=total
 common_den[r]=lcm(DEN,error.denominator)
 factor=common_den[r]//DEN;offset=error.numerator*(common_den[r]//error.denominator)
 num_upper[r]=[x*factor+offset for x in raw[r]]
 ck('positive_discarded_tail_order'+str(r),error>0)
 # N=0 removes only the unit pattern; its full moment is exact by binomial expansion.
 exact0=sum((F(comb(r,j)*(-1)**(r-j))*prod(full_moment(p,d,j) for p,d in zip(ps,ds)) for j in range(r+1)),F())
 ck('N0_full_moment_inside_certified_interval_order'+str(r),F(raw[r][0],DEN)<=exact0<=F(num_upper[r][0],common_den[r]))
primes=[v for v in range(37,971) if all(v%d for d in range(2,isqrt(v)+1))]
ck('exact152_owner_window',len(primes)==152 and primes[0]==37 and primes[-1]==967)
head={int(p):F(d) for p,d in old['constants']['actual_head_caps'].items()}
ck('literal_ten_head_caps',sorted(head)==[3,5,7,11,13,17,19,23,29,31])
E115=F(19740202146111572828188083,495176015714152109959649689600)
ck('inherited_E115_formula',E115==F(15,1000)*4**12*117**12/F(2**115))
PRIME_TAIL=F(512,9529569)
RESULT={}
for r in (3,4):
 rows=[]
 for v in primes:
  best_n=None;best_num=None;best_Dpower=None
  for n in range(v-3-5*r+1):
   D=v-3-n;Dpower=D**r;num=num_upper[r][n]
   if best_n is None or num*best_Dpower<best_num*Dpower:
    best_n=n;best_num=num;best_Dpower=Dpower
  n=best_n;D=v-3-n;cap=F(r*(v-1),D);moment=F(best_num,common_den[r]);fee=moment/F(D**r)
  ck('owner_D_invariant_order'+str(r),D>=5*r)
  ck('owner_cap_invariant_order'+str(r),cap<F(v,5))
  rows.append(dict(owner_prime=v,selected_nonunit_patterns=n,complement_D=D,threshold=F(r-1,r),
    conditional_Haar_cap=cap,complete_moment_upper=moment,violation_fee=fee))
 finite=sum((row['violation_fee'] for row in rows),F());W=finite+PRIME_TAIL
 simple=F(8631,1000000) if r==3 else F(397,50000)
 ck('simple_complete_owner_fee_order'+str(r),W<simple)
 actual=dict(head);actual.update({row['owner_prime']:row['conditional_Haar_cap'] for row in rows})
 allodd=[p for p in range(3,971,2) if all(p%d for d in range(2,isqrt(p)+1))]
 ck('complete162_finite_Euler_factors_order'+str(r),len(actual)==162 and sorted(actual)==allodd)
 factors=[]
 for p,cap in sorted(actual.items()):
  moment2=1+cap*(F(3,p-1)+F(2,(p-1)**2))
  factors.append(dict(prime=p,cap=cap,moment2=moment2,euler_correction=moment2*F(p-1,p)**12))
 correction=prod(x['euler_correction'] for x in factors)
 Aupper=F(3,1000) if r==3 else F(8,1000)
 ck('new_finite_Euler_correction_order'+str(r),0<correction<Aupper)
 E=5*Aupper*4**12*117**12/F(2**115)
 ck('same_V_complete_large_owner_tail_order'+str(r),E==(E115 if r==3 else F(8,3)*E115))
 RESULT[str(r)]=dict(moment_order=r,grid_K=K,common_moment_denominator=common_den[r],
  positive_layer_full_coordinate_moments=TOT[r],discarded_grid_tail_upper=TAIL[r],
  upper_moment_numerators=num_upper[r],rows=rows,finite_owner_fee=finite,prime_tail_fee=PRIME_TAIL,
  total_owner_fee=W,simple_total_owner_fee_upper=simple,minimum_D=min(x['complement_D'] for x in rows),
  finite_Euler_factors=factors,finite_Euler_correction=correction,finite_Euler_strict_upper=Aupper,
  complete_large_owner_tail=E,same_large_owner_threshold=2**115,
  owner_plus_large_tail_plus_ordinary=W+E+F(1,65536))
# Exact numerical source hash and certificate producer identity are retained.
def enc(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):enc(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [enc(v) for v in x]
 return x
OUT=dict(schema='owner-moved-threshold-positive-layer-exact-v1',status='PASS',ordinary_exact_arithmetic=True,new_lean_verification=False,
 source=dict(path=SOURCE.name,sha256=sha256(SOURCE.read_bytes()).hexdigest()),
 producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
 prefix_count=LENGTH,grid_K=K,integer_grid_cells=K**3,source_probability_denominator=DEN,
 check_count=sum(checks.values()),checks=dict(checks),results=RESULT,elapsed_seconds=time.monotonic()-START)
args.output.write_text(json.dumps(enc(OUT),indent=2)+'\n')
print(json.dumps(dict(status='PASS',check_count=OUT['check_count'],elapsed_seconds=OUT['elapsed_seconds'],
 results={r:dict(owner_fee=float(v['total_owner_fee']),simple_upper=str(v['simple_total_owner_fee_upper']),
  discarded_tail=float(v['discarded_grid_tail_upper']),min_D=v['minimum_D'],Euler=float(v['finite_Euler_correction']),
  Euler_upper=str(v['finite_Euler_strict_upper']),E=float(v['complete_large_owner_tail']),
  total_plus_E_plus_ordinary=float(v['owner_plus_large_tail_plus_ordinary'])) for r,v in RESULT.items()}),indent=2))
