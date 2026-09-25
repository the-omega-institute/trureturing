#!/usr/bin/env python3
"""Complete same-source network budgets for the two Report624 interfaces.
Uses exact rational finite rows and the analytic infinite prime-tail bound.
No new Lean verification.
"""
from fractions import Fraction as F
from pathlib import Path
from math import prod, isqrt, ceil
from heapq import heappop,heappush
from hashlib import sha256
from itertools import combinations
import argparse,json,time
START=time.monotonic()
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
SOURCE=Path(__file__).with_name('arbitrary_pure_source_certificate.json')
source=json.loads(SOURCE.read_text());checks={}
def ck(k,v):
 if not v:raise ArithmeticError(k)
 checks[k]=True
ck('source_complete',source['complete'] is True and source['models']['root_one']['complete'] is True)
ck('source_producer_pin',sha256(SOURCE.with_suffix('.py').read_bytes()).hexdigest()==source['producer_sha256'])
ck('source_kernel_pin',sha256(SOURCE.with_suffix('.cpp').read_bytes()).hexdigest()==source['kernel_sha256'])
gamma=F(source['models']['root_one']['gate_lower']);alpha=F(source['Haar_factor'])
ck('gamma_root',gamma==F(534185412720319,23749451159961600))
ck('alpha',alpha==F(2673,110656))
ps=(3,5,7);caps=(F(2),F(4,3),F(7,5));boundary=971
head={3:F(2),5:F(4,3),7:F(7,5),11:F(11,9),13:F(13,11),17:F(17,15),19:F(19,17),23:F(5,3),29:F(20,11),31:F(2)}
for role,(p,c) in enumerate(zip(ps,caps)):
 ck('head_sorted_role_'+str(role),all(cp/u<=c/p for u,cp in head.items() if u>=p))
 ck('outside_sorted_role_'+str(role),F(1,5)<=c/p)
heap=[(1,(0,0,0))];seen={(0,0,0)};labels=[]
while len(labels)<boundary:
 d,e=heappop(heap);labels.append((d,e))
 for j,p in enumerate(ps):
  ee=tuple(x+(i==j) for i,x in enumerate(e))
  if ee not in seen:seen.add(ee);heappush(heap,(d*p,ee))
powers=[];top=labels[-1][0]
for p in ps:
 row=[];x=1
 while x<=top:row.append(x);x*=p
 powers.append(row)
rebuilt=sorted((a*b*c,(i,j,k)) for i,a in enumerate(powers[0]) for j,b in enumerate(powers[1]) for k,c in enumerate(powers[2]) if a*b*c<=top)
ck('cofactor_prefix_complete',rebuilt==labels)
def kernel(e,f):return prod(c/F(p**max(i,j)) if max(i,j) else F(1) for p,c,i,j in zip(ps,caps,e,f))
def row(e):return prod(1+c/F(p-1) if i==0 else c/F(p**i)*(i+1+F(1,p-1)) for p,c,i in zip(ps,caps,e))
factors=tuple(1+c*(F(3,p-1)+F(2,(p-1)**2)) for p,c in zip(ps,caps))
allmoment=prod(factors);moment=allmoment;rowsum=F();square=F();moments=[]
for n,(_,e) in enumerate(labels):
 cross=sum((kernel(e,f) for _,f in labels[:n]),F());diagonal=kernel(e,e)
 rowsum+=row(e);square+=2*cross+diagonal;moment-=2*(row(e)-cross)-diagonal
 ck('moment_'+str(n),moment==allmoment-2*rowsum+square and moment>0 and(not moments or moment<=moments[-1]))
 moments.append(moment)
primes=[v for v in range(37,boundary) if all(v%j for j in range(2,isqrt(v)+1))]
rows=[]
for v in primes:
 fee,n=min((moments[n]/(v-3-n)**2,n) for n in range(v-12))
 D=v-3-n;density=F(2*(v-1),D)
 ck('row_domain_'+str(v),D>=10)
 ck('row_cap_'+str(v),density<F(v,5))
 ck('row_fee_'+str(v),fee==moments[n]/D**2)
 rows.append({'owner_prime':v,'selected_nonunit_patterns':n,'complement_D':D,'threshold':F(1,2),'conditional_Haar_cap':density,'cofactor_moment':moments[n],'violation_fee':fee})
finite=sum((r['violation_fee'] for r in rows),F())
ck('finite_window',len(rows)==152 and rows[0]['owner_prime']==37 and rows[-1]['owner_prime']==967)
n0=7
AA=tuple(c*F(p*(p+1),(p-1)**2*p**n0) for p,c in zip(ps,caps))
BB=tuple(c*F(p,(p-1)*p**n0)*(n0+1+F(2,p-1)) for p,c in zip(ps,caps))
cube=sum(AA[i]*prod(factors[j] for j in range(3) if j!=i) for i in range(3))
cube+=2*sum(BB[i]*BB[j]*factors[3-i-j] for i in range(3) for j in range(i+1,3))
scaled=cube*3**n0;C=ceil(scaled)
ck('cube_uniform_constant',scaled<C)
ck('scaled_tail_diagonal_ratios',all(F(3,p)<=1 for p in ps))
ck('scaled_tail_cross_ratios',all(F(3,ps[i]*ps[j])*F(n0+2,n0+1)**2<1 for i in range(3) for j in range(i+1,3)))
ck('cube_window_at_971',2*n0**3+3<=boundary<=2*(n0+1)**3+1)
ck('cube_future_density',F(2*(2*n0**3+2),n0**3+1)==4<=F(boundary,5))
tail=F(6*C)*F(n0+1,n0)**2/F(n0**4)*F(3,2)/3**n0
fee=finite+tail;ordinary=F(1,65536);raw=gamma-fee-ordinary;haar=alpha*raw
ck('positive_root_one_budget',raw>0)
# The simple bound is chosen only after computing the exact fee; the raw criterion is unchanged.
fee_simple=F(ceil(fee*100000),100000)
ck('simple_fee_upper',fee<fee_simple)
head_den=ceil(1/haar)
if haar==F(1,head_den):head_den+=1
ck('simple_head_lower',haar>F(1,head_den))
# One actual finite correction supports both network scopes. New rows
# need not be dominated coordinatewise by Report621's old finite rows.
actual_caps=dict(head)
actual_caps.update({r['owner_prime']:r['conditional_Haar_cap'] for r in rows})
small_factors=[]
for p in sorted(actual_caps):
 cp=actual_caps[p];tp=1+cp*(F(3,p-1)+F(2,(p-1)**2))
 small_factors.append({'prime':p,'cap':cp,'moment':tp,'euler_correction':tp*F(p-1,p)**12})
A=prod(r['euler_correction'] for r in small_factors)
ck('complete_small_prime_correction_domain',sorted(actual_caps)==[p for p in range(3,971,2) if all(p%d for d in range(2,isqrt(p)+1))])
ck('new_actual_euler_correction',0<A<F(3,1000))
K=115;V=2**K;E=F(15,1000)*4**12*(K+2)**12/F(2**K)
ck('complete_E115',E==F(19740202146111572828188083,495176015714152109959649689600))
ck('dyadic_tail_ratio',F(1,2)*F(112,111)**12<F(3,5))
ck('large_owner_same_invariant',F(2*(V-1),V-3)<4<F(V,5))
ck('root_one_simple_gate',gamma>F(449,20000))
mixed_raw=raw-E;mixed_haar=alpha*mixed_raw
ck('mixed_arity_positive_reserve',mixed_raw>0)
ck('mixed_arity_head_bound',mixed_haar>F(1,5000))
ck('mixed_arity_simple_head_bound',alpha*(F(449,20000)-F(1411,100000)-ordinary-E)>F(1,5000))
ck('matching_source_complete',source['models']['matching']['complete'] is True and source['models']['matching']['complete_cases']==list(range(20)))
gamma_match=F(source['models']['matching']['gate_lower'])
ck('matching_exact_gate',gamma_match==F(135228904182589,189995609279692800))
match_raw=gamma_match-E;match_haar=alpha*match_raw
ck('matching_only_large_positive',match_raw>0)
ck('matching_only_large_head_bound',match_haar>F(1,62000))

def encode(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [encode(v) for v in x]
 return x
result={'schema':'arbitrary-pure-common-network-extensions-v1','status':'PASS','source':{'path':SOURCE.name,'sha256':sha256(SOURCE.read_bytes()).hexdigest(),'producer_sha256':source['producer_sha256'],'kernel_sha256':source['kernel_sha256']},'scope':{'head':'Exactly Report624 root-one head, including arbitrary central pure phases and finite heights; fixed mixed inventory and outside first-root layout remain.','outside':'At each owner prime >=37 one fixed tuple of at most three distinct smaller head or declared network parents; arbitrary finite size/crossing/depth/height and globally fixed numerical-label phases.','ordinary':'Declared disjoint extension domains with Haar complement budget 2/(v-1); inherited Type I total fee 1/65536 is explicitly charged. No undeclared private-interior parents.','law':'One actual head submeasure, then normalized capped rows in increasing owner order; no survival conditioning.','excluded':'For this all-three-parent branch: more than three parents per owner and multiple tuples not contained in one such fixed union; both branches retain the respective head restrictions and declared ordinary interfaces.'},'constants':{'head_gate':gamma,'alpha':alpha,'reference_parents':ps,'reference_caps':caps,'actual_head_caps':head,'minimum_complement_D':10,'conditional_density_rule':'v/5','threshold':F(1,2)},'moment_table':{'all_factors':factors,'all_moment':allmoment,'prefix':labels,'complete_tail_moments':moments},'finite_rows':rows,'finite_fee':finite,'tail':{'boundary':boundary,'cube_start':n0,'selected_count':'n^3-1','D':'v-n^3-2','scaled_start':scaled,'uniform_scaled_constant':C,'moment_upper':str(C)+'*3^(-n)','interval_count':'6*(n+1)^2','fee':tail},'consequence':{'total_owner_fee':fee,'simple_total_owner_fee_upper':fee_simple,'ordinary_single_head_fee':ordinary,'raw_good_lower':raw,'head_lower':haar,'simple_head_strict_lower':F(1,head_den),'full_density_strict_lower':f'1/({head_den} Q_off)'},'checks':checks,'check_count':len(checks),'new_lean_verification':False,'elapsed_seconds':time.monotonic()-START,'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
result['large_owner_tail']={'threshold':V,'dyadic_start':K,'finite_factors':small_factors,'finite_euler_correction':A,'correction_strict_upper':F(3,1000),'complete_tail_upper':E,'conditional_density_rule':'2(v-1)/(v-3)<4<v/5; normalized N=0 row on the actual ordinary extension domain'}
result['root_one_mixed_arity']={'scope':'Exactly Report624 root-one head and Report619 ordinary interfaces; below 2^115 each owner has one fixed union of at most three smaller head/network parents; at or above 2^115 any fixed finite union of smaller head/network parents. One actual joint law and one globally fixed phase per distinct numerical original.','raw_good_lower':mixed_raw,'head_lower':mixed_haar,'simple_head_strict_lower':F(1,5000),'full_density_strict_lower':'1/(5000 Q_off)','fee_accounting':'Charge the complete all-three-parent bound conservatively for the actual small owners, the complete new tail for large owners, and the ordinary Type I fee once. No actual owner uses two rows.'}
result['matching_only_large_owners']={'scope':'Exactly Report624 matching head; all added owner primes are at least 2^115 with any fixed finite union of smaller head or earlier declared owner parents; every non-head original is a pure owner power or assigned owner mixed label; no added small owners or private/Type I blocks.','head_gate':gamma_match,'raw_good_lower':match_raw,'head_lower':match_haar,'simple_head_strict_lower':F(1,62000),'full_density_strict_lower':'1/(62000 Q_off)','padding':'All small outside coordinates are absent; their positive T factors are numerical upper padding, not a second actual law.'}
args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
print(json.dumps(encode({'checks':len(checks),'elapsed':result['elapsed_seconds'],'finite_fee':float(finite),'tail_scaled_start':scaled,'tail_constant':C,'tail_fee':tail,'total_fee':float(fee),'simple_fee':fee_simple,'raw':float(raw),'head':float(haar),'simple_head':F(1,head_den),'min_D':min(r['complement_D'] for r in rows),'max_D':max(r['complement_D'] for r in rows)}),indent=2))
