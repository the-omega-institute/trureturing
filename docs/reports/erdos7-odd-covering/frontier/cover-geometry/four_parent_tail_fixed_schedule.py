#!/usr/bin/env python3
"""Exact complete four-role hinge bounds on the unchanged 657/658 row schedule.

Only owners at or above a selected finite prime cutoff are upgraded to four
parents; every actual h, cap, Euler factor and infinite continuation fee stays
fixed. All means are complete; the finite convolution computes only the
negative part of the stop-loss identity, so no positive tail is discarded.
"""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt, prod
from pathlib import Path
import argparse,json

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
checks=Counter()
def ck(name,ok):
 if not ok:raise ArithmeticError(name)
 checks[name]+=1
PINS={
 'ordinary_domain_five_parent_certificate.json':'e46183469f280d262da37a9c33005e724690fc20b0106202c42c9913ed8d8ec0',
 'joint_square_pair_225_star_certificate.json':'cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5',
}
data={}
for name,pin in PINS.items():
 b=(args.directory/name).read_bytes();ck('source_pin',sha256(b).hexdigest()==pin);data[name]=json.loads(b)
old=data['joint_square_pair_225_star_certificate.json'];oldrows=old['finite_rows'];original=data['ordinary_domain_five_parent_certificate.json']
primes=[p for p in range(37,1253)if all(p%d for d in range(2,isqrt(p)+1))]
ck('complete_owner_window',[r['owner']for r in oldrows]==primes and len(primes)==193)
ck('same_row_count',len(original['finite_rows'])==193)
for a,b in zip(oldrows,original['finite_rows']):
 ck('unchanged_actual_row',all(a[k]==b[k]for k in('owner','h','D','t','N','cap')))
ck('unchanged_five_tail',F(old['complete_five_parent_tail'])==F(original['complete_five_parent_tail']))
for name in('Euler_endpoint','Euler_scale','Euler_counts','M0_lower','M0_upper','Podd_lower','Podd_upper','Ctail','ordinary_typeI_fee'):
 ck('unchanged_Euler_and_TypeI',old[name]==original[name])

S=10**75
ceildiv=lambda n,d:-((-n)//d)
TMAX=max(ceildiv(F(r['t']).numerator,F(r['t']).denominator)for r in oldrows)
ps=(3,5,7,11);K={3:F(2,3),5:F(4,15),7:F(1,6),11:F(1,10)};D={3:F(2),5:F(4,3),7:F(7,5),11:F(11,9)}
zeta=F(1549,1716)*F(3793,4080)*F(5455,5814)
ck('four_role_factor',zeta==F(original['branch_parameters']['four']['factor']))
mean=prod(1+K[p]+D[p]/(p*(p-1))for p in ps)-1
ck('complete_four_role_mean',mean==F(23,9)==F(original['branch_parameters']['four']['exact_EC']))
low,high=[0,S]+[0]*(TMAX-1),[0,S]+[0]*(TMAX-1)
for p in ps:
 alo,ahi=[0]*(TMAX+1),[0]*(TMAX+1)
 for j,prob in enumerate((1-K[p],K[p]-D[p]/p**2),1):
  ck('nonnegative_initial_atom',prob>=0);alo[j]=prob.numerator*S//prob.denominator;ahi[j]=ceildiv(prob.numerator*S,prob.denominator)
 ppow=p**3
 for j in range(3,TMAX+1):
  num,den=D[p].numerator*(p-1),D[p].denominator*ppow
  alo[j],ahi[j]=num*S//den,ceildiv(num*S,den);ppow*=p
 nlo,nhi=[0]*(TMAX+1),[0]*(TMAX+1)
 for i in range(1,TMAX+1):
  for j in range(1,TMAX//i+1):
   nlo[i*j]+=low[i]*alo[j];nhi[i*j]+=high[i]*ahi[j]
 for i in range(1,TMAX+1):
  nlo[i]//=S;nhi[i]=ceildiv(nhi[i],S);ck('complete_negative_part_atom_bounds',0<=nlo[i]<=nhi[i])
 low,high=nlo,nhi
pl=pu=ml=mu=0;hl=[];hu=[]
for t in range(TMAX+1):
 if t:pl+=low[t];pu+=high[t];ml+=t*low[t];mu+=t*high[t]
 l=mean-t+F((t+1)*pl-ml,S);u=mean-t+F((t+1)*pu-mu,S)
 ck('complete_integer_hinge_interval',0<=l<=u)
 hl.append(l);hu.append(u)
rows=[]
for row in oldrows:
 t=F(row['t']);n=t.numerator//t.denominator;f=t-n;h=row['h'];v=row['owner']
 ck('fixed_rational_threshold',t==F(v-2)-F(1,65536)-h and f==1-F(1,65536) and n+1<=TMAX)
 fl=zeta*((1-f)*hl[n]+f*hl[n+1])/h;fu=zeta*((1-f)*hu[n]+f*hu[n+1])/h
 ck('four_role_row_interval',0<=fl<=fu and fu-fl<F(1,10**60))
 oldlow,oldup=F(row['fee_lower']),F(row['fee_upper'])
 ck('four_vs_three_strict_comparison',fl>oldup)
 rows.append(dict(owner=v,h=h,cap=row['cap'],threshold=row['t'],
                  three_lower=str(oldlow),three_upper=str(oldup),four_lower=str(fl),four_upper=str(fu),
                  increment_lower=str(fl-oldup),increment_upper=str(fu-oldlow),upper_fee_difference=str(fu-oldup)))
# These differences compare explicit complete comparison fees; they do not
# assert that actual losses attain either comparison expression.
base3=sum((F(r['three_upper'])for r in rows),F());fourall=sum((F(r['four_upper'])for r in rows),F())
ck('same_three_total',base3==F(old['finite_fee_upper']))
alpha=F(old['projection_alpha']);gamma=F(193,100000)
fixed=F(old['complete_five_parent_tail'])+F(old['ordinary_typeI_fee'])
policies=[];all_policy_cuts={}
for p in old['policies']:
 fee=F(p['fee']);ck('same_complete_arbitrary_tail',fee==F(original[p['kind']+'_policy']['fee']))
 cuts=[]
 for cutindex,cutoff in enumerate(primes+[1253]):
  lo=sum((F(r['three_lower']if i<cutindex else r['four_lower'])for i,r in enumerate(rows)),F())
  up=sum((F(r['three_upper']if i<cutindex else r['four_upper'])for i,r in enumerate(rows)),F())
  raw_lower=gamma-up-fixed-fee;raw_upper=gamma-lo-fixed-fee
  cuts.append(dict(cutoff=cutoff,three_parent_rows=cutindex,four_parent_rows=193-cutindex,
                   finite_fee_lower=str(lo),finite_fee_upper=str(up),
                   extra_fee_upper_over_old=str(up-base3),
                   raw_reserve_lower=str(raw_lower),raw_reserve_upper=str(raw_upper),
                   projected_lower=str(alpha*raw_lower),projected_upper=str(alpha*raw_upper)))
 first=next(c for c in cuts if F(c['raw_reserve_lower'])>0)
 idx=cuts.index(first)
 ck('minimal_positive_cutoff_boundary',idx>0 and F(cuts[idx-1]['raw_reserve_upper'])<0)
 first_density=next(c for c in cuts if F(c['projected_lower'])>F(1,2000000))
 ix=cuts.index(first_density)
 ck('minimal_preserved_density_boundary',ix>0 and F(cuts[ix-1]['projected_upper'])<F(1,2000000))
 all_policy_cuts[p['kind']]=cuts
 keycuts={first['cutoff'],cuts[idx-1]['cutoff'],first_density['cutoff'],cuts[ix-1]['cutoff']}
 policies.append(dict(kind=p['kind'],K=p['K'],arbitrary_tail=str(fee),
                      first_positive_cutoff=first['cutoff'],first_preserving_2000000_cutoff=first_density['cutoff'],
                      previous_positive_test_cutoff=cuts[idx-1]['cutoff'],previous_density_test_cutoff=cuts[ix-1]['cutoff'],
                      computed_cutoff_count=len(cuts),cutoffs={str(c['cutoff']):c for c in cuts if c['cutoff']in keycuts}))
common_cut=max(p['first_positive_cutoff']for p in policies)
common_density_cut=max(p['first_preserving_2000000_cutoff']for p in policies)
for p in policies:
 for c in all_policy_cuts[p['kind']]:
  if c['cutoff']in(common_cut,common_density_cut):p['cutoffs'][str(c['cutoff'])]=c
 p['cutoffs']=dict(sorted(p['cutoffs'].items(),key=lambda item:int(item[0])))
result=dict(schema='fixed-schedule-four-parent-tail-v1',status='PASS',new_lean_verification=False,
 source_sha256=PINS,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
 head_gate=str(gamma),projection_alpha=str(alpha),scale=str(S),threshold_max=TMAX,
 four_role_primes=ps,four_role_first_caps={str(p):str(K[p])for p in ps},four_role_deep_caps={str(p):str(D[p])for p in ps},
 four_role_omitted_head_factor=str(zeta),complete_four_role_mean=str(mean),
 unchanged_five_parent_tail=old['complete_five_parent_tail'],unchanged_TypeI=old['ordinary_typeI_fee'],
 rows=rows,old_three_parent_fee=str(base3),all_four_parent_fee_upper=str(fourall),
 common_positive_cutoff=common_cut,common_preserving_2000000_cutoff=common_density_cut,
 policies=policies,checks=dict(checks),check_count=sum(checks.values()))
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=result['check_count'],all_four_fee=float(fourall),
 common_positive_cutoff=common_cut,common_preserving_2000000_cutoff=common_density_cut,
 policies=[dict(kind=p['kind'],first_positive_cutoff=p['first_positive_cutoff'],
 first_preserving_2000000_cutoff=p['first_preserving_2000000_cutoff'],
 first_positive_margin=float(F(p['cutoffs'][str(p['first_positive_cutoff'])]['projected_lower'])),
 first_preserved_density_margin=float(F(p['cutoffs'][str(p['first_preserving_2000000_cutoff'])]['projected_lower'])))for p in policies]),indent=2))
