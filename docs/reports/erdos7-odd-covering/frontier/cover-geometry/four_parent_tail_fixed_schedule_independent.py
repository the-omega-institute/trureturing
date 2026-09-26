#!/usr/bin/env python3
"""Independent exact-rational all-height hinge audit of the fixed four-parent cut.
Reads only pinned657/658 JSON and candidate data. No producer is read/imported.
The entire infinite expectation is retained; only the finite negative part of
an integer hinge is enumerated. All193 rows and all194 cutoffs are recomputed.
"""
from argparse import ArgumentParser
from pathlib import Path
from fractions import Fraction as F
from math import prod,isqrt
from hashlib import sha256
import json
p=ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--witness',type=Path,default=None)
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=p.parse_args();checks={}
def ck(k,c):
 checks[k]=checks.get(k,0)+1
 if not c:raise RuntimeError(k)
paths=[a.directory/'ordinary_domain_five_parent_certificate.json',a.directory/'joint_square_pair_225_star_certificate.json',a.witness or a.directory/'four_parent_tail_fixed_schedule.json']
raw=[p.read_bytes() for p in paths];old,net,witness=map(json.loads,raw)
pins=['e46183469f280d262da37a9c33005e724690fc20b0106202c42c9913ed8d8ec0','cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5','fa79d1c28aea101da734ac687fe9ddb6e39bc6bd212a206183e049d1e929f758']
for r,h in zip(raw,pins):ck('pinned_input',sha256(r).hexdigest()==h)
rows=net['finite_rows'];oldrows=old['finite_rows'];candidate_rows=witness['rows']
owners=[n for n in range(37,1253) if all(n%d for d in range(2,isqrt(n)+1))]
ck('complete_prime_owner_window',len(owners)==193 and [r['owner'] for r in rows]==owners)
ck('same_row_counts',len(oldrows)==len(candidate_rows)==len(rows))
for x,y,z in zip(oldrows,rows,candidate_rows):
 ck('unchanged_h_cap_and_threshold',all(x[k]==y[k] for k in ('owner','h','cap','D','t','N')) and all(y[k]==z[k] for k in ('owner','h','cap')) and F(y['t'])==F(z['threshold']))
 v=y['owner'];h=y['h']
 ck('exact_actual_domain_calibration',y['N']==0 and F(y['cap'])==F(v-1,h) and F(y['D'])==F(v-2)-F(1,65536) and F(y['t'])==F(y['D'])-h)
for key in ('finite_endpoint','Euler_endpoint','Euler_scale','Euler_counts','M0_lower','M0_upper','Podd_lower','Podd_upper','Ctail','coordinate_moments','sharp_halfrow_constant7','complete_five_parent_tail','ordinary_typeI_fee'):
 ck('unchanged_full_network_parameter',old[key]==net[key])
ck('unchanged_generic_complete_moment',F(old['complete_fifth_role_count_moment7'])==F(net['complete_generic_five_role_moment7']))
ck('all_Euler_factors_retained',net['Euler_counts']=={'head':10,'finite':193,'half':123} and sum(net['Euler_counts'].values())==326)
ck('baseline_full_fee_decomposition',F(net['fee_before_arbitrary'])==F(net['finite_fee_upper'])+F(net['complete_five_parent_tail'])+F(net['ordinary_typeI_fee']))
ck('candidate_complete_tail_and_TypeI',F(witness['unchanged_five_parent_tail'])==F(net['complete_five_parent_tail']) and F(witness['unchanged_TypeI'])==F(net['ordinary_typeI_fee']))
roles=[(3,F(2,3),F(2)),(5,F(4,15),F(4,3)),(7,F(1,6),F(7,5)),(11,F(1,10),F(11,9))]
ck('candidate_four_roles',witness['four_role_primes']==[p for p,k,d in roles])
for prime,k,d in roles:
 ck('candidate_caps',F(witness['four_role_first_caps'][str(prime)])==k and F(witness['four_role_deep_caps'][str(prime)])==d)
 # The remaining geometric tail has total d/p^2 and its exact first moment.
 tailmass=d/F(prime**2);tailmean=d*F(3*prime-2,prime**2*(prime-1))
 ck('probability_distribution_normalization',1-k>=0 and k-tailmass>=0 and (1-k)+(k-tailmass)+tailmass==1)
 ck('complete_geometric_mean',1-k+2*(k-tailmass)+tailmean==1+k+d/F(prime*(prime-1)))
means={n:prod(1+k+d/F(p*(p-1)) for p,k,d in roles[:n])-1 for n in (3,4)}
ck('complete_three_and_four_means',means[3]==F(11,5) and means[4]==F(23,9))
ck('mean_matches_inherited_branches',means[3]==F(net['branch_parameters']['exact_EC']) and means[4]==F(old['branch_parameters']['four']['exact_EC'])==F(witness['complete_four_role_mean']))
factors={n:prod(F(net['coordinate_mass_upper'][str(p)]) for p in ((11,13,17,19) if n==3 else (13,17,19))) for n in (3,4)}
ck('omitted_actual_head_factors',factors[3]==F(net['branch_parameters']['factor']) and factors[4]==F(old['branch_parameters']['four']['factor'])==F(witness['four_role_omitted_head_factor']))
thresholds=[F(r['t']) for r in rows];N=max(t.numerator//t.denominator+1 for t in thresholds)
ck('complete_negative_part_endpoint',N==1079==witness['threshold_max'])
# Exact product convolution. X>=1 implies product<=N uses no atom X>N.
law=[F(0)]*(N+1);law[1]=F(1);hinges={};lawchecks=[]
for role,(prime,k,d) in enumerate(roles,1):
 atom=[F(0),1-k,k-d/F(prime**2)]+[d*(prime-1)/prime**j for j in range(3,N+1)]
 nxt=[F(0)]*(N+1)
 for i in range(1,N+1):
  if not law[i]:continue
  for j in range(1,N//i+1):nxt[i*j]+=law[i]*atom[j]
 law=nxt
 ck('finite_negative_part_subprobability',all(x>=0 for x in law) and sum(law)<=1)
 if role in (3,4):
  cumulativeP=F(0);cumulativeV=F(0);table=[]
  for n in range(N+1):
   if n:cumulativeP+=law[n];cumulativeV+=n*law[n]
   # C=product(X)-1. The complete mean, not a truncated mean, appears here.
   value=means[role]-n+(n+1)*cumulativeP-cumulativeV
   ck('positive_complete_integer_hinge',value>=0);table.append(value)
  ck('hinges_monotone',all(x>=y for x,y in zip(table,table[1:])))
  hinges[role]=table
fees={3:[],4:[]};rowdata=[];rowhash=sha256();displayScale=10**80
def bounds(x):
 z=x*displayScale;lo=z.numerator//z.denominator;hi=-(-z.numerator//z.denominator)
 return {'lower':str(F(lo,displayScale)),'upper':str(F(hi,displayScale)),'decimal':float(x)}
for inherited,claim,t in zip(rows,candidate_rows,thresholds):
 n=t.numerator//t.denominator;u=t-n
 ck('fixed_rational_interpolation',u==F(65535,65536))
 values={}
 for count,name in ((3,'three'),(4,'four')):
  hinge=(1-u)*hinges[count][n]+u*hinges[count][n+1]
  fee=factors[count]*hinge/inherited['h'];fees[count].append(fee);values[count]=fee
  ck('candidate_interval_contains_exact_hinge_fee',F(claim[name+'_lower'])<=fee<=F(claim[name+'_upper']))
  if count==3:
   ck('same_three_parent_certified_row',F(claim['three_lower'])==F(inherited['fee_lower']) and F(claim['three_upper'])==F(inherited['fee_upper']))
   ck('inherited_three_parent_interval_contains_exact_fee',F(inherited['fee_lower'])<=fee<=F(inherited['fee_upper']))
 ck('strict_four_vs_three_fee',values[4]>values[3])
 ck('candidate_difference_encloses_exact_increment',F(claim['increment_lower'])<=values[4]-values[3]<=F(claim['increment_upper']))
 ck('increment_interval_accounting',F(claim['increment_lower'])==F(claim['four_lower'])-F(claim['three_upper']) and F(claim['increment_upper'])==F(claim['four_upper'])-F(claim['three_lower']))
 ck('upper_fee_difference_is_accounting_only',F(claim['upper_fee_difference'])==F(claim['four_upper'])-F(claim['three_upper']))
 rowhash.update(json.dumps([inherited['owner'],str(values[3]),str(values[4])],separators=(',',':')).encode()+b'\n')
 rowdata.append(dict(owner=inherited['owner'],h=inherited['h'],four_fee=bounds(values[4]),increment=bounds(values[4]-values[3])))
ck('original_finite_fee_interval',F(net['finite_fee_lower'])<=sum(fees[3])<=F(net['finite_fee_upper']))
ck('candidate_old_finite_upper',F(witness['old_three_parent_fee'])==F(net['finite_fee_upper']))
ck('candidate_all_four_upper',F(witness['all_four_parent_fee_upper'])==sum(F(r['four_upper']) for r in candidate_rows))
gamma=F(193,100000);alpha=F(net['projection_alpha']);fixed=F(net['complete_five_parent_tail'])+F(net['ordinary_typeI_fee'])
ck('current_head_target',F(witness['head_gate'])==gamma and F(witness['projection_alpha'])==alpha)
cutoffs=owners+[1253];cutresults=[];policyresults=[]
for inherited,claim in zip(net['policies'],witness['policies']):
 ck('same_full_arbitrary_policy',(inherited['kind'],inherited['K'])==(claim['kind'],claim['K']) and F(inherited['fee'])==F(claim['arbitrary_tail']))
 tail=F(inherited['fee']);records=[]
 finiteExact=sum(fees[4]);finiteLower=sum(F(r['four_lower']) for r in candidate_rows);finiteUpper=sum(F(r['four_upper']) for r in candidate_rows)
 for ci,cut in enumerate(cutoffs):
  if ci:
   k=ci-1;finiteExact+=fees[3][k]-fees[4][k]
   finiteLower+=F(candidate_rows[k]['three_lower'])-F(candidate_rows[k]['four_lower'])
   finiteUpper+=F(candidate_rows[k]['three_upper'])-F(candidate_rows[k]['four_upper'])
  rawExact=gamma-finiteExact-fixed-tail;projected=alpha*rawExact
  record=dict(cutoff=cut,three_parent_rows=ci,four_parent_rows=193-ci,finite_fee_lower=finiteLower,finite_fee_upper=finiteUpper,extra_fee_upper_over_old=finiteUpper-F(net['finite_fee_upper']),raw_reserve_lower=gamma-finiteUpper-fixed-tail,raw_reserve_upper=gamma-finiteLower-fixed-tail,projected_lower=alpha*(gamma-finiteUpper-fixed-tail),projected_upper=alpha*(gamma-finiteLower-fixed-tail))
  ck('finite_cut_brackets_exact',finiteLower<=finiteExact<=finiteUpper)
  ck('complete_reserve_brackets_exact',record['projected_lower']<=projected<=record['projected_upper'])
  records.append((record,projected,finiteExact))
  if str(cut) in claim['cutoffs']:
   candidate=claim['cutoffs'][str(cut)]
   for key,value in record.items():ck('candidate_cut_accounting_exact',F(candidate[key])==value)
 firstPositive=next(i for i,(row,value,_) in enumerate(records) if value>0)
 firstDensity=next(i for i,(row,value,_) in enumerate(records) if value>F(1,2000000))
 ck('all_194_cutoffs',len(records)==claim['computed_cutoff_count']==194)
 ck('cut_reserves_increasing',all(x[1]<y[1] for x,y in zip(records,records[1:])))
 ck('first_positive_cutoff_matches',cutoffs[firstPositive]==claim['first_positive_cutoff'] and cutoffs[firstPositive-1]==claim['previous_positive_test_cutoff'])
 ck('first_density_cutoff_matches',cutoffs[firstDensity]==claim['first_preserving_2000000_cutoff'] and cutoffs[firstDensity-1]==claim['previous_density_test_cutoff'])
 ck('first_positive_certified_boundary',records[firstPositive][0]['projected_lower']>0 and records[firstPositive-1][0]['projected_upper']<=0)
 ck('first_density_certified_boundary',records[firstDensity][0]['projected_lower']>F(1,2000000) and records[firstDensity-1][0]['projected_upper']<=F(1,2000000))
 selected=sorted(set([cutoffs[firstPositive-1],cutoffs[firstPositive],cutoffs[firstDensity-1],cutoffs[firstDensity],139,149,181,191]))
 outputcuts=[]
 for cut in selected:
  idx=cutoffs.index(cut);record,value,exactfee=records[idx]
  outputcuts.append(dict(cutoff=cut,three_parent_rows=idx,four_parent_rows=193-idx,finite_fee=bounds(exactfee),projected_reserve=bounds(value)))
 policyresults.append(dict(kind=inherited['kind'],K=inherited['K'],complete_arbitrary_fee=str(tail),first_positive_cutoff=cutoffs[firstPositive],first_preserving_2000000_cutoff=cutoffs[firstDensity],computed_cutoff_count=len(records),cutoffs=outputcuts))
ck('common_positive_cut',max(p['first_positive_cutoff'] for p in policyresults)==witness['common_positive_cutoff']==149)
ck('common_density_cut',max(p['first_preserving_2000000_cutoff'] for p in policyresults)==witness['common_preserving_2000000_cutoff']==191)
result=dict(schema='fixed-schedule-four-parent-tail-independent-v1',status='PASS',new_lean_verification=False,read_same_round_producer=False,input_files=[p.name for p in paths],input_sha256=[sha256(r).hexdigest() for r in raw],verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),method='Exact Fraction product convolution plus complete-mean negative-part hinge identity; no finite-height cutoff on positive mass.',head_gate=str(gamma),projection_alpha=str(alpha),role_mean3=str(means[3]),role_mean4=str(means[4]),omitted_factor3=str(factors[3]),omitted_factor4=str(factors[4]),finite_owner_count=len(rows),complete_negative_part_endpoint=N,unchanged_Euler_factors=326,exact_row_fee_hash=rowhash.hexdigest(),display_interval_scale=str(displayScale),row_fee_intervals=rowdata,unchanged_complete_five_parent_tail=net['complete_five_parent_tail'],unchanged_TypeI=net['ordinary_typeI_fee'],common_positive_cutoff=149,common_preserving_2000000_cutoff=191,policies=policyresults,scope='Four-parent upgrade on finite owner rows cut<=v<1253 with every inherited h,cap and all326Euler factors fixed, full generic5 tail and full arbitrary-parent policy fee retained. Negative prior-cut reserve refutes this fixed budget certificate, not actual survivor mass or covering.',checks=checks,check_count=sum(checks.values()))
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','check_count','common_positive_cutoff','common_preserving_2000000_cutoff','exact_row_fee_hash')}))
for pol in policyresults:
 print(pol['kind'],pol['first_positive_cutoff'],pol['first_preserving_2000000_cutoff'],[(c['cutoff'],c['projected_reserve']['decimal']) for c in pol['cutoffs']])
