#!/usr/bin/env python3
"""Paired-response owner fees on unchanged193 rows, with old noncanonical bounds.

Ordinary numerical evidence, no Lean or LP. Complete means plus finite negative
parts retain every positive-height tail. Canonical fees are exact Fractions;
all386 old branch comparisons use rigorous directed integer intervals.
"""
from fractions import Fraction as F
from pathlib import Path
from math import prod, comb
from functools import lru_cache
import argparse, hashlib, itertools, json, sys
sys.set_int_max_str_digits(0)
PINS={
 'four_parent_tail_fixed_schedule.json':'fa79d1c28aea101da734ac687fe9ddb6e39bc6bd212a206183e049d1e929f758',
 'ordinary_domain_five_parent_certificate.json':'e46183469f280d262da37a9c33005e724690fc20b0106202c42c9913ed8d8ec0',
 'joint_square_pair_225_star_certificate.json':'cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5',
}
COUNTS={}
def check(ok,label):
 COUNTS[label]=COUNTS.get(label,0)+1
 if not ok:raise RuntimeError(label)
def atom(p,k1,d,j):
 if j==1:return 1-k1
 if j==2:return k1-d/F(p*p)
 return d*(p-1)/p**j
def mean(p,k1,d):return 1+k1+d/F(p*(p-1))
def convolution(a,b,N):
 r=[F(0)]*(N+1)
 for i in range(1,N+1):
  if not a[i]:continue
  for j in range(1,N//i+1):
   if b[j]:r[i*j]+=a[i]*b[j]
 return r
def prefixes(values):
 mass=[values[0]]; moment=[values[0]]
 for j,v in enumerate(values[1:],1):
  mass.append(mass[-1]+v); moment.append(moment[-1]+j*v)
 return mass,moment
def hinge(mass,mu,pre,s):
 n=s.numerator//s.denominator
 return mu-s*mass+s*pre[0][n]-pre[1][n]
OUTPUT_SCALE=10**90
def rounded(x):
 lo=F((x.numerator*OUTPUT_SCALE)//x.denominator,OUTPUT_SCALE)
 hi=F(-((-x.numerator*OUTPUT_SCALE)//x.denominator),OUTPUT_SCALE)
 return lo,hi
def summary(x):
 lo,hi=rounded(x)
 return {'lower':str(lo),'upper':str(hi),'decimal':float(x)}
def digest(value):return hashlib.sha256(json.dumps(value,separators=(',',':'),sort_keys=True).encode()).hexdigest()

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path,default=None);args=ap.parse_args()
 data={}
 for name,sha in PINS.items():
  raw=(args.directory/name).read_bytes();check(hashlib.sha256(raw).hexdigest()==sha,'input pin');data[name]=json.loads(raw)
 old=data['four_parent_tail_fixed_schedule.json'];rows=old['rows'];source657=data['ordinary_domain_five_parent_certificate.json'];source658=data['joint_square_pair_225_star_certificate.json']
 check(len(rows)==193,'193 unchanged rows')
 map657={r['owner']:r for r in source657['finite_rows']}
 map658={r['owner']:r for r in source658['finite_rows']}
 primes=[v for v in range(37,1253) if all(v%d for d in range(2,int(v**0.5)+1))]
 check([r['owner'] for r in rows]==primes,'complete prime owner window')
 for row in rows:
  v,h=row['owner'],row['h'];r=map657[v]
  check(h==r['h'] and F(row['cap'])==F(r['cap']),'657 unchanged h and cap')
  check(F(row['cap'])==F(v-1,h) and F(row['cap'])/v<F(1,10),'same full-history cap invariant')
  check(F(row['threshold'])==v-2-F(1,65536)-h,'same actual rational threshold')
  r658=map658[v]
  check(h==r658['h'] and row['cap']==r658['cap'] and row['threshold']==r658['t'],'658 unchanged h cap threshold')
  check(row['three_lower']==r658['fee_lower'] and row['three_upper']==r658['fee_upper'],'unchanged inherited three-parent bounds')
 check(old['source_sha256']['joint_square_pair_225_star_certificate.json']==PINS['joint_square_pair_225_star_certificate.json'],'658 row source retained')
 for key in ('Euler_counts','M0_lower','M0_upper','Podd_lower','Podd_upper','Ctail','complete_five_parent_tail'):
  check(source657[key]==source658[key],'unchanged Euler and complete tail inputs')
 N=max((F(r['threshold'])+1).__ceil__() for r in rows)
 check(N==1080,'finite negative-part endpoint')
 R0=F('4772450719173523/8462661375168000');R7=F('27737260658149/40298387500800');R11=F('5537579678017/8548142803200');R711=F('10660439701/13568480640')
 D={q:(F(5,6) if q==7 else F(q-2,q-1)-F(2,q*(q-2))) for q in (7,11,13,17,19)}
 @lru_cache(None)
 def matching(vertices):
  if not vertices:return F(1)
  v=vertices[0];rest=vertices[1:]
  value=D[v]*matching(rest)
  for q in rest:
   edge=F(1,v*(v-2)*(q-1))+F(1,(v-1)*q*(q-2))
   value-=edge*matching(tuple(u for u in rest if u!=q))
  return value
 universe=tuple(D)
 for support,expected in (((),R0),((7,),R7),((11,),R11),((7,11),R711)):
  check(matching(tuple(q for q in universe if q not in support))==expected,'matching recurrence reconstructs paired response')
 a,b=F(1,6),F(1,10)
 tau=(R0-a*R7-b*R11+a*b*R711,R7-b*R711,R11-a*R711,R711)
 check(all(v>=0 for v in tau),'positive paired comparison coefficients')
 check(tau[0]+a*tau[1]+b*tau[2]+a*b*tau[3]==R0,'complete tau total')
 laws={3:(F(2,3),F(2)),5:(F(4,15),F(4,3)),7:(a,F(7,5)),11:(b,F(11,9))}
 arrays={p:[F(0)]+[atom(p,*laws[p],j) for j in range(1,N+1)] for p in laws}
 center=convolution(arrays[3],arrays[5],N)
 pos7=arrays[7][:];pos7[1]=F(0)
 pos11=arrays[11][:];pos11[1]=F(0)
 blocks=(center,convolution(center,pos7,N),convolution(center,pos11,N),None)
 blocks=blocks[:3]+(convolution(blocks[1],pos11,N),)
 block_prefixes=tuple(prefixes(z) for z in blocks)
 cm=mean(3,*laws[3])*mean(5,*laws[5]);m7=mean(7,*laws[7])-(1-a);m11=mean(11,*laws[11])-(1-b)
 block_mass=(F(1),a,b,a*b);block_mean=(cm,cm*m7,cm*m11,cm*m7*m11)
 paired_mean=sum((c*m for c,m in zip(tau,block_mean)),F(0))
 check(paired_mean==F(8,3)*(R0+R7/5+R11/9+R711/45),'complete nonprobability product mean')
 count_mean=paired_mean-R0
 check(count_mean==sum((c*(mu-m) for c,mu,m in zip(tau,block_mean,block_mass)),F(0)),'count subtracts tau mass not one')
 D={q:(F(5,6) if q==7 else F(q-2,q-1)-F(2,q*(q-2))) for q in (7,11,13,17,19)}
 zeta4=D[13]*D[17]*D[19]
 oldcoef=(zeta4*(1-a)*(1-b),zeta4*(1-b),zeta4*(1-a),zeta4)
 check(all(x<=y for x,y in zip(tau,oldcoef)),'paired block coefficients improve canonical old comparison')
 canonical=[];old_exact=[]
 for row in rows:
  s=F(row['threshold'])+1; h=row['h']
  bs=[hinge(m,mu,pre,s) for m,mu,pre in zip(block_mass,block_mean,block_prefixes)]
  check(all(x>=0 for x in bs),'complete block stoploss nonnegative')
  fee=sum((c*x for c,x in zip(tau,bs)),F(0))/h
  oldfee=sum((c*x for c,x in zip(oldcoef,bs)),F(0))/h
  check(F(row['four_lower'])<=oldfee<=F(row['four_upper']),'reconstructed old full4 fee')
  check(0<=fee<=oldfee,'canonical paired improvement')
  canonical.append(fee);old_exact.append(oldfee)
 print(json.dumps({'stage':'canonical complete','rows':len(rows),'sum_paired':float(sum(canonical)),'sum_old':float(sum(old_exact)),'first_paired':float(canonical[0])}),flush=True)
 #Complete old branch census at unchanged thresholds. Scale arithmetic bounds
 #each atom and multiplicative convolution; the exact infinite mean supplies
 #the omitted positive tail, with only the negative part discretized.
 SCALE=10**90
 heads=(3,5,7,11,13,17,19,23,29,31); outside=(37,41,43,47)
 role_laws=[]
 for p in heads:
  if p in laws:k,d=laws[p]
  elif p in D:k,d=F(1,p-1),F(p,p-2)
  else:
   d={23:F(5,3),29:F(20,11),31:F(2)}[p];k=d/p
  role_laws.append((p,k,d))
 for p in outside:role_laws.append((p,F(1,10),F(p,10)))
 role_atoms=[];role_means=[]
 for p,k,d in role_laws:
  values=[F(0)]+[atom(p,k,d,j) for j in range(1,N+1)]
  check(all(v>=0 for v in values),'each role atom nonnegative')
  low=[int(v*SCALE) for v in values];high=[-((-v.numerator*SCALE)//v.denominator) for v in values]
  role_atoms.append((low,high));role_means.append(mean(p,k,d))
 def iconv(a,b,up):
  out=[0]*(N+1)
  for i in range(1,N+1):
   ai=a[i]
   if ai:
    for j in range(1,N//i+1):
     if b[j]:out[i*j]+=(ai*b[j]+(SCALE-1 if up else 0))//SCALE
  return out
 @lru_cache(None)
 def distribution(roles):
  if not roles:
   out=[0]*(N+1);out[1]=SCALE;return (out,out)
  if len(roles)==1:return role_atoms[roles[0]]
  aa=distribution(roles[:-1]);bb=role_atoms[roles[-1]]
  return iconv(aa[0],bb[0],False),iconv(aa[1],bb[1],True)
 runner_low=[F(0) for _ in rows];runner_high=[F(0) for _ in rows];runner_kind=[None for _ in rows]
 branch_count=[0 for _ in rows];branch_records=[]
 for size in range(5):
  for subset in itertools.combinations(range(10),size):
   k=4-size;roles=subset+tuple(range(10,10+k));T=tuple(heads[i] for i in subset)
   eligible=[ix for ix,row in enumerate(rows) if not k or outside[k-1]<row['owner']]
   for ix in eligible:branch_count[ix]+=1
   if T==(3,5,7,11) and k==0:continue
   aa=distribution(roles);prelo=prefixes(aa[0]);prehi=prefixes(aa[1]);mu=prod((role_means[i] for i in roles),start=F(1));factor=prod((D[q] for q in D if q not in T),start=F(1))
   max_width=F(0)
   for ix in eligible:
    row=rows[ix];s=F(row['threshold'])+1;n=s.numerator//s.denominator
    flo=factor*(mu-s+(s*prelo[0][n]-prelo[1][n])/SCALE)/row['h']
    fhi=factor*(mu-s+(s*prehi[0][n]-prehi[1][n])/SCALE)/row['h']
    check(F(0)<=flo<=fhi,'directed complete branch fee')
    check(fhi-flo<F(1,10**70),'narrow allbranch row interval')
    max_width=max(max_width,fhi-flo)
    runner_low[ix]=max(runner_low[ix],flo)
    if fhi>runner_high[ix]:runner_high[ix]=fhi;runner_kind[ix]={'head':T,'outside_count':k}
   branch_records.append({'head':T,'outside_count':k,'eligible_rows':len(eligible),'maximum_interval_width':str(max_width)})
  print(json.dumps({'stage':'branch census','head_subset_size':size,'branches_done':len(branch_records)+1}),flush=True)
 check(len(branch_records)+1==386,'complete386 padded branch census')
 check(branch_count[:5]==[210,330,375,385,386],'early owner eligibility counts')
 old3=[F(r['three_upper']) for r in rows]
 old3lo=[F(r['three_lower']) for r in rows]
 cintervals=[rounded(v) for v in canonical]
 combined_low=[max(cintervals[i][0],runner_low[i],old3lo[i]) for i in range(193)]
 combined_high=[max(cintervals[i][1],runner_high[i],old3[i]) for i in range(193)]
 checks=[]
 for i,row in enumerate(rows):
  clo,chi=cintervals[i]
  check(chi-clo<=F(1,OUTPUT_SCALE),'outward canonical row rounding')
  check(clo>runner_high[i] and clo>old3[i],'paired lower dominates every old alternative')
  check(combined_low[i]==clo and combined_high[i]==chi,'canonical row equals allbranch interval')
  check(combined_high[i]<=F(row['four_upper']),'new allbranch bound no worse than inherited4')
  checks.append({'owner':row['owner'],'h':row['h'],'cap':row['cap'],'s':str(F(row['threshold'])+1),
                'paired_lower':str(clo),'paired_upper':str(chi),'paired_decimal':float(canonical[i]),
                'old_canonical_lower':row['four_lower'],'old_canonical_upper':row['four_upper'],
                'old_noncanonical_max_lower':str(runner_low[i]),'old_noncanonical_max_upper':str(runner_high[i]),
                'maximizing_noncanonical_type':runner_kind[i],
                'saving_lower':str(F(row['four_lower'])-chi),'saving_upper':str(F(row['four_upper'])-clo)})
 check(all(v=={'head':(3,5,7,13),'outside_count':0} for v in runner_kind),'same old runner-up at all193 rows')
 alpha=F(old['projection_alpha']);gate=F(old['head_gate']);fixed=F(old['unchanged_five_parent_tail'])+F(old['unchanged_TypeI'])
 policies=[]
 for policy in old['policies']:
  tail=F(policy['arbitrary_tail']);cutoffs=[]
  for start in range(194):
   cutoff=rows[start]['owner'] if start<193 else 1253
   finite_lo=sum(old3lo[:start],F(0))+sum(combined_low[start:],F(0))
   finite_hi=sum(old3[:start],F(0))+sum(combined_high[start:],F(0))
   reserve_lo=alpha*(gate-fixed-tail-finite_hi)
   reserve_hi=alpha*(gate-fixed-tail-finite_lo)
   old_finite_lo=sum(old3lo[:start],F(0))+sum((F(v['four_lower']) for v in rows[start:]),F(0))
   old_finite_hi=sum(old3[:start],F(0))+sum((F(v['four_upper']) for v in rows[start:]),F(0))
   old_reserve_lo=alpha*(gate-fixed-tail-old_finite_hi)
   old_reserve_hi=alpha*(gate-fixed-tail-old_finite_lo)
   gain=alpha*sum((old_exact[i]-canonical[i] for i in range(start,193)),F(0))
   cutoffs.append({'cutoff':cutoff,'three_parent_rows':start,'four_parent_rows':193-start,
                   'finite_fee_lower':str(finite_lo),'finite_fee_upper':str(finite_hi),
                   'projected_reserve_lower':str(reserve_lo),'projected_reserve_upper':str(reserve_hi),
                   'projected_reserve_decimal':float(reserve_lo),
                   'old_projected_reserve_lower':str(old_reserve_lo),'old_projected_reserve_upper':str(old_reserve_hi),
                   'reserve_improvement':summary(gain)})
  positive=next(i for i,v in enumerate(cutoffs) if F(v['projected_reserve_lower'])>0)
  density=next(i for i,v in enumerate(cutoffs) if F(v['projected_reserve_lower'])>F(1,2000000))
  check(positive>0 and F(cutoffs[positive-1]['projected_reserve_upper'])<0,'strict previous positive cutoff fails')
  check(density>0 and F(cutoffs[density-1]['projected_reserve_upper'])<F(1,2000000),'strict previous density cutoff fails')
  check(cutoffs[positive]['cutoff']==policy['first_positive_cutoff'],'positive cutoff unchanged')
  check(cutoffs[density]['cutoff']==policy['first_preserving_2000000_cutoff'],'density cutoff unchanged')
  retained={0,193,positive-1,positive,density-1,density}
  retained.update(i for i,v in enumerate(cutoffs) if v['cutoff'] in (137,191))
  policies.append({'kind':policy['kind'],'final_switch_power':policy['K'],'unchanged_arbitrary_tail':str(tail),
                   'first_positive_cutoff':cutoffs[positive]['cutoff'],'first_density_2000000_cutoff':cutoffs[density]['cutoff'],
                   'computed_cutoff_count':len(cutoffs),'all_cutoffs_sha256':digest(cutoffs),
                   'decisive_cutoffs':[cutoffs[i] for i in sorted(retained)]})
 result={'schema':'paired-owner-fixed-row-certificate-v1','status':'PASS','new_lean_verification':False,'input_sha256':PINS,
         'program_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'matching_unary_masses':{str(q):str(D[q]) for q in D},
         'matching_edge_formula':'1/[q(q-2)(s-1)]+1/[(q-1)s(s-2)]',
         'paired_response_constants':list(map(str,(R0,R7,R11,R711))),'tau_block_coefficients':list(map(str,tau)),
         'complete_tau_mass':str(R0),'complete_product_mean':str(paired_mean),'complete_count_mean':str(count_mean),'threshold_shift':'s=t+1; product mean subtracts s times tau mass','finite_negative_part_endpoint':N,
         'canonical_total':summary(sum(canonical,F(0))),'old_four_total':summary(sum(old_exact,F(0))),
         'allbranch_upper_total':summary(sum(combined_high,F(0))),
         'canonical_dominates_noncanonical_rows':193,
         'noncanonical_dominates_canonical_rows':0,
         'exact_canonical_row_fees_sha256':digest([str(v) for v in canonical]),
         'head_gate':old['head_gate'],'projection_alpha':old['projection_alpha'],
         'unchanged_five_parent_tail':old['unchanged_five_parent_tail'],'unchanged_TypeI':old['unchanged_TypeI'],
         'unchanged_Euler_counts':source657['Euler_counts'],
         'output_rounding_scale':str(OUTPUT_SCALE),
         'rows':checks,'branch_census':branch_records,'branch_counts':branch_count,'policies':policies,
         'all326_Euler_factors_changed':False,'actual_rows_reoptimized':False,'directed_scale':str(SCALE),
         'checks':COUNTS,'check_count':sum(COUNTS.values()),
         'scope':'Canonical paired fee uses verified arbitrary-phase measure-domination theorem with uniform678 response constants. Only canonical parents3,5,7,11 receive it. The remaining385 of386 padded branch types retain old655 product/omitted-mass bounds and original order-dependent outside envelopes; lower parent counts additionally covered by inherited3-parent bound. Fixed193 rows,h,caps,ordinary domains,Euler factors,5-parent tail and both arbitrary-parent tails remain attached to one source. Numerical allbranch maxima require the named existing source/branch interface; no unrestricted Erdős7 conclusion.'}
 output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','checks':result['check_count'],'canonical_total':float(sum(canonical)),'allbranch_total':float(sum(combined_high)),
                    'canonical_dominates_rows':result['canonical_dominates_noncanonical_rows'],'noncanonical_dominates_rows':result['noncanonical_dominates_canonical_rows'],
                    'policies':[(p['kind'],p['first_positive_cutoff'],p['first_density_2000000_cutoff']) for p in policies],'output':str(output)},indent=2))
if __name__=='__main__':main()
