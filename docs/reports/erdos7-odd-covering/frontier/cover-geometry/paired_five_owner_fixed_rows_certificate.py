#!/usr/bin/env python3
"""Paired five-parent fees on the unchanged 193 rows, with all 638 branches.

Ordinary arithmetic certificate; no Lean or optimizer. The same 678 source
measure bridge is supplied separately. Positive tails are complete. Only the
canonical branch gets the paired bound; all other 637 keep inherited bounds.
Every complete policy retains the original five-parent and arbitrary tails.
"""
from fractions import Fraction as F
from pathlib import Path
from math import prod,comb
from functools import lru_cache
import argparse,hashlib,itertools,json,sys
sys.set_int_max_str_digits(0)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path)
args=parser.parse_args();ROOT=args.directory
PINS={
 'four_parent_tail_fixed_schedule.json':'fa79d1c28aea101da734ac687fe9ddb6e39bc6bd212a206183e049d1e929f758',
 'ordinary_domain_five_parent_certificate.json':'e46183469f280d262da37a9c33005e724690fc20b0106202c42c9913ed8d8ec0',
 'paired_owner_fixed_rows_certificate.json':'c8a317de0b4a2e96e75811664615d2af9f473fc2b463f46d4af993b1a49adab6',
}
SCALE=10**90
checks={}
def ck(name,b):
 checks[name]=checks.get(name,0)+1
 if not b:raise ArithmeticError(name)
def rd(x):return F(x.numerator*SCALE//x.denominator,SCALE),F(-((-x.numerator*SCALE)//x.denominator),SCALE)
def sm(x):return {'lower':str(rd(x)[0]),'upper':str(rd(x)[1]),'decimal':float(x)}
def atom(p,k,d,j):
 if j==1:return 1-k
 if j==2:return k-d/F(p*p)
 return d*(p-1)/p**j
def mean(p,k,d):return 1+k+d/F(p*(p-1))
def conv(a,b,N):
 out=[F(0)]*(N+1)
 for i in range(1,N+1):
  if a[i]:
   for j in range(1,N//i+1):
    if b[j]:out[i*j]+=a[i]*b[j]
 return out
def prefixes(a):
 mass=[a[0]];mom=[a[0]]
 for j,v in enumerate(a[1:],1):mass.append(mass[-1]+v);mom.append(mom[-1]+j*v)
 return mass,mom
def hinge(m,mu,pre,s):
 n=s.numerator//s.denominator
 return mu-s*m+s*pre[0][n]-pre[1][n]
pins={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in PINS}
for n in PINS:ck('input pin',pins[n]==PINS[n])
old=json.loads((ROOT/'four_parent_tail_fixed_schedule.json').read_text());rows=old['rows'];new4=json.loads((ROOT/'paired_owner_fixed_rows_certificate.json').read_text());source657=json.loads((ROOT/'ordinary_domain_five_parent_certificate.json').read_text())
ck('193 unchanged rows',len(rows)==193)
ck('four row identity',all(a['owner']==b['owner'] and a['h']==b['h'] and a['cap']==b['cap'] for a,b in zip(rows,new4['rows'])))
primes=[v for v in range(37,1253) if all(v%d for d in range(2,int(v**.5)+1))]
ck('complete prime window',primes==[r['owner'] for r in rows])
map657={r['owner']:r for r in source657['finite_rows']}
for row in rows:
 r=map657[row['owner']];v=row['owner'];h=row['h']
 ck('unchanged inherited h cap',h==r['h'] and row['cap']==r['cap'])
 ck('actual cap invariant',F(row['cap'])==F(v-1,h) and F(row['cap'])/v<F(1,10))
 ck('actual rational threshold',F(row['threshold'])==v-2-F(1,65536)-h)
ck('inherited Euler tail inputs',old['unchanged_five_parent_tail']==source657['complete_five_parent_tail'] and old['unchanged_TypeI']==source657['ordinary_typeI_fee'])
N=max((F(r['threshold'])+1).__ceil__() for r in rows);ck('1080 negative endpoint',N==1080)
Q=(7,11,13,17,19);D={q:(F(5,6) if q==7 else F(q-2,q-1)-F(2,q*(q-2))) for q in Q}
@lru_cache(None)
def match(V):
 if not V:return F(1)
 v=V[0];R=V[1:]
 return D[v]*match(R)-sum((F(1,v*(v-2)*(q-1))+F(1,(v-1)*q*(q-2)))*match(tuple(u for u in R if u!=q)) for q in R)
R=tuple(match(tuple(q for q in Q if q not in T)) for T in ((13,),(7,13),(11,13),(7,11,13)))
ck('matching constants',R==tuple(map(F,('621424177961/986324169600','5990546387/7827969600','1199347867/1660478400','20681057/23721120'))))
a,b=F(1,6),F(1,10);tau=(R[0]-a*R[1]-b*R[2]+a*b*R[3],R[1]-b*R[3],R[2]-a*R[3],R[3]);ck('positive tau',all(x>0 for x in tau))
laws={3:(F(2,3),F(2)),5:(F(4,15),F(4,3)),7:(a,F(7,5)),11:(b,F(11,9)),13:(F(1,12),F(13,11))}
arr={p:[F(0)]+[atom(p,*laws[p],j) for j in range(1,N+1)] for p in laws}
base=conv(conv(arr[3],arr[5],N),arr[13],N);pos7=arr[7][:];pos7[1]=F(0);pos11=arr[11][:];pos11[1]=F(0)
blocks=[base,conv(base,pos7,N),conv(base,pos11,N)];blocks.append(conv(blocks[1],pos11,N));pres=[prefixes(x) for x in blocks]
base_mean=prod(mean(p,*laws[p]) for p in (3,5,13));posmean7=mean(7,*laws[7])-(1-a);posmean11=mean(11,*laws[11])-(1-b)
bmass=(F(1),a,b,a*b);bmean=(base_mean,base_mean*posmean7,base_mean*posmean11,base_mean*posmean7*posmean11)
mu=sum(c*m for c,m in zip(tau,bmean));ck('mass R0',sum(c*m for c,m in zip(tau,bmass))==R[0])
zeta=D[17]*D[19];oldcoeff=(zeta*(1-a)*(1-b),zeta*(1-b),zeta*(1-a),zeta);ck('blockwise improvement',all(x<y for x,y in zip(tau,oldcoeff)))
canon=[];oldcanon=[]
for r in rows:
 s=F(r['threshold'])+1;hs=[hinge(m,v,p,s) for m,v,p in zip(bmass,bmean,pres)]
 ck('all block hinge nonnegative',all(v>=0 for v in hs));c=sum(x*y for x,y in zip(tau,hs))/r['h'];o=sum(x*y for x,y in zip(oldcoeff,hs))/r['h'];ck('strict canonical improvement',0<c<o);canon.append(c);oldcanon.append(o)
print(json.dumps({'stage':'canonical','sum_new':float(sum(canon)),'sum_old':float(sum(oldcanon)),'first_new':float(canon[0])}),flush=True)
heads=(3,5,7,11,13,17,19,23,29,31);outside=(37,41,43,47,53);rlaws=[]
for p in heads:
 if p in laws:k,d=laws[p]
 elif p in D:k,d=F(1,p-1),F(p,p-2)
 else:d={23:F(5,3),29:F(20,11),31:F(2)}[p];k=d/p
 rlaws.append((p,k,d))
for p in outside:rlaws.append((p,F(1,10),F(p,10)))
rarr=[];rmeans=[]
for p,k,d in rlaws:
 vs=[F(0)]+[atom(p,k,d,j) for j in range(1,N+1)];ck('all atoms positive',all(v>=0 for v in vs));rarr.append(([int(v*SCALE) for v in vs],[-((-v.numerator*SCALE)//v.denominator) for v in vs]));rmeans.append(mean(p,k,d))
def iconv(a,b,up):
 out=[0]*(N+1)
 for i in range(1,N+1):
  if a[i]:
   for j in range(1,N//i+1):
    if b[j]:out[i*j]+=(a[i]*b[j]+(SCALE-1 if up else 0))//SCALE
 return out
@lru_cache(None)
def dist(rs):
 if len(rs)==1:return rarr[rs[0]]
 aa=dist(rs[:-1]);bb=rarr[rs[-1]]
 return iconv(aa[0],bb[0],False),iconv(aa[1],bb[1],True)
rlo=[F(0)]*193;rhi=[F(0)]*193;rkind=[None]*193;counts=[0]*193;brecs=[]
for size in range(6):
 for ss in itertools.combinations(range(10),size):
  k=5-size;roles=ss+tuple(range(10,10+k));T=tuple(heads[i] for i in ss);eligible=[i for i,r in enumerate(rows) if not k or outside[k-1]<r['owner']]
  for i in eligible:counts[i]+=1
  if T==(3,5,7,11,13) and k==0:continue
  aa=dist(roles);pl=prefixes(aa[0]);ph=prefixes(aa[1]);mn=prod(rmeans[i] for i in roles);fac=prod(D[q] for q in Q if q not in T)
  width=F(0)
  for i in eligible:
   r=rows[i];s=F(r['threshold'])+1;n=s.numerator//s.denominator
   lo=fac*(mn-s+(s*pl[0][n]-pl[1][n])/SCALE)/r['h'];hi=fac*(mn-s+(s*ph[0][n]-ph[1][n])/SCALE)/r['h'];ck('directed full hinge',0<lo<=hi);ck('narrow interval',hi-lo<F(1,10**70));width=max(width,hi-lo);rlo[i]=max(rlo[i],lo)
   if hi>rhi[i]:rhi[i]=hi;rkind[i]={'head':T,'outside_count':k}
  brecs.append({'head':T,'outside_count':k,'eligible_rows':len(eligible),'max_width':str(width)})
 print(json.dumps({'stage':'census','size':size,'done':len(brecs)+1}),flush=True)
ck('638 branch census',len(brecs)+1==638)
ck('early owner eligibility',counts[:6]==[252,462,582,627,637,638])
ci=[rd(x) for x in canon];combined=[(max(ci[i][0],rlo[i]),max(ci[i][1],rhi[i])) for i in range(193)]
for i,r in enumerate(rows):ck('new five no greater old five',combined[i][1]<=oldcanon[i]);ck('five above four',combined[i][0]>F(new4['rows'][i]['paired_upper']))
alpha=F(old['projection_alpha']);gate=F(old['head_gate']);fixed=F(old['unchanged_five_parent_tail'])+F(old['unchanged_TypeI']);v3=[(F(r['three_lower']),F(r['three_upper'])) for r in rows];v4=[(F(r['paired_lower']),F(r['paired_upper'])) for r in new4['rows']]
def pfx(vs,side):return [F(0)]+list(itertools.accumulate(v[side] for v in vs))
p3=[pfx(v3,z) for z in (0,1)];p4=[pfx(v4,z) for z in (0,1)];p5=[pfx(combined,z) for z in (0,1)]
def cutoff(i):return rows[i]['owner'] if i<193 else 1253
def reserve(i,j,tail,side):return alpha*(gate-fixed-tail-(p3[1-side][i]+p4[1-side][j]-p4[1-side][i]+p5[1-side][193]-p5[1-side][j]))
# All 18,915 ordered cutoff pairs per complete policy are decided by
# rational intervals. Displayed decimals never participate in a comparison.
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
old5=[rd(x) for x in oldcanon];pold5=[pfx(old5,z) for z in (0,1)]
legacy4=[(F(r['four_lower']),F(r['four_upper'])) for r in rows];plegacy4=[pfx(legacy4,z) for z in (0,1)]
for i,row in enumerate(rows):
 if row['owner']>=67:
  inherited=map657[row['owner']]
  ck('old complete five fee reconstruction',F(inherited['fee_lower'])<=oldcanon[i]<=F(inherited['fee_upper']))
ck('exception only owner41',[rows[i]['owner'] for i in range(193) if rlo[i]>ci[i][1]]==[41])
ck('all remaining canonical dominant',all(ci[i][0]>rhi[i] for i in range(193) if rows[i]['owner']!=41))
ck('exception41 outside37',rkind[1]=={'head':(3,5,7,11),'outside_count':1})
pol=[]
for pp in old['policies']:
 tail=F(pp['arbitrary_tail']);target=F(1,2000000);frontier=[];allhash=hashlib.sha256();evaluated=0
 for i in range(194):
  first=None;prior=None
  for j in range(i,194):
   lo,hi=reserve(i,j,tail,0),reserve(i,j,tail,1)
   ck('cutoff reserve enclosure',lo<=hi)
   ck('cutoff density decision separated',lo>target or hi<target)
   ck('cutoff positivity decision separated',lo>0 or hi<0)
   if prior is not None:ck('five cutoff reserve increases',prior[1]<lo)
   if first is None and lo>target:
    first={'four_cutoff':cutoff(i),'five_cutoff':cutoff(j),'reserve_lower':str(lo),'reserve_upper':str(hi),'decimal':float(lo),
           'previous_five_cutoff':cutoff(j-1) if j>i else None,'previous_reserve_upper':str(prior[1]) if prior else None}
   prior=(lo,hi);allhash.update((str(i)+':'+str(j)+':'+str(lo)+':'+str(hi)+'\n').encode());evaluated+=1
  if first is not None:frontier.append(first)
 ck('complete ordered cutoff count',evaluated==18915)
 # Keep only undominated cutoff pairs: earlier releases permit more parents.
 pareto=[];last_five=1254
 for v in frontier:
  if v['five_cutoff']<last_five:pareto.append(v);last_five=v['five_cutoff']
 fixedfour=137 if pp['kind']=='RS' else 191
 chosen=next(v for v in frontier if v['four_cutoff']==fixedfour)
 ck('retained first five cutoff',chosen['five_cutoff']==(397 if pp['kind']=='RS' else 587))
 ck('retained prior five cutoff fails',F(chosen['previous_reserve_upper'])<target)
 direct=[]
 for tg in (F(0),target):
  j=next(j for j in range(194) if reserve(j,j,tail,0)>tg)
  ck('direct prior cutoff fails',reserve(j-1,j-1,tail,1)<tg)
  direct.append({'target':str(tg),'cutoff':cutoff(j),'reserve_lower':str(reserve(j,j,tail,0)),'reserve_upper':str(reserve(j,j,tail,1)),
                 'decimal':float(reserve(j,j,tail,0)),'previous_cutoff':cutoff(j-1),'previous_upper':str(reserve(j-1,j-1,tail,1))})
 # Attribute changes separately: 683's four-parent gain already reaches
 #397/587 with the inherited five-parent fees. New paired five fees improve
 #reserves but do not advance these cutoffs while the old tail is retained.
 i=next(i for i,r in enumerate(rows) if r['owner']==fixedfour);comparisons=[]
 for label,pfour,pfive in (('legacy666_four_and655_five',plegacy4,pold5),('baseline683_four_and655_five',p4,pold5),('paired_four_andfive',p4,p5)):
  def rr(j,side):return alpha*(gate-fixed-tail-(p3[1-side][i]+pfour[1-side][j]-pfour[1-side][i]+pfive[1-side][193]-pfive[1-side][j]))
  j=next(j for j in range(i,194) if rr(j,0)>target)
  ck('baseline cutoff separation',rr(j-1,1)<target)
  comparisons.append({'comparison':label,'four_cutoff':fixedfour,'five_cutoff':cutoff(j),'reserve_lower':str(rr(j,0)),
                      'reserve_upper':str(rr(j,1)),'decimal':float(rr(j,0)),'previous_five_cutoff':cutoff(j-1),'previous_reserve_upper':str(rr(j-1,1))})
 ck('new five cutoff same as683 baseline',comparisons[1]['five_cutoff']==comparisons[2]['five_cutoff'])
 pol.append({'kind':pp['kind'],'final_switch_power':pp['K'],'unchanged_arbitrary_tail':str(tail),'fixed_four_policy':chosen,
             'direct_three_to_five':direct,'density_pareto_frontier':pareto,'all_cutoff_pair_count':evaluated,
             'all_cutoff_pairs_sha256':allhash.hexdigest(),'baseline_policy_comparison':comparisons})
result={'schema':'paired-five-owner-fixed-row-certificate-v1','status':'PASS','new_lean_verification':False,
 'scope':'Conditional on the actual678 matching source measurable-marginal domination and inherited666 ordinary/private/network interface. Only canonical3,5,7,11,13 uses the paired theorem. All other637 of638 padded five-parent types retain655 product and omitted-mass bounds, with early-owner eligibility. The universal fee is their maximum: owner41 uses old outside37; all other192 use paired canonical. All193 h/caps, all326 Euler factors, complete five-parent tail, TypeI fee and arbitrary-parent tails stay unchanged. No unrestricted Erdos7 conclusion.',
 'input_sha256':pins,'program_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'matching_unary_masses':{str(q):str(D[q]) for q in Q},'paired_response_constants':list(map(str,R)),
 'response_supports':[[13],[7,13],[11,13],[7,11,13]],'tau_block_coefficients':list(map(str,tau)),
 'complete_tau_mass':str(R[0]),'complete_product_mean':str(mu),'complete_count_mean':str(mu-R[0]),
 'old_five_omitted_factor':str(zeta),'old_five_unweighted_product_mean':str(prod(mean(p,*laws[p]) for p in laws)),
 'old_five_complete_product_mean':str(zeta*prod(mean(p,*laws[p]) for p in laws)),
 'old_five_complete_count_mean':str(zeta*(prod(mean(p,*laws[p]) for p in laws)-1)),
 'threshold_shift':'s=t+1; complete hinge subtracts s times tau mass','finite_negative_part_endpoint':N,
 'canonical_total':sm(sum(canon)),'old_five_total':sm(sum(oldcanon)),'allbranch_upper_total':sm(sum(x[1] for x in combined)),
 'canonical_wins_rows':192,'noncanonical_wins_rows':1,'exceptional_owners':[41],
 'exact_canonical_row_fees_sha256':digest(list(map(str,canon))),
 'exact_old_five_row_fees_sha256':digest(list(map(str,oldcanon))),
 'head_gate':old['head_gate'],'projection_alpha':old['projection_alpha'],'unchanged_five_parent_tail':old['unchanged_five_parent_tail'],
 'unchanged_TypeI':old['unchanged_TypeI'],'unchanged_Euler_counts':source657['Euler_counts'],
 'actual_rows_reoptimized':False,'all326_Euler_factors_changed':False,'output_rounding_scale':str(SCALE),
 'branch_counts':counts,'branch_census':brecs,
 'rows':[{'owner':r['owner'],'h':r['h'],'cap':r['cap'],'threshold':r['threshold'],'s':str(F(r['threshold'])+1),
          'paired_lower':str(ci[i][0]),'paired_upper':str(ci[i][1]),'paired_decimal':float(canon[i]),
          'old_canonical_lower':str(old5[i][0]),'old_canonical_upper':str(old5[i][1]),
          'old_noncanonical_max_lower':str(rlo[i]),'old_noncanonical_max_upper':str(rhi[i]),'maximizing_noncanonical_type':rkind[i],
          'combined_lower':str(combined[i][0]),'combined_upper':str(combined[i][1])} for i,r in enumerate(rows)],
 'policies':pol,'checks':checks,'check_count':sum(checks.values())}
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'check_count':result['check_count'],'canonical_total':float(sum(canon)),
 'old_five_total':float(sum(oldcanon)),'combined_total':float(sum(x[1] for x in combined)),
 'exceptional_owners':[41],'policies':[{'kind':v['kind'],'four':v['fixed_four_policy']['four_cutoff'],
 'five':v['fixed_four_policy']['five_cutoff'],'reserve':v['fixed_four_policy']['decimal']} for v in pol],'output':str(output)},indent=2))
