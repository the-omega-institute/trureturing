#!/usr/bin/env python3
"""Complete five-parent moment and finite-prime tail on unchanged actual rows.

Ordinary exact arithmetic; source and tail inequalities are proved separately.
All 638 padded parent types and all exponent heights are retained. Finite owner
rows, all 326 Euler factors, Type I and both arbitrary-parent tails are unchanged.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from math import prod,comb,isqrt
import argparse,hashlib,itertools,json,sys
sys.set_int_max_str_digits(0)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
PINS={
 'paired_five_owner_fixed_rows_certificate.json':'aef68901053153b6c6090063572b9d1e59d8c82ce5bbc5e9b8a1533f8b2bcb5e',
 'paired_owner_fixed_rows_certificate.json':'c8a317de0b4a2e96e75811664615d2af9f473fc2b463f46d4af993b1a49adab6',
 'four_parent_tail_fixed_schedule.json':'fa79d1c28aea101da734ac687fe9ddb6e39bc6bd212a206183e049d1e929f758',
 'ordinary_domain_five_parent_certificate.json':'e46183469f280d262da37a9c33005e724690fc20b0106202c42c9913ed8d8ec0',
}
CHECKS={}
def ck(name,value):
 CHECKS[name]=CHECKS.get(name,0)+1
 if not value:raise ArithmeticError(name)
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
SCALE=10**90
def roundpair(lo,hi):
 return (F(lo.numerator*SCALE//lo.denominator,SCALE),F(-((-hi.numerator*SCALE)//hi.denominator),SCALE))
def interval_range(lo,hi):
 a,b=roundpair(lo,hi)
 return {'lower':str(a),'upper':str(b),'decimal_lower':float(lo),'decimal_upper':float(hi)}
def interval(x):
 scale=SCALE
 return {'lower':str(F(x.numerator*scale//x.denominator,scale)),
         'upper':str(F(-((-x.numerator*scale)//x.denominator),scale)),'decimal':float(x)}
data={}
for n,sha in PINS.items():
 raw=(args.directory/n).read_bytes();ck('input pin',hashlib.sha256(raw).hexdigest()==sha);data[n]=json.loads(raw)
p5=data['paired_five_owner_fixed_rows_certificate.json'];p4=data['paired_owner_fixed_rows_certificate.json'];old=data['four_parent_tail_fixed_schedule.json'];s657=data['ordinary_domain_five_parent_certificate.json'];rows=old['rows']
ck('same193 owner rows',len(rows)==193 and all(a['owner']==b['owner']==c['owner'] for a,b,c in zip(rows,p4['rows'],p5['rows'])))
for a,b,c,d in zip(rows,p4['rows'],p5['rows'],s657['finite_rows']):
 ck('finite h cap unchanged',a['h']==b['h']==c['h']==d['h'] and a['cap']==b['cap']==c['cap']==d['cap'])
 ck('finite history cap below one tenth',F(a['cap'])/a['owner']<F(1,10))
ck('all326 Euler counts unchanged',p5['unchanged_Euler_counts']==p4['unchanged_Euler_counts']==s657['Euler_counts']=={'head':10,'finite':193,'half':123})
ck('same original W5 and TypeI',p5['unchanged_five_parent_tail']==p4['unchanged_five_parent_tail']==old['unchanged_five_parent_tail']==s657['complete_five_parent_tail'] and p5['unchanged_TypeI']==old['unchanged_TypeI']=='1/65536')
Q=(7,11,13,17,19)
D={q:(F(5,6) if q==7 else F(q-2,q-1)-F(2,q*(q-2))) for q in Q}
@lru_cache(None)
def matching(V):
 if not V:return F(1)
 p=V[0];rest=V[1:]
 return D[p]*matching(rest)-sum((F(1,p*(p-2)*(q-1))+F(1,(p-1)*q*(q-2)))*matching(tuple(r for r in rest if r!=q)) for q in rest)
supports=((13,),(7,13),(11,13),(7,11,13));R=tuple(matching(tuple(q for q in Q if q not in T)) for T in supports)
ck('same enlarged-support responses',list(map(str,R))==p5['paired_response_constants'])
a,b=F(1,6),F(1,10);tau=(R[0]-a*R[1]-b*R[2]+a*b*R[3],R[1]-b*R[3],R[2]-a*R[3],R[3])
ck('same positive paired measure',all(c>0 for c in tau) and list(map(str,tau))==p5['tau_block_coefficients'])
# u(1)=k, u(e)=d*p^(-e) for e>=2. All moments below are COMPLETE
# geometric sums; no coordinate depth or product cutoff appears.
def moments(p,k,d):
 q=F(1,p);geom=[1/(1-q)]
 for r in range(1,7):geom.append(q/(1-q)*sum(comb(r,j)*geom[j] for j in range(r)))
 out=[F(1)]
 for r in range(1,8):
  delta=2**r-1
  out.append(1+k*delta+d*(sum(comb(r,j)*geom[j] for j in range(r))-1-q*delta))
 ck('complete role mean',out[1]==1+k+d/F(p*(p-1)))
 ck('positive role moments',all(x>0 for x in out) and all(out[j]<=out[j+1] for j in range(7)))
 return out
heads=(3,5,7,11,13,17,19,23,29,31);outside=(37,41,43,47,53)
laws={3:(F(2,3),F(2)),5:(F(4,15),F(4,3))}
for p in Q:laws[p]=(F(1,p-1),F(p,p-2))
for p,d in ((23,F(5,3)),(29,F(20,11)),(31,F(2))):laws[p]=(d/p,d)
for p in outside:laws[p]=(F(1,10),F(p,10))
M={p:moments(p,*laws[p]) for p in heads+outside}
for p,(k,d) in laws.items():ck('legal decreasing depth caps',0<d/F(p*p)<=k<1)
positive7=[m-(1-a) for m in M[7]];positive11=[m-(1-b) for m in M[11]]
paired_product_moments=[]
for j in range(8):
 pair=tau[0]+tau[1]*positive7[j]+tau[2]*positive11[j]+tau[3]*positive7[j]*positive11[j]
 paired_product_moments.append(M[3][j]*M[5][j]*M[13][j]*pair)
ck('paired mass and first moment',str(paired_product_moments[0])==p5['complete_tau_mass'] and str(paired_product_moments[1])==p5['complete_product_mean'])
ck('paired count mean',str(paired_product_moments[1]-paired_product_moments[0])==p5['complete_count_mean'])
def count7(product_moments):return sum((-1)**(7-j)*comb(7,j)*product_moments[j] for j in range(8))
newM7=count7(paired_product_moments);ck('positive paired count seventh moment',newM7>0)
canonical=(3,5,7,11,13);zeta=D[17]*D[19]
oldcanonical=zeta*count7([prod(M[p][j] for p in canonical) for j in range(8)])
ck('paired improves old canonical full moment',newM7<oldcanonical)
branches=[];runner=F(0);runner_type=None
for size in range(6):
 for T in itertools.combinations(heads,size):
  k=5-size;roles=T+outside[:k];factor=prod(D[q] for q in Q if q not in T)
  oldmoment=factor*count7([prod(M[p][j] for p in roles) for j in range(8)])
  ck('positive complete branch moment',oldmoment>0)
  if T==canonical and k==0:
   ck('old canonical census moment',oldmoment==oldcanonical);adopted=newM7;method='paired'
  else:
   adopted=oldmoment;method='old-product-omitted-mass'
   ck('paired exceeds every old noncanonical moment',newM7>oldmoment)
   if oldmoment>runner:runner=oldmoment;runner_type={'head':T,'outside_count':k}
  branches.append({'head':T,'outside_count':k,'old_count_moment7':str(oldmoment),'adopted_count_moment7':str(adopted),'method':method})
ck('all638 branch types',len(branches)==638)
ck('all637 unchanged noncanonical types',sum(r['method']=='old-product-omitted-mass' for r in branches)==637)
ck('runner type3571117',runner_type=={'head':(3,5,7,11,17),'outside_count':0})
# Reconstruct the former generic five-role moment, including its deliberately
# enlarged fifth role first cap1/10 and deep cap13/10.
generic=[M[p] for p in (3,5,7,11)]+[moments(13,F(1,10),F(13,10))]
oldgeneric=count7([prod(x[j] for x in generic) for j in range(8)])
ck('inherited generic full moment',str(oldgeneric)==s657['complete_fifth_role_count_moment7'])
# Same actual relative half-threshold rows. Only the numerical upper bound
#on their total loss changes. The finite prime window is not a cutoff on
#allowed owners; the odd-integer integral pays the entire remainder.
A7=F(2**7*6**6,7**7);ck('same sharp halfrow constant',str(A7)==s657['sharp_halfrow_constant7'])
maximizer=F(7,12);ck('sharp scalar equality',2*maximizer-1==A7*maximizer**7)
start=1253;old_denominator=6*(start-4)**6
ck('same original tail boundary',start==s657['finite_endpoint'])
ck('halfrow cap bound at left endpoint',F(2*(start-1),start*(start-3))<F(1,10))
oldW5=A7*oldgeneric/old_denominator
ck('inherited W5 reconstructed',str(oldW5)==s657['complete_five_parent_tail'])
integer_paired_W5=A7*newM7/old_denominator
END=10000
sieve=bytearray([1])*END;sieve[0]=sieve[1]=0
for p in range(2,isqrt(END-1)+1):
 if sieve[p]:
  for multiple in range(p*p,END,p):sieve[multiple]=0
primes=[p for p in range(start,END) if sieve[p]]
ck('finite prime census',len(primes)==1025 and primes[0]==1259 and primes[-1]==9973)
finite_lo=finite_hi=0;prime_terms=[]
for p in primes:
 den=(p-3)**7;lo=SCALE//den;hi=-(-SCALE//den)
 ck('directed prime term',F(lo,SCALE)<=F(1,den)<=F(hi,SCALE))
 ck('prime term rounding unit',0<=hi-lo<=1)
 finite_lo+=lo;finite_hi+=hi;prime_terms.append((p,lo,hi))
finite=(F(finite_lo,SCALE),F(finite_hi,SCALE))
ck('narrow finite sum',0<finite[1]-finite[0]<=F(len(primes),SCALE))
first_odd=END if END%2 else END+1
# For decreasing f(x)=(x-3)^(-7), each odd v contributes at most
#(1/2)*integral_(v-2)^v f(x)dx. These intervals tile from END-1.
odd_residual=F(1,12*(first_odd-5)**6)
ck('odd residual exact endpoint',first_odd==10001 and odd_residual==F(1,12*9996**6))
scalar=(finite[0]+odd_residual,finite[1]+odd_residual)
newW5=roundpair(A7*newM7*scalar[0],A7*newM7*scalar[1])
ck('strict whole tail improvement',0<newW5[0]<=newW5[1]<integer_paired_W5<oldW5)
ck('tail interval precision',newW5[1]-newW5[0]<F(1,10**72))
prime_generic=roundpair(A7*oldgeneric*scalar[0],A7*oldgeneric*scalar[1])
prime_oldcanonical=roundpair(A7*oldcanonical*scalar[0],A7*oldcanonical*scalar[1])
ck('all moment variants ordered',newW5[1]<prime_oldcanonical[0]<prime_generic[0])
alpha=F(old['projection_alpha']);gate=F(old['head_gate']);typeI=F(old['unchanged_TypeI']);target=F(1,2000000)
vs3=[(F(r['three_lower']),F(r['three_upper'])) for r in rows];vs4=[(F(r['paired_lower']),F(r['paired_upper'])) for r in p4['rows']];vs5=[(F(r['combined_lower']),F(r['combined_upper'])) for r in p5['rows']]
def prefixes(vs):return [[F(0)]+list(itertools.accumulate(v[z] for v in vs)) for z in (0,1)]
pre3,pre4,pre5=map(prefixes,(vs3,vs4,vs5))
def cutoff(i):return rows[i]['owner'] if i<193 else 1253
def reserve(i,j,tail,w5,side):
 return alpha*(gate-typeI-tail-w5[1-side]-(pre3[1-side][i]+pre4[1-side][j]-pre4[1-side][i]+pre5[1-side][193]-pre5[1-side][j]))
policies=[]
for pp,prior in zip(old['policies'],p5['policies']):
 ck('same inherited arbitrary policy',pp['kind']==prior['kind'] and F(pp['arbitrary_tail'])==F(prior['unchanged_arbitrary_tail']) and pp['K']==prior['final_switch_power'])
 tail=F(pp['arbitrary_tail']);fixed_four=137 if pp['kind']=='RS' else 191;i_fixed=next(i for i,r in enumerate(rows) if r['owner']==fixed_four)
 pairs=hashlib.sha256();count=0;frontier=[]
 for i in range(194):
  first=None;prev=None
  for j in range(i,194):
   lo,hi=reserve(i,j,tail,newW5,0),reserve(i,j,tail,newW5,1)
   ck('allpair rational enclosure',lo<=hi)
   ck('allpair density separated',lo>target or hi<target)
   ck('allpair positivity separated',lo>0 or hi<0)
   if prev is not None:ck('fixed-four later-five monotonicity',prev[1]<lo)
   if first is None and lo>target:
    first={'four_cutoff':cutoff(i),'five_cutoff':cutoff(j),'reserve_lower':str(lo),'reserve_upper':str(hi),'decimal':float(lo),
           'previous_five_cutoff':cutoff(j-1) if j>i else None,'previous_reserve_upper':str(prev[1]) if prev else None}
   prev=(lo,hi);pairs.update((str(i)+':'+str(j)+':'+str(lo)+':'+str(hi)+'\n').encode());count+=1
  if first is not None:frontier.append(first)
 ck('all18915 cutoff pairs',count==18915)
 pareto=[];last=1254
 for v in frontier:
  if v['five_cutoff']<last:pareto.append(v);last=v['five_cutoff']
 chosen=next(v for v in frontier if v['four_cutoff']==fixed_four);j=next(i for i,r in enumerate(rows) if r['owner']==chosen['five_cutoff'])
 ck('new paying five cutoff',chosen['five_cutoff']==(373 if pp['kind']=='RS' else 443))
 ck('previous five cutoff misses target',F(chosen['previous_reserve_upper'])<target)
 oldj=next(j for j in range(i_fixed,194) if reserve(i_fixed,j,tail,(oldW5,oldW5),0)>target)
 ck('old tail policy reproduces684 cutoff',cutoff(oldj)==prior['fixed_four_policy']['five_cutoff'])
 ck('old tail policy reproduces684 endpoint',str(reserve(i_fixed,oldj,tail,(oldW5,oldW5),0))==prior['fixed_four_policy']['reserve_lower'])
 ck('new cutoff failed with old tail',reserve(i_fixed,j,tail,(oldW5,oldW5),1)<target)
 direct=[]
 for tg in (F(0),target):
  ii=next(i for i in range(194) if reserve(i,i,tail,newW5,0)>tg)
  ck('direct previous cutoff fails',reserve(ii-1,ii-1,tail,newW5,1)<tg)
  direct.append({'target':str(tg),'cutoff':cutoff(ii),'reserve_lower':str(reserve(ii,ii,tail,newW5,0)),
                 'reserve_upper':str(reserve(ii,ii,tail,newW5,1)),'decimal':float(reserve(ii,ii,tail,newW5,0)),
                 'previous_cutoff':cutoff(ii-1),'previous_upper':str(reserve(ii-1,ii-1,tail,newW5,1))})
 attribution=[]
 for label,w in (('inherited_generic_integer_tail',(oldW5,oldW5)),('paired_integer_tail',(integer_paired_W5,integer_paired_W5)),
                 ('old_generic_prime_tail',prime_generic),('old_canonical_prime_tail',prime_oldcanonical),('paired_prime_tail',newW5)):
  jj=next(jj for jj in range(i_fixed,194) if reserve(i_fixed,jj,tail,w,0)>target)
  ck('attribution preceding cutoff fails',reserve(i_fixed,jj-1,tail,w,1)<target)
  attribution.append({'comparison':label,'five_cutoff':cutoff(jj),'tail_lower':str(w[0]),'tail_upper':str(w[1]),
                      'reserve_lower':str(reserve(i_fixed,jj,tail,w,0)),'reserve_upper':str(reserve(i_fixed,jj,tail,w,1)),
                      'decimal':float(reserve(i_fixed,jj,tail,w,0)),'previous_five_cutoff':cutoff(jj-1),
                      'previous_reserve_upper':str(reserve(i_fixed,jj-1,tail,w,1))})
 ck('prime scalar alone already gives final cutoffs',attribution[2]['five_cutoff']==attribution[4]['five_cutoff'])
 # Even deleting the entire residual above10000 from this comparison cannot
 #make the preceding fixed-row cutoff meet the target. This only concerns
 #further scalar-tail refinement, not other estimates or the actual problem.
 prefix_fee_lower=A7*newM7*finite[0]
 ceiling=reserve(i_fixed,j-1,tail,(prefix_fee_lower,prefix_fee_lower),1)
 ck('preceding cutoff still fails with zero residual',ceiling<target)
 policies.append({'kind':pp['kind'],'final_switch_power':pp['K'],'unchanged_arbitrary_tail':str(tail),
                  'fixed_four_policy':chosen,'finite_row_counts':{'three':i_fixed,'four':j-i_fixed,'five':193-j},
                  'old_five_cutoff':cutoff(oldj),'old_tail_reserve_at_new_cutoff_upper':str(reserve(i_fixed,j,tail,(oldW5,oldW5),1)),
                  'attribution':attribution,'preceding_cutoff_zero_residual_reserve_upper':str(ceiling),
                  'direct_three_to_five':direct,'density_pareto_frontier':pareto,'all_cutoff_pair_count':count,
                  'all_cutoff_pairs_sha256':pairs.hexdigest()})
result={'schema':'paired-five-owner-prime-tail-certificate-v1','status':'PASS','new_lean_verification':False,
 'scope':'Ordinary complete-moment certificate conditional on the same678 source, measurable retained13 paired theorem, all-height numerical-label completion, inherited655 branch and half-row arguments, and666/684 ordinary/private/network assumptions. Canonical3,5,7,11,13 paired seventh moment exceeds all637 old noncanonical moments; all638 padded branches are covered. Actual half-row caps2(v-1)/(v-3), denominator(v-3)^7, finite193 h/caps, Euler326 and arbitrary-parent tails remain unchanged. Full five-parent tail uses all1025 actual primes in1253<=v<10000 and a complete odd-integer integral remainder from10001. The reported scalar interval encloses the finite prime sum plus that upper remainder; it is not an equality for the actual infinite prime sum. No unrestricted Erdos7 conclusion.',
 'input_sha256':PINS,'program_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'paired_response_constants':list(map(str,R)),'tau_block_coefficients':list(map(str,tau)),
 'coordinate_laws':{str(p):{'first_cap':str(k),'deep_multiplier':str(d),'moments0to7':list(map(str,M[p]))} for p,(k,d) in laws.items()},
 'paired_product_moments0to7':list(map(str,paired_product_moments)),
 'paired_count_moment7':str(newM7),'old_canonical_count_moment7':str(oldcanonical),
 'old_noncanonical_max_count_moment7':str(runner),'old_noncanonical_max_type':runner_type,
 'old_generic_count_moment7':str(oldgeneric),'allbranch_count_moment7':str(newM7),'branch_census':branches,
 'all638_branch_moments_sha256':digest(branches),'tail_start':start,
 'prime_window_end_exclusive':END,'finite_prime_count':len(primes),'finite_prime_values':primes,
 'prime_rounding_scale':str(SCALE),'finite_prime_terms_sha256':digest(prime_terms),
 'finite_prime_scalar_lower':str(finite[0]),'finite_prime_scalar_upper':str(finite[1]),
 'odd_remainder_first_integer':first_odd,'odd_remainder_scalar_upper':str(odd_residual),
 'complete_scalar_upper_expression_lower':str(scalar[0]),'complete_scalar_upper_expression_upper':str(scalar[1]),
 'actual_tail_row':'N=0 relative half threshold; c_v=2(v-1)/(v-3)',
 'owner_tail_fee':'A7*M7/(v-3)^7','sharp_halfrow_constant7':str(A7),
 'old_complete_five_parent_tail':str(oldW5),'paired_integer_tail_baseline':str(integer_paired_W5),
 'new_complete_five_parent_tail_lower':str(newW5[0]),'new_complete_five_parent_tail_upper':str(newW5[1]),
 'new_tail_interval_meaning':'Interval encloses A7*M7*(finite exact prime scalar sum + complete odd integral upper remainder), not the unknown actual infinite prime fee.',
 'tail_saving':interval_range(oldW5-newW5[1],oldW5-newW5[0]),
 'fractional_tail_reduction':interval_range((oldW5-newW5[1])/oldW5,(oldW5-newW5[0])/oldW5),
 'constant_projected_reserve_gain':interval_range(alpha*(oldW5-newW5[1]),alpha*(oldW5-newW5[0])),
 'head_gate':str(gate),'projection_alpha':str(alpha),'unchanged_TypeI':str(typeI),
 'unchanged_Euler_counts':s657['Euler_counts'],'finite_row_count':193,'actual_rows_reoptimized':False,
 'all326_Euler_factors_changed':False,'policies':policies,'checks':CHECKS,'check_count':sum(CHECKS.values())}
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'check_count':result['check_count'],'new_tail_upper':float(newW5[1]),'old_tail':float(oldW5),
 'fractional_reduction':float((oldW5-newW5[1])/oldW5),'projected_gain':float(alpha*(oldW5-newW5[1])),
 'policies':[{'kind':p['kind'],'four':p['fixed_four_policy']['four_cutoff'],'five':p['fixed_four_policy']['five_cutoff'],
 'reserve':p['fixed_four_policy']['decimal']} for p in policies],'output':str(output)},indent=2))
