#!/usr/bin/env python3
"""Exact finite data for same-source support-aware pair activation and exchanges.

No source construction or infinite-tail theorem is inferred from this table.
The ordinary proof uses all32 measurable marginal dominations on one fixed
678 source. No owner-row fees or policy cutoffs are recalculated here.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import lru_cache
from pathlib import Path
from math import prod
import argparse,hashlib,json
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path);args=parser.parse_args()
CHECKS={}
def ck(name,value):
 CHECKS[name]=CHECKS.get(name,0)+1
 if not value:raise ArithmeticError(name)
def subsets(xs):return [x for n in range(len(xs)+1) for x in combinations(xs,n)]
def digest(v):return hashlib.sha256(json.dumps(v,sort_keys=True,separators=(',',':')).encode()).hexdigest()
Q=(7,11,13,17,19)
D={q:(F(5,6) if q==7 else F(q-2,q-1)-F(2,q*(q-2))) for q in Q}
a={q:F(1,q-1) for q in Q}
def edge(q,r):return F(1,q*(q-2)*(r-1))+F(1,(q-1)*r*(r-2))
@lru_cache(None)
def H(U):
 if not U:return F(1)
 q=U[0];rest=U[1:]
 return D[q]*H(rest)-sum(edge(q,r)*H(tuple(x for x in rest if x!=r)) for r in rest)
def response(T):return H(tuple(q for q in Q if q not in T))
responses=[]
for T in subsets(Q):
 x=response(T);ck('all32 positive responses',x>0);responses.append({'queried':T,'response':str(x)})
 for q in Q:
  if q not in T:ck('queried-support monotonicity',response(T+(q,))>x)
for q,r in combinations(Q,2):
 ck('unary prime monotonicity',D[q]<D[r])
 for u in Q:
  if u not in (q,r):ck('edge prime monotonicity',edge(q,u)>edge(r,u))
 for W in subsets(tuple(p for p in Q if p not in (q,r))):
  difference=H(tuple(sorted(W+(r,))))-H(tuple(sorted(W+(q,))))
  formula=(D[r]-D[q])*H(W)+sum((edge(q,u)-edge(r,u))*H(tuple(x for x in W if x!=u)) for u in W)
  ck('exact smaller queried prime exchange',difference==formula and difference>0)
def coefficients(P,K):
 q,r=P;rs=[response(K+T) for T in ((),(q,),(r,),(q,r))]
 return (rs[3],rs[1]-a[r]*rs[3],rs[2]-a[q]*rs[3],rs[0]-a[q]*rs[1]-a[r]*rs[2]+a[q]*a[r]*rs[3])
blocks=('++','+0','0+','00');contexts=[];ratios={p:[] for p in Q};minimum=[None]*4
for P in combinations(Q,2):
 q,r=P
 for K in subsets(tuple(p for p in Q if p not in P)):
  cs=coefficients(P,K)
  for j,c in enumerate(cs):
   ck('all320 block coefficients positive',c>0)
   item=(c,P,K)
   if minimum[j] is None or item<minimum[j]:minimum[j]=item
  ck('exact pair total',cs[3]+a[q]*cs[1]+a[r]*cs[2]+a[q]*a[r]*cs[0]==response(K))
  ck('exact first pair marginal coefficient',cs[1]+a[r]*cs[0]==response(K+(q,)))
  ck('exact second pair marginal coefficient',cs[2]+a[q]*cs[0]==response(K+(r,)))
  for p in K:
   without=coefficients(P,tuple(u for u in K if u!=p))
   for j,(new,old) in enumerate(zip(without,cs)):
    ratio=new/old;lower=F(4,5) if p==7 else F(5,6)
    ck('all480 two-sided contractions',lower<=ratio<=D[p])
    ratios[p].append((ratio,P,K,blocks[j]))
  contexts.append({'pair':P,'retained':K,'coefficients_pp_p0_0p_00':list(map(str,cs))})
ck('80 contexts',len(contexts)==80)
ck('480 coefficient ratios',sum(map(len,ratios.values()))==480)
min7=min(ratios[7]);minothers=min((entry,p) for p in Q if p!=7 for entry in ratios[p])
ck('exact p7 contraction minimum',min7==(F(1915424773533541,2340864476042190),(11,13),(7,),'00'))
ck('exact pge11 contraction minimum',minothers==((F(574546060482833,661191624184410),(7,13),(11,),'00'),11))
expected_min=(F(77690927,118918800),F(17004889549,29631167280),F(175232434423,363891528000),F(84106036967663,211566534379200))
ck('exact coefficient minima',tuple(x[0] for x in minimum)==expected_min)
# Complete-law tail comparisons reduce to depth1 and2 plus the prime ratio.
def u(p,e):
 if p==3:return F(2,3**e)
 if p==5:return F(4,3*5**e)
 return F(1,p-1) if e==1 else F(1,(p-2)*p**(e-1))
def mean(p):return F(2) if p==3 else F(4,3) if p==5 else F(p-1,p-2)
for q,r in combinations(Q,2):ck('Q full-height tail starting inequalities',u(q,1)>u(r,1) and u(q,2)>u(r,2) and q<r)
for p in Q:
 ck('central3 weighted mean',F(4,5)*mean(3)>=mean(p))
 ck('central3 weighted tail starts',all(F(4,5)*u(3,e)>=u(p,e) for e in (1,2)) and 3<p)
 if p>=11:
  ck('central5 weighted mean',F(5,6)*mean(5)>=mean(p))
  ck('central5 weighted tail starts',all(F(5,6)*u(5,e)>=u(p,e) for e in (1,2)) and 5<p)
later=((23,F(5,3)),(29,F(20,11)),(31,F(2)),(37,F(37,10)))
for q in (3,5,7,11):
 for p,d in later:ck('central and activation role tail starts',u(q,1)>=d/p and u(q,2)>=d/(p*p) and q<p)
for p,d in later[:3]:ck('retained13 later-head tail starts',u(13,1)>=d/p and u(13,2)>=d/(p*p) and 13<p)
ck('outside singleton13 domination fails',u(13,1)<F(1,10))
# Counterexamples delimit what the actual theorem does NOT claim.
def pair_first(P,K):
 q,r=P
 return response(K)+response(K+(q,))/F(q-2)+response(K+(r,))/F(r-2)+response(K+P)/F((q-2)*(r-2))
canonical_first=F(8,3)*mean(13)*pair_first((7,11),(13,))
wrong_first=F(8,3)*mean(7)*pair_first((11,13),(7,))
product_gap=wrong_first-canonical_first
count_gap=wrong_first-response((7,))-(canonical_first-response((13,)))
ck('wrong pair product counterexample',product_gap==F(372464259439,2260326222000)>0)
ck('wrong pair owner-count hinge counterexample',count_gap==F(150250149338951,1410443562528000)>0)
atomgap=coefficients((7,13),())[3]-coefficients((7,11),())[3]
ck('smaller-prime exchange is not atomwise',atomgap>0)
mass=response(())
ck('canonical four marginal source inequalities',all(mass<=response(T) for T in ((),(7,),(11,),(7,11))))
source_gap=mass-response((13,))/12
ck('canonical four do not imply retained13 source',source_gap==F(270508276995713,528916335948000)>0)
ck('positive constants not ordered by unquerying',response((13,))>response(()))
ck('adaptive branch choice counterexample',1-F(1,2)**2>F(1,2))
result={'schema':'support-aware-pair-exchange-certificate-v1','status':'PASS','new_lean_verification':False,
 'scope':'Exact finite inputs for an ordinary conditional all-threshold <=4/5 parent theorem on ONE actual678 source with all32 measurable marginal dominations and fixed pure references. No source construction or193-row/policy repricing. Pair activation uses equal-mass upper-tail/supermodular order; unquerying uses genuine two-sided measure contraction. The proof chooses the two smallest selectedQ primes as protected pair; arbitrary partition maxima and positive constant payoffs are not asserted.',
 'program_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'Q':Q,
 'unary_masses':{str(q):str(D[q]) for q in Q},'pair_first_caps':{str(q):str(a[q]) for q in Q},
 'responses':responses,'contexts':contexts,'contexts_sha256':digest(contexts),
 'block_minima':{b:{'value':str(v),'pair':P,'retained':K} for b,(v,P,K) in zip(blocks,minimum)},
 'contraction_ratio_count':480,
 'contraction_minima':{str(p):{'value':str(min(v)[0]),'pair':min(v)[1],'retained':min(v)[2],'block':min(v)[3]} for p,v in ratios.items()},
 'contraction_maxima':{str(p):{'value':str(max(v)[0]),'pair':max(v)[1],'retained':max(v)[2],'block':max(v)[3]} for p,v in ratios.items()},
 'counterexamples':{'wrong_pair_product_first_moment':str(wrong_first),'canonical_product_first_moment':str(canonical_first),
  'wrong_pair_product_gap':str(product_gap),'wrong_pair_owner_count_hinge_gap':str(count_gap),
  'smaller_pair_zero_zero_atom_decrease':str(atomgap),
  'four_response_source_retained13_event_mass_cap':'1/12',
  'four_response_source_retained13_event_excess_at_cap':str(source_gap),
  'outside37_first_tail':str(F(1,10)),'X13_first_tail':str(u(13,1))},
 'checks':CHECKS,'check_count':sum(CHECKS.values())}
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','check_count':result['check_count'],'contexts':len(contexts),'ratios':sum(map(len,ratios.values())),
 'product_partition_counterexample':str(product_gap),'count_partition_counterexample':str(count_gap),'output':str(output)},indent=2))
