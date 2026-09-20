#!/usr/bin/env python3
"""Exact six-prime prefix certificate from explicit pinned geometry inputs.

Independent standard-library evaluation of the basic comparison formulas in
Michael Schroeder, Nine Prime Divisors in Odd Distinct Covering Systems,
edition 1.0.1, Sections 3--5, 8--9, DOI 10.5281/zenodo.22759614.
No source verifier is imported and no geometry or Lean checker is run.
The required geometry input carries source identity and its MIT notice.
Python 3.10+; use --geometry FILE --output FILE from any working directory.
"""
import argparse,json,hashlib,sys
from fractions import Fraction as Q
from itertools import product
from functools import lru_cache
from pathlib import Path
from collections import defaultdict

PRIMES=(7,11,13,17,19,23)
THRESHOLDS=(2,4,4,8,8,12)
CAPS=tuple(Q(p-1,p-1-t) for p,t in zip(PRIMES,THRESHOLDS))
RATIOS=tuple(sorted({Q(t,m) for t in THRESHOLDS for m in range(1,t)}))
GEOMETRY_MODS=(3,9,27,5,15,45)
BATCHES={};QUERIES=0

def ceil_decimal(x):
 assert x>=0
 n,d=x.numerator*10**10,x.denominator
 return Q((n+d-1)//d,10**10)

def depth_moments(p,positive,cutoff):
 if not positive:return [(0,Q(1))],(Q(1),Q(0)),(Q(0),Q(0))
 kept=[(j,Q(p-1,p**(j+1))) for j in range(1,cutoff)]
 tail=(Q(1,p**cutoff),Q(1,p**cutoff)*(cutoff+Q(1,p-1)))
 total=(Q(1,p),Q(1,p-1))
 assert sum((w for j,w in kept),Q(0))+tail[0]==total[0]
 assert sum((j*w for j,w in kept),Q(0))+tail[1]==total[1]
 return kept,total,tail

def linear_sum(ws,cs,m3,m5):
 mass=sum(ws);peak=max(ws)
 inc=[max(sum(w for x,w in zip(cs,ws) if x%d==r) for r in range(d)) for d in GEOMETRY_MODS]
 a,u=m3;b,v=m5
 return a*b*(mass+sum(inc))+u*b*inc[2]+a*v*sum(inc[3:])+ (a+u)*(b+v)*peak

def cache_values(cache,cs,ws,positive3,positive5):
 global QUERIES
 uv=list(product(range(1,12) if positive3 else [0],range(1,9) if positive5 else [0]))
 labels=[];lines=[str(len(cs))]+[f'{x} {w} 0' for x,w in zip(cs,ws)]
 for u,v in uv:
  for threshold in RATIOS:
   d=threshold.denominator
   nums=[d,d,d*(1+u),d*(1+v),d*(1+v),d*(1+v),d*(1+u)*(1+v)]
   labels.append((u,v,threshold,d))
   lines.append(' '.join(map(str,[len(labels)-1,d,d,*nums,threshold.numerator])))
 payload=('\n'.join(lines)+'\n').encode();key=hashlib.sha256(payload).hexdigest()
 record=cache[key];arr=record['integer_maxima']
 raw=(json.dumps(arr,separators=(',',':'))+'\n').encode()
 assert hashlib.sha256(raw).hexdigest()==record['cache_file_sha256']
 assert len(arr)==len(labels)
 BATCHES[key]={'sha256':hashlib.sha256(raw).hexdigest(),'queries':len(arr)}
 result={}
 for i,(a,lab) in enumerate(zip(arr,labels)):
  assert len(a)==3 and a[0]==i and a[1]==lab[3] and 0<=a[2]<2**30
  u,v,t,d=lab;result[u,v,t]=Q(a[2],d)
 QUERIES+=len(arr)
 return result

def envelope(cache,a,b,c,j):
 cells=[x for x in range(135) if x%3!=0 and x%9!=1 and x%27!=b and x%5!=0 and x%15!=a]
 mass=Q(0);whole=Q(0);values={t:Q(0) for t in RATIOS}
 for pos3,pos5 in product((False,True),repeat=2):
  ws=[(1 if pos3 else 4)*(1 if pos5 else 16-4*(x%5==c)-(x%5==j)) for x in cells]
  geom=cache_values(cache,cells,ws,pos3,pos5)
  u,um,ut=depth_moments(3,pos3,12);v,vm,vt=depth_moments(5,pos5,9)
  ur=(um[0]-ut[0],um[1]-ut[1])
  scale=Q(1,(1 if pos3 else 6)*(1 if pos5 else 20))
  mass+=scale*um[0]*vm[0]*sum(ws)
  whole+=scale*linear_sum(ws,cells,um,vm)
  omitted=linear_sum(ws,cells,ut,vm)+linear_sum(ws,cells,ur,vt)
  assert omitted>=0
  for t in RATIOS:
   values[t]+=scale*(sum((wu*wv*geom[du,dv,t] for du,wu in u for dv,wv in v),Q(0))+omitted)
 return mass,whole,values

def multiplier_prefixes():
 table={1:Q(1)};mean=Q(1);out=[]
 for p,cap in zip(PRIMES,CAPS):
  out.append((dict(table),mean))
  nxt=defaultdict(Q)
  for current,weight in table.items():
   for new in range(current,32,current):
    e=new//current-1
    prob=1-cap/p if e==0 else cap*Q(p-1,p**(e+1))
    nxt[new]+=weight*prob
  table=nxt;mean*=1+cap/Q(p-1)
 return out

GEOMETRY_SHA256='0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1'

def fee(q):
 return {5:Q(7,24),7:Q(1,8),11:Q(1,24),13:Q(1,48)}.get(q,Q(1,2**((q-1)//2)))

def budgets(mass):
 children=([(5,7,11,13,q) for q in (17,19,23,29,31,37)]+
           [(5,7,11,17,q) for q in (19,23)]+[(5,7,11,19,23)]+
           [(5,7,13,17,q) for q in (19,23)]+[(5,7,13,19,23)])
 assert len(set(children))==12
 reference=(3,5,7,11,13,17);caps=(Q(1),Q(1),Q(3,2),Q(5,3),Q(3,2),Q(2))
 rows=[]
 for J in children:
  physical=(3,)+J
  assert all(p<=q for p,q in zip(reference,physical))
  E=Q(1493,3072)-sum(map(fee,J),Q(0))
  local=(Q(3,10),)+tuple(Q(2,q-1) for q in J[1:])
  coefficients=tuple(a*b for a,b in zip(caps[1:],local))
  assert E>0 and max(coefficients)<=Q(1,2) and E<mass
  rows.append({'children':J,'reference_to_physical':list(zip(reference,physical)),
   'outside_budget':str(E),'coordinate_marginal_caps':list(map(str,caps)),
   'child_descendant_coefficients':list(map(str,local)),
   'marginal_attachment_coefficients':list(map(str,coefficients)),
   'root_attachment_coefficient':'1','mass_minus_expense':str(mass-E)})
 Emax=max(Q(r['outside_budget']) for r in rows)
 assert Emax==Q(283,6144)
 simple=Q(1,20)-Emax
 assert simple==Q(121,30720)>0 and mass>Q(1,20)
 return {'rows':rows,'maximum_outside_budget':str(Emax),
  'uniform_live_mass_lower_bound':str(mass-Emax),
  'simple_strict_live_mass_lower_bound':str(simple),
  'simple_strict_core_haar_lower_bound':str(simple/Q(15,2))}

def main():
 if sys.version_info<(3,10):raise SystemExit('Python 3.10 or later is required')
 if not __debug__:raise SystemExit('Assertions required; do not run with -O')
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--geometry',type=Path,required=True)
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 raw=args.geometry.read_bytes();geometry_sha=hashlib.sha256(raw).hexdigest()
 assert geometry_sha==GEOMETRY_SHA256,'Unexpected geometry input digest'
 geometry=json.loads(raw);cache=geometry['batches']
 assert geometry['schema']=='six-prime-prefix-geometry-input-v1' and len(cache)==72
 assert geometry['source_verifier_sha256']=='e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135'
 expected={(a,b,c,-1,j,0,0,0,-1) for a in (1,2) for b in (2,4) for c in (a,3-a) for j in range(1,5)}
 assert len(expected)==32
 dists=multiplier_prefixes();results=[]
 for node in sorted(expected):
  a,b,c,_,j,*_=node
  gamma=3*(a==1)+(b%3==a%3)
  reserve=Q(135,4)+gamma+(9-gamma)*(Q(c==a,5)+Q(j==a,20))
  mass,whole,vals=envelope(cache,a,b,c,j);loss=[];unrounded=[]
  for p,t,(table,mean) in zip(PRIMES,THRESHOLDS,dists):
   small={m:w for m,w in table.items() if m<t}
   below=sum(small.values(),Q(0));belowfirst=sum((m*w for m,w in small.items()),Q(0))
   numerator=sum((m*w*vals[Q(t,m)] for m,w in small.items()),Q(0))+(mean-belowfirst)*whole-t*(1-below)*mass
   cost=numerator/(p-1-t);rounded=ceil_decimal(cost)
   assert cost<=rounded<cost+Q(1,10**10)
   unrounded.append(cost);loss.append(rounded)
  surplus=reserve-sum(loss[:4],Q(0));live=surplus/135;haar=live/Q(15,2)
  assert surplus>0
  results.append({'node':node,'reserve_lower_bound_cell_units':str(reserve),
   'stage_primes':PRIMES,'unrounded_loss_upper_bounds_cell_units':list(map(str,unrounded)),
   'rounded_loss_upper_bounds_cell_units':list(map(str,loss)),
   'prefix_indices_used':[0,1,2,3],'unused_later_stage_indices':[4,5],
   'prefix_surplus_lower_bound_cell_units':str(surplus),
   'prefix_live_mass_lower_bound':str(live),
   'original_haar_survival_lower_bound':str(haar)})
 worst=min(results,key=lambda r:Q(r['prefix_live_mass_lower_bound']))
 assert worst['prefix_live_mass_lower_bound']=='68006602781/1350000000000'
 assert set(BATCHES)==set(cache) and len(BATCHES)==72 and QUERIES==51840
 assert Q(worst['prefix_live_mass_lower_bound'])>Q(1,20)
 out={'schema':'six-prime-prefix-certificate-v1',
  'scope':'Rational postprocessing of all 32 basic anchor vertices and attachment budgets for Chapter 28 remaining 12 core sets. Geometry maxima, infinite-height comparison, actual submeasure construction, physical-prime transport and graph recursion are separate mathematical premises; no Lean replay.',
  'source':{key:geometry[key] for key in ('source_doi','source_archive_url','source_archive_sha256','source_verifier_sha256','source_geometry_cpp_sha256')},
  'geometry_input_sha256':geometry_sha,'source_verifier_imported':False,'geometry_reexecuted':False,
  'basic_vertex_count':len(results),'unique_geometry_batches':len(BATCHES),'integer_query_reads':QUERIES,
  'prefix_primes':[3,5,7,11,13,17],'coordinate_marginal_caps':['1','1','3/2','5/3','3/2','2'],
  'global_density_cap':'15/2','cell_to_haar_denominator':135,'worst':worst,
  'geometry_batches_used':BATCHES,'rows':results,
  'remaining_core_budgets':budgets(Q(worst['prefix_live_mass_lower_bound']))}
 args.output.write_text(json.dumps(out,indent=2)+'\n')
 print('PASS: all 32 basic vertices and 12 attachment budgets; prefix mass lower bound > 1/20; graph-block scope at most six vertices.')
if __name__=='__main__':main()
