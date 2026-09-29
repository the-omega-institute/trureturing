"""All old phases and all26 shallow multioutside supports, with no outside11.

Reuses the pinned complete753 catalogue and754's116 fixed source laws,
adding only32 literal old45 integer laws. No solver, optimality, or new
full-source enumeration is an input to this exact consumer.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from collections import Counter
from math import prod
import json

DEPENDENCIES={
 'fibre_credit_depth_two_no11_all_supports_weights.json':'c7c42cb8abb8ce9ae1ea9e1cded9645b0cde62b0ef295a8bd8a22810eaf1dead',
 'fibre_credit_depth_two_actual_joint_catalogue.cpp':'a0da6f067b6e268ab24b46488c8a17e0225855d58667120530540918ff232f58',
 'fibre_credit_depth_two_actual_joint_catalogue.py':'b38e644c34558adcf7b4f56ceb6007aea18001a1e27569634e0860490750f3dc',
 'fibre_credit_depth_two_actual_joint_catalogue.json':'fb2093552efc1816c53727f75a6f84bcfee6c496d67bbf45ad002fa3a7375afc',
 'fibre_credit_depth_two_last_three_weights.json':'9c7034042d71dbc425ffcf4c630f9bb5f9f7d27cf5d80b78fc2559c0e4c5a9c4'}
P=(13,17,19,23,29);THRESHOLDS=(4,4,4,6,6)
MODS=(3,5,9,15,45);K48=(0,12,24,12,42,8,8,22,36,22,57)

def need(ok,msg):
 if not ok:raise RuntimeError(msg)

def caps(points,remaining,weights):
 zero=[];seven=[sum(weights)]
 for d in MODS:
  first=[0]*d;second=[0]*d
  for x,r,w in zip(points,remaining,weights):first[x%d]+=r*w;second[x%d]+=w
  zero.append(max(first));seven.append(max(second))
 return zero+seven

rho=[F(1,p-a) for p,a in zip(P,THRESHOLDS)]
factor=prod(1+r for r in rho);multi=factor-1-sum(rho)
outside_haar=prod(F(p,p-a) for p,a in zip(P,THRESHOLDS))
need((factor,multi,sum(rho[:3]),sum(rho[3:]),outside_haar)
     ==(F(7168,5083),F(12166,228735),F(149,585),F(40,391),F(551,135)),
     'exact outside coefficients')

def metric(den,cp,h4,h6,t):
 M=sum(cp);K=sum(k*c for k,c in zip(K48,cp))
 cost=factor*F(K,48*den)+multi*(1+F(M,den))+sum(rho[:3])*F(h4,den)+sum(rho[3:])*F(h6,den)
 reserve=216569*den-12166*M-6720*K-58259*h4-23400*h6
 density=(1-cost)/(315*F(t,den)*outside_haar)
 need(density==F(reserve,294076965*t),'exact integer reserve and Haar transport')
 return dict(D=den,M=M,K=K,H4_upper=h4,H6_upper=h6,maximum_weight=t,
             reserve=reserve,cost_upper=str(cost),Haar_lower=str(density),caps=cp)

def calculate(directory,literal_path):
 for name,digest in DEPENDENCIES.items():
  need(sha256((directory/name).read_bytes()).hexdigest()==digest,'pinned prior source '+name)
 cat=json.loads((directory/'fibre_credit_depth_two_actual_joint_catalogue.json').read_text())
 oldlaws=json.loads((directory/'fibre_credit_depth_two_last_three_weights.json').read_text())['rows']
 literal=json.loads(literal_path.read_text())
 need(cat['actual_source_count']==112893 and cat['paired_group_count']==3193,'complete inherited catalogue')
 shape3=cat['rows'][3];points=shape3['old45_points']
 need(literal['shape']==3 and literal['old45_points']==points and len(points)==16,'same old45 shape')

 # N75 forces total deleted incidences21, the sum of the five maxima.
 # Every such b is the sum of five maximum masks, even if some disjoint
 # masks share a root color. Distinct colors1..5 give an actual witness.
 choices=[];sizes=[]
 for d in MODS:
  n=[sum(x%d==a for x in points) for a in range(d)];sizes.append(max(n))
  choices.append([a for a,v in enumerate(n) if v==max(n)])
 need(sizes==[8,5,4,3,1] and prod(map(len,choices))==256,'complete targeted maximum-mask layouts')
 all75={}
 for phases in product(*choices):
  b=tuple(sum(x%d==a for d,a in zip(MODS,phases)) for x in points)
  all75.setdefault(b,phases)
 required={}
 for b,phases in all75.items():
  cp=caps(points,[6-v for v in b],[1]*16);M=sum(cp);K=sum(k*c for k,c in zip(K48,cp))
  if K==1865 and M in (148,149):required[b]=(M,phases)
 need(Counter(m for m,phases in required.values())=={148:12,149:20},'all32 target actual sources')
 newlaws={tuple(r['b']):r for r in literal['rows']}
 need(len(newlaws)==len(literal['rows'])==32 and set(newlaws)==set(required),'exact32 literal coverage')
 joint_counts=Counter()
 for n,m,k,h4,count,b in shape3['joint_groups']:
  if n==75 and k==1865 and m in (148,149):
   need(h4==29,'all sources at target triples have the same certified hinge')
   joint_counts[m]+=count
 need(joint_counts==Counter({148:12,149:20}),'targeted source counts match full catalogue')

 records=[];exceptions={};uniform_count=0;uniform_groups=0;skipped_new=0
 for shape,row in enumerate(cat['rows']):
  need(row['H6_numerator']==10,'inherited same-source H6')
  for group,(n,m,k,h4,count,b) in enumerate(row['joint_groups']):
   remaining=[6-v for v in b];cp=caps(row['old45_points'],remaining,[1]*len(b))
   need(sum(remaining)==n and sum(cp)==m and sum(x*y for x,y in zip(K48,cp))==k,'uniform representative exact caps')
   if shape>=4 and n==75 and k==1873 and m in (146,147):continue
   if shape==3 and n==75 and k==1865 and m in (148,149):skipped_new+=count;continue
   value=metric(n,cp,h4,10,1)
   need(value['reserve']>0,'all remaining uniform groups pass')
   value.update(kind='uniform',shape=shape,group=group,source_count=count)
   records.append(value);uniform_count+=count;uniform_groups+=1
  for case in row['exceptional_hinge4']:
   key=(shape,tuple(case['b']));need(key not in exceptions,'old exception uniqueness');exceptions[key]=case
 need(skipped_new==32,'only target32 replace uniform laws')
 assigned={(r['shape'],tuple(r['b'])):r for r in oldlaws}
 need(len(assigned)==len(oldlaws)==len(exceptions)==116 and set(assigned)==set(exceptions),'old116 laws retained exactly')
 old_values=[]
 for key,law in assigned.items():
  shape,b=key;w=law['weights'];points0=cat['rows'][shape]['old45_points'];remaining=[6-v for v in b]
  need(len(w)==len(points0)==len(b) and all(type(v)is int and 0<=v<=120 for v in w) and max(w)>0,'fixed old integer weights')
  need(exceptions[key]['H4_numerator']==29,'inherited old same-source H4')
  den=sum(r*v for r,v in zip(remaining,w));t=max(w)
  value=metric(den,caps(points0,remaining,w),29*t,10*t,t)
  need(value['reserve']>0,'old116 conservative hinge laws pass')
  value.update(kind='old_weighted',shape=shape,source_count=1);records.append(value);old_values.append(value)

 new_values=[];actual_witnesses=[]
 for b,law in newlaws.items():
  phases=law['maximal_old_phases'];w=law['weights'];remaining=[6-v for v in b]
  need(len(phases)==5 and all(a in allowed for a,allowed in zip(phases,choices)),'one actual maximum phase per label')
  need(tuple(sum(x%d==a for d,a in zip(MODS,phases)) for x in points)==b,'literal actual same-source b witness')
  need(len(w)==16 and all(type(v)is int and 0<=v<=6 for v in w) and max(w)>0,'new literal small integer source law')
  den=sum(r*v for r,v in zip(remaining,w));t=max(w)
  value=metric(den,caps(points,remaining,w),29*t,10*t,t)
  need(value['reserve']>0,'new32 conservative hinge laws pass')
  value.update(kind='new_weighted',shape=3,source_count=1,b=list(b),weights=w)
  records.append(value);new_values.append(value)
  # Full literal old315 realization, for a finite source witness only.
  rules=[[3,0],[5,0],[9,4],[15,shape3['a15']],[45,shape3['a45']],[7,0]]
  for color,(d,a) in enumerate(zip(MODS,phases),1):
   while a%7!=color:a+=d
   need(0<=a<7*d,'literal CRT range');rules.append([7*d,a])
  hist=Counter()
  for x in range(315):
   if all(x%d!=a for d,a in rules):hist[x%45]+=1
  need(dict(hist)==dict(zip(points,remaining)),'full actual315 witness has the same fibre counts')
  actual_witnesses.append(dict(b=list(b),actual_core_originals=rules))

 need(uniform_count==112745 and uniform_groups==3187 and len(records)==3335,'uniform groups and parameter rows')
 need(sum(r['source_count'] for r in records)==112893,'complete source count retained')
 worst=max(records,key=lambda r:F(r['cost_upper']));minimum=min(records,key=lambda r:F(r['Haar_lower']))
 newmin=min(new_values,key=lambda r:F(r['Haar_lower']));newworst=max(new_values,key=lambda r:F(r['cost_upper']))
 need(F(minimum['Haar_lower'])==F(24842,294076965)>F(1,12000),'uniform no11 Haar lower')
 need(all(F(r['reserve'],r['maximum_weight'])>=24842 for r in records),'same-source common integer reserve')
 need(F(newmin['Haar_lower'])==F(2004511,1764461790),'paired new32 minimum Haar')
 need(F(newworst['cost_upper'])==F(87888344,89892855),'new32 maximum conservative cost')
 return dict(scope='All actual fixed old and singleton phases; all26 shallow multioutside supports; arbitrary finite core3/5/7 heights; at most five outside primes, all >=13, each outside exponent <=1',
             minimal_five_outside_primes=P,thresholds=THRESHOLDS,outside_factor=str(factor),
             multioutside_factor=str(multi),outside_Haar_factor=str(outside_haar),
             inherited_actual_sources=112893,uniform_actual_sources=uniform_count,
             old_weighted_sources=116,new_weighted_sources=32,checked_parameter_rows=len(records),
             targeted_layouts_checked=256,distinct_target_size_vectors=len(all75),
             maximum_cost=worst['cost_upper'],Haar_survivor_lower=minimum['Haar_lower'],
             simple_strict_lower='1/12000',worst_Haar_profile=minimum,worst_cost_profile=worst,
             new32_minimum_Haar=newmin['Haar_lower'],new32_maximum_cost=newworst['cost_upper'],
             new32_results=new_values,actual_new_source_witnesses=actual_witnesses,
             no_solver_or_optimality_premise=True,weighted_hinges_are_conservative=True,
             same_old45_weights_with_actual_uniform7_fibres=True,lean_verification=False)

if __name__ == '__main__':
 directory=Path(__file__).resolve().parent
 result=calculate(directory,directory/'fibre_credit_depth_two_no11_all_supports_weights.json')
 result=json.loads(json.dumps(result))
 expected=json.loads(Path(__file__).with_suffix('.json').read_text())
 need(result==expected,'retained result agrees with exact recomputation')
 print(json.dumps(result,indent=2))
