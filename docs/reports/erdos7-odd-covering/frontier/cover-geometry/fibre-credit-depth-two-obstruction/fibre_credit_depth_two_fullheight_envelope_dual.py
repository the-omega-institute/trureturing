"""Exact same-source sharp-hinge budget obstruction; no optimizer or native oracle.

Fourteen literal complete numerical queries provide valid lower hinge cuts.
The conclusion concerns one conditional-uniform7 source ansatz and its
specified all-height union budget, not actual covering or all source laws.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
from math import prod
import json

def need(ok,msg):
 if not ok:raise RuntimeError(msg)

MODS=(3,5,9,15,45)
LABELS=(3,5,9,15,45,7,21,35,63,105,315)
K48=(0,12,24,12,42,8,8,22,36,22,57)
P=(13,17,19,23,29)

def calculate(catalogue,literal):
 need(sha256(catalogue.read_bytes()).hexdigest()=='fb2093552efc1816c53727f75a6f84bcfee6c496d67bbf45ad002fa3a7375afc','pinned actual catalogue')
 need(sha256(literal.read_bytes()).hexdigest()=='f90089abe1647c3a847e3354356d35328b4582bcbb77919d1bd7a3f12e9c2f19','pinned literal dual input')
 cat=json.loads(catalogue.read_text())['rows'][4];raw=json.loads(literal.read_text())
 X=cat['old45_points'];b=raw['b'];r=[6-v for v in b];n=len(X);nv=n+13
 need(raw['shape']==4 and X==raw['old45_points'] and len(b)==n==16,'one actual source')
 need(cat['joint_groups'][25][:4]==[75,147,1861,29] and cat['joint_groups'][25][5]==b,'catalogue source identity')
 phases=raw['old_phases'];colors=raw['root_colors']
 need(len(phases)==5 and all(type(a)is int and 0<=a<d for d,a in zip(MODS,phases)),'actual phase dictionary')
 need(len(colors)==5 and all(type(c)is int and 1<=c<=6 for c in colors),'actual live7 root colors')
 rules=[[3,0],[5,0],[9,4],[15,cat['a15']],[45,cat['a45']],[7,0]]
 for d,a,color in zip(MODS,phases,colors):
  while a%7!=color:a+=d
  need(0<=a<7*d,'actual CRT range');rules.append([7*d,a])
 survivors=[z for z in range(315) if all(z%d!=a for d,a in rules)]
 fibres=[[z for z in survivors if z%45==x] for x in X]
 need([len(f) for f in fibres]==r and len(survivors)==75,'complete literal315 source realization')
 need(all(any(z%7==5 for z in f) for f in fibres),'common untouched query root5')

 # Cylinder cap epigraphs. For every exact numerical cylinder, check that
 # it is dominated by an included row; every included row must be attained.
 groups=[[tuple(i for i,x in enumerate(X) if x%d==a) for a in range(d)] for d in MODS]
 groups=[[g for g in gs if g] for gs in groups]
 cap_vectors=[]
 for gs in groups:cap_vectors.append([[r[i] if i in g else 0 for i in range(n)] for g in gs])
 cap_vectors.append([[1]*n])
 for gs in groups:cap_vectors.append([[int(i in g) for i in range(n)] for g in gs])
 matrix=[];checked_cylinders=0
 for slot,(d,vectors) in enumerate(zip(LABELS,cap_vectors)):
  actual=[[sum(z%d==a for z in f) for f in fibres] for a in range(d)]
  need(all(any(all(u<=v for u,v in zip(row,cap)) for cap in vectors) for row in actual),'every literal cylinder dominated on same source')
  need(all(cap in actual for cap in vectors),'every claimed exact cap row attained')
  checked_cylinders+=len(actual)
  for vector in vectors:
   row=vector+[0]*13;row[n+slot]=-1;matrix.append(row)

 query_witnesses=raw['query_witnesses'];need(len(query_witnesses)==14,'fourteen literal queries')
 forms=set();query_readings=[]
 for witness in query_witnesses:
  t=witness['threshold'];query=witness['numerical_query']
  need(t in (4,6) and [d for d,a in query]==[1]+list(LABELS),'complete distinct numerical query labels')
  need(all(type(a)is int and 0<=a<d for d,a in query),'every numerical query phase in range')
  # This reads the actual315 cells directly. No inferred A/B decomposition,
  # pair maximizer or native-proposed coefficient is trusted.
  coefficients=[sum(max(sum(z%d==a for d,a in query)-t,0) for z in f) for f in fibres]
  need(coefficients==witness['coefficients'],'literal actual query exactly realizes each hinge coefficient')
  identity=(t,tuple(coefficients));need(identity not in forms,'distinct hinge constraints');forms.add(identity)
  row=coefficients+[0]*13;row[n+11+(t==6)]=-1;matrix.append(row)
  query_readings.append(dict(threshold=t,uniform_numerator=sum(coefficients)))

 equality=r+[0]*13;certs={tuple(row['thresholds']):row for row in raw['rows']}
 need(len(certs)==len(raw['rows'])==32 and set(certs)==set(product((4,6),repeat=5)),'all threshold vectors')
 results=[]
 for thresholds,row in sorted(certs.items()):
  rho=[F(1,p-a-1) for p,a in zip(P,thresholds)];fac=prod(1+v for v in rho);B=fac-1-sum(rho)
  coeff=[F(0)]*n+[fac*F(k,48)+B for k in K48]+[sum(v for v,a in zip(rho,thresholds) if a==4),sum(v for v,a in zip(rho,thresholds) if a==6)]
  scale=row['scale'];need(type(scale)is int and scale>0 and all((v*scale).denominator==1 for v in coeff),'exact objective scaling')
  c=[int(v*scale) for v in coeff];multipliers=[0]*len(matrix);used=set()
  for i,v in row['multipliers']:
   need(type(i)is int and 0<=i<len(matrix) and i not in used and type(v)is int and v>0,'positive integer dual multiplier')
   multipliers[i]=v;used.add(i)
  columns=[sum(v*line[j] for v,line in zip(multipliers,matrix)) for j in range(nv)]
  nu=min(F(c[j]+columns[j],r[j]) for j in range(n))
  need(all(c[j]+columns[j]-nu*equality[j]>=0 for j in range(nv)),'all exact dual column inequalities')
  lower=B+nu/scale;need(lower>F(51,50),'sharp budget lower bound strictly exceeds51/50')
  need(str(lower)==row['proposed_lower'],'retained lower agrees with independent rational reconstruction')
  results.append(dict(thresholds=thresholds,exact_cost_lower=str(lower),normalization_dual=str(nu),scale=scale,nonzero_multipliers=len(used)))
 minimum=min(F(v['exact_cost_lower']) for v in results)
 return dict(scope=__doc__,actual_core_originals=rules,old45_points=X,remaining=r,
             actual315_source_size=len(survivors),literal_numerical_cylinders_checked=checked_cylinders,
             literal_complete_queries_checked=len(query_witnesses),query_readings=query_readings,
             constraints=len(matrix),variables=nv,threshold_count=32,
             minimum_certified_cost=str(minimum),simple_strict_lower='51/50',rows=results,
             all_nonnegative_real_old45_weights=True,sharp_actual_hinges=True,
             full_five_outside_heights=True,actual_covering_or_all_source_obstruction=False,
             no_solver_native_or_optimality_premise=True,lean_verification=False)

if __name__ == '__main__':
 base=Path(__file__).resolve().parent
 result=calculate(base/'fibre_credit_depth_two_actual_joint_catalogue.json',
                  base/'fibre_credit_depth_two_fullheight_envelope_dual_input.json')
 result=json.loads(json.dumps(result))
 expected=json.loads(Path(__file__).with_suffix('.json').read_text())
 need(result==expected,'retained result agrees with exact recomputation')
 print(json.dumps(result,indent=2))
