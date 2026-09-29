#!/usr/bin/env python3
"""Exact independent audit of a finite 11-regime dual; no LP/model imports."""
from fractions import Fraction as F
from itertools import product, combinations
from pathlib import Path
from hashlib import sha256
from math import prod
from argparse import ArgumentParser
import json

HERE=Path(__file__).resolve().parent
parser=ArgumentParser(description=__doc__)
parser.add_argument('--base',type=Path,default=HERE.parent)
parser.add_argument('--witness',type=Path,default=HERE/'clustered11_regime_dual.json')
parser.add_argument('--output',type=Path,default=HERE/'clustered11_regime_independent.json')
args=parser.parse_args()
base=args.base
witness_path=args.witness
witness=json.loads(witness_path.read_text())
names=('clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json','remaining33_global_root_exclusion_certificate.json')
inputs={n:json.loads((base/n).read_text()) for n in names}
checks=0

def ck(value,label):
 global checks
 checks+=1
 if not value:raise RuntimeError(label)

def mult(values):
 out=F(1)
 for x in values:out*=x
 return out

for n in names:ck(sha256((base/n).read_bytes()).hexdigest()==witness['source_sha256'][n],'pinned actual source '+n)
Q=(7,11,13,17,19)
g=F(200163067,201247200)
orig=inputs[names[0]]['actual_originals']
added=inputs[names[1]]['first_tested_success']['added_higher_pure_originals']
allorig=orig+added
ck(len(allorig)==109 and len({x['modulus'] for x in allorig})==109,'one phase for each of109 distinct originals')
ck({(o['modulus'],o['residue']) for o in added}=={(27,4),(81,13),(243,40),(729,121),(125,2),(625,27),(3125,152),(15625,777)},'actual eight higher pure labels')

def fac(n):
 out={}
 for p in (3,5)+Q:
  e=0
  while n%p==0:n//=p;e+=1
  if e:out[p]=e
 ck(n==1,'full prime factorization')
 return out
factorizations=[(o,fac(o['modulus'])) for o in allorig]
central={}
for p in (3,5):
 pure=[o for o,f in factorizations if set(f)=={p}]
 N=max(o['modulus'] for o in pure)
 live=[x for x in range(N) if all(x%o['modulus']!=o['residue'] for o in pure)]
 caps={a:F(sum(x%(p*p)==a for x in live),N) for a in range(p*p)}
 weak=4 if p==3 else 2
 reference=F(2) if p==3 else F(4,3)
 weight=F(1,p*p)
 gamma=weight/(reference*caps[weak])
 ck(caps[weak]==(F(41,729) if p==3 else F(469,15625)),'central pure capacity')
 ck(gamma==(F(81,82) if p==3 else F(1875,1876)),'actual gamma')
 weights={a:(weight if a==weak else reference/F(p*p)) for a,k in caps.items() if k}
 ck(sum(weights.values())==1,'central probability source')
 central[p]=(caps,weights,weak,gamma)
# Reconstruct cells from physical CRT residues and actual central mixed originals.
cmix=[o for o,f in factorizations if set(f)=={3,5}]
def address(x):
 a,b=x%9,x%25
 return 3*(a%3)+a//3,5*(b%5)+b//5
xs=sorted([x for x in range(225) if central[3][0][x%9] and central[5][0][x%25] and all(x%o['modulus']!=o['residue'] for o in cmix)],key=address)
ck(len(xs)==80,'central80 cells')
for q in Q:
 pure=[o for o,f in factorizations if set(f)=={q}]
 ck(len(pure)==1 and (pure[0]['modulus'],pure[0]['residue'])==(q,0),'actual outside reference uniform off root0')
for p,q in combinations(Q,2):
 pair=[o for o,f in factorizations if set(f).intersection(Q)=={p,q}]
 ck(len(pair)==4,'four pair labels')
 ck(any(o['modulus']==p*q and o['residue']==1 for o in pair),'entire root1 pair forbidden')
 for o in pair:ck(o['residue']%p==1 and o['residue']%q==1,'other pair labels are subevents')
local={q:[] for q in Q}
for o,f in factorizations:
 outside=set(f).intersection(Q)
 if len(outside)==1 and len(f)>1:
  q=next(iter(outside));qp=q**f[q];cm=o['modulus']//qp
  ck(qp<=q*q and set(f)<={3,5,q},'literal shallow unary label')
  local[q].append((cm,o['residue']%cm,qp,o['residue']%qp))
# Each coordinate has three actual surviving atom sets, not an assumed count vector.
parts={}
for x in xs:
 for q in Q:
  alive={z for z in range(q*q) if z%q and all(x%cm!=a or z%qp!=b for cm,a,qp,b in local[q])}
  sets=(frozenset(z for z in alive if z%q!=1),frozenset(alive.intersection({1})),frozenset(z for z in alive if z%q==1 and z!=1))
  ck(set.union(*(set(s) for s in sets))==alive,'regimes partition exact local source')
  ck(len(sets[1]) in (0,1) and len(sets[2]) in (0,q-1),'special/other root1 types are whole or empty')
  for root in range(2,q):ck(sum(z%q==root for z in sets[0]) in (0,q),'nonroot first roots whole or empty')
  if q>=11:ck(all(9+q*j in alive for j in range(q)),'global root9 actually intact')
  parts[x,q]=sets
regimes=((-1,-1),)+tuple((i,t) for i in range(5) for t in (0,1))
columns=[];region_sets={};mass={};reward={}
for x in xs:
 for regime in regimes:
  j,t=regime
  sets=tuple(parts[x,q][t+1 if i==j else 0] for i,q in enumerate(Q))
  if not all(sets):continue
  key=(address(x),regime);columns.append(key);region_sets[key]=sets
  mass[key]=mult(F(len(A),q*(q-1)) for q,A in zip(Q,sets))
  reward[key]=g*central[3][1][x%9]*central[5][1][x%25]*mass[key]
ck(len(columns)==419,'419 positive same-source variables')
ck(sum(reward.values())/g==F(305684996597,646498195200),'complete actual source mass')
# Literal query coefficient from atom counts divided by the true query normalizer.
def query_coefficient(key,choices):
 factors=[]
 for q,A,choice in zip(Q,region_sets[key],choices):
  if choice==-1:
   count=len(A);normalizer=F(1)
  elif choice==1:
   count=int(1 in A);normalizer=F(1,q*(q-2)) # actual square query1modq²
  else:
   root=1 if choice==0 else choice
   count=sum(z%q==root for z in A);normalizer=F(1,q-1)
  if not count:return F(0)
  factors.append(F(count,q*(q-1))/normalizer)
 return mult(factors)
# Generate every declared nonzero global query independently of producer indexing.
menus=((-1,0,1,2,3,4,5,6),)+((-1,0,1,9),)*4
qrows={};query_masks={};queries_by_support=[0]*32
for choices in product(*menus):
 if sum(z in (0,1) for z in choices)>1:continue
 h={i:v for i,key in enumerate(columns) if (v:=query_coefficient(key,choices))}
 if not h:continue
 T=sum(1<<i for i,c in enumerate(choices) if c!=-1)
 qrows[choices]=(T,h)
 query_masks[choices]=sum(1<<i for i in h)
 queries_by_support[T]+=1
ck(len(qrows)==512,'512 nonzero global outside query tuples')
# Actual central selectors, indexed by inherited physical/root-major labels.
weight3={address(x)[0]:central[3][1][x%9] for x in xs}
weight5={address(x)[1]:central[5][1][x%25] for x in xs}
gamma3,gamma5=central[3][3],central[5][3]
def axis(weights,level,block,gamma,weak,deep):
 if level==0:return {0:weights}
 if level==1:return {root:{i:w for i,w in weights.items() if i//block==root} for root in sorted({i//block for i in weights})}
 if level==2:return {i:{i:w} for i,w in weights.items()}
 return {i:{i:deep*(gamma if i==weak else 1)} for i in weights}
selectors={};cmasks={}
for mode in range(16):
 e3,e5=divmod(mode,4)
 a3=axis(weight3,e3,3,gamma3,4,F(1));a5=axis(weight5,e5,5,gamma5,10,F(4,5))
 for left,right in product(a3,a5):
  address0=(mode,left,right)
  coeff={cell:a3[left].get(cell[0],F(0))*a5[right].get(cell[1],F(0)) for cell,regime in columns}
  selectors[address0]=coeff
  cmasks[address0]=sum(1<<i for i,(cell,regime) in enumerate(columns) if coeff[cell])
ck(len(selectors)==559,'559 literal central selectors')
rows_count=0;entries_count=0;group_nonempty=[False]*512
for (mode,left,right),mask in cmasks.items():
 for choices,qmask in query_masks.items():
  nz=(mask&qmask).bit_count()
  if nz:
   rows_count+=1;entries_count+=nz;group_nonempty[32*mode+qrows[choices][0]]=True
ck(rows_count==135584,'all complete literal rows')
ck(entries_count==650752,'all response nonzero entries')
ck(all(group_nonempty),'all512 fee groups represented')
C=list(map(F,inputs[names[2]]['combined512_coefficients']))
ck(len(C)==512 and all(c>=0 for c in C),'full coefficient inventory')
for i,q in enumerate(Q):
 if q>=11:C[32*8+(1<<i)]+=g/F(q*(q-2))
# Validate exact witness without any use of numerical solver output.
den=witness['denominator'];ck(type(den) is int and den==10**15,'positive exact denominator')
loads=[F(0)]*512
residual={key:reward[key] for key in columns}
seen=set()
for row in witness['rows']:
 mode,T,left,right=row['mode'],row['support'],row['left'],row['right']
 choices=tuple(row['outside_choices']);N=row['numerator']
 ck(type(N) is int and N>0,'nonnegative rational multiplier')
 ck((mode,left,right) in selectors,'legal fixed central selector')
 ck(choices in qrows and qrows[choices][0]==T,'legal one-global outside query and support')
 adr=(mode,T,left,right,choices)
 ck(adr not in seen,'no duplicate witness address');seen.add(adr)
 lam=F(N,den);loads[32*mode+T]+=lam
 central_coeff=selectors[mode,left,right]
 for idx,h in qrows[choices][1].items():
  key=columns[idx];cc=central_coeff[key[0]]
  if cc:residual[key]-=lam*cc*h
ck(len(seen)==700,'700 positive literal dual rows')
for j in range(512):ck(loads[j]<=C[j],'exact complete fee budget '+str(j))
expected_res={(tuple(row['cell']),tuple(row['regime'])):F(row['residual']) for row in witness['residuals']}
ck(set(expected_res)==set(columns),'all419 residual addresses')
for key,value in residual.items():ck(value==expected_res[key],'exact residual reconstruction')
upper=sum(max(F(0),r) for r in residual.values())
target=F(193,100000)
ck(upper==F(witness['expected']['upper']),'exact upper matches witness')
ck(upper==F(676452579812687931521867,8935026225378244992000000000000000000),'literal candidate upper')
ck(F(0)<upper<target,'strict positive upper below original target')
ck(F(witness['expected']['target'])==target,'original threshold retained')
ck(sum(r>0 for r in residual.values())==312,'positive residual count')
result={
 'status':'PASS','checks':checks,'new_lean_verification':False,'optimizer_used':False,
 'active_variables':len(columns),'outside_query_tuples':len(qrows),'literal_rows':rows_count,'matrix_nonzero_entries':entries_count,
 'dual_rows':len(seen),'fee_groups':len(C),'positive_residual_count':sum(r>0 for r in residual.values()),
 'source_mass':str(sum(reward.values())/g),'exact_upper':str(upper),'target':str(target),'strictly_below_target':upper<target,
 'witness_sha256':sha256(witness_path.read_bytes()).hexdigest(),
 'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'scope':'Fixed109source and f(central coarse cell, none-or-unique-root1/special-other regime) only. Complete512 fees and fullmode8 additions. No exactzero optimum or unrestricted full5 conclusion.',
}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
