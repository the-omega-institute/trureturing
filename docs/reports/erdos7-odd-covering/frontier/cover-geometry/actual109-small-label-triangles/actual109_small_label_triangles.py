#!/usr/bin/env python3
"""Literal common-layout audit of two small triangles on the fixed109 source."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from math import prod, lcm
from hashlib import sha256
import argparse, json

ap=argparse.ArgumentParser()
ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=ap.parse_args(); checks=0
def ck(b,label):
 global checks
 checks+=1
 if not b:raise RuntimeError(label)
names=('clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json')
raw={n:(a.base/n).read_bytes() for n in names}
D={n:json.loads(v) for n,v in raw.items()}
originals=D[names[0]]['actual_originals']+D[names[1]]['first_tested_success']['added_higher_pure_originals']
ck(len(originals)==109 and len({o['modulus'] for o in originals})==109,'109 distinct fixed originals')
Q=(7,11,13,17,19)
def factor(n):
 out={}
 for p in (3,5)+Q:
  e=0
  while n%p==0:n//=p;e+=1
  if e:out[p]=e
 ck(n==1,'original factors in seven coordinates')
 return out
facts=[(o,factor(o['modulus'])) for o in originals]
ck(all(len(set(f).intersection(Q))<=2 for _,f in facts),'all actual originals accounted for by pure central local or pair cases')
central={}
for p in (3,5):
 pure=[o for o,f in facts if set(f)=={p}]
 N=max(o['modulus'] for o in pure)
 counts=[0]*(p*p)
 for z in range(N):
  if all(z%o['modulus']!=o['residue'] for o in pure):counts[z%(p*p)]+=1
 weak=4 if p==3 else 2
 weights={r:(F(1,p*p) if r==weak else F(2,9) if p==3 else F(4,75)) for r,n in enumerate(counts) if n}
 ck(sum(weights.values())==1,'central prescribed reference mass1')
 ck(F(counts[weak],N)==(F(41,729) if p==3 else F(469,15625)),'actual higher-pure weak capacity')
 central[p]=weights
cmixed=[o for o,f in facts if set(f)=={3,5}]
ck(all(225%o['modulus']==0 for o in cmixed),'central mixed originals resolved modulo225')
local={q:[] for q in Q}
for o,f in facts:
 outside=set(f).intersection(Q)
 if len(outside)==1 and len(f)>1:
  q=next(iter(outside));qp=q**f[q];cm=o['modulus']//qp
  ck(qp<=q*q and set(f)<={3,5,q},'local constraint depends on retained central and outside square')
  ck(225%cm==0,'all local central cofactors resolved modulo225')
  local[q].append((cm,o['residue']%cm,qp,o['residue']%qp))
for q in Q:
 pure=[o for o,f in facts if set(f)=={q}]
 ck([(o['modulus'],o['residue']) for o in pure]==[(q,0)],'outside reference is uniform off actual root0')
for p,q in combinations(Q,2):
 ps=[o for o,f in facts if set(f).intersection(Q)=={p,q}]
 ck(len(ps)==4 and any(o['modulus']==p*q and o['residue']==1 for o in ps),'actual pair root1 ban present')
 ck(all(o['residue']%p==1 and o['residue']%q==1 for o in ps),'all other actual pair exclusions are subevents')
central_mass=[F(0)]*225
cell_data=[]
for x in range(225):
 if x%9 not in central[3] or x%25 not in central[5]:continue
 if any(x%o['modulus']==o['residue'] for o in cmixed):continue
 A=[];B=[]
 for q in Q:
  live=[z for z in range(q*q) if z%q and all(x%cm!=r or z%qp!=s for cm,r,qp,s in local[q])]
  A.append(F(sum(z%q==1 for z in live),q*(q-1)))
  B.append(F(sum(z%q!=1 for z in live),q*(q-1)))
 outside=prod(B)+sum(A[i]*prod(B[j] for j in range(5) if j!=i) for i in range(5))
 mass=central[3][x%9]*central[5][x%25]*outside
 central_mass[x]=mass
 cell_data.append({'x_mod225':x,'mass':str(mass)})
source_mass=sum(central_mass)
ck(source_mass==F(305684996597,646498195200),'same unnormalized692 actual109 source')
ck(sum(bool(v) for v in central_mass)==79,'79 positive central cells')
triangles=[]
for labels in ((3,5,15),(3,5,9)):
 needed=sorted(set(labels)|{lcm(d,e) for d,e in combinations(labels,2)})
 marg={d:[sum(central_mass[x] for x in range(225) if x%d==r) for r in range(d)] for d in needed}
 maximum={d:max(v) for d,v in marg.items()}
 envelope=3*sum(maximum[d] for d in labels)+2*sum(maximum[lcm(d,e)] for d,e in combinations(labels,2))
 best=F(-1);winners=[];records=[]
 for residues in product(*(range(d) for d in labels)):
  unary=[marg[d][r] for d,r in zip(labels,residues)]
  pair=[sum(central_mass[x] for x in range(225) if x%labels[i]==residues[i] and x%labels[j]==residues[j]) for i,j in combinations(range(3),2)]
  value=3*sum(unary)+2*sum(pair)
  direct=sum(central_mass[x]*((1+sum(x%d==r for d,r in zip(labels,residues)))**2-1) for x in range(225))
  ck(value==direct,'literal one-layout square agrees with factor expansion')
  ck(value<=envelope,'independent same-source envelope valid')
  if value>best:best=value;winners=[list(residues)]
  elif value==best:winners.append(list(residues))
  records.append({'residues':list(residues),'value':str(value)})
 witness=winners[0]
 terms={'unary':{str(d):str(marg[d][r]) for d,r in zip(labels,witness)},'pairs':[]}
 for i,j in combinations(range(3),2):
  terms['pairs'].append({'labels':[labels[i],labels[j]],'mass':str(sum(central_mass[x] for x in range(225) if x%labels[i]==witness[i] and x%labels[j]==witness[j]))})
 triangles.append({'labels':list(labels),'layout_count':len(records),'independent_actual_mass_envelope':str(envelope),'exact_common_layout_maximum':str(best),'strict_shared_label_saving':str(envelope-best),'saving_positive':envelope>best,'maximizing_layouts':winners,'first_witness_terms':terms,'marginal_maxima':{str(d):{'mass':str(maximum[d]),'residues':[r for r,v in enumerate(marg[d]) if v==maximum[d]]} for d in needed},'layouts':records})
result={'status':'PASS','checks':checks,'source_sha256':{n:sha256(v).hexdigest() for n,v in raw.items()},'program_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'new_lean_verification':False,'optimizer_used':False,'source_mass':str(source_mass),'central_cells':cell_data,'triangles':triangles,'scope':'Fixed actual109 unnormalized rho0 Phi rhoQ. Exact complete shared-label layouts on two selected triangles only; queries independent of fixed forbidden phases. No complete central9x25 cluster, no complete Gamma or new continuation gate.'}
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','checks':checks,'source_mass':str(source_mass),'triangles':[{k:r[k] for k in ('labels','layout_count','independent_actual_mass_envelope','exact_common_layout_maximum','strict_shared_label_saving','maximizing_layouts')} for r in triangles],'output':str(a.output)}))
