#!/usr/bin/env python3
"""Exact standalone replay of the fixed109 full512 eleven-regime dual; no optimizer."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
from hashlib import sha256
import json,argparse
Q=(7,11,13,17,19)
G=F(200163067,201247200)
class Model:
 def __init__(self,base):
  self.base=Path(base);self.checks=0
  names=('clustered_global_phase_fixture.json','clustered_higher_pure_capacity_obstruction.json','remaining33_global_root_exclusion_certificate.json')
  self.pins={n:sha256((self.base/n).read_bytes()).hexdigest() for n in names}
  self.ck(self.pins[names[0]]=='4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6')
  self.ck(self.pins[names[2]]=='36e1be912a058df44a9ce3b13c89d97574620176b921e037568ceb96dd0f87d4')
  js=[json.loads((self.base/n).read_text()) for n in names];orig=js[0]['actual_originals'];high=js[1]['first_tested_success'];added=high['added_higher_pure_originals']
  self.ck(high['n']==4 and F(high['gamma3'])==F(81,82) and F(high['gamma5'])==F(1875,1876))
  self.ck({(o['modulus'],o['residue']) for o in added}=={(27,4),(81,13),(243,40),(729,121),(125,2),(625,27),(3125,152),(15625,777)})
  self.ck(len(orig+added)==len({o['modulus'] for o in orig+added})==109)
  for p,weak,w,D,cap,gamma in ((3,4,F(1,9),F(2),F(41,729),F(81,82)),(5,2,F(1,25),F(4,3),F(469,15625),F(1875,1876))):
   pp=[(o['modulus'],o['residue']) for o in added if o['modulus']%p==0];depth=max(x[0] for x in pp)
   actual=F(sum(all(x%m!=r for m,r in pp) for x in range(weak,depth,p*p)),depth)
   self.ck(actual==cap and w/(D*actual)==gamma)
  local=[[] for q in Q]
  for o in orig:
   c=o['modulus'];b=o['residue'];qq=[]
   for i,q in enumerate(Q):
    if c%q==0:
     power=1
     while c%q==0:c//=q;power*=q
     qq.append((i,power))
   if len(qq)==1 and c>1:
    i,d=qq[0];local[i].append((c,b%c,d,b%d))
   if len(qq)==2:self.ck(all(b%Q[i]==1 for i,d in qq))
  for i,j in combinations(range(5),2):self.ck(any(o['modulus']==Q[i]*Q[j] and o['residue']==1 for o in orig))
  I=(0,1,2,4,5);J=tuple(m for m in range(20) if m!=5)
  self.cells=tuple((l,m) for l,m in product(I,J) if not(l<3 and m<5))
  self.w=[F(0) if l==3 else F(1,9) if l==4 else F(2,9) for l in range(6)]
  self.v=[F(0) if m==5 else F(1,25) if m==10 else F(4,75) for m in range(20)]
  self.regimes=[(-1,-1)]+[(i,t) for i in range(5) for t in (0,1)]
  self.masses={};self.allowed={};self.atomcounts={}
  for ci,(l,m) in enumerate(self.cells):
   c=next(x for x in range(l//3+3*(l%3),225,9) if x%25==m//5+5*(m%5));cs=[]
   for i,q in enumerate(Q):
    atoms=[z for z in range(q*q) if z%q and all(c%cm!=cr or z%qm!=qr for cm,cr,qm,qr in local[i])]
    count=(sum(z%q!=1 for z in atoms),int(1 in atoms),sum(z%q==1 and z!=1 for z in atoms))
    self.ck(count[1] in (0,1) and count[2] in (0,q-1))
    self.ck(all(sum(z%q==r for z in atoms) in (0,q) for r in range(2,q)))
    if i:self.ck(all(9+q*k in atoms for k in range(q)))
    self.allowed[ci,i]=set(z%q for z in atoms)
    self.atomcounts[ci,i]=count
    cs.append(tuple(F(n,q*(q-1)) for n in count))
   for ri,(j,t) in enumerate(self.regimes):self.masses[ci,ri]=prod(cs[i][1+t] if i==j else cs[i][0] for i in range(5))
  self.variables=[(ci,ri) for ci in range(80) for ri in range(11) if self.masses[ci,ri]];self.index={x:i for i,x in enumerate(self.variables)}
  self.source=[G*self.w[self.cells[ci][0]]*self.v[self.cells[ci][1]]*self.masses[ci,ri] for ci,ri in self.variables]
  self.ck(sum(self.source,F(0))/G==F(305684996597,646498195200))
  self.C=list(map(F,js[2]['combined512_coefficients']))
  for i,q in enumerate(Q):
   if i:self.C[256+(1<<i)]+=G*F(1,q*(q-2))
  self.ck(len(self.C)==512 and min(self.C)>=0)
  def axis(weights,level,block,deep,weak,gamma):
   live=[i for i,t in enumerate(weights) if t]
   if level==0:return [(0,weights)]
   if level==1:return [(r,[v if i//block==r else F(0) for i,v in enumerate(weights)]) for r in range(len(weights)//block)]
   if level==2:return [(r,[v if i==r else F(0) for i,v in enumerate(weights)]) for r in live]
   return [(r,[deep*(gamma if r==weak else 1) if i==r else F(0) for i in range(len(weights))]) for r in live]
  self.selectors=[];self.by_mode=[]
  for mode in range(16):
   e3,e5=divmod(mode,4);ids=[]
   for (a,x),(b,y) in product(axis(self.w,e3,3,F(1),4,F(81,82)),axis(self.v,e5,5,F(4,5),10,F(1875,1876))):
    ids.append(len(self.selectors));self.selectors.append((mode,a,b,{ci:x[l]*y[m] for ci,(l,m) in enumerate(self.cells) if x[l]*y[m]}))
   self.by_mode.append(ids)
  self.ck(len(self.selectors)==559)
  # -1 whole;0 root1;1 special-deep;>=2 literal nonroot first root.
  self.queries=[];self.by_T=[[] for T in range(32)];self.hrows=[]
  for choices in product((-1,0,2,3,4,5,6,1),*((-1,0,9,1),)*4):
   if sum(x in (0,1) for x in choices)>1:continue
   T=sum(1<<i for i,x in enumerate(choices) if x!=-1);h={}
   for ci,ri in self.variables:
    j,t=self.regimes[ri];v=F(1)
    for i,q in enumerate(Q):
     typ=1+t if i==j else 0;choice=choices[i];count=self.atomcounts[ci,i][typ]
     if choice==-1:factor=F(count,q*(q-1))
     elif choice==0:factor=F(count,q) if typ else F(0)
     elif choice==1:factor=F(q-2,q-1) if typ==1 and count else F(0)
     else:factor=F(int(typ==0 and choice in self.allowed[ci,i]))
     v*=factor
     if not v:break
    if v:h[self.index[ci,ri]]=v
   if h:
    self.by_T[T].append(len(self.queries));self.queries.append((T,choices));self.hrows.append(h)
  self.addresses=[];self.by_group=[[] for i in range(512)];self.nnz=0
  for si,(mode,a,b,central) in enumerate(self.selectors):
   for qi,(T,choices) in enumerate(self.queries):
    support=[idx for idx in self.hrows[qi] if self.variables[idx][0] in central]
    if support:
     ai=len(self.addresses);self.addresses.append((si,qi));self.by_group[32*mode+T].append(ai);self.nnz+=len(support)
 def ck(self,v):
  self.checks+=1
  if not v:raise ValueError('check '+str(self.checks))
 def row(self,ai):
  si,qi=self.addresses[ai];central=self.selectors[si][3]
  return {i:h*central[ci] for i,h in self.hrows[qi].items() if (ci:=self.variables[i][0]) in central}
 def group(self,ai):
  si,qi=self.addresses[ai];return 32*self.selectors[si][0]+self.queries[qi][0]
 def measure(self):
  return dict(schema='clustered109-eleven-regime-v1',source_sha256=self.pins,checks=self.checks,actual_source_mass=str(sum(self.source,F(0))/G),active_variables=len(self.variables),active_regimes_by_cell=[sum((ci,ri) in self.index for ri in range(11)) for ci in range(80)],possible_regimes=11,raw_variable_addresses=880,central_selectors=len(self.selectors),outside_queried_menus=[7,3,3,3,3],outside_global_query_tuples=len(self.queries),nonzero_literal_rows=len(self.addresses),matrix_nonzero_entries=self.nnz,fee_groups=512,nonempty_fee_groups=sum(bool(x) for x in self.by_group),prior_target='193/100000',full_mode8=True,scope='Fixed109 actual source; regime field only. Exact menu/count model; no optimization verdict.')
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--base',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--witness',type=Path,default=Path(__file__).with_name('clustered11_regime_dual.json'));ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'));a=ap.parse_args()
 m=Model(a.base);raw=a.witness.read_bytes();j=json.loads(raw);m.ck(j['schema']=='clustered109-eleven-regime-dual-v1');m.ck(j['source_sha256']==m.pins)
 D=j['denominator'];m.ck(isinstance(D,int) and D>0)
 sel={(mode,left,right):si for si,(mode,left,right,row) in enumerate(m.selectors)};queries={choices:qi for qi,(T,choices) in enumerate(m.queries)};addresses={pair:ai for ai,pair in enumerate(m.addresses)}
 residual=m.source[:];loads=[F(0)]*512;seen=set()
 for r in j['rows']:
  N=r['numerator'];central=(r['mode'],r['left'],r['right']);choices=tuple(r['outside_choices']);T=r['support']
  m.ck(isinstance(N,int) and N>0);m.ck(central in sel and choices in queries)
  si,qi=sel[central],queries[choices];m.ck(m.queries[qi][0]==T);m.ck((si,qi) in addresses)
  key=(si,qi);m.ck(key not in seen);seen.add(key);ai=addresses[key];lam=F(N,D);loads[m.group(ai)]+=lam
  for idx,v in m.row(ai).items():residual[idx]-=lam*v
 for i in range(512):m.ck(loads[i]<=m.C[i])
 upper=sum((max(F(0),r) for r in residual),F(0));ex=j['expected']
 m.ck(len(m.variables)==ex['active_variables']==419);m.ck(len(m.queries)==ex['query_tuples']==512);m.ck(len(m.addresses)==ex['literal_rows']==135584)
 m.ck(sum(m.source,F(0))/G==F(ex['source_mass']));m.ck(len(seen)==ex['dual_rows']==700);m.ck(upper==F(ex['upper']))
 m.ck(F(0)<upper<F(1,10**12)<F(ex['target'])==F(193,100000));m.ck(sum(r>0 for r in residual)==ex['positive_residual_count'])
 m.ck(len(j['residuals'])==len(m.variables))
 for (ci,ri),r,claimed in zip(m.variables,residual,j['residuals']):m.ck(claimed['cell']==list(m.cells[ci]) and claimed['regime']==list(m.regimes[ri]) and F(claimed['residual'])==r)
 result=dict(schema='clustered109-eleven-regime-dual-verification-v1',status='PASS',optimizer_used=False,new_lean_verification=False,program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),witness_sha256=sha256(raw).hexdigest(),source_sha256=m.pins,checks=m.checks,active_variables=len(m.variables),global_query_tuples=len(m.queries),complete_literal_rows=len(m.addresses),response_nonzero_entries=m.nnz,dual_rows=len(seen),upper=str(upper),target='193/100000',positive_rounding_residuals=sum(r>0 for r in residual),full_mode8=True,scope=j['scope'],residuals=[dict(cell=list(m.cells[ci]),regime=list(m.regimes[ri]),residual=str(r)) for (ci,ri),r in zip(m.variables,residual)])
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('residuals','source_sha256')},indent=2))
