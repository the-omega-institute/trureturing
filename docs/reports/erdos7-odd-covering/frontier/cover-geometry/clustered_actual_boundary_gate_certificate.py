#!/usr/bin/env python3
"""Exact same-source separation of generic and actual central deep caps.

Uses fixed numerical witnesses only; no optimizer, floating-point decisions,
randomness, or new Lean verification. All query roots, central selectors and
complete nonnegative charges remain explicit.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from hashlib import sha256
import argparse,json
P=argparse.ArgumentParser(description=__doc__)
P.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
P.add_argument('--output',type=Path)
args=P.parse_args(); checks={}
def ck(name,value):
 if not value:raise ArithmeticError(name)
 checks[name]=checks.get(name,0)+1
WNAME='clustered_actual_boundary_gate_witness.json'
WRAW=(args.directory/WNAME).read_bytes();W=json.loads(WRAW)
inputs={}
for name,pin in W['source_sha256'].items():
 raw=(args.directory/name).read_bytes();ck('input_pin',sha256(raw).hexdigest()==pin);inputs[name]=json.loads(raw)
S=inputs['clustered_exact_actual_source.json']; old=inputs['remaining33_global_root_exclusion_certificate.json']
ck('source_fixture_pin',S['source_fixture_sha256']==W['source_sha256']['clustered_global_phase_fixture.json'])
Q=(7,11,13,17,19);I=(0,1,2,4,5);J=tuple(m for m in range(20)if m!=5)
coords=tuple((l,m)for l,m in product(I,J)if not(l<3 and m<5));ck('coordinates',coords==tuple(map(tuple,W['coordinates'])))
ck('one_corner',W['corner']==[4,10]);i,j=W['corner']; n=len(coords)
H={tuple(v['cell']):v['H_by_support_and_root7']for v in S['cells']}
ck('all_actual_cells',set(H)==set(coords))
for c in coords:
 ck('all_supports',len(H[c])==32)
 for T,row in enumerate(H[c]):
  ck('query_roots',len(row)==(6 if T&1 else 1))
  H[c][T]=list(map(F,row));ck('nonnegative_response',min(H[c][T])>=0)
C=list(map(F,old['combined512_coefficients']));g=F(200163067,201247200)
ck('complete_coefficients',len(C)==512 and min(C)>=0 and F(old['constants']['g'])==g)
for u,q in enumerate(Q):
 if u:C[32*9+(1<<u)]+=g*F(1,q*(q-2))
choices3=((0,),tuple(range(2)),I,I);choices5=((0,),tuple(range(4)),J,J)
def selector(mode,a,b,actual):
 ex,ey=divmod(mode,4)
 ck('selector_left_legal',a in choices3[ex]);ck('selector_right_legal',b in choices5[ey])
 out=[]
 for l,m in coords:
  x=2*(1 if l==i else 2);y=3 if m==j else 4
  if ex==1:x*=int(l//3==a)
  if ex==2:x*=int(l==a)
  if ex==3:x=(9 if actual and l==i else 18)*int(l==a)
  if ey==1:y*=int(m//5==b)
  if ey==2:y*=int(m==b)
  if ey==3:y=(45 if actual and m==j else 60)*int(m==b)
  out.append(x*y)
 return out
menus={actual:[[(a,b,selector(4*ex+ey,a,b,actual))for a,b in product(choices3[ex],choices5[ey])]for ex,ey in product(range(4),repeat=2)]for actual in(False,True)}
ck('all_literal_selectors',sum(map(len,menus[False]))==559 and sum(map(len,menus[True]))==559)
def response(c,T,k):return H[c][T][k-1 if T&1 else 0]
def coefficients(mode,T,a,b,k,actual):
 ck('fixed_root7_legal',k in range(1,7))
 vec=selector(mode,a,b,actual)
 return [F(v,1350)*response(c,T,k)for c,v in zip(coords,vec)]
source=[g*F((1 if l==i else 2)*(3 if m==j else 4),675)*H[l,m][0][0]for l,m in coords]
source_mass=sum(source,F())/g;ck('source_mass',source_mass==F(W['expected']['source_mass']))
# Every dual group is a convex combination of legitimate complete generic queries.
D=W['dual_denominator']; ck('positive_dual_denominator',isinstance(D,int)and D>0)
ck('all_nonzero_dual_groups',{int(k)for k in W['generic_dual']}=={k for k,c in enumerate(C)if c})
residual=source[:]; terms=0
for group,rows in W['generic_dual'].items():
 group=int(group);mode,T=divmod(group,32)
 ck('dual_partition',sum(t['numerator']for t in rows)==D)
 for term in rows:
  a,b,k=term['left'],term['right'],term['root7'];v=term['numerator']
  ck('dual_weight_nonnegative',isinstance(v,int)and v>=0)
  lam=C[group]*F(v,D);vec=coefficients(mode,T,a,b,k,False)
  for h,z in enumerate(vec):residual[h]-=lam*z
  terms+=1
upper=sum((max(v,F())for v in residual),F())
ck('generic_upper_reproduced',upper==F(W['expected']['generic_upper']))
ck('generic_cannot_pay',upper<F(193,100000))
# Positive field is checked against every literal central selector and all SIX
# fixed query roots at7. No pointwise query-root selection is permitted.
TD=W['field_denominator']; nums=W['field_numerators']
ck('field_size',len(nums)==n and TD==12)
for v in nums:ck('field_range',isinstance(v,int)and 0<=v<=TD)
theta=list(F(v,TD)for v in nums)
gate=sum((v*t for v,t in zip(source,theta)),F());unit=sum(source,F()); charged=[]; screens=0
for mode,menu in enumerate(menus[True]):
 for T in range(32):
  group=32*mode+T
  if not C[group]:continue
  best=F();bestunit=F()
  for a,b,vec in menu:
   for k in (range(1,7)if T&1 else(1,)):
    qvec=[F(v,1350)*response(c,T,k)for c,v in zip(coords,vec)]
    value=sum((v*t for v,t in zip(qvec,theta)),F());un=sum(qvec,F())
    best=max(best,value);bestunit=max(bestunit,un);screens+=1
    ck('full_nonnegative_screen',value>=0)
  fee=C[group]*best;gate-=fee;unit-=C[group]*bestunit;charged.append(str(fee))
ck('positive_gate_reproduced',gate==F(W['expected']['actual_positive_gate']))
ck('positive_gate_pays',gate>F(193,100000))
ck('unit_gate_reproduced',unit==F(W['expected']['unit_gate']))
Ds=[F(5,6)]+[F(q-2,q-1)-F(2,q*(q-2))for q in Q[1:]];Dall=prod(Ds,start=F(1));scaled=Dall*gate
ck('factor_masses_bounded',all(0<v<1 for v in Ds))
ck('thinned_gate_pays',scaled>F(193,100000))
out=dict(schema='clustered-same-law-boundary-gate-certificate-v1',status='PASS',new_lean_verification=False,scope='Fixed101-original fixture, same exact outside law and complete512charges. Generic deep-cap gate upper for every cell field in[0,1]; actual uniform-in-leaf positive denominator12 field at one corner. No arbitrary central higher-pure or95-corner transfer; no unrestricted covering conclusion.',source_sha256=W['source_sha256'],witness_sha256=sha256(WRAW).hexdigest(),program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),corner=W['corner'],source_mass=str(source_mass),generic_field_universal_upper=str(upper),actual_field_gate=str(gate),actual_field_gate_decimal=float(gate),actual_unit_gate=str(unit),field_denominator=TD,generic_dual_terms=terms,complete_actual_query_screens=screens,uniform_factor_thinning=list(map(str,Ds)),uniform_thinning_product=str(Dall),thinned_gate=str(scaled),thinned_gate_decimal=float(scaled),checks=checks,check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k not in('source_sha256','checks')}),flush=True)
