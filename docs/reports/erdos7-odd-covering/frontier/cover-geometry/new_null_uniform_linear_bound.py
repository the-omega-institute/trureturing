#!/usr/bin/env python3
"""Uniform all-labelled-layout gate bounds for three actual null geometries.

The source uses its baseline and independently minimized negative edge-linear
terms. Complete fees use monotone zero-activation response uppers. Actual root
selectors and the actual15 mask are retained. No layout enumeration is used;
actual-source interpretation retains one common root table satisfying all fifty
incidences on every actual unmasked cell, including the extra cells.
Continuation composition remains a separate mathematical obligation.
"""
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,lcm
from pathlib import Path
from hashlib import sha256
import argparse,json
P=argparse.ArgumentParser(description=__doc__)
P.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
P.add_argument('--output',type=Path)
args=P.parse_args();checks={}
def ck(name,condition):
 if not condition:raise ArithmeticError(name)
 checks[name]=checks.get(name,0)+1
name='remaining33_global_root_exclusion_certificate.json';pin='dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4'
raw=(args.directory/name).read_bytes();ck('source_pin',sha256(raw).hexdigest()==pin);source=json.loads(raw)
Q=(7,11,13,17,19);E=tuple(combinations(range(5),2));EM=tuple(sum(1<<q for q in e)for e in E);EP=tuple((e,f)for e,f in combinations(range(10),2)if not EM[e]&EM[f])
r=tuple(F(1,q-1)for q in Q);a=tuple(F(1,q*(q-2))for q in Q)
b=tuple(a[u]*r[v]+r[u]*a[v]for u,v in E);d=tuple(r[u]*r[v]for u,v in E)
g=F(200163067,201247200);C=list(map(F,source['combined512_coefficients']))
ck('source_g',g==F(source['constants']['g']));ck('complete_nonnegative_fees',len(C)==512 and min(C)>=0)
for u in range(1,5):C[32*9+(1<<u)]+=g*a[u]
DC=lcm(g.denominator,*(v.denominator for v in C));GI=int(g*DC);CI=[int(v*DC)for v in C];target=F(1,100);nominal_target=F(193,100000)
ck('uniform_floor_pays_nominal_target',target>nominal_target)
# Constant-layout responses depend only on actual activation count and whether
# the current actual ternary leaf is the one shared by all ten9qs originals.
H={}
for n,active in product(range(4),(0,1)):
 Z=tuple(F(5,6)-F(n,35)if u==0 else F(q-2,q-1)-2*a[u]for u,q in enumerate(Q))
 beta=tuple(b[e]+active*d[e]for e in range(10))
 ck('uniform_strict_box',1-sum(beta[e]/(Z[u]*Z[v])for e,(u,v)in enumerate(E))>=F(754111121894423,876550251053789))
 for T in range(32):
  zp=lambda mask:prod((Z[u]for u in range(5)if not mask>>u&1),start=F(1))
  h=zp(T)-sum((beta[e]*zp(T|EM[e])for e in range(10)if not T&EM[e]),F())+sum((beta[e]*beta[f]*zp(T|EM[e]|EM[f])for e,f in EP if not T&(EM[e]|EM[f])),F())
  ck('exact_positive_response',0<h<=1);H[n,active,T]=h
DH=lcm(*(h.denominator for h in H.values()));HI={k:int(h*DH)for k,h in H.items()}

def make_menus(I,J,LIVE,col,i,j):
 x=[0 if l not in I else 1 if l==i else 2 for l in range(6)]
 y=[0 if m not in J else 3 if m==j else 4 for m in range(20)]
 MX=[[x],[[x[l]if l//3==r else 0 for l in range(6)]for r in range(2)],[[x[l]if l==z else 0 for l in range(6)]for z in I],[[9 if l==z else 0 for l in range(6)]for z in I]]
 MY=[[y],[[y[m]if m//5==s else 0 for m in range(20)]for s in range(4)],[[y[m]if m==z else 0 for m in range(20)]for z in J],[[60 if m==z else 0 for m in range(20)]for z in J]]
 menus=[];original_count=0
 for ex,ey in product(range(4),repeat=2):
  originals=[]
  for xx,yy in product(MX[ex],MY[ey]):
   vec=[0]*10
   for l,m in LIVE:vec[2*I.index(l)+int(m//5==col)]+=xx[l]*yy[m]
   originals.append(tuple(vec))
  original_count+=len(originals);unique=sorted(set(originals))
  kept=[u for u in unique if not any(u!=v and all(a<=b for a,b in zip(u,v))for v in unique)]
  for v in kept:ck('retained_selector_original',v in originals)
  for u in originals:ck('exact_selector_domination',any(all(a<=b for a,b in zip(u,v))for v in kept))
  menus.append(kept)
 ck('literal559_selectors',original_count==559);ck('mode0_singleton',len(menus[0])==1)
 return menus

# Source expansion about beta=b. Its pair interactions are nonnegative.
LINEAR={};QUADRATIC={}
for n in range(4):
 Z=tuple(F(5,6)-F(n,35)if u==0 else F(q-2,q-1)-2*a[u]for u,q in enumerate(Q))
 zp=lambda mask:prod((Z[u]for u in range(5)if not mask>>u&1),start=F(1))
 for e in range(10):
  value=-d[e]*zp(EM[e])+sum((d[e]*b[f]*zp(EM[e]|EM[f])for f in range(10)if not EM[e]&EM[f]),F())
  ck('negative_linear_source_coefficient',value<0);LINEAR[n,e]=value
  for T in range(32):
   if T&EM[e]:continue
   # Worst derivative in the activity box is at every other cap b+d.
   derivative=-zp(T|EM[e])+sum(((b[f]+d[f])*zp(T|EM[e]|EM[f])for f in range(10)if not (T|EM[e])&EM[f]),F())
   ck('strict_negative_query_derivative',derivative<0)
 for e,f in EP:
  value=d[e]*d[f]*zp(EM[e]|EM[f]);ck('positive_quadratic_source_coefficient',value>0);QUADRATIC[n,e,f]=value
 for active in(0,1):
  ck('concentrated_expansion_identity',H[n,active,0]==H[n,0,0]+active*sum((LINEAR[n,e]for e in range(10)),F())+active*sum((QUADRATIC[n,e,f]for e,f in EP),F()))
DL=lcm(*(v.denominator for v in LINEAR.values()),DH)
LI={k:int(v*DL)for k,v in LINEAR.items()}
BASE={n:int(H[n,0,0]*DL)for n in range(4)}
geometries=[]
for z3,z5,expected_cells in ((0,5,85),(3,0,83),(0,0,87)):
 I=tuple(l for l in range(6)if l!=z3);J=tuple(m for m in range(20)if m!=z5)
 LIVE=tuple((l,m)for l,m in product(I,J)if not(l<3 and m<5));ck('actual_live_cell_count',len(LIVE)==expected_cells)
 weak5=tuple(min(m for m in J if m//5==s)for s in range(4));multiplicity=tuple(sum(m//5==s for m in J)for s in range(4))
 ck('actual_corner_coverage',sum(multiplicity)*len(I)==95)
 cases=tuple(product(I,weak5));colroles=(0,1,2)if z5==5 else(0,1)
 leafroles=tuple(min(l for l in I if l//3==r)for r in range(2))
 for j in J:
  rep=weak5[j//5];p=lambda m:rep if m==j else j if m==rep else m
  ck('quinary_root_preserving',all(p(m)//5==m//5 for m in J))
  ck('quinary_live_bijection',{(l,p(m))for l,m in LIVE}==set(LIVE))
  for m in J:ck('quinary_weight_transport',(j==m)==(rep==p(m)))
 prep={(col,i,j):make_menus(I,J,LIVE,col,i,j)for col in colroles for i,j in cases}
 roles=[]
 for row,col,ell in product((0,1),colroles,leafroles):
  n=lambda l,m:int(l//3==row)+int(m//5==col)+int(l==ell)
  h=[[HI[int(l//3==row)+activecol+int(l==ell),0,T]for l in I for activecol in(0,1)]for T in range(32)]
  gates=[]
  for i,j in cases:
   x={l:1 if l==i else 2 for l in I};y={m:3 if m==j else 4 for m in J}
   baseline=sum(x[l]*y[m]*BASE[n(l,m)]for l,m in LIVE)
   minima=[];selected=[]
   for e in range(10):
    candidates=[sum(x[l]*y[m]*LI[n(l,m),e]for m in J if(l,m)in LIVE)for l in I]
    at=min(range(len(I)),key=lambda k:candidates[k]);minima.append(candidates[at]);selected.append(I[at])
   masslower=F(baseline+sum(minima),675*DL)
   fees=0;menus=prep[col,i,j]
   for mode,menu in enumerate(menus):
    for T in range(32):
     c=CI[32*mode+T]
     if c:
      screen=max(sum(v*z for v,z in zip(vec,h[T]))for vec in menu)
      fees+=c*screen;ck('full_nonzero_fee_upper_screen',screen>=0)
   feeupper=F(fees,DC*675*DH);gate=g*masslower-feeupper
   ck('uniform_complete_corner_floor',gate>target)
   gates.append(dict(weak_corner=[i,j],source_baseline=str(F(baseline,675*DL)),source_linear_lower=str(masslower),linear_minimizing_layout=selected,complete_fee_upper=str(feeupper),gate_lower=str(gate),gate_lower_decimal=float(gate),above_target=gate>target))
  worst=min(gates,key=lambda x:F(x['gate_lower']))
  roles.append(dict(square7_roles=[row,col,ell],computed_corners=20,represented_corners=95,all_corners_above_target=all(x['above_target']for x in gates),minimum=worst,corners=gates))
 worst=min(roles,key=lambda x:F(x['minimum']['gate_lower']))
 geometries.append(dict(nulls=[z3,z5],actual_I=I,actual_J=J,live_cells=len(LIVE),column_role_representatives=colroles,square_leaf_representatives=leafroles,weak_quinary_representatives=weak5,weak_quinary_multiplicities=multiplicity,role_count=len(roles),all_roles_above_target=all(x['all_corners_above_target']for x in roles),worst_role=worst['square7_roles'],minimum=worst['minimum'],roles=roles))
out=dict(schema='actual-new-null-uniform-linear-source-bound-v1',status='PASS',new_lean_verification=False,scope='Uniform all-labelled-layout lower comparison: source retains baseline plus independently minimized negative edge-linear terms, discards nonnegative pair terms; all fees use zero-activation response uppers. This is a conservative lower bound, not a response identity. An actual-source interpretation requires one common root table satisfying all50 retained incidences on every actual unmasked cell, including those outside the old80-cell support; no unrestricted covering result is claimed.',source_sha256={name:pin},program_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),field='constant_one',target=str(target),nominal_target=str(nominal_target),response_common_denominator=DH,linear_common_denominator=DL,coefficient_common_denominator=DC,geometries=geometries,checks=checks,check_count=sum(checks.values()))
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=out['check_count'],all_pay=all(g['all_roles_above_target']for g in geometries),uniform_floor=str(target),role_count=sum(g['role_count']for g in geometries),geometries=[dict(nulls=g['nulls'],minimum=g['minimum']['gate_lower'],role=g['worst_role'],corner=g['minimum']['weak_corner'])for g in geometries])),flush=True)
