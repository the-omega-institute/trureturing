#!/usr/bin/env python3
"""Exact one-corner tests of the four existing fields under changed square7 roles.

This refutes direct reuse of these four witnesses in the tested configurations;
it makes no optimality claim over other fields or survivor sources.
"""
from fractions import Fraction as F
from itertools import combinations,product
from math import prod,lcm
from pathlib import Path
from hashlib import sha256
import json,argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args();checks={}
def ck(k,b):
 if not b:raise ArithmeticError(k)
 checks[k]=checks.get(k,0)+1
pins={'remaining33_global_root_exclusion_certificate.json':'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','binary_leaf_pair_library_certificate.json':'4f64080de7056488b7299992ce8da2b7615410e8ddccc597ade50b323bff470d'}
d={}
for name,pin in pins.items():
 raw=(args.directory/name).read_bytes();ck('source_pin',sha256(raw).hexdigest()==pin);d[name]=json.loads(raw)
source=d['remaining33_global_root_exclusion_certificate.json'];fields=d['binary_leaf_pair_library_certificate.json']
Q=(7,11,13,17,19);I=(0,1,2,4,5);J=tuple(m for m in range(20)if m!=5);LIVE=tuple((l,m)for l,m in product(I,J)if not(l<3 and m<5))
E=tuple(combinations(range(5),2));EM=tuple(sum(1<<u for u in e)for e in E);PAIRS=tuple((e,f)for e,f in combinations(range(10),2)if not EM[e]&EM[f])
r=[F(1,q-1)for q in Q];a=[F(1,q*(q-2))for q in Q];b=[a[u]*r[v]+r[u]*a[v]for u,v in E];inc=[r[u]*r[v]for u,v in E]
g=F(200163067,201247200);C=list(map(F,source['combined512_coefficients']))
for u in range(1,5):C[32*9+(1<<u)]+=g*a[u]
DC=lcm(g.denominator,*(v.denominator for v in C));GI=int(g*DC);CI=[int(v*DC)for v in C]
def orbit(i,j,l,m):return('r'if i<3 else str(i),('eq'if i==l else'other')if i<3 and l<3 else'r'if l<3 else str(l),j//5,m//5,j==m)
KEYS=sorted({orbit(i,j,l,m)for i,j in product(I,J)for l,m in LIVE});IX={v:k for k,v in enumerate(KEYS)}
ck('field_orbits',fields['orbit_keys']==[list(x)for x in KEYS])
# One globally fixed original layout: all ten9qs roles at leaf5.
configs=[('baseline',1,2,5,False),('column1',1,1,5,False),('row0_column1',0,1,5,False),('uniform_unary',1,2,5,True)]
weak=(4,15);rows=[]
for name,row,col,leaf,uniform in configs:
 H=[]
 for T in range(32):
  ht=[]
  for l in I:
   for activecol in range(2):
    n=3 if uniform else int(l//3==row)+int(l==leaf)+activecol
    Z=[F(5,6)-F(n,35)if u==0 else F(q-2,q-1)-2*a[u]for u,q in enumerate(Q)]
    beta=[b[e]+inc[e]*int(l==5)for e in range(10)]
    zprod=lambda M:prod((Z[u]for u in range(5)if not M>>u&1),start=F(1))
    h=zprod(T)-sum((beta[e]*zprod(T|EM[e])for e in range(10)if not T&EM[e]),F())+sum((beta[e]*beta[f]*zprod(T|EM[e]|EM[f])for e,f in PAIRS if not T&(EM[e]|EM[f])),F())
    ck('positive_response',0<h<=1);ht.append(h)
  H.append(ht)
 DH=lcm(*(v.denominator for h in H for v in h));HI=[[int(v*DH)for v in h]for h in H]
 case=[]
 for fi,f in enumerate(fields['families']):
  den=f['denominator'];nums=f['numerators'];i,j=weak
  x=[0 if l==3 else 1 if l==i else 2 for l in range(6)];y=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
  MX=[[x],[[x[l]if l//3==k else 0 for l in range(6)]for k in range(2)],[[x[l]if l==k else 0 for l in range(6)]for k in I],[[9 if l==k else 0 for l in range(6)]for k in I]]
  MY=[[y],[[y[m]if m//5==k else 0 for m in range(20)]for k in range(4)],[[y[m]if m==k else 0 for m in range(20)]for k in J],[[60 if m==k else 0 for m in range(20)]for k in J]]
  menus=[]
  for m3,m5 in product(range(4),repeat=2):
   vecs=[]
   for xx in MX[m3]:
    for yy in MY[m5]:
     coeff=[0]*10
     for l,m in LIVE:coeff[2*I.index(l)+int(m//5==col)]+=xx[l]*yy[m]*nums[IX[orbit(i,j,l,m)]]
     vecs.append(coeff)
   menus.append(vecs)
  ck('all_literal_selectors',sum(map(len,menus))==559)
  mass=sum(v*h for v,h in zip(menus[0][0],HI[0]));fees=0
  for mode in range(16):
   for T in range(32):
    maximum=max(sum(v*h for v,h in zip(sel,HI[T]))for sel in menus[mode])
    fees+=CI[32*mode+T]*maximum;ck('literal_full_selector_maximum',maximum>=0)
  gate=F(GI*mass-fees,DC*675*den*DH)
  case.append(dict(family=fi,gate=str(gate),gate_decimal=float(gate)))
 if name!='baseline':ck('all_four_existing_fields_negative',max(F(z['gate'])for z in case)<0)
 else:ck('baseline_family0_pays',F(case[0]['gate'])>F(193,100000))
 rows.append(dict(name=name,row=row,column=col,leaf=leaf,uniform_unary=uniform,weak_corner=weak,family_gates=case))
out=dict(schema='square7-small-exact-gate-v1',status='PASS',new_lean_verification=False,source_sha256=pins,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),layout=[5]*10,rows=rows,checks=checks,check_count=sum(checks.values()),scope='One fixed weak corner suffices to rule out each of four supplied whole families in each changed configuration. No claim about the optimum over other fields, all sources or actual covering.')
args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'PASS','checks':out['check_count'],'rows':[{ 'name':r['name'],'best_at_corner':max(z['gate_decimal']for z in r['family_gates'])}for r in rows]},indent=2))
