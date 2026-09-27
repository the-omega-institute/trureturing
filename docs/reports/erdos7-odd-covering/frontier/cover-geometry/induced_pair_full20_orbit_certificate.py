#!/usr/bin/env python3
"""Reconstruct the full20 gate from640 using literal menus and source orbits."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from math import prod
from hashlib import sha256
import json,time
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=Path(__file__).with_name('remaining33_global_root_exclusion_certificate.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
start=time.monotonic()
raw=args.source.read_bytes();old=json.loads(raw)
def ck(ok):
 if not ok:raise ArithmeticError('independent exact gate assertion')
Q=(7,11,13,17,19);g=F(old['constants']['g']);alpha=F(old['constants']['alpha']);C=list(map(F,old['combined512_coefficients']))
for i,q in enumerate(Q):
 if q!=7:C[32*9+(1<<i)]+=g/F(q*(q-2))
a=[F(1,q*(q-2))for q in Q];r=[F(1,q-1)for q in Q]
Z=[F(q-2,q-1)-(2*a[i]if i else 0)for i,q in enumerate(Q)]
H=[]
for T in range(32):
 vals=[]
 for n in (0,1,2,3):
  z=Z.copy();z[0]-=F(n,35);U=[i for i in range(5)if not T>>i&1]
  vals.append(prod(z[i]for i in U)-sum(((a[i]*r[j]+r[i]*a[j])*prod(z[k]for k in U if k not in (i,j))for i,j in combinations(U,2)),F()))
 ck(min(vals)>0)
 ck(vals[2]==2*vals[1]-vals[0] and vals[3]==3*vals[1]-2*vals[0])
 H.append((vals[0],vals[0]-vals[1]))
THREE=((0,1),(0,3),(3,4),(3,0));FIVE=((0,1),(0,5),(5,6),(5,0),(5,10))
records=[];allreadings=0;literal=0;minval=None;minwit=None
for k3,(z,w)in enumerate(THREE):
 x=[0 if i==z else 1 if i==w else 2 for i in range(6)]
 sx=[[x],[[x[i]if i//3==a else 0 for i in range(6)]for a in range(2)],[[x[i]if i==a else 0 for i in range(6)]for a in range(6)if x[a]],[[9 if i==a else 0 for i in range(6)]for a in range(6)if x[a]]]
 for k5,(zz,ww)in enumerate(FIVE):
  y=[0 if i==zz else 3 if i==ww else 4 for i in range(20)]
  sy=[[y],[[y[i]if i//5==a else 0 for i in range(20)]for a in range(4)],[[y[i]if i==a else 0 for i in range(20)]for a in range(20)if y[a]],[[60 if i==a else 0 for i in range(20)]for a in range(20)if y[a]]]
  forms=[]
  for mode in range(16):
   terms=[]
   for xx in sx[mode//4]:
    for yy in sy[mode%4]:
     b=sum(xx[l]*yy[m]for l in range(6)for m in range(20)if not(l<3 and m<5))
     ds=[sum(xx[l]*yy[m]*((l//3==rr)+(m//5==ss)+(l==ll))for l in range(6)for m in range(20)if not(l<3 and m<5))for rr,ss,ll in product(range(2),range(4),range(6))]
     terms.append((b,ds))
   forms.append(terms)
  case_min=None;cw=None
  for layout in range(48):
   pairs=[set((b,ds[layout])for b,ds in ts)for ts in forms]
   b,d=next(iter(pairs[0]));gate=g*(H[0][0]*b-H[0][1]*d)/675
   for mode in range(16):
    for T,(h0,hn)in enumerate(H):
     gate-=C[32*mode+T]*max(h0*b-hn*d for b,d in pairs[mode])/675
     allreadings+=1
   if case_min is None or gate<case_min:case_min=gate;cw=layout
   if minval is None or gate<minval:minval=gate;minwit=[z,w,zz,ww,layout]
  multiplicity=(6,9,6,9)[k3]*(20,75,60,75,150)[k5]
  literal+=multiplicity*48
  records.append(dict(corner=[z,w,zz,ww],multiplicity=multiplicity,minimum=str(case_min),layout=cw))
ck(literal==547200 and allreadings==20*48*512)
expected=F(203129722400814193208791597,20692505911553620784640000000)
ck(minval==expected)
out=dict(producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),status='PASS',minimum=str(minval),witness=minwit,source_sha256=sha256(raw).hexdigest(),independent_orbit_cases=20,layouts_per_case=48,literal_layout_corner_addresses=literal,complete512_readings=allreadings,minimum_induced_response=str(min(h0-3*hn for h0,hn in H)),records=records,candidate_producer_read=False,candidate_data_read=False,new_lean_verification=False,elapsed=time.monotonic()-start)
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='records'},indent=2))
