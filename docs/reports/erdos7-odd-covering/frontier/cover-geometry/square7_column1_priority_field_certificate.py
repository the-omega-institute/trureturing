#!/usr/bin/env python3
"""Exact whole-family certificate for square7 roles (1,1,5).

All ten 9qs roles are fixed at leaf5. All95 fields share exact priority
constraints and every charged selector menu is retained. No new Lean result.
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
FIELD_DENOMINATOR=1048576
FIELD_NUMERATORS=(690045, 969640, 754475, 697470, 697472, 969640, 1005988, 1005988, 969640, 969640, 830037, 915018, 858184, 969640, 828739, 816302, 985715, 815977, 838411, 969640, 736433, 1048575, 811330, 746438, 746434, 1048575, 1048575, 1048575, 1048575, 1048576, 894197, 940788, 921968, 1048575, 894411, 877675, 1014925, 877902, 900581, 1048576, 697467, 673145, 673146, 969640, 969640, 935827, 935827, 889163, 824926, 935827, 800456, 948189, 787518, 808961, 935827, 601171, 901232, 702486, 615781, 616016, 850720, 882609, 882631, 850720, 850721, 711495, 847530, 731198, 850720, 712252, 706252, 882631, 706237, 723309, 850721, 736433, 1048575, 811330, 746438, 746492, 1048575, 1048576, 1048576, 1048575, 1048576, 894197, 940788, 922267, 1048575, 894411, 877906, 1014925, 877902, 900715, 1048576, 616148, 594606, 594653, 850721, 850721, 821054, 821055, 822531, 706396, 821054, 688181, 850721, 681658, 698100, 821055, 536403, 633557, 555361, 487929, 530398, 633557, 722340, 827264, 641866, 654329, 492679, 650823, 494939, 641866, 499587, 589349, 698556, 586566, 599825, 654329, 547691, 737801, 399575, 445846, 583576, 737801, 740502, 740502, 673189, 717216, 590865, 688489, 577306, 739772, 595972, 654517, 733357, 640158, 655039, 717216, 697467, 673425, 673146, 969640, 969640, 935827, 935827, 889163, 824926, 935827, 800456, 948189, 787518, 808961, 935827, 562340, 548819, 343227, 592600, 592600, 513815, 505030, 490463, 463827, 548819, 462541, 532641, 422433, 422995, 505030)

ck('new_field_shape',len(FIELD_NUMERATORS)==len(KEYS)==180)
for n in FIELD_NUMERATORS:ck('new_field_bounds',isinstance(n,int)and 0<=n<=FIELD_DENOMINATOR)
for i,j in product(I,J):
 for l,m in LIVE:
  n=FIELD_NUMERATORS[IX[orbit(i,j,l,m)]]
  ck('new_field_ternary_priority',n<=FIELD_NUMERATORS[IX[orbit(l,j,l,m)]])
  ck('new_field_quinary_priority',n<=FIELD_NUMERATORS[IX[orbit(i,m,l,m)]])
# All ten original9qs roles share leaf5; square7 roles are (row1,column1,leaf5).
H=[]
for T in range(32):
 ht=[]
 for l in I:
  for activecol in range(2):
   n=int(l//3==1)+int(l==5)+activecol
   Z=[F(5,6)-F(n,35)if u==0 else F(q-2,q-1)-2*a[u]for u,q in enumerate(Q)]
   beta=[b[e]+inc[e]*int(l==5)for e in range(10)]
   zprod=lambda M:prod((Z[u]for u in range(5)if not M>>u&1),start=F(1))
   h=zprod(T)-sum((beta[e]*zprod(T|EM[e])for e in range(10)if not T&EM[e]),F())+sum((beta[e]*beta[f]*zprod(T|EM[e]|EM[f])for e,f in PAIRS if not T&(EM[e]|EM[f])),F())
   ck('positive_response',0<h<=1);ht.append(h)
 H.append(ht)
DH=lcm(*(v.denominator for h in H for v in h));HI=[[int(v*DH)for v in h]for h in H]
records=[];den=FIELD_DENOMINATOR;nums=FIELD_NUMERATORS
for i,j in product(I,J):
 x=[0 if l==3 else 1 if l==i else 2 for l in range(6)];y=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
 MX=[[x],[[x[l]if l//3==k else 0 for l in range(6)]for k in range(2)],[[x[l]if l==k else 0 for l in range(6)]for k in I],[[9 if l==k else 0 for l in range(6)]for k in I]]
 MY=[[y],[[y[m]if m//5==k else 0 for m in range(20)]for k in range(4)],[[y[m]if m==k else 0 for m in range(20)]for k in J],[[60 if m==k else 0 for m in range(20)]for k in J]]
 menus=[]
 for m3,m5 in product(range(4),repeat=2):
  vecs=[]
  for xx in MX[m3]:
   for yy in MY[m5]:
    coeff=[0]*10
    for l,m in LIVE:coeff[2*I.index(l)+int(m//5==1)]+=xx[l]*yy[m]*nums[IX[orbit(i,j,l,m)]]
    vecs.append(coeff)
  menus.append(vecs)
 ck('all_literal_selectors',sum(map(len,menus))==559)
 mass=sum(v*h for v,h in zip(menus[0][0],HI[0]));fees=0
 for mode in range(16):
  for T in range(32):
   maximum=max(sum(v*h for v,h in zip(sel,HI[T]))for sel in menus[mode])
   fees+=CI[32*mode+T]*maximum;ck('literal_full_selector_maximum',maximum>=0)
 gate=F(GI*mass-fees,DC*675*den*DH)
 ck('complete_positive_corner',gate>F(193,100000))
 records.append(dict(weak3=i,weak5=j,gate=str(gate)))
minimum=min(records,key=lambda row:F(row['gate']));gate=F(minimum['gate'])
network_name='joint_square_pair_225_star_certificate.json';network_pin='cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5'
raw=(args.directory/network_name).read_bytes();ck('network_pin',sha256(raw).hexdigest()==network_pin);network=json.loads(raw)
alpha=F(network['projection_alpha']);policies=[]
for p in network['policies']:
 fee=F(network['finite_fee_upper'])+F(network['complete_five_parent_tail'])+F(network['ordinary_typeI_fee'])+F(p['fee'])
 margin=alpha*(gate-fee);ck('complete_network_density',margin>F(1,2000000))
 policies.append(dict(kind=p['kind'],K=p['K'],complete_fee=str(fee),projected_margin=str(margin),density_denominator=2000000))
out=dict(schema='square7-column1-priority-family-v1',status='PASS',new_lean_verification=False,source_sha256={**pins,network_name:network_pin},producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),square7_roles=[1,1,5],layout=[5]*10,orbit_keys=KEYS,field_denominator=den,field_numerators=nums,corner_count=95,minimum=minimum,uniform_gate='193/100000',corner_gates=records,policies=policies,checks=checks,check_count=sum(checks.values()),scope='One fixed all9qsleaf5 layout, square7 roles row1,column1,leaf5; all remaining665 hypotheses retained. New exact whole95 priority family, not a claim covering arbitrary9qs layouts.')
args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status='PASS',checks=out['check_count'],minimum=minimum,minimum_decimal=float(gate),policy_margins=[float(F(p['projected_margin']))for p in policies]),indent=2))
