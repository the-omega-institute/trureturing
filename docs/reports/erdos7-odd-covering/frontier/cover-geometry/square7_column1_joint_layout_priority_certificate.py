#!/usr/bin/env python3
"""Exact joint-layout whole-family certificates for square7 roles (1,1,5).

All-leaf4 uses one dyadic180 family; all-regular0 uses the constant-one
family. Each branch checks all95 corners, all559 literal selectors and
all512 charged modes. All outside phases are globally fixed. No Lean result.
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
LEAF4_NUMERATORS=(783202, 1048576, 815688, 783536, 783573, 1048576, 1048576, 1048576, 1048556, 1048572, 869005, 1048576, 898532, 1048556, 872533, 873517, 1040245, 876037, 896378, 1048572, 709988, 955147, 749628, 711780, 711260, 944160, 981036, 981036, 944161, 944172, 797258, 957713, 818607, 954868, 801560, 796789, 975972, 794337, 807127, 990504, 686896, 662105, 661413, 910065, 910543, 878357, 878332, 899211, 757444, 906906, 742981, 910543, 740553, 756169, 892914, 783202, 1048576, 815688, 783536, 783573, 1048576, 1048576, 1048576, 1048556, 1048564, 869005, 1048576, 898532, 1048556, 872533, 873517, 1040245, 876037, 896378, 1048564, 757420, 1007794, 785457, 757091, 757335, 1007794, 1033539, 1033907, 1007791, 1007793, 857410, 957713, 883751, 1007791, 851175, 855808, 1009271, 850756, 880395, 1007793, 729607, 704284, 704308, 971390, 971390, 937508, 937506, 932817, 824496, 937508, 799895, 944314, 796636, 819594, 937506, 421253, 903566, 661648, 536285, 540861, 855961, 616732, 861348, 849664, 860521, 605671, 861348, 578462, 849664, 670403, 642731, 677011, 615786, 594716, 860521, 480475, 813481, 652541, 510586, 503647, 813481, 882598, 882598, 784466, 707701, 628394, 787203, 651770, 784466, 639254, 608694, 649615, 606297, 607421, 707701, 766936, 704284, 704308, 991227, 991227, 937508, 937506, 991227, 824496, 937508, 799895, 944314, 814046, 819594, 937506, 395260, 457514, 443655, 595999, 595999, 540549, 555832, 455040, 508371, 663317, 480353, 453533, 479346, 482414, 630580)

def certify(name,layout,kind,FIELD_NUMERATORS):
 ck('new_field_shape',len(FIELD_NUMERATORS)==len(KEYS)==180)
 for n in FIELD_NUMERATORS:ck('new_field_bounds',isinstance(n,int)and 0<=n<=FIELD_DENOMINATOR)
 for i,j in product(I,J):
  for l,m in LIVE:
   n=FIELD_NUMERATORS[IX[orbit(i,j,l,m)]]
   ck('new_field_ternary_priority',n<=FIELD_NUMERATORS[IX[orbit(l,j,l,m)]])
   ck('new_field_quinary_priority',n<=FIELD_NUMERATORS[IX[orbit(i,m,l,m)]])
 # One globally fixed layout; square7 roles stay (row1,column1,leaf5).
 H=[]
 for T in range(32):
  ht=[]
  for l in I:
   for activecol in range(2):
    n=int(l//3==1)+int(l==5)+activecol
    Z=[F(5,6)-F(n,35)if u==0 else F(q-2,q-1)-2*a[u]for u,q in enumerate(Q)]
    beta=[b[e]+inc[e]*int(l==layout[e])for e in range(10)]
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
 return dict(name=name,layout=layout,field_kind=kind,field_denominator=den,field_numerators=nums,corner_count=95,minimum=minimum,uniform_gate='193/100000',corner_gates=records,policies=policies)

branches=[certify('all_leaf4',(4,)*10,'orbit180',LEAF4_NUMERATORS),certify('all_regular0',(0,)*10,'constant_one',(FIELD_DENOMINATOR,)*180)]
network_name='joint_square_pair_225_star_certificate.json';network_pin='cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5'
out=dict(schema='square7-column1-joint-layout-priority-family-v1',status='PASS',new_lean_verification=False,source_sha256={**pins,network_name:network_pin},producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),square7_roles=[1,1,5],orbit_keys=KEYS,branches=branches,checks=checks,check_count=sum(checks.values()),scope='Two fixed layouts: all9qsleaf4 and all9qsregular0, with square7 roles row1,column1,leaf5 and all remaining665/666 hypotheses. Each branch uses one entire priority95 family. No arbitrary mixed-layout conclusion. Stored policy checks are658 three-parent;666 inherited via193/100000 and unchanged interfaces.')
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=out['check_count'],branches=[dict(name=p['name'],minimum=p['minimum'],minimum_decimal=float(F(p['minimum']['gate'])))for p in branches]),indent=2))
