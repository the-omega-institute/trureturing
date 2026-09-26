#!/usr/bin/env python3
"""Prepare exact integer intervals for all five live leaf roles.

The 5**10 layouts assign each of the ten 9qs central roles to one of five
live leaves. Simultaneous permutations of the three regular leaves leave
1,657,470 canonical layouts. Each layout selects one entire priority95
family, used for every corner and query. Pinned certificates 640 and 658
supply the exact gate coefficients; two explicit whole95 fields supply the boundary weights.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
from math import prod,lcm
from hashlib import sha256
from collections import Counter
import struct
import argparse,json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
parser.add_argument('--output',type=Path)
parser.set_defaults(column=1)

args=parser.parse_args();checks=Counter()
def ck(name,value):
 if not value:raise ArithmeticError(name)
 checks[name]+=1
PINS={'remaining33_global_root_exclusion_certificate.json':'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','joint_square_pair_225_star_certificate.json':'cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5'}
sources={}
for name,pin in PINS.items():
 raw=(args.directory/name).read_bytes();ck('source_pin',sha256(raw).hexdigest()==pin);sources[name]=json.loads(raw)
base=sources['remaining33_global_root_exclusion_certificate.json'];network=sources['joint_square_pair_225_star_certificate.json']
Q=(7,11,13,17,19);I=(0,1,2,4,5);J=tuple(m for m in range(20)if m!=5)
CELLS=tuple(product(range(6),range(20)));LIVE=tuple((l,m)for l,m in product(I,J)if not(l<3 and m<5));CASES=tuple(product(I,(0,6,10,15)))
EDGES=tuple(combinations(range(5),2));EM=tuple(sum(1<<q for q in e)for e in EDGES);PAIRS=tuple((e,f)for e,f in combinations(range(10),2)if not EM[e]&EM[f])
g=F(200163067,201247200);r=tuple(F(1,q-1)for q in Q);a=tuple(F(1,q*(q-2))for q in Q)
B0=tuple(a[u]*r[v]+r[u]*a[v]for u,v in EDGES);B1=tuple(r[u]*r[v]for u,v in EDGES)
C=list(map(F,base['combined512_coefficients']));ck('complete512_nonnegative',len(C)==512 and min(C)>=0)
ck('same_unit_gate_coefficient',g==F(base['constants']['g'])==F(network['g']))
for u in range(1,5):C[32*9+(1<<u)]+=g*a[u]
DC=lcm(g.denominator,*(x.denominator for x in C));GI=int(g*DC);CI=[int(x*DC)for x in C]

# Exact matching polynomial coefficients for four unary profiles.
polys={}
for n in range(4):
 Z=tuple(F(5,6)-F(n,35)if q==7 else F(q-2,q-1)-2*a[u]for u,q in enumerate(Q))
 ck('uniform_strict_shearer_box',1-sum((B0[e]+B1[e])/(Z[u]*Z[v])for e,(u,v)in enumerate(EDGES))>=F(754111121894423,876550251053789))
 for T in range(32):
  def zprod(mask):return prod((Z[u]for u in range(5)if not mask>>u&1),start=F(1))
  es=[e for e in range(10)if not T&EM[e]];ps=[(e,f)for e,f in PAIRS if not T&(EM[e]|EM[f])]
  b=zprod(T)-sum((B0[e]*zprod(T|EM[e])for e in es),F())+sum((B0[e]*B0[f]*zprod(T|EM[e]|EM[f])for e,f in ps),F())
  us=[F()]*10
  for e in es:us[e]=-B1[e]*zprod(T|EM[e])+sum((B1[e]*B0[f]*zprod(T|EM[e]|EM[f])for f in es if not EM[e]&EM[f]),F())
  vs=[B1[e]*B1[f]*zprod(T|EM[e]|EM[f])if(e,f)in ps else F()for e,f in PAIRS]
  polys[n,T]=(b,us,vs)
DH=lcm(*(x.denominator for b,us,vs in polys.values()for x in[b]+us+vs))
responses={}
for(n,T),(b,us,vs)in polys.items():
 bi=int(b*DH);ui=[int(x*DH)for x in us];vi=[int(x*DH)for x in vs]
 for mask in range(1024):
  value=bi+sum(ui[e]for e in range(10)if mask>>e&1)+sum(v for(e,f),v in zip(PAIRS,vi)if mask>>e&1 and mask>>f&1)
  ck('all_local_subset_responses_positive',value>0);responses[n,T,mask]=value

def orbit(i,j,l,m):return('r'if i<3 else str(i),('eq'if i==l else'other')if i<3 and l<3 else'r'if l<3 else str(l),j//5,m//5,j==m)
KEYS=sorted({orbit(i,j,l,m)for i,j in product(I,J)for l,m in LIVE});INDEX={key:k for k,key in enumerate(KEYS)}
ck('orbit_count',len(KEYS)==180)
def profile(l,m):return 2*I.index(l)+int(m//5==args.column)

# The second field is one simultaneous whole95 family, fixed for all layouts.
OPTIMIZED_NUMERATORS=(702997, 972070, 755492, 708224, 708143, 972070, 1007200, 1007200, 972070, 972070, 855235, 924150, 886806, 972070, 855223, 820723, 1006477, 820712, 843418, 972070, 757545, 1048576, 803941, 763366, 763359, 1048576, 1048576, 1048576, 1048575, 1048576, 880470, 946028, 903830, 1048575, 880185, 877741, 1048576, 877651, 900642, 1048576, 747183, 720140, 720142, 1025689, 1025689, 988629, 988629, 935661, 901877, 988629, 869800, 1023566, 835077, 858368, 988629, 680536, 936256, 728886, 685139, 685335, 897656, 954485, 954485, 897656, 897656, 750588, 924150, 770215, 897656, 749057, 799457, 933672, 799229, 830214, 897656, 757545, 1048576, 803941, 763672, 763432, 1048576, 1048576, 1048576, 1048575, 1048576, 880470, 946028, 904729, 1048575, 880185, 877741, 1048576, 877651, 902258, 1048576, 686519, 662127, 662125, 947171, 947171, 912947, 912947, 935661, 777331, 942795, 763006, 826689, 777023, 798898, 912947, 516560, 665017, 548378, 515529, 513616, 665017, 832727, 973955, 663765, 664955, 249613, 730526, 569682, 717761, 563801, 626263, 692261, 626871, 649825, 664955, 503289, 722866, 570128, 511315, 518243, 721353, 820361, 929410, 718593, 717939, 627411, 819001, 635225, 805430, 628131, 676783, 778340, 679998, 703886, 738679, 747183, 720140, 721598, 1025689, 1025689, 988629, 988912, 935661, 901877, 988629, 869800, 1023566, 835077, 858402, 988912, 493677, 376847, 373538, 563387, 685332, 542754, 541881, 685332, 544053, 648002, 533632, 494102, 449192, 458251, 541881)
FAMILIES=[dict(name='constant_one',denominator=1,numerators=[1]*180),dict(name='optimized_common_field',denominator=1048576,numerators=OPTIMIZED_NUMERATORS)]
for f in FAMILIES:
 den=f['denominator'];nums=f['numerators'];ck('field_shape',0<den<=2**20 and len(nums)==180)
 for num in nums:ck('field_bounds',isinstance(num,int)and 0<=num<=den)
 for i,j in product(I,J):
  for l,m in LIVE:
   v=nums[INDEX[orbit(i,j,l,m)]]
   ck('ternary_priority',nums[INDEX[orbit(l,j,l,m)]]>=v)
   ck('quinary_priority',nums[INDEX[orbit(i,m,l,m)]]>=v)
B=2**32
floor=lambda x:x.numerator//x.denominator
ceil=lambda x:-((-x.numerator)//x.denominator)
GL=floor(g*B);CU=[ceil(c*B)for c in C]
ck('coefficient_enclosures',F(GL,B)<=g and all(F(c,B)>=z for c,z in zip(CU,C)))
ck('coefficient_sum_bound',sum(CU)<7*B)
TARGET=ceil(F(193,100000)*2**40)
LOW=[];HIGH=[]
for n in range(4):
 for mask in range(1024):
  for T in range(32):
   z=F(responses[n,T,mask],DH);ck('exact_local_response_in_unit',0<z<=1)
   l=max(0,floor(z*B));h=min(B,ceil(z*B));ck('exact_response_interval',F(l,B)<=z<=F(h,B))
   LOW.append(l);HIGH.append(h)
PREP=[]
for f in FAMILIES:
 den=f['denominator'];nums=f['numerators'];cases=[]
 for i,j in CASES:
  x=[0 if l==3 else 1 if l==i else 2 for l in range(6)];y=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
  MX=[[x],[[x[l]if l//3==b else 0 for l in range(6)]for b in range(2)],[[x[l]if l==b else 0 for l in range(6)]for b in I],[[9 if l==b else 0 for l in range(6)]for b in I]]
  MY=[[y],[[y[m]if m//5==b else 0 for m in range(20)]for b in range(4)],[[y[m]if m==b else 0 for m in range(20)]for b in J],[[60 if m==b else 0 for m in range(20)]for b in J]]
  menus=[]
  for e3,e5 in product(range(4),repeat=2):
   rows=[]
   for xx in MX[e3]:
    for yy in MY[e5]:
     v=[0]*10
     for l,m in LIVE:v[profile(l,m)]+=xx[l]*yy[m]*nums[INDEX[orbit(i,j,l,m)]]
     rows.append(tuple(v))
   unique=sorted(set(rows));kept=[u for u in unique if not any(u!=v and all(a<=b for a,b in zip(u,v))for v in unique)]
   for v in kept:ck('retained_selector_is_original',v in rows and min(v)>=0 and sum(v)<=675*den)
   for v in rows:ck('complete_menu_domination',any(all(a<=b for a,b in zip(v,u))for u in kept))
   menus.append(kept)
  ck('mass_selector_singleton',len(menus[0])==1);cases.append(menus)
 PREP.append(cases)
# All products stay below these exact arithmetic ceilings.
for f in FAMILIES:
 D=675*f['denominator']*B
 ck('screen_accumulator_signed64',D<2**63)
 ck('fee_accumulator_signed128',D*sum(CU)<2**127)
 ck('signed_gate_accumulator_128',(GL+sum(CU))*D<2**127)
output=args.output or Path(__file__).with_suffix('.bin')
with output.open('wb')as out:
 def put(x):out.write(struct.pack('<Q',x))
 for x in(0x314c4146454c5546,1,B,GL,TARGET,1657470):put(x)
 for x in CU:put(x)
 for table in(LOW,HIGH):
  for x in table:put(x)
 for f,cases in zip(FAMILIES,PREP):
  put(f['denominator'])
  for menus in cases:
   for menu in menus:
    put(len(menu))
    for v in menu:
     for x in v:put(x)
manifest=dict(schema='row0-column1-two-field-full-layout-input-v1',profile_column=args.column,status='PASS',new_lean_verification=False,source_sha256=PINS,preparer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),binary_sha256=sha256(output.read_bytes()).hexdigest(),binary_bytes=output.stat().st_size,B=32,P=32,R=40,g_lower=GL,coefficient_upper_sum=sum(CU),target_q40=TARGET,target_gate='193/100000',canonical_layout_count=1657470,actual_layout_count=5**10,orbit_keys=KEYS,families=FAMILIES,family_denominators=[f['denominator']for f in FAMILIES],corner_representatives=CASES,selector_counts=[[sum(map(len,menus))for menus in cases]for cases in PREP],checks=dict(checks),check_count=sum(checks.values()))
output.with_suffix(output.suffix+'.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=manifest['check_count'],bytes=manifest['binary_bytes'],target_q40=TARGET,selector_count_range=[min(x for row in manifest['selector_counts']for x in row),max(x for row in manifest['selector_counts']for x in row)])))
