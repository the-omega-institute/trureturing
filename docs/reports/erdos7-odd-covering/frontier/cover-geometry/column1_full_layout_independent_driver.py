#!/usr/bin/env python3
"""Rebuild all exact interval data and independently check every five-leaf layout.
Requires only Python's standard library, a C++17 compiler with int128, two
pinned canonical JSON inputs and a numerical library witness, and the companion independently authored C++.
Intermediate binaries and selection bytes are temporary; only result JSON is kept.
"""
from argparse import ArgumentParser
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import product,combinations
from math import prod
from array import array
from tempfile import TemporaryDirectory
import json,subprocess,sys
p=ArgumentParser(description=__doc__)
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--cpp',type=Path,default=Path(__file__).with_name('column1_full_layout_independent.cpp'))
p.add_argument('--witness',type=Path,default=Path(__file__).with_name('column1_full_leaf_pair_library_interval_certificate.json'))
p.add_argument('--mode',choices=('smoke','full'),default='full')
p.add_argument('--cxx',default='clang++')
p.add_argument('--threads',type=int,default=8)
p.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
a=p.parse_args();checks={}
def ck(k,c):
 checks[k]=checks.get(k,0)+1
 if not c:raise RuntimeError(k)
names=['remaining33_global_root_exclusion_certificate.json','joint_square_pair_225_star_certificate.json']
raw=[(a.directory/n).read_bytes() for n in names]
pins=['dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4','cbdc3903174d5640ea6518160abaaa9ac567424f9f8afc717128e1202f378be5']
for r,h in zip(raw,pins):ck('canonical_source_pin',sha256(r).hexdigest()==h)
base,net=map(json.loads,raw);cppraw=a.cpp.read_bytes()
b=a.witness.read_bytes();w=json.loads(b);fieldWitnesses={a.witness.name:sha256(b).hexdigest()}
ck('field_witness_roles',w['square7_roles']==[1,1,5])
for name,h in zip(names,pins):ck('witness_source_pin',w['source_sha256'][name]==h)
ck('exact_final_two_fields',len(w['families'])==2 and [f['name'] for f in w['families']]==['constant_one','optimized_common_field'])
families=[]
for fi,f in enumerate(w['families']):
 den=f['denominator'];nums=f['numerators'];ck('dyadic_normalization_exact',den>0 and (1<<20)%den==0)
 scaled=[n*((1<<20)//den) for n in nums]
 for n,ss in zip(nums,scaled):ck('same_rational_field',F(n,den)==F(ss,1<<20))
 if fi==0:ck('constant_one_field',len(nums)==180 and all(n==den for n in nums))
 families.append(dict(denominator=1<<20,numerators=scaled))
ck('valid_thread_count',1<=a.threads<=64)
A=1<<32;E=A;R=40;gamma=F(193,100000);target=(gamma.numerator*(1<<R)+gamma.denominator-1)//gamma.denominator
Q=(7,11,13,17,19);edges=list(combinations(range(5),2));r=[F(1,q-1) for q in Q];aa=[F(1,q*(q-2)) for q in Q]
g=F(200163067,201247200);C=list(map(F,base['combined512_coefficients']))
for k in range(1,5):C[288+(1<<k)]+=g*aa[k]
ck('complete_512_nonnegative',len(C)==512 and min(C)>=0)
gL=g.numerator*E//g.denominator;CU=[(c.numerator*E+c.denominator-1)//c.denominator for c in C]
ck('lower_source_coefficient',0<=F(gL,E)<=g)
for c,cu in zip(C,CU):ck('upper_fee_coefficient',c<=F(cu,E)<c+F(1,E))
ck('coefficient_int64_range',max(gL,max(CU),sum(CU))<1<<63)
words=[0x314c4146454c5546,2,A,gL,target,1657470,len(families),0]+CU
z0=[F(5,6)]+[F(q-2,q-1)-2*aa[k] for k,q in enumerate(Q) if k]
beta0=[aa[i]*r[j]+r[i]*aa[j] for i,j in edges];delta=[r[i]*r[j] for i,j in edges]
zmin=list(z0);zmin[0]-=F(3,35)
strict=1-sum((beta0[e]+delta[e])/(zmin[i]*zmin[j]) for e,(i,j) in enumerate(edges))
ck('uniform_strict_matching_box',strict>0)
HL=[];HU=[];minimumH=F(1)
for n in range(4):
 zz=list(z0);zz[0]-=F(n,35);terms=[]
 for T in range(32):
  U=set(k for k in range(5) if not(T>>k&1));es=[e for e,ends in enumerate(edges) if set(ends)<=U]
  terms.append((prod(zz[k] for k in U),[(e,prod(zz[k] for k in U-set(edges[e]))) for e in es],[(e,f,prod(zz[k] for k in U-set(edges[e])-set(edges[f]))) for e,f in combinations(es,2) if set(edges[e]).isdisjoint(edges[f])]))
 for mask in range(1024):
  beta=[beta0[e]+delta[e]*int(bool(mask>>e&1)) for e in range(10)]
  for zero,singles,doubles in terms:
   h=zero-sum((beta[e]*v for e,v in singles),F(0))+sum((beta[e]*beta[f]*v for e,f,v in doubles),F(0))
   ck('direct_matching_response_in_unit',0<h<=zero<=1);minimumH=min(minimumH,h)
   numerator=A*h.numerator;lo=numerator//h.denominator;hi=(numerator+h.denominator-1)//h.denominator
   ck('exact_outward_H_bounds',h.denominator*lo<=numerator<=h.denominator*hi)
   ck('H_range_and_width',0<=lo<=hi<=A and hi-lo<=1)
   HL.append(lo);HU.append(hi)
ck('complete_H_table',len(HL)==len(HU)==4*1024*32)
words.extend(HL);words.extend(HU)
I=(0,1,2,4,5);J=tuple(m for m in range(20) if m!=5);corners=list(product(I,(0,6,10,15)))
keys=[tuple(k) for k in w['orbit_keys']];ki={k:i for i,k in enumerate(keys)}
def orbit(i,j,l,m):
 return ('r' if i<3 else str(i),('eq' if i==l else 'other') if i<3 and l<3 else 'r' if l<3 else str(l),j//5,m//5,j==m)
def menus(weights,p,live,deep):
 n=len(weights)
 return [[weights],[[weights[k] if k//p==b else 0 for k in range(n)] for b in range(n//p)],[[weights[k] if k==t else 0 for k in range(n)] for t in live],[[deep if k==t else 0 for k in range(n)] for t in live]]
profileidx={(l,t):2*k+t for k,l in enumerate(I) for t in (0,1)}
ck('field_key_inventory',len(keys)==len(ki)==180 and {orbit(i,j,l,m) for i,j,l,m in product(I,J,I,J) if not(l<3 and m<5)}==set(keys))
# The key is invariant under simultaneous regular permutations. Verify the two
# generating transpositions; quinary permutations only preserve column/equality.
for u,v in ((0,1),(1,2)):
 def sw(x):return v if x==u else u if x==v else x
 ck('regular_transport_field_key',all(orbit(i,j,l,m)==orbit(sw(i),j,sw(l),m) for i,j,l,m in product(I,J,I,J) if not(l<3 and m<5)))
 ck('regular_transport_local_profile',all((l//3,l==5)==(sw(l)//3,sw(l)==5) for l in I))
ck('twenty_corner_coverage',len(corners)==20 and 5*sum((5,4,5,5))==95)
rawcount=retcount=0;selectorCounts=[]
ck('two_final_families',len(families)==2)
for fi,fam in enumerate(families):
 den=fam['denominator'];nums=fam['numerators'];ck('field_denominator',den==1<<20);ck('field_shape',len(nums)==180)
 words.append(den)
 for x in nums:ck('field_numerator_box',isinstance(x,int) and 0<=x<=den)
 for i,j,l,m in product(I,J,I,J):
  if l<3 and m<5:continue
  val=nums[ki[orbit(i,j,l,m)]]
  ck('ternary_priority',nums[ki[orbit(l,j,l,m)]]>=val)
  ck('quinary_priority',nums[ki[orbit(i,m,l,m)]]>=val)
 caseCounts=[]
 for i,j in corners:
  w=[0 if l==3 else 1 if l==i else 2 for l in range(6)];v=[0 if m==5 else 3 if m==j else 4 for m in range(20)]
  xm=menus(w,3,I,9);ym=menus(v,5,J,60)
  theta={(l,m):0 if l<3 and m<5 else nums[ki[orbit(i,j,l,m)]] for l,m in product(I,J)}
  caseCount=0
  for xmode,ymode in product(range(4),repeat=2):
   original=[]
   for x,y in product(xm[xmode],ym[ymode]):
    ck('selector_integer_weight_mass',min(x)>=0 and min(y)>=0 and sum(x)<=9 and sum(y)<=75)
    coeff=[0]*10
    for l,m in product(I,J):coeff[profileidx[l,int(m//5==1)]]+=x[l]*y[m]*theta[l,m]
    coeff=tuple(coeff);ck('selector_profile_mass',min(coeff)>=0 and sum(coeff)<=675*den);original.append(coeff)
   unique=set(original);frontier=sorted(c for c in unique if not any(c!=d and all(x<=y for x,y in zip(c,d)) for d in unique))
   for coeff in frontier:ck('retained_is_original',coeff in unique)
   for coeff in original:ck('all_original_menus_dominated',any(all(x<=y for x,y in zip(coeff,d)) for d in frontier))
   if xmode==ymode==0:ck('source_menu_singleton',len(frontier)==1 and frontier[0]==original[0])
   words.append(len(frontier))
   for coeff in frontier:words.extend(coeff)
   rawcount+=len(original);retcount+=len(frontier);caseCount+=len(frontier)
  caseCounts.append(caseCount)
 selectorCounts.append(caseCounts)
 M=675*den*A;feeBound=sum(CU)*M;gateBound=(gL+sum(CU))*M
 ck('screen_int64_safe',M<1<<63);ck('fee_int128_safe',feeBound<1<<127);ck('gate_int128_safe',gateBound<1<<127)
 ck('threshold_product_int128_safe',target*(675*den*(1<<24))<1<<127)
ck('complete_literal_and_retained_counts',rawcount==len(families)*20*559 and 0<retcount<=rawcount)
words[7]=retcount
ck('binary_schema_word_count',len(words)==8+512+len(HL)+len(HU)+321*len(families)+10*retcount)
packed=array('Q',words)
ck('eight_byte_unsigned_words',packed.itemsize==8)
if sys.byteorder!='little':packed.byteswap()
binary=packed.tobytes();binarySha=sha256(binary).hexdigest()
# Independently determine exact canonical and transported cardinalities.
counts=[1,0,0,0]
for _ in range(10):
 nxt=[0,0,0,0]
 for k,c in enumerate(counts):
  nxt[k]+=(k+2)*c
  if k<3:nxt[k+1]+=c
 counts=nxt
ck('regular_class_cardinalities',counts==[1024,58025,465751,1132670])
ck('canonical_and_transport_totals',sum(counts)==1657470 and sum(c*m for c,m in zip(counts,(1,3,6,6)))==5**10)
# Every generated .bin and compiled executable lives only in this directory.
with TemporaryDirectory(prefix='independent-five-leaf-',dir='/tmp') as tmp:
 tmp=Path(tmp);inputPath=tmp/'input.bin';selectionPath=tmp/'selection.bin';exePath=tmp/'checker'
 inputPath.write_bytes(binary)
 subprocess.run([a.cxx,'-std=c++17','-O3','-pthread',str(a.cpp),'-o',str(exePath)],check=True)
 command=[str(exePath),str(inputPath),str(selectionPath),str(a.threads)]+(['smoke'] if a.mode=='smoke' else [])
 run=subprocess.run(command,stdout=subprocess.PIPE,text=True,check=True)
 enumeration=json.loads(run.stdout);selection=selectionPath.read_bytes()
ck('cpp_source_unchanged',a.cpp.read_bytes()==cppraw)
ck('enumeration_status',enumeration['status']=='PASS')
if a.mode=='full':
 ck('complete_canonical_and_actual_count',enumeration['canonical_layout_count']==sum(counts) and enumeration['actual_layout_count']==5**10)
 ck('independent_regular_class_counts',enumeration['regular_class_counts']==counts)
 ck('all_complete_accepted_corners',enumeration['accepted_complete_corner_gates']==20*sum(counts))
 ck('all_complete_accepted_screens',enumeration['accepted_complete_screen_maxima']==512*20*sum(counts))
 ck('complete_whole_family_selection',len(selection)==sum(counts) and all(x<len(families) for x in selection))
 ck('family_selection_counts',list(map(selection.count,range(len(families))))==enumeration['family_selection_counts'])
else:
 smoke_count=4
 ck('smoke_layouts_only',enumeration['checked_layouts']==len(selection)==smoke_count and all(x<len(families) for x in selection))
 ck('smoke_family_count',enumeration['family_count']==len(families))
 ck('smoke_complete_corners',enumeration['accepted_complete_corner_gates']==20*smoke_count and enumeration['accepted_complete_screen_maxima']==10240*smoke_count)
ck('all_selected_gates_above_target',enumeration['minimum_selected_lower_q40']>=target)
ck('target_implies_gamma',F(target,1<<R)>=gamma)
policies=[]
for policy in net['policies']:
 fee=F(net['fee_before_arbitrary'])+F(policy['fee']);alpha=F(net['projection_alpha']);margin=alpha*(gamma-fee)
 ck('complete_tail_density',margin>F(1,2000000))
 t=(fee+F(1,2000000)/alpha)*(1<<R);threshold=t.numerator//t.denominator+1
 ck('target_exceeds_complete_policy_threshold',target>=threshold)
 policies.append(dict(kind=policy['kind'],K=policy['K'],complete_fee=str(fee),projection_alpha=str(alpha),reserve_at_gamma193=str(margin),reserve_at_gamma193_decimal=float(margin),strict_density_denominator=2000000,strict_threshold_q40=threshold))
delta=g-F(gL,E)+sum(F(cu,E)-c for cu,c in zip(CU,C));err=(g+sum(C))/A+delta+F(1,1<<R)
result=dict(schema='column1-full-layout-independent-certificate-v2',mode=a.mode,field_witness_sha256=fieldWitnesses,family_count=len(families),profile_column=1,status='PASS',new_lean_verification=False,read_same_round_producer=False,source_sha256=dict(zip(names,pins)),driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),cpp_sha256=sha256(cppraw).hexdigest(),reconstructed_input_sha256=binarySha,reconstructed_input_bytes=len(binary),selection_sha256=sha256(selection).hexdigest(),selection_bytes=len(selection),precisions=dict(B=32,P=32,R=40),uniform_strictness_margin=str(strict),minimum_rational_H=str(minimumH),rational_H_count=len(HL),original_selector_count=rawcount,retained_selector_count=retcount,selector_counts=selectorCounts,public_gate_rounding_error_bound=str(err),public_gate_rounding_error_bound_decimal=float(err),gate_lower_bound='193/100000',density_denominator=2000000,enumeration=enumeration,policies=policies,checks=checks,check_count=sum(checks.values()),scope=('All five-live-leaf assignments to ten labelled9qs roles; one whole supplied family per layout.' if a.mode=='full' else 'Smoke only: allleaf5,allleaf4,allregular0,plus the first mixed gap; one whole supplied family per layout; no full-scan claim.')+' Square7roles(1,1,5),fixed nulls,retained incidences and inherited actual-source/complete658network interfaces. No unrestricted odd-covering conclusion.')
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','check_count','gate_lower_bound','density_denominator','reconstructed_input_sha256','selection_sha256')}))
