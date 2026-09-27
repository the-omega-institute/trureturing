#!/usr/bin/env python3
"""Independent same-source audit: literal H5 prefix plus18 fixed row13 originals."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter,defaultdict
from itertools import product
from math import prod
import json,hashlib,re,argparse
parser=argparse.ArgumentParser(description=__doc__)
report_root=Path(__file__).resolve().parent.parent.parent
parser.add_argument('--source',type=Path,default=report_root/'profile-notes/arithmetic/558-first-eleven-inventory-and-an-actual-phase-counterexample.md')
parser.add_argument('--heads',type=Path,default=Path(__file__).with_name('pa_finite_root_heads.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
checks={}
def ck(k,v):
 if not v or k in checks:raise ValueError(k)
 checks[k]=True
def crt(parts):
 residue=0;modulus=1
 for m,r in parts:
  if m==1:continue
  residue+=modulus*((r-residue)*pow(modulus,-1,m)%m);modulus*=m
 if not all(residue%m==r%m for m,r in parts):raise ValueError('CRT failed')
 return modulus,residue
source_originals=[]
for p0 in (5,7):
 for e in range(1,6):
  for j in (1,2):source_originals.append((p0**e,j*p0**(e-1)))
for a,b in product(range(1,6),repeat=2):
 for j in (3,4):source_originals.append(crt([(5**a,3*5**(a-1)),(7**b,j*7**(b-1))]))
ck('literal70_old_originals',len(source_originals)==70)
source_text=args.source.read_text(encoding='utf-8')
rx=re.compile(r'^\|\s*\((\d+),(\d+)\)\s*\|\s*\((\d+),(\d+),(\d+)\)\s*\|\s*\((\d+),(\d+),(\d+)\)\s*\|$')
table=[list(map(int,m.groups())) for line in source_text.splitlines() if (m:=rx.match(line))]
ck('literal25_first11_rows',len(table)==25 and {(r[0],r[1]) for r in table}==set(product(range(5),repeat=2)))
for i,(a,b,*rs) in enumerate(table):
 for j,(r5,r7,g) in enumerate((rs[:3],rs[3:])):
  ck('literal_first11_phase_'+str(i)+'_'+str(j),0<=r5<5**a and 0<=r7<7**b and 0<=g<10)
  for c in range(1,5):source_originals.append(crt([(5**a,r5),(7**b,r7),(11**c,(g+1)*11**(c-1)-1)]))
ck('literal270_source_originals',len(source_originals)==270 and len(set(source_originals))==270)
ck('source135_labels_two_each',len(Counter(m for m,r in source_originals))==135 and set(Counter(m for m,r in source_originals).values())=={2})
literal=[(13,0),(13,1),(169,2),(169,3),(2197,8),(2197,12),(65,4),(65,44),(845,344),(845,514),(325,294),(325,269),(4225,1869),(4225,1194),(1625,519),(1625,1144),(21125,519),(21125,16394)]
ck('18_distinct_original_pairs',len(literal)==18 and len(set(literal))==18)
ck('two_occurrences_per_nine_labels',len(Counter(m for m,r in literal))==9 and set(Counter(m for m,r in literal).values())=={2})
ck('whole288_distinct_originals',len(set(source_originals+literal))==288)
ck('whole144_labels_two_each',len(Counter(m for m,r in source_originals+literal))==144 and set(Counter(m for m,r in source_originals+literal).values())=={2})
originals=[]
for i,(m,r) in enumerate(literal):
 t=m;a=d=0
 while t%5==0:t//=5;a+=1
 while t%13==0:t//=13;d+=1
 ck('literal_label_and_residue_'+str(i),t==1 and d>0 and 0<=r<m)
 old=r%5**a;current=r%13**d
 ck('nested_old_phase_'+str(i),(a==0 and old==0) or(a==1 and old==4) or(a in(2,3) and old==19))
 originals.append(dict(modulus=m,residue=r,old5_exponent=a,old5_residue=old,current13_exponent=d,current13_residue=current,root13=current%13))
W26={13,65,91,143,455,325,169,715,1001,845,637,2275,1183,1625,1573,5005,3185,3575,1859,5915,4225,2197,7865,9295,7007,4459}
heads={'W26':W26,'W54':{5**a*7**b*11**c*13**d for a,b,c,d in product(range(3),range(3),range(3),(1,2))},'W72':{5**a*7**b*11**c*13**d for a,b,c,d in product(range(4),range(3),range(3),(1,2))}}
canon=json.loads(args.heads.read_text(encoding='utf-8'))
for r in canon['consumers']:ck('head_matches_canonical_'+r['name'],heads[r['name']]==set(r['labels']))
# Read each coordinate literally through height5. The first11 table uses only
# height4 old projections; the nested query regions use old5 height3. Retain
# those signatures jointly with the actual mixed-deletion flags.
slots=[(a,b,*slot) for a,b,*rs in table for slot in (rs[:3],rs[3:])]
coordinate_signatures={}
for p in (5,7):
 masks={}
 for z in range(p**4):
  masks[z]=sum(1<<i for i,(a,b,r5,r7,g) in enumerate(slots)
               if z%p**(a if p==5 else b)==(r5 if p==5 else r7))
 hist=Counter()
 for z in range(p**5):
  if any(z%p**e in (p**(e-1),2*p**(e-1)) for e in range(1,6)):continue
  mixed=any(z%p**e in tuple(j*p**(e-1) for j in ((3,) if p==5 else (3,4))) for e in range(1,6))
  region=(0 if z%5!=4 else 1 if z%25!=19 else 2 if z%125!=19 else 3) if p==5 else 0
  hist[masks[z%p**4],mixed,region]+=1
 coordinate_signatures[p]=hist
 ck('literal_pure_count_'+str(p),sum(hist.values())=={5:1563,7:11205}[p])
 ck('literal_mixed_count_'+str(p),sum(n for (bits,mixed,region),n in hist.items() if mixed)=={5:781,7:5602}[p])
old_hist=Counter();color_cache={}
for (b5,m5,region),n5 in coordinate_signatures[5].items():
 for (b7,m7,_),n7 in coordinate_signatures[7].items():
  if m5 and m7:continue
  bits=b5&b7
  if bits not in color_cache:
   mask=0;t=bits
   while t:
    bit=t&-t;mask|=1<<slots[bit.bit_length()-1][4];t-=bit
   if not(mask&(1<<3) and mask&(1<<6) and not mask&(1<<9)):raise ValueError('actual source color invariant')
   color_cache[bits]=mask
  old_hist[region,color_cache[bits].bit_count()]+=n5*n7
period=5**5*7**5
ck('literal_old_survivor_mass',F(sum(old_hist.values()),period)==F(13138253,52521875))
regions=[F() for _ in range(4)]
for (region,K),n in old_hist.items():
 allowed=1-F(1464*K,14641)
 actual_fibre_mass=min(F(1),F(5,3)*allowed)
 regions[region]+=F(n,period)*actual_fibre_mass
mass=sum(regions,F());mu5=sum(regions[1:],F());mu25=sum(regions[2:],F());mu125=regions[3]
ck('lambda11_mass',mass==F(19543635187,92276732625))
ck('mu5',mu5==F(9070623361,92276732625))
ck('mu25',mu25==F(15701435,738213861))
ck('mu125',mu125==F(3244691,762617625))
region_data=[]
for i,(r5,w) in enumerate(zip((0,4,44,19),regions)):
 active=[o for o in originals if r5%5**o['old5_exponent']==o['old5_residue']]
 rootsets={name:sorted({o['root13'] for o in active if o['modulus'] in W}) for name,W in heads.items()}
 forbidden={z for z in range(13**3) if any(z%13**o['current13_exponent']==o['current13_residue'] for o in active)}
 b=F(len(forbidden),13**3);ell=max(F(),F(3,2)*b-F(1,2))
 region_data.append(dict(representative=r5,mass=w,root_sets=rootsets,root_counts={k:len(v) for k,v in rootsets.items()},actual_forbidden_count=len(forbidden),actual_forbidden_fraction=b,actual_loss_fraction=ell))
for i,want in enumerate(((6,4,4),(10,8,8),(13,12,12),(13,12,13))):ck('root_counts_'+str(i),tuple(region_data[i]['root_counts'][n] for n in heads)==want)
for i,b in enumerate((F(366,2197),F(730,2197),F(1093,2197),F(97,169))):ck('actual_union_fraction_'+str(i),region_data[i]['actual_forbidden_fraction']==b)
# Independent closed full-moment formulas; higher coordinate tails enter their
# full first moments, so no finite exponent cutoff is used.
def hinge(coords,t):
 mass0=prod(v[1] for v in coords);mean=prod(u+c/F(p-1) for p,u,c in coords)
 p1=[u-c/F(p) for p,u,c in coords];one=prod(p1)
 two=sum((c*F(p-1,p*p)*prod(p1[j] for j in range(len(coords)) if j!=i) for i,(p,u,c) in enumerate(coords)),F())
 three=sum((c*F(p-1,p**3)*prod(p1[j] for j in range(len(coords)) if j!=i) for i,(p,u,c) in enumerate(coords)),F())
 return mean-t*mass0+sum(F(t-n)*v for n,v in ((1,one),(2,two),(3,three)) if n<t)
x=F(1563,3125);y=F(11205,16807);mixed=F(4375162,52521875)
coords=[(5,x,F(1)),(7,y,F(1))];hs={}
for p,t,cap in ((11,2,F(5,3)),(13,2,F(3,2)),(17,4,F(2)),(19,4,F(9,5))):hs[p]=hinge(coords,t);coords.append((p,F(1),cap))
phi=hinge(coords,3);S11=hs[11]/3-(x*y-mixed-mass);H11=F(1,12)-mixed+S11;A11=x*y-F(1,12)-hs[11]/3
ck('F11_known',hs[11]==F(145566677,1260525000))
ck('F13_known',hs[13]==F(16293608641,83194650000))
ck('S11_known',S11==F(7707153701,55366039575000))
ck('H11_known',H11==F(9458012327,55366039575000))
ck('actual_prefix_identity',mass==A11+H11)
T=F(257,51);alpha=x*y-F(1,12)-hs[11]/3-hs[13]/4-hs[17]/4-hs[19]/5;G=(T-2)*alpha-phi
A5=F(44887686823492905683,27146767546602063360);A7=F(20281636668601030051,20313907687933516800);A57=F(585035299774741193,203139076879335168);c0=F(6168733163201163811,542935350932041267200)
ck('NC4_joint_identity',G==-c0+A5*(x-F(1,2))+A7*(y-F(2,3))+A57*(x-F(1,2))*(y-F(2,3)))
ck('NC4_strict_near_critical',G<0)
def charge(m):
 es=[]
 for p in (5,7,11,13):
  e=0
  while m%p==0:m//=p;e+=1
  es.append(e)
 a,b,c,d=es
 return 3*(x if a==0 else F(1,5**a))*(y if b==0 else F(1,7**b))*(F(1) if c==0 else F(5,3*11**c))/13**d
results={}
for name,W in heads.items():
 theta=F(1,4)*(x+F(1,4))*(y+F(1,6))*F(7,6)-sum((charge(m) for m in W),F())
 M=F(21,26)*A11-theta-hs[17]/4-hs[19]/5;deficit=M-phi/(T-2);eta=F(26,3)*deficit
 E=sum((w['mass']*max(0,w['root_counts'][name]-6) for w in region_data),F())
 P=sum((w['mass']*min(5,3*max(0,6-w['root_counts'][name])) for w in region_data),F())
 Q=E-P/3;margin=Q-7*H11-eta
 ck('strict_reverse_'+name,margin>0)
 coeff=next(r['deficit_coefficients'] for r in canon['consumers'] if r['name']==name)
 dd=[F(z) for z in coeff];interp=dd[0]+dd[1]*(x-F(1,2))+dd[2]*(y-F(2,3))+dd[3]*(x-F(1,2))*(y-F(2,3))
 ck('canonical_parameter_specific_D_'+name,deficit==interp)
 results[name]=dict(Theta=theta,M=M,D=deficit,eta=eta,E=E,P=P,Q=Q,reverse_margin=margin,reverse_margin_decimal=float(margin))
ck('Q26_formula',results['W26']['Q']==4*mu5+3*mu25)
ck('Q54_formula',results['W54']['Q']==2*mu5+4*mu25-F(5,3)*(mass-mu5))
ck('Q72_formula',results['W72']['Q']==results['W54']['Q']+mu125)
loss13=sum((r['mass']*r['actual_loss_fraction'] for r in region_data),F());final=mass-loss13;R=2+phi/final
ck('actual_loss_formula',loss13==(mu25-mu125)*F(541,2197)+mu125*F(61,169))
ck('actual_final_mass_positive',final>0)
ck('actual_PA_query_bound_below_target',R<T)
minimum=min(r['reverse_margin'] for r in results.values())
result=dict(scope='Ordinary exact counterexample to the proposed JC0 implication that NC4 G<0 plus one actual prefix forces one of the three finite-head weighted sufficient conditions. Correct Q=E-P/3. Does not refute any sufficient theorem, imply actual PA failure, or settle Erdos7.',source_markdown_sha256=hashlib.sha256(args.source.read_bytes()).hexdigest(),head_data_sha256=hashlib.sha256(args.heads.read_bytes()).hexdigest(),source_table=table,coordinate_signature_counts={p:len(h) for p,h in coordinate_signatures.items()},old_region_colorcount_counts=[dict(region=r,color_count=k,count=n) for (r,k),n in sorted(old_hist.items())],original_count=288,numerical_label_count=144,full_original_pairs=source_originals+literal,row13_originals=originals,x=x,y=y,mixed=mixed,lambda11=mass,mu5=mu5,mu25=mu25,mu125=mu125,S11=S11,H11=H11,G=G,G_decimal=float(G),Phi=phi,hinges=hs,regions=region_data,heads=results,minimum_reverse_margin=minimum,minimum_reverse_margin_decimal=float(minimum),actual_loss13=loss13,actual_loss13_decimal=float(loss13),actual_final_mass=final,actual_query_bound=R,actual_query_bound_decimal=float(R),checks=checks,check_count=len(checks))
args.output.write_text(json.dumps(result,default=lambda q:str(q) if isinstance(q,F) else q,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['G','G_decimal','mu5','mu25','mu125','minimum_reverse_margin','minimum_reverse_margin_decimal','actual_loss13','actual_loss13_decimal','actual_query_bound','actual_query_bound_decimal','check_count']},default=str,indent=2))
