"""Consume retained charged-seven source exclusions with the fixed report509 dual.

All280 globally fixed coarse projection choices are checked with exact weights
and signed residuals. Row validity is reused from pinned report509 inputs.
Ordinary source-comparison mathematics, not a Lean or unrestricted-cover proof.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod
from functools import lru_cache
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input-dir',type=Path,default=ROOT)
parser.add_argument('--output',type=Path)
args=parser.parse_args();BASE=args.input_dir
PINS={
 'mixed_split_zero_support_bound_certificate.json':'6d646fc00498e8c2d17258118b9a6c8fa1a5c746ce57a0318f51199ee000000b',
 'mixed_split_zero_support_bound.json':'9e20cfb8c1d640a836d596b7573e6b2ecb85d0a7714dd2df875430bab737ba18',
 'randomized_completion_support.json':'35bb2ad24786cc125f188c59a073e6df23e42433eb8195f01fd3b21b16c28938',
 'common_law_mass_tail.json':'3781704377f2ca6234ed55f3eff1a37d2f8665a3810b02c694aebdc2fc063cb4'}
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
def need(x,s):
 if not x: raise ValueError(s)
sources={}
for name,digest in PINS.items():
 raw=(BASE/name).read_bytes();need(hashlib.sha256(raw).hexdigest()==digest,'pinned input '+name)
 sources[name]=json.loads(raw)
source=sources['common_law_mass_tail.json']['common_seven_core_law']
need(F(source['unnormalized_mass_lower'])==F(7235955529,450000000000)
     and F(source['unnormalized_joint_density_cap'])==F(27,2),'same actual source')
need(tuple(map(F,source['conditional_caps']))==tuple(c for p,c in CAPS),'same conditional caps')
def load(s):return (prod(max(1,x) for x in s[:3])+prod(max(1,-x) for x in s[:3])-1)*prod(s[3:])
allrows=[]
def complete(s):
 if len(s)==7:allrows.append(s);return
 for f in range(1,39):
  child=s+(f,)
  if load(child)>38:break
  complete(child)
third=list(range(2,39))+list(range(-2,-39,-1))
for a in third:
 for b in third+[0]:
  for c in [0]+third:
   if load((a,b,c))<=38:complete((a,b,c))
rows=[s for s in allrows if load(s)>=20]
need((len(allrows),len(rows))==(23408,20076),'profile order')
@lru_cache(None)
def shell(p,E,ref,cells,f):
 if f>E:return F(p-1,p**f) if ref in cells else F()
 def exact(x):
  if x==ref:return False
  z=x-ref;v=0
  while z%p==0:z//=p;v+=1
  return v==f-1
 return F(sum(map(exact,cells)),p**E)
@lru_cache(None)
def initial(a,b):
 r=2 if a>0 else 1
 xs=tuple(x for x in range(27) if x%3==r and x%9!=1 and x!=4)
 ys=tuple(y for y in range(25) if y%5 and y!=1 and not(r==2 and y%5==2))
 z=shell(3,3,2 if a>0 else 7,xs,abs(a))
 if b==0:return z*F(sum(y%5 not in(3,4) for y in ys),25)
 ref=3 if b>0 else 4
 return z*shell(5,2,ref,tuple(y for y in ys if y%5==ref),abs(b))
def common(s):return prod(1-C/p if f==1 else C*F(p-1,p**f) for (p,C),f in zip(CAPS[1:],s[3:]))
def weight(s):
 f=s[2];v=F(4,7) if f==0 else F(3,2)*F(6,7**abs(f))
 return initial(*s[:2])*v*common(s)
weights=list(map(weight,rows)); allweights=list(map(weight,allrows))
overflow=F(221,675)-sum(allweights,F())
cert=sources['mixed_split_zero_support_bound_certificate.json'];D=cert['denominator']
loads=[F()]*len(rows);price=F()
for kind,rhs in [('pairs',1),('genuine_triples',2),('triangle_cliques',1),('quads',3),('zero_pairs',1),('zero_triangle_cliques',1),('order',0)]:
 for *ids,n in cert[kind]:
  y=F(n,D);price+=rhs*y
  for j,i in enumerate(ids):loads[i]+=(-1 if kind=='order' and j==1 else 1)*y
old=price+sum((max(w-l,F()) for w,l in zip(weights,loads)),F())+overflow
ret=sources['mixed_split_zero_support_bound.json']
need(old==F(ret['exact_upper']) and price==F(ret['row_price_units'],D),'same509 residual upper')
need(ret['certificate_sha256']==PINS['mixed_split_zero_support_bound_certificate.json'],'old certificate binding')
need(cert['mode']=='zero_full7874' and cert['reference']==[2,7,3,4],'same exact-zero chart')
@lru_cache(None)
def correction(a,b,r21,r35,r63,r105=None):
 out=F();root=2 if a>0 else 1
 for c in (2,4,5,7,8):
  xs=tuple(x for x in range(27) if x%3==root and x%9==c and x!=4)
  mx=shell(3,3,2 if a>0 else 7,xs,abs(a))
  if not mx:continue
  for d in range(1,5):
   ys=tuple(y for y in range(25) if y%5==d and y!=1 and not(root==2 and d==2))
   if b==0:my=F(len(ys),25) if d not in(3,4) else F()
   else:my=shell(5,2,3 if b>0 else 4,ys,abs(b))
   s=int(root==r21)+int(d==r35)+int(c==r63)
   if r105 is not None:s+=int(root==r105%3 and d==r105%5)
   out+=mx*my*max(F(3*s-4,14),F())
 return out
results=[]
common_weights=list(map(common,allrows))
phase3=list(product((1,2),(1,2,3,4),(2,4,5,7,8)))
phase105=[d for d in range(15) if d%3 and d%5 and d!=2]
need(phase105==[1,4,7,8,11,13,14],'all allowed105 old projections')
phases=phase3+[(*v,d) for v in phase3 for d in phase105]
for phase in phases:
 total=F()
 for x,y in product(range(27),range(25)):
  if x%3==0 or x%9==1 or x==4 or y%5==0 or y==1 or(x%3==2 and y%5==2):continue
  s=int(x%3==phase[0])+int(y%5==phase[1])+int(x%9==phase[2])
  if len(phase)==4:s+=int(x%3==phase[3]%3 and y%5==phase[3]%5)
  total+=max(F(3*s-4,14),F())/675
 delta=[correction(s[0],s[1],*phase)*cw if s[2]==0 else F() for s,cw in zip(allrows,common_weights)]
 need(all(0<=dw<=w for w,dw in zip(allweights,delta)),'nonnegative revised weights')
 overflow_delta=total-sum(delta,F());need(0<=overflow_delta<=overflow,'full corrected overflow')
 middle_delta=[dw for s,dw in zip(allrows,delta) if load(s)>=20]
 need(total>=F(2,945),'uniform shallow overlap mass')
 new=price+sum((max(w-dw-l,F()) for w,l,dw in zip(weights,loads,middle_delta)),F())+overflow-overflow_delta
 need(new<old,'strict same-source improvement in every branch')
 results.append({'projection':phase,'total_credit':str(total),'overflow_credit':str(overflow_delta),'upper':str(new),'saving':str(old-new)})
parent_results,results=results[:40],results[40:]
parent={r['projection']:r for r in parent_results}
for row in results:
 previous=parent[row['projection'][:3]]
 need(F(row['total_credit'])>=F(previous['total_credit']) and F(row['overflow_credit'])>=F(previous['overflow_credit']) and F(row['upper'])<=F(previous['upper']),'adding105 preserves same-source domination')
worst=max(results,key=lambda x:F(x['upper']));new=F(worst['upper']);m=F(7235955529,450000000000)
parent_worst=max(parent_results,key=lambda x:F(x['upper']));parent_upper=F(parent_worst['upper'])
need(len(parent_results)==40 and parent_worst['projection']==(2,2,4),'retained three-projection bound')
need(len(results)==280 and [r['projection'] for r in results if F(r['upper'])==new]==[(2,2,4,1)],'complete global four-projection branches')
need(new<parent_upper<old,'both source-comparison improvements')
need(F(worst['total_credit'])==F(2,525) and F(worst['total_credit'])==F(9,5)*F(parent_worst['total_credit']) and F(worst['overflow_credit'])==F(9,5)*F(parent_worst['overflow_credit']),'exact worst-branch correction scaling')
need(new>m,'remaining source-mass gap')
out={'inputs':PINS,'old_upper':str(old),'uniform_upper':str(new),'uniform_saving':str(old-new),
     'worst':worst,'branches':results,'phase105_domain':phase105,
     'three_projection_branches':parent_results,'three_projection_upper':str(parent_upper),
     'improvement_from105':str(parent_upper-new),'gap_to_m7':str(new-m),'m7':str(m),
     'full_profile_count':len(allrows),'middle_profile_count':len(rows),
     'scope':'Upper bound for actual exact-zero bad-source mass in the fixed completed chart, retaining all four selected shallow7 projections and the original report509 dual. Arbitrary auxiliary supports keep their old bound. No uniform-theta substitution, optimizer claim, unrestricted noncoverage or Lean verification.',
     'decimals':{'old':float(old),'new':float(new),'saving':float(old-new),'three_projection_upper':float(parent_upper),'improvement_from105':float(parent_upper-new),'gap':float(new-m)}}
out=json.loads(json.dumps(out))
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(out==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained result mismatch')
print(json.dumps({k:out[k] for k in ('worst','decimals','full_profile_count','middle_profile_count')},indent=2))
