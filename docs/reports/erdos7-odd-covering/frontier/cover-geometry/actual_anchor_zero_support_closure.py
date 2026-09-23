"""Close the fixed mixed split/common exact-zero chart using actual45/75 anchors.

Reuses the pinned report509 valid rows. Reconstructs full infinite overflow,
561 globally fixed anchor pairs, pure-overlap source reserves, and two rational
price certificates. Standard library; no optimizer, geometry producer or Lean.
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
 'six_prime_prefix_certificate.json':'ecdeb6246626c101b7bb16130366a7d22bf8d71775d5f28997b85e74c796ee61',
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
from collections import defaultdict
from bisect import bisect_left

# The same four basic vertices support the lower reserve. No source producer
# is rerun, and the charged-process domination remains a mathematical premise.
prefix=sources['six_prime_prefix_certificate.json']
vertices=[r for r in prefix['rows'] if r['node'][:3]==[2,4,1]]
need({r['node'][4] for r in vertices}=={1,2,3,4} and len(vertices)==4,'same four pure5 vertices')
vertex_lowers=[]
for r in vertices:
 j=r['node'][4]
 R=F(135,4)+F(9,20)*int(j==2)
 need(F(r['reserve_lower_bound_cell_units'])==R,'old reserve contains only15 credit')
 vertex_lowers.append((R-sum(map(F,r['rounded_loss_upper_bounds_cell_units'][:5]),F()))/135)
m7=F(source['unnormalized_mass_lower'])
need(min(vertex_lowers)==m7,'same mass lower from four vertices')

@lru_cache(None)
def later(s):
 return (F(4,7) if s[2]==0 else F(9,7**abs(s[2])))*common(s)
allmass=defaultdict(F)
for s in allrows:allmass[s[:2]]+=later(s)
groups=defaultdict(list)
for s,l in zip(rows,loads):groups[s[:2]].append((l/later(s),later(s),l))
coeff={}
for ab in allmass:
 entries=sorted(groups[ab]);rat=[x[0] for x in entries];sl=[F()];sd=[F()]
 for _,p,l in entries:sl.append(sl[-1]+p);sd.append(sd[-1]+l)
 coeff[ab]=(rat,sl,sd)
def residual(ab,t):
 rat,sl,sd=coeff[ab];i=bisect_left(rat,t)
 return t*(sl[i]-allmass[ab])-sd[i]

anchors=((3,0),(5,0),(9,1),(15,2),(25,1),(27,4))
cells=[n for n in range(675) if all(n%d!=a for d,a in anchors)]
need(len(cells)==221,'six-anchor joint CRT cells')
@lru_cache(None)
def conditional(p,E,res,ref):
 if res==ref:return tuple((f,F((p-1)*p**E,p**f)) for f in range(E+1,39))
 z=res-ref;v=0
 while z%p==0:z//=p;v+=1
 return ((v+1,F(1)),)
bycell={}
for n in cells:
 x,y=n%27,n%25;sg3=1 if x%3==2 else -1;sg5=1 if y%5==3 else -1
 a=[(sg3*f,p) for f,p in conditional(3,3,x,2 if sg3==1 else 7)]
 b=[(sg5*f,p) for f,p in conditional(5,2,y,3 if sg5==1 else 4)] if y%5 in (3,4) else [(0,F(1))]
 bycell[n]={(u,v):p*q/675 for (u,p),(v,q) in product(a,b) if (u,v) in allmass}
initial_mass=defaultdict(F)
for dd in bycell.values():
 for ab,w in dd.items():initial_mass[ab]+=w
need(all(initial_mass[ab]==initial(*ab) for ab in allmass),'literal cell-to-shell reconstruction')
need(price+F(221,675)+sum((residual(ab,t) for ab,t in initial_mass.items()),F())==old,'grouped exact509 signed dual')
def legal(m):return [r for r in range(m) if all(r%d!=a for d,a in anchors if m%d==0)]
legal45,legal75=legal(45),legal(75)
need((len(legal45),len(legal75))==(17,33),'complete legal phase domains')
@lru_cache(None)
def initial_chart(r,s):
 removed=[n for n in cells if n%45==r or n%75==s]
 rm=defaultdict(F)
 for n in removed:
  for ab,w in bycell[n].items():rm[ab]+=w
 t={ab:w-rm[ab] for ab,w in initial_mass.items()}
 need(all(w>=0 for w in t.values()),'nonnegative exact A8 weights')
 return t,F(221-len(removed),675)

cpath=BASE/'actual_anchor_zero_support_closure_certificate.json'
raw=cpath.read_bytes();certnew=json.loads(raw)
need(certnew['schema']=='actual-anchor-zero-support-prices-v1' and certnew['reference']==[2,7,3,4],'new certificate chart')
need(certnew['source_certificate_sha256']==PINS['mixed_split_zero_support_bound_certificate.json'],'new prices bind existing valid rows')
den=certnew['denominator'];need(type(den) is int and den==10**14,'price denominator')
rhs=dict(pairs=1,genuine_triples=2,triangle_cliques=1,quads=3,zero_pairs=1,zero_triangle_cliques=1,order=0)
representatives=[]
for entry in certnew['representatives']:
 r,s=entry['phase'];need((r,s) in ((14,11),(14,14)),'declared representative')
 t,total=initial_chart(r,s);ws=[t[v[:2]]*later(v) for v in rows]
 tail=total-sum((t[v[:2]]*later(v) for v in allrows),F());need(tail>=0,'complete overflow')
 ls=[F()]*len(rows);pprice=F();seen=set()
 for kind,index,num in entry['prices']:
  need(kind in rhs and type(index) is int and 0<=index<len(cert[kind]),'existing valid source row')
  need(type(num) is int and num>0 and (kind,index) not in seen,'unique positive rational price')
  seen.add((kind,index));y=F(num,den);pprice+=rhs[kind]*y
  for j,i in enumerate(cert[kind][index][:-1]):ls[i]+=(-1 if kind=='order' and j==1 else 1)*y
 result=pprice+sum((max(w-l,F()) for w,l in zip(ws,ls)),F())+tail
 need(result==F(entry['exact_upper']) and tail==F(entry['overflow']) and pprice==F(entry['row_price']),'complete rational certificate consumption')
 need(result<m7,'representative strict source separation')
 representatives.append({'phase':[r,s],'initial':t,'total':total,'upper':result,'overflow':tail,'active_prices':len(seen),'negative_loads':sum(l<0 for l in ls)})
need(sorted(tuple(r['phase']) for r in representatives)==[(14,11),(14,14)],'exactly two representative certificates')
branches=[];matched=defaultdict(int)
for r,s in product(legal45,legal75):
 t,total=initial_chart(r,s)
 upper_old=price+total+sum((residual(ab,w) for ab,w in t.items()),F())
 need(upper_old<=old,'restricting initial chart cannot worsen fixed dual')
 n45=sum(n%45==r for n in cells);n75=sum(n%75==s for n in cells)
 credit45=F(1,45)-F(n45,675);credit75=F(1,75)-F(n75,675)
 need(credit45>=0 and credit75>=0,'individual pure-overlap credits')
 need(credit45==F(int(r%9==4),135)+F(int(r%5==1),225)-F(int(r%9==4 and r%5==1),675),'CRT45 credit formula')
 need(credit75==F(4*int(s%3==1),675),'CRT75 credit formula')
 lower=m7+credit45+credit75;chosen=None;upper=upper_old
 if upper_old>=lower:
  match=[rep for rep in representatives if rep['initial']==t and rep['total']==total]
  need(len(match)==1,'every unresolved pair has exactly one complete weight type')
  rep=match[0];upper=rep['upper'];chosen=rep['phase'];matched[tuple(chosen)]+=1
 need(lower>upper,'same-source closure at every global phase pair')
 branches.append({'phase':[r,s],'initial_cells':int(total*675),'n45':n45,'n75':n75,
                  'reserve_credit45':str(credit45),'reserve_credit75':str(credit75),
                  'source_lower':str(lower),'fixed509_upper':str(upper_old),
                  'representative':chosen,'final_upper':str(upper),'margin':str(lower-upper)})
need(len(branches)==561 and dict(matched)=={(14,11):8,(14,14):8},'all561 branches and sixteen repaired weight cases')
need(sum(F(r['fixed509_upper'])<m7 for r in branches)==374,'unchanged-reserve closure count')
need(sum(F(r['fixed509_upper'])<F(r['source_lower']) for r in branches)==545,'corrected-reserve closure count')
minimum=min(branches,key=lambda r:F(r['margin']))
need(F(minimum['margin'])>F(1,26000),'uniform comparison margin, not a Haar survival bound')
repout=[{k:(str(v) if isinstance(v,F) else v) for k,v in rep.items() if k not in ('initial','total')} for rep in representatives]
out={'inputs':PINS,'certificate_sha256':hashlib.sha256(raw).hexdigest(),'m7':str(m7),
     'full_profile_count':len(allrows),'middle_profile_count':len(rows),'legal45':legal45,'legal75':legal75,
     'basic_vertex_lowers':list(map(str,vertex_lowers)),
     'phase_pairs':len(branches),'fixed_dual_closes_with_m7':374,'fixed_dual_closes_with_corrected_reserve':545,
     'repriced_weight_type_counts':[[*k,v] for k,v in sorted(matched.items())],
     'representatives':repout,'minimum':minimum,'minimum_margin':minimum['margin'],
     'branches':branches,'scope':'Noncoverage for the fixed completed source chart with later references(2,7,3,4), split3/5/7 and common11/13/17/19, arbitrary legal45/75 completion phases and arbitrary finite original later heights. Old-only phases are arbitrary subject to this normalized chart. Ordinary source argument and exact rational certificates; no uniform positive Haar constant, new geometry, Lean verification or unrestricted Erdos7 conclusion.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(out==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained exact result mismatch')
print(json.dumps({'phase_pairs':561,'minimum_margin':minimum['margin'],'minimum_margin_float':float(F(minimum['margin'])),'minimum_phase':minimum['phase'],'representatives':repout},indent=2))
