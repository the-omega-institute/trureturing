"""Close all reference orbits for split3/5/7 and common11/13/17/19.

One actual source, fixed numerical-label selectors, exact45/75 reserves and
full infinite overflow. Consumes rational prices on existing509 rows only;
no optimizer, geometry rerun, uniform Haar floor or Lean claim.
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
 'actual_anchor_zero_support_closure_certificate.json':'6483e06d26923ee001995feeb52010e044767925e7c0dffd17d2980b10d0b87c',
 'all_first_root_source_types.py':'71d1f2ca381be47d89fe199f905c7d4b8acee58dd46fa36e65b967af76d3b798',
 'mixed_chart_reference_orbits.py':'5a0dce1eba5fdd8e1cd5ca65eb946f4bd350fb7790537d2ede39a36419ca92c9',

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
 if name.endswith('.json'):sources[name]=json.loads(raw)
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
import importlib.util

def helper(name):
 path=BASE/(name+'.py')
 spec=importlib.util.spec_from_file_location(name,path)
 need(spec is not None and spec.loader is not None,'canonical helper available')
 mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 return mod
orbit=helper('mixed_chart_reference_orbits').audit(BASE)
need(orbit['ordered_configurations']==24300 and orbit['actual_stabilizer_orbits']==44,'complete actual orbit transport')
anchor=helper('all_first_root_source_types')
mass,vecs,classes=anchor.classes(2,4,1)
need(mass==F(221,675) and len(classes)==44,'same worst initial source')

vertices=[r for r in sources['six_prime_prefix_certificate.json']['rows'] if r['node'][:3]==[2,4,1]]
need(len(vertices)==4 and {r['node'][4] for r in vertices}=={1,2,3,4},'same source vertices')
vertex_lower=[]
for r in vertices:
 R=F(135,4)+F(9,20)*int(r['node'][4]==2)
 need(F(r['reserve_lower_bound_cell_units'])==R,'basic reserve without45/75 credits')
 vertex_lower.append((R-sum(map(F,r['rounded_loss_upper_bounds_cell_units'][:5]),F()))/135)
m7=F(source['unnormalized_mass_lower']);need(min(vertex_lower)==m7,'same source mass lower')
@lru_cache(None)
def later(s):return (F(4,7) if s[2]==0 else F(9,7**abs(s[2])))*common(s)
allmass=defaultdict(F)
for s in allrows:allmass[s[:2]]+=later(s)
rhs=dict(pairs=1,genuine_triples=2,triangle_cliques=1,quads=3,zero_pairs=1,zero_triangle_cliques=1,order=0)
vectors=[('source509',price,loads)]
def prices(name,entries,den):
 need(type(den) is int and den>0,'positive integer price denominator')
 ls=[F()]*len(rows);pp=F();seen=set()
 for kind,i,num in entries:
  need(kind in rhs and type(i) is int and 0<=i<len(cert[kind]),'verified509 row reference')
  need(type(num) is int and num>0 and (kind,i) not in seen,'unique strictly positive price')
  seen.add((kind,i));y=F(num,den);pp+=rhs[kind]*y
  for j,index in enumerate(cert[kind][i][:-1]):ls[index]+=(-1 if kind=='order' and j==1 else 1)*y
 return name,pp,ls
oldnew=sources['actual_anchor_zero_support_closure_certificate.json']
need(oldnew['source_certificate_sha256']==PINS['mixed_split_zero_support_bound_certificate.json'],'515 row identity')
for r in oldnew['representatives']:
 vectors.append(prices('anchor'+','.join(map(str,r['phase'])),r['prices'],oldnew['denominator']))
cp=BASE/'mixed_reference_zero_support_closure_certificate.json';raw=cp.read_bytes();new=json.loads(raw)
need(new['schema']=='mixed-reference-zero-support-prices-v1' and new['source_certificate_sha256']==PINS['mixed_split_zero_support_bound_certificate.json'],'new row identity')
for r in new['prices']:vectors.append(prices(r['name'],r['rows'],new['denominator']))
need(len(vectors)==7 and len({v[0] for v in vectors})==7,'seven declared price vectors')
coeff=[]
for name,pp,ls in vectors:
 groups=defaultdict(list)
 for s,l in zip(rows,ls):groups[s[:2]].append((l/later(s),later(s),l))
 cc={}
 for ab in allmass:
  entries=sorted(groups[ab]);rat=[e[0] for e in entries];SL=[F()];SD=[F()]
  for _,w,l in entries:SL.append(SL[-1]+w);SD.append(SD[-1]+l)
  cc[ab]=(rat,SL,SD)
 coeff.append(cc)
@lru_cache(None)
def term(k,ab,t):
 rat,SL,SD=coeff[k][ab];i=bisect_left(rat,t)
 return t*(SL[i]-allmass[ab])-SD[i]
def upper(t,total,k):return vectors[k][1]+total+sum((term(k,ab,w) for ab,w in t.items()),F())

def legal(m):
 return [r for r in range(m) if all(r%d!=a for d,a in ((3,0),(5,0),(9,1),(15,2),(25,1),(27,4)) if m%d==0)]
cells=[n for n in range(675) if all(n%d!=a for d,a in ((3,0),(5,0),(9,1),(15,2),(25,1),(27,4)))]
legal45,legal75=legal(45),legal(75)
need((len(cells),len(legal45),len(legal75))==(221,17,33),'literal joint source domain')
phase_removed={(r,s):tuple(n for n in cells if n%45==r or n%75==s) for r,s in product(legal45,legal75)}
credit={}
for r,s in phase_removed:
 c=F(1,45)+F(1,75)-F(sum(n%45==r for n in cells)+sum(n%75==s for n in cells),675)
 formula=F(int(r%9==4),135)+F(int(r%5==1),225)-F(int(r%9==4 and r%5==1),675)+F(4*int(s%3==1),675)
 need(c==formula and c>=0,'same-phase pure-overlap credit')
 credit[r,s]=c
@lru_cache(None)
def conditional(p,E,res,ref):
 if res==ref:return tuple((f,F((p-1)*p**E,p**f)) for f in range(E+1,39))
 z=res-ref;v=0
 while z%p==0:z//=p;v+=1
 return ((v+1,F(1)),)
results=[];totals=defaultdict(int)
for sig,meta in classes.items():
 a3,b3,a5,b5=ref=meta['reference'];aa,bb,aA,bA,oA,aB,bB,oB=[vecs[i] for i in sig]
 initial={}
 for u,v in allmass:
  v3=aa if u>0 else bb
  v5=(aA if v>0 else bA if v<0 else oA) if u>0 else (aB if v>0 else bB if v<0 else oB)
  initial[u,v]=v3[abs(u)]*v5[abs(v) if v else 1]
 # The A6 comparison covers all actual phase pairs if already belowm7.
 base_values=[upper(initial,mass,k) for k in range(7)]
 best=min(range(7),key=lambda k:base_values[k])
 if base_values[best]<m7:
  results.append({**meta,'method':'A6','price':vectors[best][0],'upper':str(base_values[best]),'minimum_margin':str(m7-base_values[best]),'covered_phase_pairs':561})
  totals[vectors[best][0]]+=561
  continue
 bycell={}
 for n in cells:
  x,y=n%27,n%25;sg=1 if x%3==2 else -1
  xs=[(sg*f,p) for f,p in conditional(3,3,x,a3 if sg==1 else b3)]
  if y%5==a5%5:ys=[(f,p) for f,p in conditional(5,2,y,a5)]
  elif y%5==b5%5:ys=[(-f,p) for f,p in conditional(5,2,y,b5)]
  else:ys=[(0,F(1))]
  bycell[n]={(u,v):p*q/675 for (u,p),(v,q) in product(xs,ys) if (u,v) in allmass}
 literal={ab:F() for ab in allmass}
 for dd in bycell.values():
  for ab,w in dd.items():literal[ab]+=w
 need(literal==initial,'each class matches its literal CRT chart')
 margins=[];counts=defaultdict(int);worst=None
 for (r,s),ns in phase_removed.items():
  t=dict(initial)
  for n in ns:
   for ab,w in bycell[n].items():t[ab]-=w
  need(all(w>=0 for w in t.values()),'nonnegative refined initial weights')
  total=F(221-len(ns),675);lower=m7+credit[r,s];chosen=None
  for k in range(7):
   value=upper(t,total,k)
   if value<lower:chosen=k;break
  need(chosen is not None,'strict closure in every actual reference/phase chart')
  gap=lower-value;margins.append(gap);name=vectors[chosen][0];counts[name]+=1;totals[name]+=1
  if worst is None or gap<F(worst['margin']):worst={'phase':[r,s],'lower':str(lower),'upper':str(value),'margin':str(gap),'price':name}
 need(len(margins)==561,'all561 globally fixed phase choices')
 results.append({**meta,'method':'A8+reserve','covered_phase_pairs':561,'minimum_margin':str(min(margins)),'worst':worst,'price_counts':dict(counts)})
need(len(results)==44 and sum(r['configuration_count'] for r in results)==24300,'all44 orbit representatives')
need(sum(r['covered_phase_pairs'] for r in results)==44*561 and sum(totals.values())==44*561,'all24684 representative phase cases')
minimum=min(results,key=lambda r:F(r['minimum_margin']));gap=F(minimum['minimum_margin'])
need(gap>F(1,3000000),'strict all-reference source separation, not a Haar floor')
out={'inputs':PINS,'certificate_sha256':hashlib.sha256(raw).hexdigest(),'source_mass_lower':str(m7),'basic_vertex_lowers':list(map(str,vertex_lower)),
     'orbit_audit':orbit,'full_profiles':len(allrows),'middle_profiles':len(rows),'reference_orbits':44,'reference_prefix_configurations':24300,
     'phase_pairs_per_orbit':561,'representative_phase_cases':44*561,'price_counts':dict(totals),
     'price_vectors':[{'name':name,'row_price':str(pp),'negative_loads':sum(l<0 for l in ls)} for name,pp,ls in vectors],
     'minimum_margin':str(gap),'minimum':minimum,'orbits':results,
     'scope':'Same-source exact-zero noncoverage in all worst-source reference charts for split3/5/7 and common11/13/17/19. Finite tree maps and rational comparisons checked; full scope uses existing nonworst and deleted-root reductions. Original later labels retain one global centre selector. No uniform Haar constant, other split pattern, new geometry, optimizer or Lean claim.'}
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
else:need(out==json.loads(Path(__file__).with_suffix('.json').read_text()),'retained all-reference result mismatch')
print(json.dumps({'orbits':44,'representative_phase_cases':44*561,'minimum_margin':str(gap),'minimum_margin_float':float(gap),'minimum_reference':minimum['reference'],'price_counts':dict(totals)},indent=2))
