"""Exact support certificates for two centres with mixed first-root agreement.

Reconstructs all profiles and all six-anchor weight classes. Each positive
clique row is verified by literal original-label inventories. No optimizer,
scratch graph or producer is used. Default execution compares adjacent data.
The source construction and the full-graph comparison bridge remain ordinary
mathematical inputs; this is not a Lean theorem or unrestricted E7 settlement.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from functools import lru_cache
from itertools import product,combinations
from math import prod,factorial
import argparse,json,hashlib,importlib.util

CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
M7=F(7235955529,450000000000)
EPSILON=F(1,2*3**12)+F(1,4*5**8)
FLOOR=F(1,80000000000)
def need(b,msg):
 if not b:raise ValueError(msg)
def atom(p,c,f):return 1-c/p if f==1 else c*F(p-1,p**f)
def valuation(n,p):
 need(n!=0,'nonzero finite valuation input');v=0
 while n%p==0:n//=p;v+=1
 return v
def pairs(h):
 return [(j+1,j+1) for j in range(h+1)]+[v for f in range(h+2,39) for v in ((f,h+1),(h+1,f))]
def pure(p,h):
 alpha=F(1,2) if p==3 else F(3,4)
 d={(1,1):alpha-F(1 if h else 2,p)}
 for j in range(1,h):d[j+1,j+1]=F(p-1,p**(j+1))
 if h:d[h+1,h+1]=F(p-2,p**(h+1))
 for f in range(h+2,39):d[f,h+1]=d[h+1,f]=F(p-1,p**f)
 need(min(d.values())>=0 and sum(d.values())+F(2,p**38)==alpha,'positive pure law with complete tail')
 return d
def universe(h3,h5):
 local=[];profiles=[]
 for a3,b3 in pairs(h3):
  for a5,b5 in pairs(h5):
   a=(a3,a5);b=(b3,b5);L=prod(a)+prod(b)-prod(min(x,y) for x,y in zip(a,b))
   if L<=38:local.append((a,b,L))
 def descend(li,L,fs=()):
  if len(fs)==5:
   Q=L*prod(fs)
   if Q>=20:profiles.append((li,fs,Q))
   return
  for f in range(1,38//(L*prod(fs))+1):descend(li,L,fs+(f,))
 for li,(a,b,L) in enumerate(local):descend(li,L)
 need(len(set(profiles))==len(profiles),'unique complete profile universe')
 return local,profiles
@lru_cache(None)
def cells(p,E,h,a,b,domain):
 if a!=b:need(valuation(a-b,p)==h,'reference split depth')
 else:need(h>=E,'shared finite prefix has a deeper split')
 d=defaultdict(F)
 for x in domain:
  if x not in (a,b):d[valuation(x-a,p)+1,valuation(x-b,p)+1]+=F(1,p**E)
  elif a!=b:
   for f in range(E+1,39):d[(f,h+1) if x==a else (h+1,f)]+=F(p-1,p**f)
  else:
   for j in range(E,h):d[j+1,j+1]+=F(p-1,p**(j+1))
   d[h+1,h+1]+=F(p-2,p**(h+1))
   for f in range(h+2,39):d[f,h+1]+=F(p-1,p**f);d[h+1,f]+=F(p-1,p**f)
 missing=(sum(t in domain for t in (a,b)) if a!=b else 2*int(a in domain))*F(1,p**38)
 need(sum(d.values())+missing==F(len(domain),p**E),'all reference-cell shells and tails accounted')
 return tuple(sorted(d.items()))
def joint_classes(h3,h5):
 R1=tuple(x for x in range(27) if x%3==1 and x%9!=1 and x!=4)
 R2=tuple(x for x in range(27) if x%3==2)
 V=tuple(y for y in range(25) if y%5 and y!=1)
 W=tuple(y for y in V if y%5!=2)
 need(len(R1)*len(V)+len(R2)*len(W)==221,'literal six-anchor joint cardinality')
 vectors=[];index={}
 def intern(v):
  if v not in index:index[v]=len(vectors);vectors.append(dict(v))
  return index[v]
 threes={};fives={}
 for a in range(27):
  for b in range(27):
   eligible=(a%3==2 and b%3==1) if h3==0 else (h3==1 and a%3 in (1,2) and a%3==b%3 and a%9!=b%9)
   if eligible:threes[a,b]=(intern(cells(3,3,h3,a,b,R1)),intern(cells(3,3,h3,a,b,R2)))
 for a in range(25):
  for b in range(25):
   eligible=(a%5 and b%5 and a%5!=b%5) if h5==0 else (a%5 and ((h5==1 and a%5==b%5 and a!=b) or (h5>=2 and a==b)))
   if eligible:fives[a,b]=(intern(cells(5,2,h5,a,b,V)),intern(cells(5,2,h5,a,b,W)))
 classes={}
 for (a,b),t in threes.items():
  for (c,d),u in fives.items():classes.setdefault(t+u,{'reference':[a,b,c,d],'configuration_count':0})['configuration_count']+=1
 expected=(121,32400) if h5==0 else ((20,6480) if h5==1 else (16,1620))
 need((len(classes),sum(v['configuration_count'] for v in classes.values()))==expected,'all shallow references in exact weight classes')
 return vectors,classes
def common_distribution():
 dist={1:F(1)}
 for p,c in CAPS:
  out=defaultdict(F)
  for r,w in dist.items():
   cap=38//r
   need(sum(atom(p,c,f) for f in range(1,cap+1))+c/F(p**cap)==1,'common-coordinate geometric tail')
   for f in range(1,cap+1):out[r*f]+=w*atom(p,c,f)
  dist=dict(out)
 return dist
def clique_dual(cert,local,profiles,keep,canonical):
 D=int(cert['denominator']);need(D>0,'positive denominator')
 inc=[0]*len(profiles);budget=0;seen=set();edges=set();capacities=set();minimum=None
 @lru_cache(None)
 def inventory(i):
  li,fs,Q=profiles[i];a,b,L=local[li]
  A=set(product(*(range(f) for f in a+fs)));B=set(product(*(range(f) for f in b+fs)))
  need(len(A|B)==Q,'literal seven-coordinate union inventory');return A,B
 for raw,z0 in cert['cliques']:
  vs=tuple(raw);z=int(z0)
  need(2<=len(vs)<=3 and vs==tuple(sorted(set(vs))) and all(type(i) is int and 0<=i<len(profiles) for i in vs) and vs not in seen and z>0,'valid distinct positive clique row')
  need(all(keep(profiles[i][0]) for i in vs),'no clique touches a separately paid deep cylinder')
  seen.add(vs);budget+=z
  for i in vs:inc[i]+=z
  for i,j in combinations(vs,2):
   if (i,j) in edges:continue
   edges.add((i,j));A,B=inventory(i);C,E=inventory(j)
   N=sum(max(int(x in A)+int(x in C),int(x in B)+int(x in E)) for x in A|B|C|E)
   qi=profiles[i][2];qj=profiles[j][2]
   need(max(qi,qj)+1<=N<=qi+qj,'same-label joint capacity bounds')
   K=canonical.mixed_pair(qi,qj,N);need(K>0,'every pair in every clique has positive exact K')
   minimum=K if minimum is None else min(minimum,K)
   capacities.add((min(qi,qj),max(qi,qj),N))
 need(minimum is not None and F(1,3)<=minimum<=16,'positive uniform fibre threshold')
 kappa=minimum if cert['kind']=='pure' else F(1,3)
 return [F(z,D) for z in inc],F(budget,D),kappa,minimum,seen,edges,capacities
def regime(cert,dist,canonical):
 h3,h5=cert['h3'],cert['h5'];cut3,cut5=cert['free_high3_cutoff'],cert['free_high5_cutoff']
 local,profiles=universe(h3,h5)
 def keep(li):
  a,b,L=local[li]
  return (not cut3 or max(a[0],b[0])<=cut3) and (not cut5 or max(a[1],b[1])<=cut5)
 if cut3:need(h3==cut3==6 and h5==0 and cert['kind']=='pure','uniform deep3 case')
 if cut5:need(h5==cut5==4 and h3==0 and cert['kind']=='joint','uniform deep5 case')
 for li,(a,b,L) in enumerate(local):
  if keep(li):
   if cut3:need(a[0]==b[0],'common3 valuations agree outside the paid cylinder')
   if cut5:need(a[1]==b[1],'common5 valuations agree outside the paid cylinder')
 cover,budget,kappa,minK,cliques,edges,capacities=clique_dual(cert,local,profiles,keep,canonical)
 factors=[prod(atom(p,c,f) for (p,c),f in zip(CAPS,fs)) for li,fs,q in profiles]
 good={n:{L:sum(w for r,w in dist.items() if L*r<n) for a,b,L in local} for n in (20,39)}
 candidates=[]
 if cert['kind']=='pure':
  law3,law5=pure(3,h3),pure(5,h5)
  if cut3:need(sum(w for (a,b),w in law3.items() if max(a,b)<=cut3)==F(1,2)-F(1,3**cut3),'entire common3 cylinder paid')
  ws=[law3[a[0],b[0]]*law5[a[1],b[1]] for a,b,L in local]
  candidates.append(({},ws));total=F(3,8);fee=EPSILON
 else:
  vectors,classes=joint_classes(h3,h5);total=F(221,675);fee=F()
  for key,meta in classes.items():
   t1,t2,f1,f2=(vectors[i] for i in key)
   ws=[t1.get((a[0],b[0]),F())*f1.get((a[1],b[1]),F())+t2.get((a[0],b[0]),F())*f2.get((a[1],b[1]),F()) for a,b,L in local]
   candidates.append((meta,ws))
 rows=[]
 for meta,ws in candidates:
  ws=[w if keep(li) else F() for li,w in enumerate(ws)]
  weights=[ws[li]*f for (li,fs,q),f in zip(profiles,factors)]
  free=total-sum(w*good[39][L] for w,(a,b,L) in zip(ws,local))
  bad=total-sum(w*good[20][L] for w,(a,b,L) in zip(ws,local))
  need(free>=0 and sum(weights)+free==bad,'exact full mass accounting without duplicate cylinder charges')
  residual=sum(max(F(),w-c) for w,c in zip(weights,cover));ideal=free+budget+residual;upper=ideal+fee
  need(upper<M7,'strict gap in every actual weight class')
  rows.append({**meta,'free_mass':str(free),'unpaid_vertex_mass':str(residual),'ideal_upper':str(ideal),'exact_upper':str(upper)})
 rows.sort(key=lambda r:F(r['exact_upper']),reverse=True);upper=F(rows[0]['exact_upper']);haar=(M7-upper)*kappa/F(16632)
 need(haar>F(1,2000000000),'every new regime has a strict original-Haar reserve')
 return {'name':cert['name'],'comparison':cert['kind'],'h3':h3,'h5':h5,'free_high3_cutoff':cut3,'free_high5_cutoff':cut5,
         'local_types':len(local),'profiles':len(profiles),'weight_classes':len(rows),'reference_configurations':sum(r.get('configuration_count',0) for r in rows),
         'clique_rows':len(cliques),'triangle_rows':sum(len(v)==3 for v in cliques),'distinct_edges':len(edges),'capacity_triples':len(capacities),
         'minimum_used_K':str(minK),'kappa':str(kappa),'fibre_threshold':str(kappa/F(1232)),'dual_budget':str(budget),
         'released_pure_tail_upper':str(fee),'uniform_upper':str(upper),'uniform_upper_float':float(upper),
         'original_Haar_lower':str(haar),'original_Haar_lower_float':float(haar),'all_classes':rows},capacities
def inherited(input_dir):
 expected={'two_coordinate_first_root_centres.json':'1982ce7e5ef22cd66062e2e59f63332a758496de21d41d1694d1f2e8e30acbe5',
           'shared_first_root_centres.json':'18ad1ceccf68f55a4ee359375571e4642c747604280fd4fc1094a1d51523cb82'}
 data={}
 for name,digest in expected.items():
  raw=(input_dir/name).read_bytes();need(hashlib.sha256(raw).hexdigest()==digest,'inherited result identity '+name);data[name]=json.loads(raw)
 split=data['two_coordinate_first_root_centres.json'];shared=data['shared_first_root_centres.json']
 need(F(split['uniform_no_anchor_strict_Haar_lower'])==FLOOR,'485 distinct-first-root bound')
 need(F(split['inherited_deleted_root_strict_Haar_lower'])==FLOOR,'484 inherited single-coordinate reduction bound')
 need(F(shared['uniform_original_Haar_strict_lower'])>FLOOR,'486 common-first-root bound')
 need(F(split['nonworst']['strict_original_Haar_lower'])>FLOOR,'all-depth nonworst sources')
 return {'numerical_inputs':expected,'different_first_roots_original_Haar_strict_lower':str(FLOOR),
         'shared_first_roots_original_Haar_strict_lower':shared['uniform_original_Haar_strict_lower'],
         'nonworst_original_Haar_strict_lower':split['nonworst']['strict_original_Haar_lower'],
         'deleted_root_original_Haar_strict_lower':str(FLOOR),'producers_rerun':False}
def tail():
 B=10**13;ell=27;c=F(2*ell*ell+1,2*ell*ell-1)
 M2=prod(F(p*(p+1),(p-1)**2) for p in (3,5,7,11,13,17,19,23,29))
 need(B>=286 and ell>=4 and 3**ell<=B,'inherited Chapter33 tail hypotheses')
 tau=c**7/F(B)*F(B,B-3)**2*sum(F(factorial(7),factorial(7-j)*ell**j) for j in range(8))
 loss=M2*tau;remaining=FLOOR-loss
 need(remaining>F(1,125000000000),'strict positive distorted tail reserve')
 return {'B':B,'ell':ell,'c':str(c),'M2':str(M2),'loss_upper':str(loss),'remaining_distorted_mass_lower':str(remaining),
         'remaining_distorted_mass_strict_lower':'1/125000000000','ordinary_input':'Chapter33 analytic prime-product estimate; not reproved by this checker.'}
def verify(certificates,input_dir,canonical):
 need(canonical.CAPS==CAPS and canonical.M7==M7,'canonical source constants')
 inputs=canonical.source_inputs(input_dir)
 need(canonical.mixed_pair(20,39,40)==0 and all(canonical.mixed_pair(q,q,2*q)==0 for q in range(20,39)),'overflow and diagonal zero witnesses')
 expected={(0,1,'joint',0,0),(0,2,'joint',0,0),(0,3,'joint',0,0),(0,4,'joint',0,4),(1,0,'joint',0,0),
           (2,0,'pure',0,0),(3,0,'pure',0,0),(4,0,'pure',0,0),(5,0,'pure',0,0),(6,0,'pure',6,0)}
 need(len(certificates)==10 and {(c['h3'],c['h5'],c['kind'],c['free_high3_cutoff'],c['free_high5_cutoff']) for c in certificates}==expected,'complete mixed-depth partition')
 dist=common_distribution();results=[];capacities=set()
 for cert in certificates:
  result,cs=regime(cert,dist,canonical);results.append(result);capacities|=cs
 H=min(F(r['original_Haar_lower']) for r in results)
 return {'scope':'Finite odd distinct original numerical moduli on3,5,7,11,13,17,19,23,29. Every later full label independently chooses one of two fixed old centres. Centres may differ arbitrarily at3 and5 and share every queried digit at the other five old primes. New certificates cover exactly one differing first digit; reports485/486 supply the other two first-root regimes.',
         'source_inputs':inputs,'regimes':results,'total_clique_rows':sum(r['clique_rows'] for r in results),
         'total_triangle_rows':sum(r['triangle_rows'] for r in results),'total_distinct_edges_by_regime':sum(r['distinct_edges'] for r in results),
         'distinct_capacity_triples':len(capacities),'new_regime_original_Haar_lower':str(H),'new_regime_original_Haar_lower_float':float(H),
         'inherited_routes':inherited(input_dir),'uniform_all_two_coordinate_original_Haar_strict_lower':str(FLOOR),
         'unrestricted_large_prime_tail':tail(),'boundary':'Ordinary exact rational certificates. The same completed conditional source, pair theorem and capacity monotonicity, full-relation upward closures, finite deleted-root reduction, inherited485/486 scope and Chapter33 analytic tail estimate remain ordinary inputs or deductions. Sparse clique constraints are used only after the full-graph closure; fully paid cylinders need not be independent. No new Lean certification; unrelated old phases and arbitrary varying remaining old coordinates are outside this statement; unrestricted Erdos7 remains open.'}
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
 ap.add_argument('--certificate',type=Path,default=Path(__file__).with_name('mixed_first_root_centres_certificate.json'))
 ap.add_argument('--output',type=Path);args=ap.parse_args()
 spec=importlib.util.spec_from_file_location('canonical_pair',args.input_dir/'fixed_anchor_two_fibre.py')
 canonical=importlib.util.module_from_spec(spec);spec.loader.exec_module(canonical)
 raw=args.certificate.read_bytes();result=verify(json.loads(raw)['certificates'],args.input_dir,canonical)
 result['certificate_sha256']=hashlib.sha256(raw).hexdigest();text=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(text)
 else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==result,'retained result differs')
 print(json.dumps({'regimes':len(result['regimes']),'clique_rows':result['total_clique_rows'],'triangle_rows':result['total_triangle_rows'],
                   'distinct_edges_by_regime':result['total_distinct_edges_by_regime'],'new_regime_Haar':result['new_regime_original_Haar_lower_float'],
                   'all_two_coordinate_Haar_floor':result['uniform_all_two_coordinate_original_Haar_strict_lower']}))
if __name__=='__main__':main()
