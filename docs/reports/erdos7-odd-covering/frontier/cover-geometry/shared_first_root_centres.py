"""Exact certificates for two centres sharing first digits at3 and5.

All old centre coordinates other than3 and5 share every queried prefix.
Reconstruct the joint six-anchor and completed-pure profile universes, verify
literal same-label pair inventories, pay every overflow and released pure tail,
and compare the adjacent retained result by default. No scratch producer,
solver or graph is imported. Ordinary proofs supply the source/closure bridge.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from functools import lru_cache
from itertools import product
from math import prod,factorial
import argparse,json,hashlib,importlib.util
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
M7=F(7235955529,450000000000)
PURE_RELEASE=F(1,2*3**12)+F(1,4*5**8)
H_FLOOR=F(1,200000000)
PAIRS=[(1,1),(2,2)]+[v for f in range(3,39) for v in ((f,2),(2,f))]
PI={v:i for i,v in enumerate(PAIRS)}

def need(value,message):
 if not value:raise ValueError(message)

def atom(p,c,f):return 1-c/p if f==1 else c*F(p-1,p**f)

def valuation(n,p):
 need(n!=0,'nonzero finite valuation argument');v=0
 while n%p==0:n//=p;v+=1
 return v

@lru_cache(None)
def anchor_coordinate(p,E,a,b,cells):
 need(valuation(a-b,p)==1,'joint anchor has split depth1')
 out=[F() for _ in PAIRS]
 for x in cells:
  if x in (a,b):
   for f in range(E+1,39):out[PI[(f,2) if x==a else (2,f)]]+=F(p-1,p**f)
  else:out[PI[valuation(x-a,p)+1,valuation(x-b,p)+1]]+=F(1,p**E)
 need(sum(out)+sum(x in cells for x in (a,b))*F(1,p**38)==F(len(cells),p**E),
      'all anchor shells and omitted reference tails accounted')
 return tuple(out)

def anchor_weight_classes():
 r1=tuple(x for x in range(27) if x%3==1 and x%9!=1 and x!=4)
 r2=tuple(x for x in range(27) if x%3==2)
 V=tuple(y for y in range(25) if y%5!=0 and y!=1)
 W=tuple(y for y in V if y%5!=2)
 need(len(r1)*len(V)+len(r2)*len(W)==221,'joint six-anchor carrier size')
 literal=sum(all(n%m!=a for a,m in ((0,3),(1,9),(4,27),(0,5),(1,25),(2,15))) for n in range(675))
 need(literal==221,'literal normalized six-anchor mass')
 vecs=[];index={}
 def intern(v):
  if v not in index:index[v]=len(vecs);vecs.append(v)
  return index[v]
 threes={}
 for a in range(27):
  for b in range(27):
   if a%3 in (1,2) and a%3==b%3 and a%9!=b%9:
    threes[a,b]=(intern(anchor_coordinate(3,3,a,b,r1)),intern(anchor_coordinate(3,3,a,b,r2)))
 fives={}
 for a in range(25):
  for b in range(25):
   if a%5 and a%5==b%5 and a!=b:
    fives[a,b]=(intern(anchor_coordinate(5,2,a,b,V)),intern(anchor_coordinate(5,2,a,b,W)))
 classes={}
 for (a3,b3),v3 in threes.items():
  for (a5,b5),v5 in fives.items():
   classes.setdefault(v3+v5,{'reference':[a3,b3,a5,b5],'configuration_count':0})['configuration_count']+=1
 need(len(threes)==108 and len(fives)==80,'all admissible ordered shallow reference pairs')
 need(len(classes)==55 and sum(x['configuration_count'] for x in classes.values())==8640,
      'all8640 references in55 exact weight classes')
 return vecs,classes

def pure_law(p,h):
 """Exact two-reference shell law, with complete pure mass at the minimum."""
 need(p in (3,5) and 1<=h<38,'finite shared-prefix comparison regime')
 alpha=F(1,2) if p==3 else F(3,4)
 d={(1,1):alpha-F(1,p)}
 for j in range(1,h):d[j+1,j+1]=F(p-1,p**(j+1))
 d[h+1,h+1]=F(p-2,p**(h+1))
 for f in range(h+2,39):d[f,h+1]=d[h+1,f]=F(p-1,p**f)
 need(min(d.values())>=0 and sum(d.values())+F(2,p**38)==alpha,
      'positive pure comparison and full two-reference tail mass')
 return d

def universe(pairs3,pairs5):
 local=[];profiles=[]
 for a3,b3 in pairs3:
  for a5,b5 in pairs5:
   a=(a3,a5);b=(b3,b5)
   L=prod(a)+prod(b)-prod(min(x,y) for x,y in zip(a,b))
   if L<=38:local.append((a,b,L))
 def descend(li,L,fs=()):
  if len(fs)==5:
   Q=L*prod(fs)
   if Q>=20:profiles.append((li,fs,Q))
   return
  for f in range(1,38//(L*prod(fs))+1):descend(li,L,fs+(f,))
 for i,(a,b,L) in enumerate(local):descend(i,L)
 need(len(set(profiles))==len(profiles),'distinct reconstructed profiles')
 return local,profiles

def common_distribution():
 dist={1:F(1)}
 for p,c in CAPS:
  need(0<=1-c/p<=1,'positive normalized common baseline')
  nxt=defaultdict(F)
  for r,w in dist.items():
   cap=38//r
   need(sum(atom(p,c,f) for f in range(1,cap+1))+c/F(p**cap)==1,
        'full geometric common-coordinate tail retained')
   for f in range(1,cap+1):nxt[r*f]+=w*atom(p,c,f)
  dist=dict(nxt)
 return dist

def dual(cert,local,profiles,canonical,keep):
 D=int(cert['denominator']);need(D>0,'positive rational dual denominator')
 inc=[0]*len(profiles);budget=0;seen=set();mink=None;capacities=set()
 @lru_cache(None)
 def inventory(i):
  li,fs,Q=profiles[i];a,b,L=local[li]
  A=set(product(*(range(f) for f in a+fs)))
  B=set(product(*(range(f) for f in b+fs)))
  need(len(A|B)==Q,'literal seven-coordinate union cardinality')
  return A,B
 for i,j,z0 in cert['edges']:
  z=int(z0)
  need(type(i) is int and type(j) is int and 0<=i<j<len(profiles) and z>0 and (i,j) not in seen,
       'distinct positive dual edges with valid indices')
  seen.add((i,j));need(keep(profiles[i][0]) and keep(profiles[j][0]),'no edge uses a separately paid deep-cylinder endpoint')
  A,B=inventory(i);C,E=inventory(j)
  N=sum(max(int(d in A)+int(d in C),int(d in B)+int(d in E)) for d in A|B|C|E)
  qi=profiles[i][2];qj=profiles[j][2]
  need(max(qi,qj)+1<=N<=qi+qj,'literal same-label inventory capacity range')
  K=canonical.mixed_pair(qi,qj,N)
  need(K>0,'positive exact pair bound')
  mink=K if mink is None else min(mink,K)
  capacities.add((min(qi,qj),max(qi,qj),N))
  inc[i]+=z;inc[j]+=z;budget+=z
 need(mink is not None and mink<=16,'valid fibre threshold')
 return [F(z,D) for z in inc],F(budget,D),mink,len(seen),capacities

def bound(weights,free,cover,budget):
 residual=sum(max(F(),w-c) for w,c in zip(weights,cover))
 return free+budget+residual,residual

def check_anchor(cert,canonical,dist):
 local,profiles=universe(PAIRS,PAIRS)
 need(len(local)==560 and len(profiles)==4863,'complete joint-anchor universe')
 cover,budget,kappa,edges,capacities=dual(cert,local,profiles,canonical,lambda _:True)
 need(kappa==F(8,15) and edges==1213,'joint certificate edge count and strength')
 factors=[prod(atom(p,c,f) for (p,c),f in zip(CAPS,fs)) for li,fs,q in profiles]
 good={n:{L:sum(w for r,w in dist.items() if L*r<n) for a,b,L in local} for n in (20,39)}
 vecs,classes=anchor_weight_classes();results=[]
 for key,meta in classes.items():
  r1,r2,V,W=(vecs[i] for i in key)
  ws=[r1[PI[a[0],b[0]]]*V[PI[a[1],b[1]]]+r2[PI[a[0],b[0]]]*W[PI[a[1],b[1]]] for a,b,L in local]
  weights=[ws[li]*f for (li,fs,q),f in zip(profiles,factors)]
  tail=F(221,675)-sum(w*good[39][L] for w,(a,b,L) in zip(ws,local))
  bad=F(221,675)-sum(w*good[20][L] for w,(a,b,L) in zip(ws,local))
  need(0<=tail<=bad and sum(weights)+tail==bad,'all joint profile and overflow mass accounted')
  upper,residual=bound(weights,tail,cover,budget)
  need(upper<M7,'strict joint-anchor gap in every weight class')
  results.append({**meta,'exact_upper':str(upper),'free_tail39':str(tail),
                  'unpaid_vertex_mass':str(residual),'single_BAD_upper':str(bad)})
 results.sort(key=lambda r:F(r['exact_upper']),reverse=True)
 U=F(results[0]['exact_upper']);haar=(M7-U)*kappa/F(16632)
 need(haar>H_FLOOR,'joint-anchor route exceeds uniform Haar floor')
 return {'h3':1,'h5':1,'local_types':len(local),'profiles':len(profiles),'weight_classes':55,
         'reference_configurations':8640,'positive_dual_edges':edges,'minimum_K':str(kappa),
         'bounded_event':'actual original fibre mass <1/2310',
         'fibre_threshold':str(kappa/F(1232)),'dual_edge_budget':str(budget),
         'uniform_exact_upper':str(U),'uniform_upper_float':float(U),
         'original_Haar_lower':str(haar),'original_Haar_lower_float':float(haar),
         'all_classes':results},capacities

def check_generic(cert,canonical,dist):
 h3,h5,cutoff=cert['h3'],cert['h5'],cert['free_high5_cutoff']
 law3,law5=pure_law(3,h3),pure_law(5,h5)
 local,profiles=universe(law3,law5)
 def keep(li):
  a,b,L=local[li];return not cutoff or max(a[1],b[1])<=cutoff
 if cutoff:
  need(cutoff==h5==4 and h3==1,'uniform common5 prefix cylinder regime')
  need(all(a[1]==b[1] for li,(a,b,L) in enumerate(local) if keep(li)),
       'retained quinary valuations are identical before the common-depth cutoff')
  retained5=sum(w for (a,b),w in law5.items() if max(a,b)<=cutoff)
  need(retained5==F(3,4)-F(1,5**cutoff),'complete deep5 cylinder paid separately')
 cover,budget,kappa,edges,capacities=dual(cert,local,profiles,canonical,keep)
 need(kappa==F(1,3),'generic common fibre threshold')
 expected={(1,2):(4378,836),(1,3):(4163,680),(2,1):(4378,837),(1,4):(4051,473)}
 need((len(profiles),edges)==expected[h3,h5],'complete generic profile and certificate size')
 ws=[law3[a[0],b[0]]*law5[a[1],b[1]] for a,b,L in local]
 weights=[(ws[li] if keep(li) else F())*prod(atom(p,c,f) for (p,c),f in zip(CAPS,fs)) for li,fs,q in profiles]
 good={n:{L:sum(w for r,w in dist.items() if L*r<n) for a,b,L in local} for n in (20,39)}
 free=F(3,8)-sum(w*good[39][L] for li,(w,(a,b,L)) in enumerate(zip(ws,local)) if keep(li))
 augmentedbad=F(3,8)-sum(w*good[20][L] for li,(w,(a,b,L)) in enumerate(zip(ws,local)) if keep(li))
 need(free>=0 and sum(weights)+free==augmentedbad,
      'complete retained, overflow and deep-cylinder accounting without double counting')
 ideal,residual=bound(weights,free,cover,budget)
 upper=ideal+PURE_RELEASE;gap=M7-upper
 need(gap>0,'strict generic gap after explicit finite pure release')
 haar=gap*kappa/F(16632);need(haar>H_FLOOR,'generic route exceeds uniform Haar floor')
 return {'name':cert['name'],'h3':h3,'h5':h5,'h5_range':'>=4, including infinity' if cutoff else str(h5),
         'profiles':len(profiles),'local_types':len(local),'positive_dual_edges':edges,
         'minimum_K':str(kappa),'bounded_event':'actual original fibre mass <1/3696',
         'fibre_threshold':str(kappa/F(1232)),'ideal_upper':str(ideal),'ideal_upper_float':float(ideal),
         'released_pure_tail_upper':str(PURE_RELEASE),'finite_prefix_upper':str(upper),
         'finite_prefix_upper_float':float(upper),'strict_gap':str(gap),
         'original_Haar_lower':str(haar),'original_Haar_lower_float':float(haar),
         'free_mass':str(free),'free_common5_cylinder':str(F(1,2*5**cutoff)) if cutoff else '0',
         'dual_edge_budget':str(budget),'unpaid_vertex_mass':str(residual)},capacities

def inherited(input_dir):
 expected={
  'independent_center_multiple_coordinates.json':'e9b66696fd2a1df603379b2b374fe41de5c42a1cd1103414415dda654a5c24d0',
  'two_coordinate_first_root_centres.json':'1982ce7e5ef22cd66062e2e59f63332a758496de21d41d1694d1f2e8e30acbe5'}
 data={}
 for name,digest in expected.items():
  raw=(input_dir/name).read_bytes();need(hashlib.sha256(raw).hexdigest()==digest,'inherited numerical result identity '+name)
  data[name]=json.loads(raw)
 deep=F(data['independent_center_multiple_coordinates.json']['original_Haar_lower'])
 need(deep==F(148455529,467775000000000) and deep>H_FLOOR,'479 deeper-prefix Haar bound')
 nonworst=F(data['two_coordinate_first_root_centres.json']['nonworst']['strict_original_Haar_lower'])
 need(nonworst==F(266133457,233887500000000) and nonworst>H_FLOOR,'485 nonworst arbitrary-depth Haar bound')
 # A shared deleted first root is removed by finite augmentation, and both
 # centres can then be made equal through its remaining queried depths.
 # The other exceptional coordinate still shares its first digit. Report478
 # (also cited explicitly in483) supplies this single-coordinate branch.
 deleted=F(1,15592500);need(deleted>H_FLOOR,'inherited shared-root single-coordinate bound')
 return {'numerical_inputs':expected,'deeper_prefix_original_Haar_lower':str(deep),
         'nonworst_original_Haar_strict_lower':str(nonworst),
         'deleted_root_original_Haar_strict_lower':str(deleted),
         'inherited_result_producers_rerun':False}

def tail():
 B=10000000000;ell=20;c=F(2*ell*ell+1,2*ell*ell-1);M2=F(14003665,540672)
 need(B>=286 and ell>=4 and 3**ell<=B,'Chapter33 analytic tail premises')
 series=sum(F(factorial(7),factorial(7-j)*ell**j) for j in range(8))
 tau=c**7/F(B)*F(B,B-3)**2*series;loss=M2*tau;remaining=H_FLOOR-loss
 need(remaining>F(1,1000000000),'strict remaining distorted tail mass')
 return {'B':B,'ell':ell,'c':str(c),'head_second_moment_factor':str(M2),
         'falling_factorial_series':str(series),'tau7':str(tau),'loss_upper':str(loss),
         'loss_upper_float':float(loss),'head_Haar_seed_strict_lower':str(H_FLOOR),
         'remaining_distorted_mass_lower':str(remaining),
         'remaining_distorted_mass_lower_float':float(remaining),
         'remaining_distorted_mass_strict_lower':'1/1000000000',
         'ordinary_analytic_input':'Inherited Chapter33 SH11-SH13 prime-product estimate; not reproved by this checker.'}

def verify(certificate,input_dir,canonical):
 need(canonical.CAPS==CAPS and canonical.M7==M7,'canonical source constants')
 identities=canonical.source_inputs(input_dir)
 need(canonical.mixed_pair(20,39,40)==0,'free load-overflow zero witness')
 need(all(canonical.mixed_pair(q,q,2*q)==0 for q in range(20,39)),
      'same-profile diagonal has no positive pair edge')
 certs=certificate['certificates']
 need(len(certs)==5 and len({c['name'] for c in certs})==5,'five distinct certificates')
 joint=[c for c in certs if c['kind']=='joint-anchor']
 generic=[c for c in certs if c['kind']=='pure-product']
 need(len(joint)==1 and len(generic)==4,'joint and generic certificate kinds')
 need({(c['h3'],c['h5'],c['free_high5_cutoff']) for c in generic}=={(1,2,0),(1,3,0),(2,1,0),(1,4,4)},
      'all four generic depth regimes')
 dist=common_distribution();anchor,capacities=check_anchor(joint[0],canonical,dist);results=[]
 for cert in generic:
  result,cs=check_generic(cert,canonical,dist);results.append(result);capacities|=cs
 reused=inherited(input_dir)
 H=min([F(anchor['original_Haar_lower'])]+[F(r['original_Haar_lower']) for r in results])
 need(H>H_FLOOR,'uniform newly checked head Haar floor')
 return {'scope':'Original finite odd distinct-label family on3,5,7,11,13,17,19,23,29; each complete later numerical label independently chooses one of two fixed centres; centres share first digits at3 and5 and every queried digit at the other five old coordinates; arbitrary later separation depths and phases.',
         'source_inputs':identities,'joint_anchor':anchor,'generic_regimes':results,
         'total_verified_edge_occurrences':anchor['positive_dual_edges']+sum(r['positive_dual_edges'] for r in results),
         'distinct_pair_capacity_triples':len(capacities),
         'finite_pure_prefix_depths':{'3':12,'5':8},'released_pure_tail_upper':str(PURE_RELEASE),
         'new_certificate_Haar_lower':str(H),'new_certificate_Haar_lower_float':float(H),
         'inherited_routes':reused,'uniform_original_Haar_strict_lower':str(H_FLOOR),
         'depth_partition':['h3=1,h5=1','h3=1,h5=2','h3=1,h5=3','h3=1,h5>=4, including infinity',
                            'h3=2,h5=1','h3>=2,h5>=2 or h3>=3,h5>=1, including infinity'],
         'unrestricted_large_prime_tail':tail(),
         'boundary':'Ordinary rational certificate, not a Lean result. The fixed complete source, its normalization and continuous-budget interpolation, full theoretical graph upward closure, baseline pure-subtraction, finite deleted-root reduction, inherited479/485 cases, and analytic Chapter33 tail estimate remain ordinary inputs or arguments. Free deep5 mass is paid separately and need not be graph-independent. First-root disagreement at one or both3/5 is outside this statement. Source producers and Lean are not rerun; unrestricted Erdos7 is unresolved.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
 ap.add_argument('--certificate',type=Path,default=Path(__file__).with_name('shared_first_root_centres_certificate.json'))
 ap.add_argument('--output',type=Path);args=ap.parse_args()
 spec=importlib.util.spec_from_file_location('canonical_pair',args.input_dir/'fixed_anchor_two_fibre.py')
 canonical=importlib.util.module_from_spec(spec);spec.loader.exec_module(canonical)
 raw=args.certificate.read_bytes();result=verify(json.loads(raw),args.input_dir,canonical)
 result['certificate_sha256']=hashlib.sha256(raw).hexdigest()
 text=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(text)
 else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==result,'retained exact result differs')
 print(json.dumps({'joint_weight_classes':result['joint_anchor']['weight_classes'],
                   'joint_configurations':result['joint_anchor']['reference_configurations'],
                   'generic_regimes':len(result['generic_regimes']),
                   'total_verified_edge_occurrences':result['total_verified_edge_occurrences'],
                   'new_certificate_Haar_lower_float':result['new_certificate_Haar_lower_float'],
                   'uniform_original_Haar_strict_lower':result['uniform_original_Haar_strict_lower'],
                   'tail_B':result['unrestricted_large_prime_tail']['B']}))

if __name__=='__main__':main()
