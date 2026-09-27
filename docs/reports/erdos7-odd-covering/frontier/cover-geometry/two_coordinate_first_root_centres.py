#!/usr/bin/env python3
"""Check simultaneous ternary/quinary first-root centre choices exactly.

Reconstruct all 7040 profiles and 24300 shallow configurations without a
producer graph or solver. The only project import is the canonical rational
pair optimizer/source verifier. The ordinary proof supplies the fixed complete
source, its normalization, upward-support closure, and original-family transfer.
Default execution compares the adjacent retained result; --output writes it.
"""
from fractions import Fraction as F
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
from itertools import product
from math import prod
import json,argparse,hashlib,importlib.util
CAPS=((7,F(3,2)),(11,F(5,3)),(13,F(3,2)),(17,F(2)),(19,F(9,5)))
M7=F(7235955529,450000000000)
MASS=F(221,675)
def need(b,msg):
 if not b:raise ValueError(msg)
def atom(p,c,f):return 1-c/p if f==1 else c*F(p-1,p**f)
def load(r,u,v):return u*v if r in ('AA','BB') else u if r[1]=='O' else u+v-1

def universe():
 rows=[];factors=[]
 def descend(r,u,v,L,fs):
  if len(fs)==5:
   Q=L*prod(fs)
   if Q>=20:rows.append((r,u,v,fs,Q));factors.append(prod(atom(p,c,f) for (p,c),f in zip(CAPS,fs)))
   return
  for f in range(1,38//(L*prod(fs))+1):descend(r,u,v,L,fs+(f,))
 for a,b in product('AB','ABO'):
  r=a+b
  for u in range(2,39):
   for v in ((1,) if b=='O' else range(2,39)):
    L=load(r,u,v)
    if L<=38:descend(r,u,v,L,())
 need(len(rows)==7040,'complete7040 profile universe');return rows,factors

@lru_cache(None)
def coordinate(p,E,ref,cells):
 out=[F() for _ in range(39)]
 for x in cells:
  if x==ref:
   for f in range(E+1,39):out[f]+=F(p-1,p**f)
  else:
   d=x-ref;e=0
   while d%p==0:d//=p;e+=1
   out[e+1]+=F(1,p**E)
 return tuple(out)

def classes():
 cells3A=tuple(x for x in range(27) if x%3==2)
 cells3B=tuple(x for x in range(27) if x%3==1 and x%9!=1 and x!=4)
 cells5W=tuple(y for y in range(25) if y%5 not in (0,2) and y!=1)
 cells5V=tuple(y for y in range(25) if y%5!=0 and y!=1)
 vecs=[];index={}
 def intern(v):
  if v not in index:index[v]=len(vecs);vecs.append(v)
  return index[v]
 t3A={a:intern(coordinate(3,3,a,cells3A)) for a in range(27) if a%3==2}
 t3B={b:intern(coordinate(3,3,b,cells3B)) for b in range(27) if b%3==1}
 t5={};n5={}
 for a in range(25):
  if a%5==0:continue
  for tag,cells in (('W',cells5W),('V',cells5V)):
   own=tuple(y for y in cells if y%5==a%5);t5[a,tag]=intern(coordinate(5,2,a,own))
 for a in range(25):
  for b in range(25):
   if not a%5 or not b%5 or a%5==b%5:continue
   for tag,cells in (('W',cells5W),('V',cells5V)):
    other=sum(y%5 not in (a%5,b%5) for y in cells);v=[F() for _ in range(39)];v[1]=F(other,25);n5[a,b,tag]=intern(tuple(v))
 out={};raw=0
 for a3,b3 in product(t3A,t3B):
  for a5 in range(25):
   if not a5%5:continue
   for b5 in range(25):
    if not b5%5 or a5%5==b5%5:continue
    key=(t3A[a3],t3B[b3],t5[a5,'W'],t5[b5,'W'],n5[a5,b5,'W'],t5[a5,'V'],t5[b5,'V'],n5[a5,b5,'V'])
    out.setdefault(key,{'count':0,'reference_example':[a3,b3,a5,b5]})['count']+=1;raw+=1
 need(raw==24300 and sum(v['count'] for v in out.values())==raw,'all24300 configurations');return vecs,out

def pair_law(p,h):
 """Full Haar joint reference factors, saturated at20; h=19 means h>=19."""
 out={}
 if h>=19:
  for j in range(19):out[j+1,j+1]=F(p-1,p**(j+1))
  out[20,20]=F(1,p**19)
 else:
  for j in range(h):out[j+1,j+1]=F(p-1,p**(j+1))
  out[h+1,h+1]=F(p-2,p**(h+1))
  for j in range(h+1,19):
   out[j+1,h+1]=F(p-1,p**(j+1))
   out[h+1,j+1]=F(p-1,p**(j+1))
  out[20,h+1]=F(1,p**19)
  out[h+1,20]=F(1,p**19)
 need(sum(out.values())==1 and min(out.values())>=0,'complete joint Haar shell law')
 return out


def nonworst(input_dir):
 data=json.loads((input_dir/'query_stoploss_completion.json').read_text())
 groups=defaultdict(list)
 for row in data['rows']:
  groups[tuple(row['node'][:3])].append(F(row['cores']['7']['live_mass_lower_cell_units'])/135)
 need(len(groups)==8 and all(len(v)==4 for v in groups.values()),'32 vertices in eight source types')
 mass=min(min(v) for key,v in groups.items() if key!=(2,4,1))
 need(mass==F(5891133457,225000000000),'seven nonworst source mass bounds')
 need(min(groups[2,4,1])==M7,'worst source type identity')
 dist={1:F(1)}
 for p,c in CAPS:
  law={1:1-c/p,**{f:atom(p,c,f) for f in range(2,20)},20:c/F(p**19)}
  need(sum(law.values())==1 and min(law.values())>=0,'positive normalized common comparison')
  nxt=defaultdict(F)
  for a,w in dist.items():
   for b,v in law.items():nxt[min(20,a*b)]+=w*v
  dist=dict(nxt)
 pay={t:sum(w for k,w in dist.items() if t*k>=20) for t in range(1,21)}
 need(all(pay[t]<=pay[t+1] for t in range(1,20)),'increasing later BAD payoff')
 rows=[]
 for h5 in range(20):
  five=pair_law(5,h5);five[1,1]-=F(1,4)
  need(min(five.values())>=0 and sum(five.values())==F(3,4),'quinary pure deletion at minimal payoff')
  @lru_cache(None)
  def g(a,b):
   return sum(w*pay[min(20,a*c+b*d-min(a,b)*min(c,d))]
              for (c,d),w in five.items())
  gg={u:g(u,1) for u in range(1,21)}
  need(all(gg[u]<=gg[u+1] for u in range(1,20)),'ternary max-valuation payoff increasing')
  need(all(gg[u]==g(1,u) for u in range(1,21)),'global centre symmetry after quinary integration')
  for h3 in range(20):
   if h3==0:
    three={2:F(5,18),**{u:F(4,3**u) for u in range(3,20)},20:F(2,3**19)}
    need(sum(three.values())==F(1,2),'distinct-root ternary upper-tail law')
    val=sum(w*gg[u] for u,w in three.items())
   else:
    three=pair_law(3,h3);three[1,1]-=F(1,2)
    need(min(three.values())>=0 and sum(three.values())==F(1,2),'same-root ternary pure deletion at minimal payoff')
    val=sum(w*g(a,b) for (a,b),w in three.items())
   rows.append({'h3':h3,'h5':h5,'ideal_BAD_upper':str(val)})
 need(len(rows)==400,'all separation depths including >=19 and coincidence')
 eps=F(1,2*3**12)+F(1,4*5**8)
 worst=max(rows,key=lambda r:F(r['ideal_BAD_upper']))
 upper=F(worst['ideal_BAD_upper'])+eps
 need((worst['h3'],worst['h5'])==(1,0),'nonworst maximum separation class')
 need(upper<F(1,40)<mass,'strict nonworst GOOD margin')
 haar=(mass-F(1,40))/F(27,2)/77
 need(haar>F(1,1000000),'nonworst original Haar floor')
 return {'separation_depth_pairs':400,'source_mass_lower':str(mass),'all_depth_cases':rows,
         'worst':worst,'released_pure_tail_upper':str(eps),
         'finite_prefix_BAD_upper':str(upper),'finite_prefix_BAD_upper_float':float(upper),
         'strict_BAD_upper':'1/40','strict_original_Haar_lower':str(haar),
         'readable_strict_original_Haar_lower':'1/1000000'}


def verify(certificate, input_dir, canonical):
 identities=canonical.source_inputs(input_dir)
 need(canonical.CAPS==CAPS and canonical.M7==M7,'canonical source constants')
 # These exact values support the ordinary full-graph upward closure and
 # free-overflow step; checking them is not a substitute for antitonicity.
 need(canonical.mixed_pair(20,39,40)==0,'free-overflow zero witness')
 need(all(canonical.mixed_pair(q,q,2*q)==0 for q in range(20,39)),
      'same-profile diagonal has no positive edge')
 rows,factors=universe()
 need(len(set(rows))==len(rows),'distinct reconstructed profiles')
 def local(r,u,v):
  return ((u if r[0]=='A' else 1,v if r[1]=='A' else 1),
          (u if r[0]=='B' else 1,v if r[1]=='B' else 1))
 certs=[];edge_values={};names=set()
 for cert in certificate['certificates']:
  name=cert['name'];need(isinstance(name,str) and name not in names,'distinct certificate names');names.add(name)
  D=int(cert['denominator']);need(D>0,'positive dual denominator')
  incident=[0]*len(rows);budget=0;seen=set();mink=None
  for i,j,z0 in cert['edges']:
   z=int(z0)
   need(type(i) is int and type(j) is int and 0<=i<j<len(rows) and z>0 and (i,j) not in seen,
        'distinct positive dual edges with valid indices')
   seen.add((i,j))
   if (i,j) not in edge_values:
    r,u,v,fs,qx=rows[i];t,s,w,gs,qy=rows[j]
    a,b=local(r,u,v);c,d=local(t,s,w)
    I=prod(min(f,g) for f,g in zip(fs,gs))
    conflict=I*(prod(min(x,y) for x,y in zip(a,d))+prod(min(x,y) for x,y in zip(b,c))-2)
    N=qx+qy-conflict
    need(max(qx,qy)+1<=N<=qx+qy,'full-label conflict inventory bounds')
    edge_values[i,j]=canonical.mixed_pair(qx,qy,N)
   K=edge_values[i,j];need(K>=F(1,3),'used edge supports common threshold')
   mink=K if mink is None else min(mink,K)
   incident[i]+=z;incident[j]+=z;budget+=z
  need(mink is not None,'nonempty edge certificate')
  certs.append({'name':name,'cover':[F(v,D) for v in incident],
                'budget':F(budget,D),'edges':len(seen),'minimum_K':mink})
 need(certs,'nonempty certificate family')
 dist={1:F(1)}
 for p,c in CAPS:
  need(0<=1-c/p<=1,'positive common baseline')
  nxt=defaultdict(F)
  for a,w in dist.items():
   cap=38//a
   need(sum(atom(p,c,f) for f in range(1,cap+1))+c/F(p**cap)==1,
        'full geometric shell tail retained')
   for f in range(1,cap+1):nxt[a*f]+=w*atom(p,c,f)
  dist=dict(nxt)
 good={n:{L:sum(w for k,w in dist.items() if L*k<n) for L in range(1,39)} for n in (20,39)}
 vecs,allclasses=classes();need(len(allclasses)==44,'44 complete weight classes')
 patterns=sorted(set((r,u,v) for r,u,v,fs,q in rows))
 # Every initial pattern capable of contributing below39 is represented.
 expected={(a+b,u,v) for a,b in product('AB','ABO') for u in range(2,39)
           for v in ((1,) if b=='O' else range(2,39)) if load(a+b,u,v)<=38}
 need(set(patterns)==expected,'all low initial loads included')
 count=sum(all(n%m!=a for a,m in ((0,3),(1,9),(4,27),(0,5),(1,25),(2,15)))
           for n in range(675))
 need(count==221 and F(count,675)==MASS,'literal six-anchor Haar mass')
 results=[]
 for key,meta in allclasses.items():
  a3,b3,aW,bW,oW,aV,bV,oV=(vecs[i] for i in key)
  coords={'AA':(a3,aW),'AB':(a3,bW),'AO':(a3,oW),'BA':(b3,aV),'BB':(b3,bV),'BO':(b3,oV)}
  anchor={(r,u,v):coords[r][0][u]*coords[r][1][v] for r,u,v in patterns}
  weights=[anchor[r,u,v]*w for (r,u,v,fs,q),w in zip(rows,factors)]
  g20=sum(w*good[20][load(r,u,v)] for (r,u,v),w in anchor.items())
  g39=sum(w*good[39][load(r,u,v)] for (r,u,v),w in anchor.items())
  tail=MASS-g39;bad=MASS-g20
  need(sum(weights)+tail==bad and 0<=tail<=bad<=MASS,'finite and all overflow mass conserved')
  bounds=[]
  for cert in certs:
   residual=sum(max(F(),w-c) for w,c in zip(weights,cert['cover']))
   upper=tail+cert['budget']+residual
   bounds.append({'certificate':cert['name'],'upper':str(upper),'unpaid_vertex_mass':str(residual)})
  best=min(bounds,key=lambda b:F(b['upper']))
  need(F(best['upper'])<M7,'every weight class has a strict dual gap')
  results.append({**meta,'selected_certificate':best['certificate'],'exact_upper':best['upper'],
                  'free_tail39':str(tail),'single_BAD_upper':str(bad),'certificate_bounds':bounds})
 need(sum(r['count'] for r in results)==24300,'every ordered reference configuration covered')
 results.sort(key=lambda r:F(r['exact_upper']),reverse=True)
 U=F(results[0]['exact_upper']);kappa=min(edge_values.values());gap=M7-U
 need(F(0)<kappa<=16 and kappa==F(1,3),'valid common small-fibre threshold')
 haar=gap*kappa/F(16632)
 need(haar>F(1,800000000),'pair route readable original Haar lower bound')
 nw=nonworst(input_dir)
 need(F(nw['strict_original_Haar_lower'])>haar,'nonworst margin exceeds pair route')
 # Deleted-root cases invoke reports483--484's finite-family reductions.
 # Their weaker inherited floor determines the no-anchor uniform statement.
 inherited=F(1,80000000000)
 need(haar>inherited and F(nw['strict_original_Haar_lower'])>inherited,
      'all freshly checked routes exceed inherited uniform floor')
 return {'scope':'Two fixed globally labelled centres split in the first digit at both3 and5 and share all queried old prefixes at7,11,13,17,19. Worst completed source: all24300 surviving-root shallow references under its six-anchor upper comparison. Seven other source types: all separation depths. Original full-label centre choices stay fixed.',
         'bounded_event':'actual original fibre mass <1/3696',
         'source_inputs':identities,'profiles':len(rows),'raw_reference_configurations':24300,
         'weight_classes':44,'anchor_survivors_mod675':count,
         'certificates':[{'name':c['name'],'positive_edges':c['edges'],'edge_budget':str(c['budget']),
                          'minimum_used_K':str(c['minimum_K'])} for c in certs],
         'distinct_verified_edges':len(edge_values),'kappa':str(kappa),
         'fibre_threshold':str(kappa/F(1232)),'m7':str(M7),
         'uniform_exact_upper':str(U),'uniform_upper_float':float(U),
         'uniform_strict_gap':str(gap),'uniform_gap_float':float(gap),
         'pair_route_Haar_lower':str(haar),'pair_route_Haar_lower_float':float(haar),
         'readable_pair_route_strict_Haar_lower':'1/800000000',
         'all_classes':results,'nonworst':nw,
         'inherited_deleted_root_strict_Haar_lower':str(inherited),
         'uniform_no_anchor_strict_Haar_lower':str(inherited),
         'boundary':'Ordinary exact certificate, not a new Lean result. Source construction, full-graph upward closure, conditional comparison, and deleted-root transfer are proved in the accompanying ordinary argument. Worst-source shared first-root splits remain outside this statement. Source producers and Lean are not rerun; unrestricted Erdos7 is unresolved.'}


def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
 ap.add_argument('--certificate',type=Path,default=Path(__file__).with_name('two_coordinate_first_root_centres_certificate.json'))
 ap.add_argument('--output',type=Path)
 args=ap.parse_args()
 spec=importlib.util.spec_from_file_location('canonical_pair',args.input_dir/'fixed_anchor_two_fibre.py')
 canonical=importlib.util.module_from_spec(spec);spec.loader.exec_module(canonical)
 raw=args.certificate.read_bytes()
 result=verify(json.loads(raw),args.input_dir,canonical)
 result['certificate_sha256']=hashlib.sha256(raw).hexdigest()
 text=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(text)
 else:need(json.loads(Path(__file__).with_suffix('.json').read_text())==result,'retained exact result differs')
 print(json.dumps({'profiles':result['profiles'],'weight_classes':result['weight_classes'],
                   'raw_reference_configurations':result['raw_reference_configurations'],
                   'distinct_verified_edges':result['distinct_verified_edges'],
                   'uniform_upper_float':result['uniform_upper_float'],
                   'pair_route_Haar_lower_float':result['pair_route_Haar_lower_float'],
                   'nonworst_separation_depth_pairs':result['nonworst']['separation_depth_pairs']}))

if __name__=='__main__':main()
