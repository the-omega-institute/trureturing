#!/usr/bin/env python3
"""Exact mixed45/75 source lower bounds on all561 actual phase pairs.

Uses explicitly supplied, content-addressed integer geometry inputs. Ordinary
formulas derive from Michael Schroeder, Nine Prime Divisors in Odd Distinct
Covering Systems, edition1.0.1, Sections6,8--9, DOI10.5281/zenodo.22759614.
No optimizer, source verifier import, geometry execution or Lean replay.
Source code copyright(c)2026 Michael Schroeder, MIT; input retains MIT notice.
Same-source screen domination and arbitrary-height comparison remain ordinary
mathematical premises. All masses are unnormalized; caps retain actual primes.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from functools import lru_cache
from hashlib import sha256
import argparse,json

GEOMETRY_SHA256='81fce342758faee5d8b9357d9b982ce79f6ebc8a9e417dd48bfd83b3e6537ca8'
PRIMES=(7,11,13,17,19)
THRESHOLDS=(2,4,4,8,8)
CAPS=tuple(F(p-1,p-1-t) for p,t in zip(PRIMES,THRESHOLDS))
# Full upstream batch schema; only t=2,4,8 enter the prefix consumer.
SOURCE_RATIOS=tuple(sorted({F(t,m) for t in (2,4,8,12) for m in range(1,t)}))
MODS=(3,9,27,5,15,45)
REGIONS=tuple(product((False,True),repeat=2))

def need(x,message):
 if not x:raise ValueError(message)

def rounded(x):
 need(x>=0,'nonnegative cost')
 return F(-(-x.numerator*10**10//x.denominator),10**10)

@lru_cache(None)
def cells(r):return tuple(x for x in range(135) if x%3 and x%9!=1 and x%27!=4 and x%5 and x%15!=2 and x%45!=r)

def weights(node,region):
 r,d,k,j,i=node
 return tuple((1 if region[0] else 4)*(1 if region[1] else 16-4*(x%5==1)-(x%5==j)-(4-i)*(x%3==d and x%5==k)) for x in cells(r))

def depth(p,positive,cutoff):
 if not positive:return ((0,F(1)),),(F(1),F()),(F(),F()),(F(1),F())
 kept=tuple((n,F(p-1,p**(n+1))) for n in range(1,cutoff))
 tail=F(1,p**cutoff),F(1,p**cutoff)*(cutoff+F(1,p-1))
 whole=F(1,p),F(1,p-1)
 retained=tuple(whole[i]-tail[i] for i in range(2))
 need((sum(w for n,w in kept),sum(n*w for n,w in kept))==retained,'exact infinite depth remainder')
 return kept,retained,tail,whole

def query(cs,ws,region,batches,used):
 uv=tuple(product(range(1,12) if region[0] else (0,),range(1,9) if region[1] else (0,)))
 lines=[str(len(cs))]+[f'{x} {w} 0' for x,w in zip(cs,ws)];labels=[]
 for u,v in uv:
  for t in SOURCE_RATIOS:
   den=t.denominator;nums=(den,den,den*(1+u),den*(1+v),den*(1+v),den*(1+v),den*(1+u)*(1+v))
   lines.append(' '.join(map(str,(len(labels),den,den,*nums,t.numerator))))
   labels.append((u,v,t,den))
 payload='\n'.join(lines)+'\n';key=sha256(payload.encode()).hexdigest()
 need(key in batches,'missing exact geometry input '+key)
 record=batches[key];need(record['query_payload']==payload,'full geometry input identity')
 raw=record['integer_maxima'];serialized=(json.dumps(raw,separators=(',',':'))+'\n').encode()
 need(sha256(serialized).hexdigest()==record['cache_file_sha256'],'integer output content identity')
 need(len(raw)==len(labels),'geometry output length')
 table={}
 for n,(row,(u,v,t,den)) in enumerate(zip(raw,labels)):
  need(len(row)==3 and all(type(q)is int for q in row) and row[0]==n and row[1]==den and 0<=row[2]<2**30,'integer geometry row')
  table[u,v,t]=F(row[2],den)
 used.add(key)
 return table

def linear(cs,ws,um,vm):
 a,u=um;b,v=vm;mass=sum(ws);peak=max(ws)
 inc=[max(sum(w for x,w in zip(cs,ws) if x%m==r) for r in range(m)) for m in MODS]
 return a*b*(mass+sum(inc))+u*b*inc[2]+a*v*sum(inc[3:])+(a+u)*(b+v)*peak

def envelope(node,batches,used):
 cs=cells(node[0]);mass=F();whole=F();values={t:F() for t in SOURCE_RATIOS}
 for region in REGIONS:
  ws=weights(node,region);need(all(w>=0 for w in ws),'nonnegative joint vertex weights')
  table=query(cs,ws,region,batches,used)
  ud,ur,ut,ua=depth(3,region[0],12);vd,vr,vt,va=depth(5,region[1],9)
  scale=F(1,(1 if region[0] else 6)*(1 if region[1] else 20))
  omitted=linear(cs,ws,ut,va)+linear(cs,ws,ur,vt)
  mass+=scale*ua[0]*va[0]*sum(ws);whole+=scale*linear(cs,ws,ua,va)
  for t in SOURCE_RATIOS:values[t]+=scale*(sum(p*q*table[u,v,t] for u,p in ud for v,q in vd)+omitted)
 return mass,whole,values

def distributions():
 table={1:F(1)};mean=F(1);out=[]
 for p,cap in zip(PRIMES,CAPS):
  out.append((dict(table),mean));nxt=defaultdict(F)
  for m,w in table.items():
   for e in range(31//m):nxt[m*(e+1)]+=w*(1-cap/p if e==0 else cap*F(p-1,p**(e+1)))
  table=nxt;mean*=1+cap/F(p-1)
 return out

def reserve(node):
 r,d,k,j,i=node;D=lambda h:F(h==1,5)+F(h==j,20)
 gamma=F(r%9==4);B=sum(x%3==d and x%5==k for x in cells(r))
 return F(135,4)+9*D(2)+gamma+(3-gamma)*D(r%5)+F(9,5)-F(B*(4-i),20)

def representative_map(r,s):
 # One map on3/5 transports BOTH phases. Preserve roots0,1,2 at5;
 # swap3/4 only when needed to put the45 ordinary root at3.
 sig=lambda x:(x%3,x%9==4,x%5==2,x%5==1)
 legal45=legal(45);rr=min(x for x in legal45 if sig(x)==sig(r));k=s%5
 if r%5!=rr%5:
  need({r%5,rr%5}=={3,4},'allowed root permutation')
  k=4 if k==3 else 3 if k==4 else k
 return rr,s%3,k

def finitephase_check(r,s):
 rr,d,k=representative_map(r,s)
 def swap(x,a,b):return b if x==a else a if x==b else x
 def crt(a,m,b,n):return next(x for x in range(a,m*n,m) if x%n==b)
 map3=[]
 for x in range(27):
  low=x%9
  if x%3==2:low=swap(low,r%9,rr%9)
  map3.append(low+9*(x//9))
 roots=list(range(5))
 if r%5!=rr%5:roots[3],roots[4]=4,3
 target=1 if k==1 else 0;map5=[]
 for x in range(25):
  digit=x//5
  if x%5==s%5:digit=swap(digit,(s%25)//5,target)
  map5.append(roots[x%5]+5*digit)
 for prime,E,images in ((3,3,map3),(5,2,map5)):
  need(sorted(images)==list(range(prime**E)),'prime-prefix bijection')
  for e in range(E+1):need(all(images[x]%prime**e==images[x%prime**e]%prime**e for x in range(prime**E)),'projection-compatible permutation')
 ss=crt(map3[s%3]%3,3,map5[s%25],25)
 need(ss in legal(75) and ss%3==d and ss%5==k,'joint75 image')
 need(crt(map3[r%9]%9,9,map5[r%5]%5,5)==rr,'joint45 image')
 for n in range(675):
  nn=crt(map3[n%27],27,map5[n%25],25)
  need(all((n%a==v)==(nn%a==v) for v,a in ANCHORS),'six anchors preserved individually')
  need((n%45==r)==(nn%45==rr) and (n%75==s)==(nn%75==ss),'both actual phase cylinders transported simultaneously')
 return ss

ANCHORS=((0,3),(1,9),(4,27),(0,5),(1,25),(2,15))
def legal(m):return tuple(r for r in range(m) if all(r%d!=a for a,d in ANCHORS if m%d==0))

def verify(geometry):
 need(geometry['schema']=='mixed-anchor-prefix-geometry-input-v1','geometry schema')
 need(geometry['source_archive_sha256']=='9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c','pinned source archive')
 need(geometry['source_verifier_sha256']=='e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135','pinned source verifier')
 need(geometry['source_geometry_cpp_sha256']=='8d7ecf1981a413daf2d3835ebe2c046b20f03010f7ce24f247bd357136e24f04','pinned source integer evaluator')
 batches=geometry['batches'];used=set();dist=distributions();results={};vertex_rows=[]
 canonical75={(r,s):finitephase_check(r,s) for r,s in product(legal(45),legal(75))}
 phases=sorted(set(representative_map(r,s) for r,s in product(legal(45),legal(75))))
 need(len(phases)==56 and (len(legal(45)),len(legal(75)))==(17,33),'complete phase domain')
 expected_nodes={(2,4,1,r,j,d,k,i,-1) for r,d,k in phases for j,i in [(j,0) for j in range(1,5)]+[(k,1)]}
 supplied_nodes=geometry['nodes'];need(len(supplied_nodes)==280 and set(map(tuple,supplied_nodes))==expected_nodes,'complete joint-vertex geometry domain')
 for r,d,k in phases:
  lower=[]
  for j,i in [(j,0) for j in range(1,5)]+[(k,1)]:
   node=r,d,k,j,i;mass,whole,values=envelope(node,batches,used);losses=[];unrounded=[]
   for p,t,(table,mean) in zip(PRIMES,THRESHOLDS,dist):
    small=[(m,w) for m,w in table.items() if m<t];prob=sum(w for m,w in small);first=sum(m*w for m,w in small)
    numerator=sum(m*w*values[F(t,m)] for m,w in small)+(mean-first)*whole-t*(1-prob)*mass
    cost=numerator/F(p-1-t);up=rounded(cost);need(cost<=up<cost+F(1,10**10),'outward rounding')
    unrounded.append(str(cost));losses.append(up)
   R=reserve(node);lo=(R-sum(losses))/135;lower.append(lo)
   vertex_rows.append({'node':[2,4,1,r,j,d,k,i,-1],'reserve':str(R),'unrounded_stage_losses':unrounded,'stage_losses':list(map(str,losses)),'lower':str(lo)})
  results[r,d,k]=min(lower)
 phase_rows=[{'phase':[r,s],'source_phase':list(representative_map(r,s)),'canonical75':canonical75[r,s],'lower':str(results[representative_map(r,s)])} for r,s in product(legal(45),legal(75))]
 need(used==set(batches),'no unused or missing input geometry batches')
 minimum=min(F(r['lower']) for r in phase_rows)
 need(minimum==F(12604673809,675000000000),'uniform mixed-anchor lower')
 return {'schema':'mixed-anchor-prefix-lower-v1','source_doi':geometry['source_doi'],'actual_phase_pairs':len(phase_rows),'source_phase_count':len(results),'joint_vertex_count':len(vertex_rows),'geometry_batch_count':len(used),'unique_integer_queries':sum(len(batches[k]['integer_maxima']) for k in used),'stage_primes':list(PRIMES),'thresholds':list(THRESHOLDS),'conditional_caps':list(map(str,CAPS)),'uniform_lower':str(minimum),'uniform_lower_float':float(minimum),'phase_lowers':phase_rows,'vertices':vertex_rows,'phase_permutations_verified':561,'source_verifier_imported':False,'source_geometry_reexecuted':False,'Lean_rerun':False,'boundary':'Exact arithmetic from explicit integer geometry inputs. Same-source ordinary screening, finite phase normalization and joint-budget interpolation are mathematical premises. This lower replaces previous weaker lower; its45/75 credits must not be added again.'}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--input-dir',type=Path,default=Path(__file__).resolve().parent)
 ap.add_argument('--geometry',type=Path)
 ap.add_argument('--output',type=Path)
 args=ap.parse_args()
 geometry=args.geometry or args.input_dir/'mixed_anchor_prefix_geometry.json'
 raw=geometry.read_bytes();need(sha256(raw).hexdigest()==GEOMETRY_SHA256,'pinned explicit integer geometry input')
 result=verify(json.loads(raw));result['geometry_input_sha256']=GEOMETRY_SHA256
 if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
 else:need(json.loads((args.input_dir/'mixed_anchor_prefix_lower.json').read_text())==result,'retained exact prefix result differs')
 print(json.dumps({k:v for k,v in result.items() if k not in ('phase_lowers','vertices')},indent=2))
if __name__=='__main__':main()
