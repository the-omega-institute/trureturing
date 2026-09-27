#!/usr/bin/env python3
"""Verify explicit original-label families at two source-mass endpoints.

Standard-library exact arithmetic and independent CRT unions. Default is
read-only; --output writes finite experimental results. The all-family
inequality and infinite limit proof are in profile note48, not inferred
from these finite computations.
"""
import argparse
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

def require(c,m):
 if not c: raise ValueError(m)

def source_label(a,b,variant):
 if b==0:
  return (a,2 if a==1 else 6 if a==2 else 3**(a-1),b,0)
 if a==0: return (a,0,b,5**(b-1))
 if a==1: return (a,1,b,2*5**(b-1))
 if a==2: return (a,1,b,3*5**(b-1))
 return (a,2*3**(a-1) if variant==398 else 1+3**(a-1),b,4*5**(b-1) if variant==402 else 2*5**(b-1))

def mixed_label(a,b):
 if b==0 and a in (1,2): return (1,a,1 if a==1 else 3,b,0)
 if b==0: return (2,a,3+3**(a-1),b,0)
 if a==0:return (3,a,0,b,4*5**(b-1))
 if a==1:return (4,a,1,b,4*5**(b-1))
 return (5,a,3 if a==2 else 4+3**(a-1),b,4*5**(b-1))

def crt_label(a,ra,b,rb,e,re):
 mods=(3**a,5**b,7**e);rs=(ra,rb,re);mod=mods[0]*mods[1]*mods[2]
 return mod,sum(r*(mod//m)*pow(mod//m,-1,m) for m,r in zip(mods,rs) if m>1)%mod

def check(N,variant):
 A,B,C=3**N,5**N,7**N
 all5=(1<<B)-1
 masks={(b,r):sum(1<<j for j in range(r, B,5**b)) for b in range(N+1) for r in {0,5**(b-1) if b else 0,2*5**(b-1) if b else 0,3*5**(b-1) if b else 0,4*5**(b-1) if b else 0}}
 state=[all5 for _ in range(A)]
 labels=[]
 for a,b in product(range(N+1),repeat=2):
  if a+b==0:continue
  aa,ra,bb,rb=source_label(a,b,variant)
  for x in range(ra,A,3**aa):state[x]&=all5^masks[bb,rb]
  labels.append(crt_label(aa,ra,bb,rb,0,0))
 t=sum((F(1,3**a) for a in range(3,N+1)),F(0));q=sum((F(1,5**b) for b in range(1,N+1)),F(0));delta=int(variant==402)
 s=F(sum(v.bit_count() for v in state),A*B)
 require(s==F(5,9)-t-q,'raw35 total')
 cells=(0,3,1,4,7)
 eta=[F(1,9)-t]+[F(1,9)]*4
 avail=[1-q,1-q,1-3*q,1-2*q,1-2*q]
 n=[eta[l]*avail[l]-(t*q if l==(2 if delta else 0) else 0) for l in range(5)]
 require(n==[F(sum(state[x].bit_count() for x in range(c,A,9)),A*B) for c in cells],'five actual cells')
 groups={j:[0]*A for j in range(1,6)};totals={j:0 for j in range(1,6)}
 for a,b in product(range(N+1),repeat=2):
  if a+b==0:continue
  j,aa,ra,bb,rb=mixed_label(a,b);bm=masks[bb,rb]
  for x in range(ra,A,3**aa):
   require(not(groups[j][x]&bm),'old-coordinate group disjointness')
   groups[j][x]|=bm;totals[j]+=(state[x]&bm).bit_count()
  for e in range(1,N+1):labels.append(crt_label(aa,ra,bb,rb,e,j*7**(e-1)))
 seven=[0]*C;seven_groups={j:0 for j in range(1,7)}
 for j in range(1,7):
  for e in range(1,N+1):
   for v in range(j*7**(e-1),C,7**e):
    require(seven[v]==0,'all seven cylinders disjoint');seven[v]=j;seven_groups[j]+=1
   if j==6:labels.append(crt_label(0,0,0,0,e,j*7**(e-1)))
 require(len(labels)==len(set(m for m,r in labels))==(N+1)**3-1,'one distinct original modulus per exponent triple')
 observed=[F(totals[j],A*B) for j in range(1,6)]
 expected=[F(4,9)-F(8,9)*q-delta*t*q,(1-q)*t,(F(5,9)-(1+delta)*t)*q,(F(1,3)-delta*t)*q,(F(1,9)+t)*q]
 require(observed==expected,'five exact old-carrier contributions')
 H=sum(observed,F(0));require(H==F(4,9)+t+q/9-(1+3*delta)*t*q,'closed H formula')
 u=F(C-seven_groups[6],C);kap=F(seven_groups[1],C)/u
 S=s-kap*H
 require(u==(5+F(1,C))/6 and kap==(1-F(1,C))/(5+F(1,C)),'pure7 normalization')
 if N==3:
  L=A*B*C;mask=bytearray(b'\1')*L
  for m,r in labels:mask[r::m]=b'\0'*len(mask[r::m])
  require(F(sum(mask),L)/u==S,'direct complete CRT union')
 h=sum(eta,F(0));dmax=max(avail)
 D=s-(max(n[0]+n[1],sum(n[2:]))+max(n))/5-(dmax/18+(h+max(sum(eta[:2]),sum(eta[2:]))+max(eta))/4+F(1,72))/5
 z=1-q;alpha1=q;beta2=q;late2=t*q if delta else F(0)
 credit=max(F(0),2*late2-F(7,300)-(z-F(3,4)+F(1,2)-alpha1-beta2)/9)
 require(S>=D+credit,'global actual source compatibility')
 if z<F(79,100) and alpha1>F(21,100) and beta2>F(21,100):
  require(S>=D+max(F(0),2*late2-F(7,300)),'neighborhood source compatibility')
 return {'height':N,'variant':variant,'labels':len(labels),'s':str(s),'cells':list(map(str,n)),'H':str(H),'S':str(S),'D':str(D),'S_minus_D':str(S-D),'direct_CRT_union':N==3}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 out={'checks':[check(N,v) for N in (3,4,5) for v in (398,402)],
      'scope':'Finite actual original-label constructions; independent raw CRT union at height3 and disjoint product-cylinder checks at heights3,4,5. Infinite limits require the ordinary proof.'}
 t,q=F(1,18),F(1,4)
 limits=[F(1,4)-(F(4,9)+t+q/9-(1+3*d)*t*q)/5 for d in (0,1)]
 require(limits==[F(53,360),F(7,45)],'exact limiting formulas')
 require(F(3,20)+F(1,225)==F(139,900),'402 exclusion limit')
 out['limit_formula_values']=list(map(str,limits))
 if args.output is not None:
  args.output.write_text(json.dumps(out,indent=2)+'\n')
 print('PASS: six finite original-label families, all source/carrier masses, disjoint cylinder classes and both full height3 CRT unions.')
 print('Ordinary source-compatibility theorem required for infinite limits; unrestricted Erdos7 remains open.')

if __name__=='__main__':
 main()
