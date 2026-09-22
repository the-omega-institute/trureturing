#!/usr/bin/env python3
"""Verify sharp aligned and attainable off-diagonal source-mass endpoints.

Read-only standard-library experiment by default. --output writes exact
finite results. The universal two-depth inequality is proved in note50;
finite CRT checks validate its explicit constructions, not all families.
"""
import argparse
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

def require(c,m):
 if not c:raise ValueError(m)

def source(a,b,kind):
 if b==0:return a,2 if a==1 else 6 if a==2 else 3**(a-1),b,0
 if a==0:return a,0,b,5**(b-1)
 if a==1:return a,1,b,2*5**(b-1)
 if a==2:return a,1,b,3*5**(b-1)
 if kind=='off-diagonal':return a,4+3**(a-1),b,3*5**(b-1)
 if b==1:return a,1+3**(a-1),b,4
 if b==2:return a,1+2*3**(a-1),b,4
 return a,1+3**(a-1),b,4*5**(b-1)

def mixed(a,b,kind):
 if b==0:
  if a==1:return 1,a,0,b,0
  if a==2:return 2,a,3,b,0
  return 2,a,2*3**(a-1),b,0
 if kind=='off-diagonal':
  if a==0:return 3,a,0,b,4*5**(b-1)
  if a==1:return 1,a,1,b,4*5**(b-1)
  if a==2:return 5,a,3,b,4*5**(b-1)
  return 5,a,7+3**(a-1),b,4*5**(b-1)
 rb=4 if b==1 else 20 if b==2 else 20+5**(b-1)
 if a==0:return (3 if b<=2 else 4),a,0,b,rb
 if a==1:return (1 if b<=2 else 2),a,1,b,rb
 if a==2:return 5,a,(3 if b<=2 else 4),b,rb
 ra=4+3**(a-1) if b==1 else 7+3**(a-1) if b==2 else 2*3**(a-1)
 return 5,a,ra,b,rb

def crt(a,ra,b,rb,e,re):
 mods=3**a,5**b,7**e;M=mods[0]*mods[1]*mods[2]
 return M,sum(r*(M//m)*pow(M//m,-1,m) for m,r in zip(mods,(ra,rb,re)) if m>1)%M

def check(N,kind):
 A,B,C=3**N,5**N,7**N
 all5=(1<<B)-1;cache={}
 def cylinder(b,r):
  key=b,r
  if key not in cache:cache[key]=sum(1<<v for v in range(r,B,5**b))
  return cache[key]
 state=[all5]*A;labels=[]
 for a,b in product(range(N+1),repeat=2):
  if a+b==0:continue
  aa,ra,bb,rb=source(a,b,kind);remove=cylinder(bb,rb)
  for x in range(ra,A,3**aa):state[x]&=all5^remove
  labels.append(crt(aa,ra,bb,rb,0,0))
 t=sum((F(1,3**a) for a in range(3,N+1)),F(0));q=sum((F(1,5**b) for b in range(1,N+1)),F(0));h=F(5,9)-t
 s=F(sum(v.bit_count() for v in state),A*B);require(s==F(5,9)-t-q,'exact source total')
 eta=[F(1,9)-t]+[F(1,9)]*4;d=[1-q,1-q,1-3*q,1-2*q,1-2*q]
 late_cell=2 if kind=='sharp402' else 3
 n=[eta[l]*d[l]-(t*q if l==late_cell else 0) for l in range(5)]
 require(n==[F(sum(state[x].bit_count() for x in range(c,A,9)),A*B) for c in (0,3,1,4,7)],'five actual source cells')
 groups={j:[0]*A for j in range(1,6)};totals=[0]*5
 for a,b in product(range(N+1),repeat=2):
  if a+b==0:continue
  j,aa,ra,bb,rb=mixed(a,b,kind);bm=cylinder(bb,rb)
  category=0 if b==0 else min(a+1,4)
  for x in range(ra,A,3**aa):
   require(not(groups[j][x]&bm),'old carriers disjoint within seven class')
   groups[j][x]|=bm;totals[category]+=(state[x]&bm).bit_count()
  for e in range(1,N+1):labels.append(crt(aa,ra,bb,rb,e,j*7**(e-1)))
 seven=bytearray(C);seven_counts=[0]*7
 for j in range(1,7):
  for e in range(1,N+1):
   for v in range(j*7**(e-1),C,7**e):
    require(seven[v]==0,'seven cylinders disjoint');seven[v]=j;seven_counts[j]+=1
   if j==6:labels.append(crt(0,0,0,0,e,j*7**(e-1)))
 require(len(labels)==len(set(m for m,r in labels))==(N+1)**3-1,'unique original modulus labels')
 loss=6*t/25 if kind=='sharp402' else 0
 expected=[(1-q)/3,h*q-loss,q/3-loss,q/9,t*q]
 observed=[F(v,A*B) for v in totals];require(observed==expected,'five cofactor category masses')
 H=sum(observed,F(0));require(H==F(1,3)+2*q/3-2*loss,'closed old-carrier total')
 u=F(C-seven_counts[6],C);k=F(seven_counts[1],C)/u;S=s-k*H
 if N==3:
  period=A*B*C;mask=bytearray(b'\1')*period
  for m,r in labels:mask[r::m]=b'\0'*len(mask[r::m])
  require(F(sum(mask),period)/u==S,'independent complete CRT union')
 D=s-(max(sum(n[:2]),sum(n[2:]))+max(n)+max(d)/18+(sum(eta)+max(sum(eta[:2]),sum(eta[2:]))+max(eta))/4+F(1,72))/5
 source_delta=3*(F(1,4)-q);eps=F(1,72)-(t*q if late_cell==2 else 0);h1=sum(eta[2:])
 global_credit=max(F(0),2*h1/125-2*source_delta/3-12*eps)
 require(S>=D+global_credit,'two-depth global compatibility')
 local=source_delta<F(1,125) and eps<F(1,2250)
 if local:require(S>=D+max(F(0),2*h1/125-2*eps),'strong neighborhood compatibility')
 require(mixed(1,0,kind)[2]==0 and mixed(2,0,kind)[2]==3,'exact shallow carrier root0/cell1')
 return {'height':N,'kind':kind,'moduli':len(labels),'s':str(s),'H':str(H),'S':str(S),'D':str(D),'global_credit':str(global_credit),'strong_neighborhood':local,'direct_CRT':N==3,'shallow_carrier':[0,1],'carrier_cap_weight':str(1-F(1,C)),'empty_cap_weight':str(F(1,C))}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 out={'rows':[check(N,kind) for N in (3,4,5,6) for kind in ('sharp402','off-diagonal')],
      'scope':'Actual finite constructions; the universal lower theorem and infinite endpoints require the ordinary proof.'}
 t,q=F(1,18),F(1,4)
 H_sharp=F(1,3)+2*q/3-12*t/25
 H_off=F(1,3)+2*q/3
 require((H_sharp,H_off)==(F(71,150),F(1,2)),'limiting carrier masses')
 limits=(F(1,4)-H_sharp/5,F(1,4)-H_off/5)
 require(limits==(F(233,1500),F(3,20)),'limiting surviving masses')
 require(F(3,20)+F(2,375)==limits[0],'sharp lower and constructed upper match')
 require(any(r['strong_neighborhood'] and F(r['global_credit'])>0 for r in out['rows']),
         'Finite examples exercise the nonzero two-depth cut')
 out['limiting_surviving_masses']=list(map(str,limits))
 if args.output is not None:args.output.write_text(json.dumps(out,indent=2)+'\n')
 print('PASS: eight original-label families, all source/carrier masses, disjoint cylinder classes, exact cap-mixture tails and two full CRT unions.')
 print('Sharp402 limit233/1500 and off-diagonal limit3/20 match the ordinary formulas; unrestricted Erdos7 remains open.')

if __name__=='__main__':
 main()
