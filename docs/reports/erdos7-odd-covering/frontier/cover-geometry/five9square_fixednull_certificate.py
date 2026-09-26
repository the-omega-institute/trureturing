#!/usr/bin/env python3
"""Verify six global-role thinnings on all fixed-null source corners and layouts."""
from fractions import Fraction as F
from itertools import product,combinations
from math import prod,lcm
from pathlib import Path
from hashlib import sha256
import argparse,json,time
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument("--source-dir",type=Path,default=Path(__file__).resolve().parent)
ap.add_argument("--certificate",type=Path,default=Path(__file__).with_suffix(".json"))
ap.add_argument("--output",type=Path)
args=ap.parse_args()
start=time.monotonic();checks={}
def ck(k,x):
 if not x:raise ArithmeticError(k)
 checks[k]=checks.get(k,0)+1
ROOT=args.source_dir
raw=(ROOT/'conditional30_fixedstar_augmented_certificate.json').read_bytes();PIN='eb45a79b8943ac56b72153c72472bf40b098366574deb249840ea28f504a9345';ck('input_pin',sha256(raw).hexdigest()==PIN);B=json.loads(raw)
Q=(7,11,13,17,19);D=[q*(q-2)*(q-1)for q in Q];rn=[q*(q-2)for q in Q];an=[q-1 for q in Q]
ED=tuple(combinations(range(5),2));EM=[sum(1<<q for q in e)for e in ED];PAIRS=[(e,f)for e,f in combinations(range(10),2)if not(EM[e]&EM[f])];KN=[rn[q]*rn[s]+an[q]*rn[s]+rn[q]*an[s]for q,s in ED]
CATS=list(map(tuple,B['thinning_categories']));WN=(2,2,2,0,1,2);VN=(4,4,4,4,4,0,3,4,4,4,4,4,4,4,4,4,4,4,4,4)
co=list(map(F,B['stages']['mixed370']['combined_coefficients']));g=F(B['constants']['g']);den=[prod(D[q]for q in range(5)if not(T>>q&1))for T in range(32)]
scaled=[co[j]/den[j%32]for j in range(512)];mass=g/den[0];CD=lcm(*(x.denominator for x in scaled),mass.denominator);CN=[int(x*CD)for x in scaled];MN=int(mass*CD)
candidate=json.loads(args.certificate.read_text());TD=candidate['theta_denominator'];THETA=candidate['theta_numerators']
ck('declared_source_pin',candidate['source_pin']==PIN)
ck('fixed_null_contract',candidate['nulls']==[3,5] and candidate['outside_primes']==list(Q))
ck('positive_integer_denominator',type(TD)is int and TD>0)
ck('six_candidate_branches',len(THETA)==6 and all(len(t)==6 and all(len(row)==20 for row in t) for t in THETA))
def category(l,m):
 if l<3 and m<5:return None
 return CATS.index((0 if l==0 else 1 if l<3 else 2,0 if m<5 else 2 if m==10 else 3 if 11<=m<15 else 1))
for i,l,m in product(range(6),range(6),range(20)):
 t=THETA[i][l][m];c=category(l,m);ck('legal_thinning',type(t)is int and 0<=t<=TD)
 if c in(None,1)or not WN[l]or not VN[m]:ck('fixed_zero_support',t==0)
# Every eligible category has a uniform all-five-decrement strict floor.
strict={};H=[[[0]*32 for c in range(10)]for T in range(32)]
for c in range(10):
 if c==1:continue
 l,m=next((l,m)for l,m in product(range(6),range(20))if category(l,m)==c)
 Zfloor=[D[q]-(rn[q]+an[q])*(int(l<3)+int(10<=m<15))-rn[q]*(int(l<3 and 10<=m<15)+int(l==0)+int(m==10))-an[q]for q in range(5)]
 ck('floor_positive',min(Zfloor)>0)
 u=[F(KN[e],Zfloor[q]*Zfloor[s])for e,(q,s)in enumerate(ED)]
 vals=[1-sum((u[e]for e in range(10)if mask>>e&1),F())+sum((u[e]*u[f]for e,f in PAIRS if mask>>e&1 and mask>>f&1),F())for mask in range(1024)]
 strict[str(c)]=str(min(vals));ck('uniform_strict',min(vals)>0)
 for A in range(32):
  Z=[z+an[q]*int(not(A>>q&1))for q,z in enumerate(Zfloor)]
  rawprod=[prod(Z[q]for q in range(5)if not(T>>q&1))for T in range(32)]
  for T in range(32):
   n=rawprod[T]-sum(KN[e]*rawprod[T|EM[e]]for e in range(10)if not(T&EM[e]))+sum(KN[e]*KN[f]*rawprod[T|EM[e]|EM[f]]for e,f in PAIRS if not(T&(EM[e]|EM[f])))
   ck('positive_response',n>0);H[T][c][A]=n
CAT=[[category(l,m)for m in range(20)]for l in range(6)]
def qs(h):
 w=[v*x for v,x in zip(VN,h)]
 return(sum(w),max(sum(w[5*i:5*i+5])for i in range(4)),max(w),60*max(x for v,x in zip(VN,h)if v))
def screen(h):
 leaf=[qs(row)for row in h];roots=[[sum(WN[l]*h[l][m]for l in range(3*i,3*i+3))for m in range(20)]for i in range(2)]
 allread=qs([roots[0][m]+roots[1][m]for m in range(20)]);rr=list(map(qs,roots))
 return allread+tuple(max(rr[0][j],rr[1][j])for j in range(4))+tuple(max(WN[l]*leaf[l][j]for l in range(6))for j in range(4))+tuple(9*max(leaf[l][j]for l in range(6)if WN[l])for j in range(4))
GD=675*TD*CD;results=[];GLOB=None
COLS=((0,1,2,3,4),(5,),(6,7,8,9),(10,),(11,12,13,14),(15,16,17,18,19))
for branch in(0,1,3,5):
 tn=THETA[branch];ROW=[]
 for block in((0,),(1,2),(3,),(4,5)):
  if branch in block and len(block)>1:ROW.extend(((branch,),tuple(l for l in block if l!=branch)))
  else:ROW.append(block)
 for rr in ROW:
  for cc in COLS:ck('stabilizer_invariant_thinning',len({tn[l][m]for l in rr for m in cc})==1)
 for rr in ROW:
  if rr==(3,):continue
  for cc in COLS:
   if cc==(5,):continue
   w,ww=rr[0],cc[0];WN=tuple(0 if l==3 else 1 if l==w else 2 for l in range(6));VN=tuple(0 if m==5 else 3 if m==ww else 4 for m in range(20))
   minimum=None;worst=None;allg=[]
   for rest in product(range(6),repeat=4):
    layout=(branch,)+rest;allocation=[sum(1<<q for q in range(5)if layout[q]==l)for l in range(6)];score=0
    for T in range(32):
     h=[[tn[l][m]*H[T][CAT[l][m]][allocation[l]]if tn[l][m]else 0 for m in range(20)]for l in range(6)];sc=screen(h)
     if T==0:score+=MN*sc[0]
     score-=sum(CN[32*mode+T]*sc[mode]for mode in range(16))
    ck('positive_complete_layout_gate',score>0);allg.append(str(score))
    if minimum is None or score<minimum:minimum=score;worst=layout
   gate=F(minimum,GD);GLOB=gate if GLOB is None else min(GLOB,gate)
   results.append(dict(leaf7=branch,source_corner=[3,w,5,ww],minimum_gate=str(gate),worst_layout=list(worst),layout_count=len(allg),gate_numerator_sha256=sha256('\n'.join(allg).encode()).hexdigest()))
 print('exact_fixednull_branch',branch,'global_min',float(GLOB),'cases',len(results),'sec',time.monotonic()-start,flush=True)
# All weak corners are covered jointly with the remaining global layouts by row/column permutations.
for source,target,swap in((1,2,(1,2)),(5,4,(4,5))):
 for l,m in product(range(6),range(20)):
  old=swap[1]if l==swap[0]else swap[0]if l==swap[1]else l
  ck('transported_branch_tables',THETA[target][l][m]==THETA[source][old][m])
ck('all90720_representative_layouts',checks['positive_complete_layout_gate']==90720)
ck('strict_global_bound',GLOB>F(1,1600000))
ck('expected_strict_category_minima',strict==candidate['strict_category_minima'])
ck('expected_representative_gates',results==candidate['representatives'])
ck('expected_minimum_gate',str(GLOB)==candidate['minimum_gate'])
ck('expected_common_lower',candidate['common_lower']=='1/1600000')
alpha=F(2673,110656)
ck('haar_bound',alpha*F(1,1600000)==F(2673,177049600000) and alpha*F(1,1600000)>F(1,67000000))
out=dict(schema='five9square-fixednull-verification-v1',status='PASS',scope=candidate['scope'],minimum_gate=str(GLOB),common_lower='1/1600000',haar_lower='2673/177049600000',checks_per_group=checks,check_count=sum(checks.values()),source_pin=PIN,certificate_sha256=sha256(args.certificate.read_bytes()).hexdigest(),producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),new_lean_verification=False)
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
