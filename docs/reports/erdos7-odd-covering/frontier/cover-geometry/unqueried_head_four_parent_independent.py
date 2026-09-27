#!/usr/bin/env python3
"""Independent complete fractional hinges and same-source omission budget.

Reads proposed row parameters, not the candidate producer. The infinite hinge
is evaluated by its exact full mean plus a finite negative-part correction.
"""
from fractions import Fraction as F
from pathlib import Path
from math import prod,isqrt
from hashlib import sha256
from collections import Counter
import argparse,json,time,sys
sys.set_int_max_str_digits(0)
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=ap.parse_args();START=time.monotonic()
candidate_path=args.directory/'unqueried_head_four_parent_certificate.json'
raw=candidate_path.read_bytes();cand=json.loads(raw)
ROWS=cand['rows'];P=(3,5,7,11);D=(F(2),F(4,3),F(7,5),F(11,9));FIRST=(F(2,3),F(4,15),F(1,6),F(1,10))
BOUND=1250;Q=10**45;DEN=Q**4;checks=Counter()
def ck(name,truth):
 if not truth:raise ArithmeticError(name)
 checks[name]+=1
trial=lambda n:n>1 and all(n%d for d in range(2,isqrt(n)+1))
PRIMES=[p for p in range(3,1253,2) if trial(p)]
OWNERS=[p for p in PRIMES if p>=37]
ck('complete193 finite owner window',len(OWNERS)==193 and [r['owner_prime'] for r in ROWS]==OWNERS)
ck('no selected nonunit pattern',all(r['N']==0 for r in ROWS))
ck('literal reference coordinates',cand['reference_primes']==list(P)
   and tuple(map(F,cand['reference_first_caps']))==FIRST and tuple(map(F,cand['reference_deep_caps']))==D)
def survival(i,e):return F(1) if e==0 else FIRST[i] if e==1 else D[i]/P[i]**e
MEAN=prod(1+FIRST[i]+D[i]/F(P[i]*(P[i]-1)) for i in range(4))-1
ck('exact complete mean',MEAN==F(23,9)==F(cand['exact_full_first_moment']))
AX=[]
for i in range(4):
 nums=[]
 for ell in range(BOUND):
  prob=survival(i,ell)-survival(i,ell+1)
  ck('positive auxiliary probabilities',prob>0)
  num=prob.numerator*Q//prob.denominator
  ck('directed probability rounding',F(num,Q)<=prob<F(num+1,Q))
  nums.append(num)
 AX.append(nums)
histlo=[0]*(BOUND+1);histhi=[0]*(BOUND+1);cells=0
for a in range(1,BOUND+1):
 for b in range(1,BOUND//a+1):
  ab=a*b
  for c in range(1,BOUND//ab+1):
   abc=ab*c
   for d in range(1,BOUND//abc+1):
    coords=(a-1,b-1,c-1,d-1);w=[AX[i][coords[i]] for i in range(4)]
    count=abc*d-1
    histlo[count]+=prod(w);histhi[count]+=prod(v+1 for v in w);cells+=1
pl=[];pu=[];cl=[];cu=[];sl=su=tl=tu=0
for c,(w,z) in enumerate(zip(histlo,histhi)):
 sl+=w;su+=z;tl+=c*w;tu+=c*z
 pl.append(sl);pu.append(su);cl.append(tl);cu.append(tu)
rows=[]
for cr in ROWS:
 v,h,t,den=cr['owner_prime'],cr['h'],cr['t'],cr['D']
 ck('same complete normalized row',den==v-3 and t==den-h and 10<=h<=den)
 cap=F(v-1,h)
 ck('strict next-parent tenth cap',cap/v<F(1,10))
 ck('candidate row threshold and actual cap',F(cr['threshold'])==F(t,den) and F(cr['conditional_Haar_cap'])==cap)
 ck('all negative-part support enumerated',t+1<BOUND)
 flo=(MEAN-t+F(t*pl[t]-cl[t],DEN))/h
 fhi=(MEAN-t+F(t*pu[t]-cu[t],DEN))/h
 ck('nonnegative narrow full-tail interval',0<flo<=fhi and fhi-flo<F(1,10**35))
 clo=F(cr['complete_hinge_lower']);chi=F(cr['complete_hinge_upper'])
 ck('candidate positive-box interval encloses independent whole hinge',clo<=flo<=fhi<=chi)
 rows.append(dict(owner_prime=v,N=0,h=h,t=t,D=den,conditional_Haar_cap=cap,
   hinge_lower=flo,hinge_upper=fhi,hinge_lower_decimal=float(flo),hinge_upper_decimal=float(fhi),
   candidate_hinge_lower=clo,candidate_hinge_upper=chi,candidate_upper_excess=chi-fhi))
FINITELO=sum(r['hinge_lower'] for r in rows);FINITEHI=sum(r['hinge_upper'] for r in rows)
HEAD={3:F(2),5:F(4,3),7:F(7,5),11:F(11,9),13:F(13,11),17:F(17,15),19:F(19,17),23:F(5,3),29:F(20,11),31:F(2)}
CAPS=dict(HEAD);CAPS.update({r['owner_prime']:r['conditional_Haar_cap'] for r in rows})
ck('complete203 Euler factor window',len(CAPS)==203 and sorted(CAPS)==PRIMES)
EULER_FACTORS=[dict(prime=p,cap=CAPS[p],factor=(1+CAPS[p]*(F(3,p-1)+F(2,(p-1)**2)))*F(p-1,p)**12) for p in PRIMES]
EULER=prod(r['factor'] for r in EULER_FACTORS)
ck('Euler inside tighter and inherited bounds',0<EULER<F(1,500)<F(3,1000))
ck('candidate all203 individual Euler factors',
 [dict(prime=r['prime'],cap=str(r['cap']),euler_factor=str(r['factor'])) for r in EULER_FACTORS]==cand['finite_Euler_factors'])
ck('candidate full Euler correction',EULER==F(cand['finite_Euler_correction']))
# Verify each head's role at depth one and two; larger depths follow as
# actual/reference prime ratios only decrease when the exponent increases.
HEAD_FIRST={3:F(2,3),5:F(4,15),7:F(1,6),11:F(1,10),13:F(1,12),17:F(1,16),19:F(1,18),
            23:F(5,69),29:F(20,319),31:F(2,31)}
for i,p in enumerate(P):
 for u,c in HEAD.items():
  if u>=p:
   ck('head first-depth ordered role',HEAD_FIRST[u]<=FIRST[i])
   ck('head deeper ordered role',c/u**2<=D[i]/p**2)
 ck('outside first-depth ordered role',F(1,10)<=FIRST[i])
 ck('outside deeper ordered role',F(1,370)<=D[i]/p**2)
Z={7:F(5,6),**{q:F(q-2,q-1)-F(2,q*(q-2)) for q in (11,13,17,19)}}
ZETA=F(5455,5814)
ck('actual omitted-coordinate bound',all(0<z<=ZETA<1 for z in Z.values()) and ZETA==Z[19])
ck('candidate same omitted-coordinate factors',{str(p):str(z) for p,z in Z.items()}==cand['unqueried_coordinate_mass_caps']
   and ZETA==F(cand['unqueried_factor']))
GAMMA=F(203129722400814193208791597,20692505911553620784640000000);ALPHA=F(2673,110656)
# Independently rebuild650's ENTIRE conservative cube fee. Every finite
# prime is independently trial-divided; the higher interval tail is analytic.
CUBE_D=(F(2),F(4,3),F(7,5),F(11,5))
T=tuple(1+d*(F(3,p-1)+F(2,(p-1)**2)) for p,d in zip(P,CUBE_D))
def cube(n):
 aa=tuple(d*F(p*(p+1),(p-1)**2*p**n) for p,d in zip(P,CUBE_D))
 bb=tuple(d*F(p,(p-1)*p**n)*(n+1+F(2,p-1)) for p,d in zip(P,CUBE_D))
 exact=prod(T)-2*prod(t-b for t,b in zip(T,bb))+prod(t-2*b+a for t,b,a in zip(T,bb,aa))
 upper=sum(aa[i]*prod(T[j] for j in range(4) if j!=i) for i in range(4))
 upper+=2*sum(bb[i]*bb[j]*prod(T[k] for k in range(4) if k not in (i,j)) for i in range(4) for j in range(i+1,4))
 return exact,upper
CUBE_QUANTUM=10**18;cube_integer=0;cube_prime_count=0
for n in range(5,10):
 mm,uu=cube(n);ck('cube positive moment and majorant',0<mm<=uu)
 for v in range(2*n**4+3,2*(n+1)**4+2,2):
  if not trial(v):continue
  den=v-n**4-2;fee=mm/den**2
  ck('cube row compatible with new invariant',F(2*(v-1),den)<=4<F(v,10))
  num=(fee.numerator*CUBE_QUANTUM+fee.denominator-1)//fee.denominator
  ck('cube upward exact rounding',fee<=F(num,CUBE_QUANTUM)<fee+F(1,CUBE_QUANTUM))
  cube_integer+=num;cube_prime_count+=1
ck('complete finite cube prime window',cube_prime_count==2058)
ck('cube scaled diagonal and cross ratios',all(F(3,p)<=1 for p in P) and F(3,15)*F(12,11)**2<1)
CUBE_TAIL=cube(10)[1]*F(11**4-10**4,10**8)*F(3,2)
CUBE=F(cube_integer,CUBE_QUANTUM)+CUBE_TAIL;TYPEI=F(1,65536)
ck('retained complete cube simple bound',0<CUBE<F(3,100000))
ck('candidate complete cube equals independent rebuild',CUBE==F(cand['complete_four_parent_cube_fee']))
E=F(19740202146111572828188083,495176015714152109959649689600)
ck('inherited full arbitrary-parent tail',E==5*F(3,1000)*F((4*117)**12,2**115))
ck('candidate literal continuation and head constants',E==F(cand['complete_arbitrary_parent_fee'])
   and 2**115==cand['arbitrary_parent_threshold'] and TYPEI==F(cand['ordinary_typeI_fee'])
   and GAMMA==F(cand['head_gate']) and ALPHA==F(cand['projection_alpha']))
ck('arbitrary-parent rows preserve tenth cap',F(2*(2**115-1),2**115-3)<4<F(2**115,10))
TOTAL=ZETA*FINITEHI+CUBE+TYPEI+E;MARGIN=GAMMA-TOTAL
ck('same-source complete positive margin',MARGIN>0)
SIMPLE_FINITE=F(10137,1000000)
ck('simple full finite hinge sum',FINITEHI<SIMPLE_FINITE)
SIMPLE_MARGIN=GAMMA-ZETA*SIMPLE_FINITE-F(3,100000)-TYPEI-E
ck('simple full density target',ALPHA*SIMPLE_MARGIN>F(1,190000))
CAND_FINITE=sum(F(r['complete_hinge_upper']) for r in ROWS)
ck('candidate finite total and independent enclosure',FINITEHI<=CAND_FINITE==F(cand['finite_hinge_upper'])<SIMPLE_FINITE)
ck('candidate individual omitted-coordinate debits',all(F(r['unqueried_fee_upper'])==ZETA*F(r['complete_hinge_upper']) for r in ROWS))
ck('candidate finite debit total',ZETA*CAND_FINITE==F(cand['finite_unqueried_fee_upper']))
CAND_TOTAL=ZETA*CAND_FINITE+CUBE+TYPEI+E
ck('candidate complete total and margins',CAND_TOTAL==F(cand['complete_total_fee'])
   and GAMMA-CAND_TOTAL==F(cand['raw_margin']) and ALPHA*(GAMMA-CAND_TOTAL)==F(cand['projected_lower']))
ck('candidate simple complete budget',GAMMA-SIMPLE_MARGIN==F(cand['simple_total_fee'])
   and ALPHA*SIMPLE_MARGIN==F(cand['simple_projected_lower']) and cand['simple_density_denominator']==190000)
def enc(x):
 if isinstance(x,F):return str(x)
 if isinstance(x,dict):return {str(k):enc(v) for k,v in x.items()}
 if isinstance(x,(tuple,list)):return [enc(v) for v in x]
 return x
out=dict(schema='independent-unqueried-head-four-parent37-v1',status='PASS',new_lean_verification=False,
 candidate_sha256=sha256(raw).hexdigest(),producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
 candidate_file=candidate_path.name,cross_bound=BOUND,cross_cells=cells,coordinate_rounding_denominator=Q,
 first_caps=FIRST,deep_caps=D,exact_full_auxiliary_mean=MEAN,check_count=sum(checks.values()),checks=dict(checks),
 rows=rows,finite_hinge_lower=FINITELO,finite_hinge_upper=FINITEHI,finite_hinge_simple_upper=SIMPLE_FINITE,
 omitted_coordinate_masses=Z,omission_factor=ZETA,finite_debit=ZETA*FINITEHI,
 Euler_factors=EULER_FACTORS,Euler_correction=EULER,inherited_Euler_upper=F(3,1000),
 complete_cube_fee=CUBE,complete_arbitrary_parent_fee=E,TypeI_fee=TYPEI,head_gate=GAMMA,
 complete_total_fee=TOTAL,raw_margin=MARGIN,alpha=ALPHA,projected_margin=ALPHA*MARGIN,
 candidate_complete_fee=CAND_TOTAL,cube_prime_count=cube_prime_count,cube_infinite_tail=CUBE_TAIL,
 simple_raw_margin=SIMPLE_MARGIN,simple_density_denominator=190000)
args.output.write_text(json.dumps(enc(out),indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=out['check_count'],cross_cells=cells,mean=str(MEAN),
 finite_lower=float(FINITELO),finite_upper=float(FINITEHI),zeta=str(ZETA),finite_debit=float(ZETA*FINITEHI),
 Euler=float(EULER),cube=float(CUBE),large=float(E),total=float(TOTAL),gamma=float(GAMMA),
 raw_margin=float(MARGIN),projected_margin=float(ALPHA*MARGIN),density_denominator=190000,
 first_rows=[dict(v=r['owner_prime'],h=r['h'],t=r['t'],hinge=float(r['hinge_upper'])) for r in rows[:3]],seconds=time.monotonic()-START),indent=2))
