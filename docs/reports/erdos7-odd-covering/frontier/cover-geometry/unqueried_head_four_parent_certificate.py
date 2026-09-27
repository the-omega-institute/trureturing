#!/usr/bin/env python3
"""Four-parent owners from37, using a preserved unqueried head coordinate.

Finite positive-box sums have directed rational weights and a complete analytic
height remainder. Selected rows, the finite Euler correction and all inherited
continuation fees belong to one fixed policy. Ordinary mathematics, not Lean.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import prod, isqrt
from hashlib import sha256
from collections import Counter, defaultdict
import argparse, json, sys
sys.set_int_max_str_digits(0)
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--directory',type=Path,default=Path(__file__).parent)
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=ap.parse_args()
checks=Counter()
def check(name,ok):
    if not ok: raise ArithmeticError(name)
    checks[name]+=1
def read_input(name,digest):
    raw=(args.directory/name).read_bytes()
    check('pinned '+name,sha256(raw).hexdigest()==digest)
    return json.loads(raw)
prior=read_input('four_parent_cutoff_exact_certificate.json','65370afa505a0fca891fef5a653b1eed979d6d311be6bca6940756e3ca651273')
head=read_input('induced_square_pair_boundary_certificate.json','1e48eef19d525c7071498d15b4ba25445c7b431f01633d081156fb39c40d772e')
P=(3,5,7,11);DEEP=(F(2),F(4,3),F(7,5),F(11,9))
FIRST=(F(2,3),F(4,15),F(1,6),F(1,10))
QHEAD=(7,11,13,17,19)
Z={7:F(5,6),**{q:F(q-2,q-1)-F(2,q*(q-2)) for q in QHEAD[1:]}}
ZETA=F(5455,5814)
check('uniform unqueried-coordinate mass cap',max(Z.values())==ZETA<1)
HEAD={3:F(2),5:F(4,3),7:F(7,5),11:F(11,9),13:F(13,11),17:F(17,15),19:F(19,17),23:F(5,3),29:F(20,11),31:F(2)}
for p,d,b in zip(P,DEEP,FIRST):
    check('outside first-depth role envelope',F(1,10)<=b)
    check('outside deep role envelope',F(1,370)<=d/F(p*p))
    for u,c in HEAD.items():
        if u<p: continue
        shallow=F(1,u-1) if u in QHEAD else c/u
        check('head first-depth role envelope',shallow<=b)
        check('head all higher depths from depth two',c/F(u*u)<=d/F(p*p))
        check('head ordered prime',u>=p)
K=28;SCALE=2**128;DEN=SCALE**4;END=1253
def survival(i,e):
    return F(1) if e==0 else FIRST[i] if e==1 else DEEP[i]/P[i]**e
MEAN=tuple(1+b+d/F(p*(p-1)) for p,d,b in zip(P,DEEP,FIRST))
AXLO=[];AXHI=[]
for i in range(4):
    lo=[];hi=[]
    for ell in range(K):
        mass=survival(i,ell)-survival(i,ell+1)
        n=mass.numerator*SCALE//mass.denominator
        check('positive coordinate layer',mass>0)
        check('directed coordinate enclosure',F(n,SCALE)<=mass<=F(n+1,SCALE))
        lo.append(n);hi.append(n+1)
    AXLO.append(lo);AXHI.append(hi)
# The entire omitted region is controlled by E[product(L_i+1) 1_{some L_i>=K}].
axis_tail=tuple(d/F(p**K)*(K+1+F(1,p-1)) for p,d in zip(P,DEEP))
TAIL=sum(axis_tail[i]*prod(MEAN[j] for j in range(4) if j!=i) for i in range(4))
tail_num=-((-TAIL.numerator*DEN)//TAIL.denominator)
check('complete union remainder rounded upwards',TAIL<=F(tail_num,DEN)<TAIL+F(1,DEN))
histlo=defaultdict(int);histhi=defaultdict(int)
cells=0
for a,b,c,d in product(range(K),repeat=4):
    C=(a+1)*(b+1)*(c+1)*(d+1)-1
    histlo[C]+=AXLO[0][a]*AXLO[1][b]*AXLO[2][c]*AXLO[3][d]
    histhi[C]+=AXHI[0][a]*AXHI[1][b]*AXHI[2][c]*AXHI[3][d]
    cells+=1
check('complete positive box',cells==K**4)
total_lo=sum(histlo.values());total_hi=sum(histhi.values())
mean_lo=sum(c*w for c,w in histlo.items());mean_hi=sum(c*w for c,w in histhi.items())
boxmass=prod(1-survival(i,K) for i in range(4))
check('box probability enclosure',F(total_lo,DEN)<=boxmass<=F(total_hi,DEN))
fullmean=prod(MEAN)-1
check('complete first moment enclosed',F(mean_lo,DEN)<=fullmean<=F(mean_hi+tail_num,DEN))
HLO=[];HHI=[]
for t in range(END):
    total_lo-=histlo.get(t,0);total_hi-=histhi.get(t,0)
    mean_lo-=t*histlo.get(t,0);mean_hi-=t*histhi.get(t,0)
    HLO.append(mean_lo-t*total_lo)
    HHI.append(mean_hi-t*total_hi+tail_num)
    check('positive hinge enclosure',0<=HLO[-1]<=HHI[-1])
flags=bytearray(b'\1')*END;flags[:2]=b'\0\0'
for p in range(2,isqrt(END)+1):
    if flags[p]: flags[p*p:END:p]=b'\0'*len(range(p*p,END,p))
primes=[p for p in range(3,END,2) if flags[p]]
rows=[]
for v in [p for p in primes if p>=37]:
    D=v-3
    h=min(range(10,D),key=lambda h:(F(HHI[D-h],h),h))
    t=D-h;cap=F(v-1,h)
    low=F(HLO[t],DEN*h);upper=F(HHI[t],DEN*h)
    check('finite row and conditional invariant',10<=h<D and 0<F(t,D)<1 and cap<F(v,10))
    check('finite complete hinge narrow enclosure',0<low<=upper and upper-low<F(1,10**10))
    rows.append(dict(owner_prime=v,N=0,h=h,t=t,D=D,threshold=F(t,D),conditional_Haar_cap=cap,
        complete_hinge_lower=low,complete_hinge_upper=upper,unqueried_fee_upper=ZETA*upper))
check('full finite owner window',len(rows)==193 and rows[0]['owner_prime']==37 and rows[-1]['owner_prime']==1249)
FINITE=sum(r['complete_hinge_upper'] for r in rows)
CHARGED=ZETA*FINITE
check('simple raw hinge upper',FINITE<F(10137,1000000))
# Reuse650's larger four-role cube comparator; the new invariant is stronger.
CUBE=F(prior['complete_four_parent_cube_fee'])
check('complete cube bound',0<CUBE<F(3,100000))
check('cube preserves new conditional invariant',F(4,1253)<F(1,10))
caps=dict(HEAD);caps.update({r['owner_prime']:r['conditional_Haar_cap'] for r in rows})
check('complete finite Euler window',sorted(caps)==primes and len(caps)==203)
factors=[dict(prime=p,cap=c,euler_factor=(1+c*(F(3,p-1)+F(2,(p-1)**2)))*F(p-1,p)**12) for p,c in sorted(caps.items())]
EULER=prod(x['euler_factor'] for x in factors)
check('finite Euler strict bound',0<EULER<F(3,1000))
LARGE=5*F(3,1000)*F((4*117)**12,2**115)
check('same proved arbitrary-parent charge',LARGE==F(prior['complete_arbitrary_parent_fee']))
check('arbitrary-parent invariant at threshold',F(2*(2**115-1),(2**115-3)*2**115)<F(1,10))
TYPEI=F(1,65536)
GAMMA=F(next(x for x in head['scopes'] if x['scope']=='twenty')['worst']['gate'])
ALPHA=F(2673,110656)
TOTAL=CHARGED+CUBE+LARGE+TYPEI
SIMPLE=ZETA*F(10137,1000000)+F(3,100000)+LARGE+TYPEI
check('whole same-law budget',TOTAL<SIMPLE<GAMMA)
check('full projected density',ALPHA*(GAMMA-TOTAL)>ALPHA*(GAMMA-SIMPLE)>F(1,190000))
def enc(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {str(k):enc(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [enc(v) for v in x]
    return x
out=dict(schema='unqueried-head-four-parent37-v1',status='PASS',new_lean_verification=False,
    baseline='00854745442107118d3176e66ccf9ad5a738cc19',
    producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
    input_sha256={n:sha256((args.directory/n).read_bytes()).hexdigest() for n in ('four_parent_cutoff_exact_certificate.json','induced_square_pair_boundary_certificate.json')},
    check_count=sum(checks.values()),checks=dict(checks),
    scope='648 head and647 ordinary/private interfaces; <=4 fixed parents at37<=v<2^115; arbitrary finite fixed union above; globally fixed numerical labels and phases; arbitrary finite heights',
    reference_primes=P,reference_first_caps=FIRST,reference_deep_caps=DEEP,
    unqueried_coordinate_mass_caps=Z,unqueried_factor=ZETA,
    box_side=K,box_cells=cells,coordinate_rounding_scale=SCALE,complete_height_remainder=TAIL,
    height_remainder_rounded=F(tail_num,DEN),exact_full_first_moment=fullmean,
    rows=rows,finite_hinge_upper=FINITE,finite_unqueried_fee_upper=CHARGED,
    complete_four_parent_cube_fee=CUBE,finite_Euler_factors=factors,finite_Euler_correction=EULER,
    arbitrary_parent_threshold=2**115,complete_arbitrary_parent_fee=LARGE,ordinary_typeI_fee=TYPEI,
    head_gate=GAMMA,projection_alpha=ALPHA,complete_total_fee=TOTAL,raw_margin=GAMMA-TOTAL,
    projected_lower=ALPHA*(GAMMA-TOTAL),simple_total_fee=SIMPLE,
    simple_projected_lower=ALPHA*(GAMMA-SIMPLE),simple_density_denominator=190000)
args.output.write_text(json.dumps(enc(out),indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=out['check_count'],finite_hinge_upper=float(FINITE),
    unqueried_factor=float(ZETA),finite_charge=float(CHARGED),cube=float(CUBE),Euler=float(EULER),
    large=float(LARGE),total=float(TOTAL),raw_margin=float(GAMMA-TOTAL),
    projected=float(ALPHA*(GAMMA-TOTAL)),simple_density_denominator=190000),indent=2))
