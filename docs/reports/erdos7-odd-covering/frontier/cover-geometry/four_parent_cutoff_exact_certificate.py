#!/usr/bin/env python3
"""Exact all-height four-parent response on one complete owner policy.

Rows are selected by exact rational comparison in one declared finite policy.
Infinite moments use exact polynomial tail buckets; all continuation and Euler
charges are included.
Report650 gives the uniform source and infinite-tail proof.
No new Lean verification or unrestricted Erdos7 resolution is claimed.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb,prod,isqrt,lcm
from itertools import product
from heapq import heappop,heappush
from hashlib import sha256
from collections import Counter
import argparse,json,sys
sys.set_int_max_str_digits(0)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
ROOT=args.directory
OLD=ROOT/'order_matched_owner_network_certificate.json'
old=json.loads(OLD.read_text())['results']['4']
CUTOFF=89;CUBE_START=1253;TAIL_N=10;PRIME_END=2*TAIL_N**4+3
P=(3,5,7,11);D=(F(2),F(4,3),F(7,5),F(11,5))
LENGTH=199
MAXR=8
checks=Counter()
def check(name,truth):
    if not truth:raise ArithmeticError(name)
    checks[name]+=1
check('pinned647 input',sha256(OLD.read_bytes()).hexdigest()=='9988d52c1c56a776e159295a8b98ed3b389e484a7946edb5b435aca8709adb4c')
PAIR=ROOT/'induced_square_pair_boundary_certificate.json'
check('pinned648 input',sha256(PAIR.read_bytes()).hexdigest()=='1e48eef19d525c7071498d15b4ba25445c7b431f01633d081156fb39c40d772e')
head_gate=F(next(s for s in json.loads(PAIR.read_text())['scopes'] if s['scope']=='twenty')['worst']['gate'])
heap=[(1,(0,0,0,0))];seen={(0,0,0,0)};patterns=[]
while len(patterns)<LENGTH:
    value,e=heappop(heap);patterns.append((value,e))
    for i,p in enumerate(P):
        ee=tuple(v+(j==i) for j,v in enumerate(e))
        if ee not in seen:seen.add(ee);heappush(heap,(value*p,ee))
H=tuple(max(e[i] for _,e in patterns) for i in range(4))
full=sorted((prod(p**e for p,e in zip(P,x)),x) for x in product(*(range(h+1) for h in H))
            if prod(p**e for p,e in zip(P,x))<=patterns[-1][0])
check('complete smooth prefix by independent Cartesian enumeration',full==patterns)
check('coordinate bounds cover full prefix',all(p**(h+1)>patterns[-1][0] for p,h in zip(P,H)))
AX=[];AXDEN=[]
for p,d,h in zip(P,D,H):
    gm=[F(1)]
    for r in range(1,MAXR+1):gm.append(sum(F(comb(r,j))*gm[j] for j in range(r))/F(p-1))
    rows=[]
    for ell in range(h):
        mass=1-d/p if ell==0 else d*F(p-1,p**(ell+1))
        rows.append([mass*(ell+1)**r for r in range(MAXR+1)])
    rows.append([d/F(p**h)*sum(F(comb(r,j)*(h+1)**(r-j))*gm[j] for j in range(r+1)) for r in range(MAXR+1)])
    check('full coordinate probability',sum(row[0] for row in rows)==1)
    for r in range(MAXR+1):
        whole=1-d/p+d/F(p)*sum(F(comb(r,j)*2**(r-j))*gm[j] for j in range(r+1))
        check('full coordinate moment decomposition',sum(row[r] for row in rows)==whole)
    den=lcm(*(x.denominator for row in rows for x in row))
    AXDEN.append(den);AX.append([[int(x*den) for x in row] for row in rows])
DEN=prod(AXDEN)
COORD=list(product(*(range(h+1) for h in H)))
WEIGHT=[[prod(AX[i][b[i]][r] for i in range(4)) for r in range(MAXR+1)] for b in COORD]
check('full joint probability',sum(w[0] for w in WEIGHT)==DEN)
COUNTS=[0]*len(COORD)
CURRENT={r:sum(w[r] for w in WEIGHT) for r in range(2,MAXR+1)}
MOM={r:[] for r in CURRENT}
# Precompute finite-difference polynomials for (volume-c)^r.
DELTA={r:[[comb(r,j)*((-c-1)**(r-j)-(-c)**(r-j)) for j in range(r)]
           for c in range(LENGTH)] for r in CURRENT}
for n,(_,e) in enumerate(patterns):
    for ix,b in enumerate(COORD):
        if all(b[i]>=e[i] for i in range(4)):
            c=COUNTS[ix];w=WEIGHT[ix]
            for r in CURRENT:CURRENT[r]+=sum(v*w[j] for j,v in enumerate(DELTA[r][c]))
            COUNTS[ix]=c+1
    for r in CURRENT:
        check('positive exact full moment',CURRENT[r]>0)
        check('strictly decreasing full moment',not MOM[r] or CURRENT[r]<MOM[r][-1])
        MOM[r].append(CURRENT[r])
for r in CURRENT:
    initial=sum(comb(r,j)*(-1)**(r-j)*sum(w[j] for w in WEIGHT) for j in range(r+1))
    final=sum(sum(comb(r,j)*(-c)**(r-j)*w[j] for j in range(r+1)) for c,w in zip(COUNTS,WEIGHT))
    check('direct initial binomial moment',initial==MOM[r][0])
    check('direct final bucket moment',final==MOM[r][-1])
FLAGS=bytearray(b'\1')*PRIME_END;FLAGS[0:2]=b'\0\0'
for p in range(2,isqrt(PRIME_END)+1):
    if FLAGS[p]:
        FLAGS[p*p:PRIME_END:p]=b'\0'*len(range(p*p,PRIME_END,p))
PRIMES=[p for p in range(3,PRIME_END,2) if FLAGS[p]]
small=[row for row in old['rows'] if row['owner_prime']<CUTOFF]
check('entire early three-parent owner window',[row['owner_prime'] for row in small]==[p for p in PRIMES if 37<=p<CUTOFF])
rows=[]
for v in [p for p in PRIMES if CUTOFF<=p<CUBE_START]:
    fee,n,r=min((F(MOM[r][n],DEN*(v-3-n)**r),n,r) for r in range(2,MAXR+1)
       for n in range(min(LENGTH,v-3-5*r+1)))
    den=v-3-n
    check('fixed row parameter consistency',r>=2 and 0<=n<LENGTH)
    check('common conditional invariant',den>=5*r and F(r*(v-1),den)<F(v,5))
    moment=F(MOM[r][n],DEN);fee=moment/F(den**r)
    rows.append(dict(owner_prime=v,selected_nonunit_patterns=n,moment_order=r,complement_D=den,
      conditional_Haar_cap=F(r*(v-1),den),threshold=F(r-1,r),exact_complete_moment=moment,violation_fee=fee))
SMALL=sum((F(r['violation_fee']) for r in small),F())
FOUR=sum((r['violation_fee'] for r in rows),F())
FINITE=SMALL+FOUR
T=tuple(1+d*(F(3,p-1)+F(2,(p-1)**2)) for p,d in zip(P,D))
def cube(n):
    aa=tuple(d*F(p*(p+1),(p-1)**2*p**n) for p,d in zip(P,D))
    bb=tuple(d*F(p,(p-1)*p**n)*(n+1+F(2,p-1)) for p,d in zip(P,D))
    exact=prod(T)-2*prod(t-b for t,b in zip(T,bb))+prod(t-2*b+a for t,b,a in zip(T,bb,aa))
    upper=sum(aa[i]*prod(T[j] for j in range(4) if j!=i) for i in range(4))
    upper+=2*sum(bb[i]*bb[j]*prod(T[k] for k in range(4) if k not in (i,j)) for i in range(4) for j in range(i+1,4))
    return exact,upper
QUANTUM=10**18;cube_rows=[];cube_total=F();cube_count=0
for n in range(5,TAIL_N):
    moment,upper=cube(n);check('cube exact positive and bounded',0<moment<=upper)
    primes=[p for p in PRIMES if 2*n**4+3<=p<=2*(n+1)**4+1]
    rounded=0
    for v in primes:
        den=v-n**4-2;fee=moment/F(den**2)
        check('cube row cap',den>=n**4+1 and F(2*(v-1),den)<=4<F(v,5))
        num=(fee.numerator*QUANTUM+fee.denominator-1)//fee.denominator
        check('upward rational row rounding',F(num,QUANTUM)>=fee and F(num,QUANTUM)<fee+F(1,QUANTUM))
        rounded+=num
    total=F(rounded,QUANTUM);cube_total+=total;cube_count+=len(primes)
    cube_rows.append(dict(n=n,first_allowed=2*n**4+3,last_allowed=2*(n+1)**4+1,
      prime_count=len(primes),first_prime=primes[0],last_prime=primes[-1],exact_moment=moment,majorant=upper,fee_upper=total))
check('entire cube prime window paid',cube_count==len([p for p in PRIMES if CUBE_START<=p<PRIME_END]))
check('scaled diagonal ratios',all(F(3,p)<=1 for p in P))
check('scaled cross ratios',F(3,15)*F(TAIL_N+2,TAIL_N+1)**2<1)
_,tailU=cube(TAIL_N)
TAIL=tailU*F((TAIL_N+1)**4-TAIL_N**4,TAIL_N**8)*F(3,2)
CUBEFEE=cube_total+TAIL
check('simple complete cube budget',CUBEFEE<F(3,100000))
HEAD={3:F(2),5:F(4,3),7:F(7,5),11:F(11,9),13:F(13,11),17:F(17,15),19:F(19,17),23:F(5,3),29:F(20,11),31:F(2)}
CAPS=dict(HEAD)
CAPS.update({r['owner_prime']:F(r['conditional_Haar_cap']) for r in small})
CAPS.update({r['owner_prime']:r['conditional_Haar_cap'] for r in rows})
check('entire finite Euler factor window',sorted(CAPS)==[p for p in PRIMES if p<CUBE_START])
factors=[dict(prime=p,cap=c,moment2=1+c*(F(3,p-1)+F(2,(p-1)**2)),
              euler_factor=(1+c*(F(3,p-1)+F(2,(p-1)**2)))*F(p-1,p)**12) for p,c in sorted(CAPS.items())]
EULER=prod(r['euler_factor'] for r in factors)
EULER_UPPER=F(3,1000)
check('new Euler correction strict upper',0<EULER<EULER_UPPER)
E=5*EULER_UPPER*F((4*117)**12,2**115)
check('same complete arbitrary-parent tail',E==F(19740202146111572828188083,495176015714152109959649689600))
TYPEI=F(1,65536)
GAMMA=F(203129722400814193208791597,20692505911553620784640000000)
check('same actual648 head gate',GAMMA==head_gate)
ALPHA=F(2673,110656)
TOTAL=FINITE+CUBEFEE+E+TYPEI;MARGIN=GAMMA-TOTAL;HEADLOW=ALPHA*MARGIN
check('positive whole complete network budget',MARGIN>0)
SIMPLE_FINITE=F(966,100000)
check('simple finite owner fee',FINITE<SIMPLE_FINITE)
SIMPLE_MARGIN=GAMMA-SIMPLE_FINITE-F(3,100000)-E-TYPEI
check('simple complete margin positive',SIMPLE_MARGIN>0)
denominator=600000
check('simple final density reciprocal',HEADLOW>ALPHA*SIMPLE_MARGIN>F(1,denominator))
def enc(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {str(k):enc(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [enc(v) for v in x]
    return x
OUT=dict(schema='four-parent-uniform89-exact-complete-policy-v1',status='PASS',new_lean_verification=False,
 baseline='1a724966729c',source_sha256={OLD.name:sha256(OLD.read_bytes()).hexdigest(),PAIR.name:sha256(PAIR.read_bytes()).hexdigest()},
 row_selection='exact minimum among orders2..8 and first N=0..198 smooth-prefix nonunit patterns withD>=5r; fixed per owner',
 producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),check_count=sum(checks.values()),checks=dict(checks),
 scope=dict(head='648 all square stars and all square pairs, remaining root incidences unchanged',
   owners='up to three fixed parents at37<=v<89; up to four at89<=v<2^115; any fixed finite union atv>=2^115',
   common_source='one sequential normalized law, joint prefix caps and original globally fixed phases',
   heights='all arbitrary finite heights and all actual original numerical labels, deduplicated once',
   ordinary='647/625/619 ordinary domains and private interfaces unchanged'),
 reference_primes=P,reference_caps=D,axis_tail_thresholds=H,exact_bucket_count=len(COORD),prefix_count=LENGTH,
 moment_common_denominator=DEN,exact_moment_numerators=MOM,early_rows=small,four_parent_rows=rows,
 early_three_parent_fee=SMALL,finite_four_parent_fee=FOUR,finite_owner_fee=FINITE,simple_finite_fee=SIMPLE_FINITE,
 cube_rows=cube_rows,cube_prime_count=cube_count,cube_finite_fee=cube_total,analytic_tail_start=PRIME_END,
 analytic_tail_n=TAIL_N,analytic_tail_fee=TAIL,complete_four_parent_cube_fee=CUBEFEE,
 finite_Euler_factors=factors,finite_Euler_correction=EULER,finite_Euler_strict_upper=EULER_UPPER,
 arbitrary_parent_threshold=2**115,complete_arbitrary_parent_fee=E,ordinary_typeI_fee=TYPEI,
 head_gate=GAMMA,projection_alpha=ALPHA,complete_total_fee=TOTAL,raw_margin=MARGIN,projected_lower=HEADLOW,
 simple_margin=SIMPLE_MARGIN,simple_density_denominator=denominator)
args.output.write_text(json.dumps(enc(OUT),indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=OUT['check_count'],buckets=len(COORD),prefix=LENGTH,
 rows=len(rows),cube_primes=cube_count,early=float(SMALL),four=float(FOUR),finite=float(FINITE),
 cube=float(CUBEFEE),Euler=float(EULER),large=float(E),total=float(TOTAL),margin=float(MARGIN),
 projected=float(HEADLOW),simple_density_denominator=denominator),indent=2))
