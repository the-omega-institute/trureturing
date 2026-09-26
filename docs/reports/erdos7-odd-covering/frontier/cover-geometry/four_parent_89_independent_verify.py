#!/usr/bin/env python3
"""Independent exact audit of the adopted four-parent89 rows and full tails."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial, lcm, prod
from hashlib import sha256
import argparse, json, sys
sys.set_int_max_str_digits(0)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--directory',type=Path,default=Path(__file__).parent)
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
BASE=args.directory
raw=(BASE/'four_parent_cutoff_exact_certificate.json').read_bytes()
data=json.loads(raw)
checks={}
def require(name,truth):
    if not truth:raise RuntimeError(name)
    checks[name]=checks.get(name,0)+1
old_raw=(BASE/'order_matched_owner_network_certificate.json').read_bytes()
require('input_digest',sha256(old_raw).hexdigest()=='9988d52c1c56a776e159295a8b98ed3b389e484a7946edb5b435aca8709adb4c')
old=json.loads(old_raw)['results']['4']
head_raw=(BASE/'induced_square_pair_boundary_certificate.json').read_bytes()
require('head_digest',sha256(head_raw).hexdigest()=='1e48eef19d525c7071498d15b4ba25445c7b431f01633d081156fb39c40d772e')
head=json.loads(head_raw)
gate=Q(next(x for x in head['scopes'] if x['scope']=='twenty')['worst']['gate'])
require('same_head',gate==Q(data['head_gate']))
ps=(3,5,7,11);ds=(Q(2),Q(4,3),Q(7,5),Q(11,5));maxima=(9,6,5,4)
# Exhaustive Cartesian enumeration; no heap or producer prefix import.
box=list(product(*(range(x+1) for x in maxima)))
patterns=sorted((prod(p**e for p,e in zip(ps,b)),b) for b in box)[:199]
require('complete_smooth_prefix',all(p**(h+1)>patterns[-1][0] for p,h in zip(ps,maxima)))
require('maximum_exponents',tuple(max(b[i] for _,b in patterns) for i in range(4))==maxima)
require('bucket_count',len(box)==2100)
# Geometric moments from Stirling numbers and factorial moments, no moment recurrence.
stirling=[[0]*9 for _ in range(9)];stirling[0][0]=1
for r in range(1,9):
    for j in range(1,r+1):stirling[r][j]=stirling[r-1][j-1]+j*stirling[r-1][j]
axis=[];axis_den=[]
for p,d,h in zip(ps,ds,maxima):
    geom=[sum(Q(stirling[r][j]*factorial(j),(p-1)**j) for j in range(r+1)) for r in range(9)]
    moments=[]
    for b in range(h+1):
        if b<h:
            mass=1-d/p if b==0 else d*Q(p-1,p**(b+1))
            moments.append([mass*(b+1)**r for r in range(9)])
        else:
            mass=d/p**h
            moments.append([mass*sum(comb(r,j)*(h+1)**(r-j)*geom[j] for j in range(r+1)) for r in range(9)])
    require('coordinate_mass',sum(m[0] for m in moments)==1)
    den=lcm(*(q.denominator for m in moments for q in m));axis_den.append(den)
    axis.append([[int(q*den) for q in m] for m in moments])
common=prod(axis_den)
volume_moments=[[prod(axis[i][b[i]][r] for i in range(4)) for r in range(9)] for b in box]
require('joint_mass',sum(x[0] for x in volume_moments)==common)
adopted={(r['selected_nonunit_patterns'],r['moment_order']) for r in data['four_parent_rows']}
require('adopted_pair_count',len(adopted)==46)
# Direct binomial moments, no finite-difference update and no producer MOM import.
counts={}
for n in {n for n,r in adopted}:
    counts[n]=[sum(all(e[i]<=b[i] for i in range(4)) for _,e in patterns[:n+1]) for b in box]
exact={}
for n,r in sorted(adopted):
    numerator=0
    for c,m in zip(counts[n],volume_moments):
        numerator+=sum(comb(r,j)*(-c)**(r-j)*m[j] for j in range(r+1))
    exact[n,r]=Q(numerator,common)
    require('positive_full_moment',numerator>0)
# Independent trial division over all finite prime windows.
primes=[2]
for v in range(3,20003,2):
    isprime=True
    for p in primes:
        if p*p>v:break
        if v%p==0:isprime=False;break
    if isprime:primes.append(v)
primes=primes[1:]
finite=Q(0)
early=[r for r in old['rows'] if r['owner_prime']<89]
require('complete_early_window',[r['owner_prime'] for r in early]==[p for p in primes if 37<=p<89])
require('early_rows_preserved',early==data['early_rows'])
for row in early:finite+=Q(row['violation_fee'])
new=data['four_parent_rows']
require('complete_four_window',[r['owner_prime'] for r in new]==[p for p in primes if 89<=p<1253])
for row in new:
    v,n,r=row['owner_prime'],row['selected_nonunit_patterns'],row['moment_order'];d=v-3-n
    require('row_parameters',d==row['complement_D'] and d>=5*r and 2<=r<=8 and 0<=n<=198)
    require('row_threshold',Q(row['threshold'])==Q(r-1,r))
    require('row_cap',Q(row['conditional_Haar_cap'])==Q(r*(v-1),d)<Q(v,5))
    require('direct_infinite_moment',exact[n,r]==Q(row['exact_complete_moment']))
    fee=exact[n,r]/d**r
    require('row_fee',fee==Q(row['violation_fee']))
    finite+=fee
require('finite_fee',finite==Q(data['finite_owner_fee'])<Q(966,100000))
# Joint role domination: all eligible explicit head coordinates at all depths
# follow from their depth1 ratio and u>=p_i; outside ratio bound is 1/5.
head_caps={3:Q(2),5:Q(4,3),7:Q(7,5),11:Q(11,9),13:Q(13,11),17:Q(17,15),19:Q(19,17),23:Q(5,3),29:Q(20,11),31:Q(2)}
for p,d in zip(ps,ds):
    require('outside_role_ratio',Q(1,5)<=d/p)
    for u,c in head_caps.items():
        if u>=p:require('head_role_ratio',c/u<=d/p)
# Compute cube moments from moments of X=L+1 and Y=min(X,n),
# using direct finite atoms for Y and tail factorial moments.
def cube(n):
    tx=[];xy=[];yy=[];aa=[];bb=[]
    for p,d in zip(ps,ds):
        g1=Q(1,p-1);g2=Q(p+1,(p-1)**2)
        tail=d/p**n
        EX2=1-d/p+d/p*(4+4*g1+g2)
        EXY=sum((1-d/p if ell==0 else d*Q(p-1,p**(ell+1)))*(ell+1)**2 for ell in range(n))
        EXY+=tail*n*(n+1+g1)
        EY2=sum((1-d/p if ell==0 else d*Q(p-1,p**(ell+1)))*(ell+1)**2 for ell in range(n))+tail*n*n
        A=EX2-2*EXY+EY2;B=EX2-EXY
        require('cube_coordinate_A',A==d*Q(p*(p+1),p**n*(p-1)**2))
        require('cube_coordinate_B',B==d*Q(p,p**n*(p-1))*(n+1+Q(2,p-1)))
        tx.append(EX2);xy.append(EXY);yy.append(EY2);aa.append(A);bb.append(B)
    M=prod(tx)-2*prod(xy)+prod(yy)
    U=sum(aa[i]*prod(tx[j] for j in range(4) if j!=i) for i in range(4))+2*sum(bb[i]*bb[j]*prod(tx[k] for k in range(4) if k!=i and k!=j) for i in range(4) for j in range(i+1,4))
    require('cube_majorant',0<M<=U)
    return M,U
cube_fee=Q(0);cube_count=0;scale=10**18
for item in data['cube_rows']:
    n=item['n'];M,U=cube(n)
    require('cube_moment_match',M==Q(item['exact_moment']) and U==Q(item['majorant']))
    domain=[v for v in primes if 2*n**4+3<=v<=2*(n+1)**4+1]
    require('cube_domain_count',len(domain)==item['prime_count'])
    subtotal=0
    for v in domain:
        D=v-n**4-2;fee=M/D**2
        require('cube_cap',Q(2*(v-1),D)<=4<Q(v,5))
        ceil=-((-fee.numerator*scale)//fee.denominator)
        require('cube_ceiling',fee<=Q(ceil,scale)<fee+Q(1,scale))
        subtotal+=ceil
    require('cube_band_fee',Q(subtotal,scale)==Q(item['fee_upper']))
    cube_fee+=Q(subtotal,scale);cube_count+=len(domain)
require('complete_cube_window',cube_count==2058==len([p for p in primes if 1253<=p<20003]))
M10,U10=cube(10)
# g(n)=4/n^5+6/n^6+4/n^7+1/n^8 decreases; this is its exact expansion.
require('tail_odd_count_expression',Q(11**4-10**4,10**8)==4*Q(1,10**5)+6*Q(1,10**6)+4*Q(1,10**7)+Q(1,10**8))
require('tail_cross_ratio',Q(3,3*5)*Q(12,11)**2<1)
tail=U10*Q(11**4-10**4,10**8)/(1-Q(1,3))
require('infinite_tail',tail==Q(data['analytic_tail_fee']))
cube_fee+=tail
require('complete_cube_fee',cube_fee==Q(data['complete_four_parent_cube_fee'])<Q(3,100000))
# Entire actual finite Euler window, reverse exact multiplication.
caps=dict(head_caps)
caps.update({r['owner_prime']:Q(r['conditional_Haar_cap']) for r in early+new})
require('finite_Euler_domain',sorted(caps)==[p for p in primes if p<1253] and len(caps)==203)
euler=Q(1)
for p,c in sorted(caps.items(),reverse=True):
    euler*= (1+c*(Q(3,p-1)+Q(2,(p-1)**2)))*Q(p-1,p)**12
require('finite_Euler',euler==Q(data['finite_Euler_correction'])<Q(3,1000))
large=Q(15,1000)*(4*117)**12/2**115
require('large_tail',large==Q(data['complete_arbitrary_parent_fee']))
alpha=Q(2673,110656);ordinary=Q(1,65536)
actual_total=finite+cube_fee+large+ordinary
require('complete_total',actual_total==Q(data['complete_total_fee']))
projected=alpha*(gate-actual_total)
simple=alpha*(gate-Q(966,100000)-Q(3,100000)-large-ordinary)
require('strict_final_density',projected>simple>Q(1,600000))
result=dict(producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),status='PASS',check_count=sum(checks.values()),checks=checks,reviewed_data_sha256=sha256(raw).hexdigest(),independent_complete_moment_pairs=len(adopted),finite_fee=str(finite),cube_fee=str(cube_fee),Euler=str(euler),complete_fee=str(actual_total),projected_margin=str(projected),simple_margin=str(simple),new_lean_verification=False)
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=result['check_count'],complete_moment_pairs=len(adopted),finite_fee=float(finite),cube_fee=float(cube_fee),Euler=float(euler),complete_fee=float(actual_total),projected_margin=float(projected),simple_margin=float(simple)),indent=2))
