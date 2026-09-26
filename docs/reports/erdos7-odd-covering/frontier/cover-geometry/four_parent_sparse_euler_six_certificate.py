"""Exact coefficient certificate for the four-parent sparse Euler-six policies.
Reads the sibling Report651 certificate. Universal source/analytic arguments
are ordinary mathematics in the accompanying result; no new Lean verification.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb, factorial, isqrt, prod
import json, hashlib, argparse
P=argparse.ArgumentParser();P.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent);P.add_argument('--output',type=Path);args=P.parse_args();SWITCH_POWER=10;PRODUCT_POWER=13
checks=0;check_categories={}
def check(q, category="budget_guard"):
 global checks
 checks+=1
 check_categories[category]=check_categories.get(category,0)+1
 if not q: raise AssertionError((category,checks))
def qstr(v):return str(v)
def ceildiv(a,b):return -(-a//b)
candidate_path=args.directory/'unqueried_head_four_parent_certificate.json'
candidate_bytes=candidate_path.read_bytes();candidate=json.loads(candidate_bytes)
check(hashlib.sha256(candidate_bytes).hexdigest()=='8bf5da7b70697b67e5f3df8b2787cbcac087841342423d028372ba4ebe903d2f','pinned651_input')
head=dict(zip((3,5,7,11,13,17,19,23,29,31),map(F,('2','4/3','7/5','11/9','13/11','17/15','19/17','5/3','20/11','2'))))
finite={r['owner_prime']:F(r['conditional_Haar_cap']) for r in candidate['rows']}
check(candidate['status']=='PASS','source_status')
check(len(finite)==193,'source_finite_rows')
zeta=F(5455,5814)
check(F(candidate['unqueried_factor'])==zeta,'source_omission_factor')
for r in candidate['rows']:
 v,h,D,t=r['owner_prime'],r['h'],r['D'],r['t']
 check(r['N']==0 and D==v-3 and t==D-h and 10<=h<D,'finite_row_policy')
 check(F(r['conditional_Haar_cap'])==F(v-1,h)<F(v,10),'finite_row_cap')
 check(F(r['unqueried_fee_upper'])==zeta*F(r['complete_hinge_upper']),'finite_hinge_fee')
check(sum((F(r['unqueried_fee_upper']) for r in candidate['rows']),F(0))==F(candidate['finite_unqueried_fee_upper']),'finite_fee_sum')
check(F(candidate['head_gate'])==F(203129722400814193208791597,20692505911553620784640000000),'head_reserve')
check(F(candidate['projection_alpha'])==F(2673,110656),'head_projection')
switch=3**SWITCH_POWER;limit=3**PRODUCT_POWER
check(SWITCH_POWER>=9);check(PRODUCT_POWER>=12);check(limit>switch)
flags=bytearray(b'\x01')*(limit+1);flags[:2]=b'\x00\x00'
for p in range(2,isqrt(limit)+1):
 if flags[p]:flags[p*p:limit+1:p]=b'\x00'*((limit-p*p)//p+1)
primes=[p for p in range(3,limit+1,2) if flags[p]]
def cube_depth(p):
 n=isqrt(isqrt((p-3)//2))
 check(2*n**4+3<=p<2*(n+1)**4+3,"dense_depth")
 return n
def sparse_depth(p):
 n=1
 while 3**n<p:n+=1
 check(3**(n-1)<p<=3**n,"sparse_depth")
 return n
def cap(p):
 if p in head:return head[p]
 if p in finite:return finite[p]
 n=cube_depth(p) if p<switch else sparse_depth(p)
 check(p-n**4-2>0,"positive_domain")
 value=F(2*(p-1),p-n**4-2)
 check(value<F(p,10),"actual_cap_invariant")
 return value
pp=(3,5,7,11);dd=tuple(map(F,('2','4/3','7/5','11/5')))
def cube_moment(n):
 T=[1+d*(F(3,p-1)+F(2,(p-1)**2)) for p,d in zip(pp,dd)]
 A=[d*F(p*(p+1),(p-1)**2*p**n) for p,d in zip(pp,dd)]
 B=[d*F(1,p**(n-1)*(p-1))*(n+1+F(2,p-1)) for p,d in zip(pp,dd)]
 M=prod(T)-2*prod(t-b for t,b in zip(T,B))+prod(t-2*b+a for t,b,a in zip(T,B,A))
 U=sum(A[i]*prod(T[j] for j in range(4) if j!=i) for i in range(4))+2*sum(B[i]*B[j]*prod(T[k] for k in range(4) if k not in (i,j)) for i in range(4) for j in range(i+1,4))
 check(0<M<=U<=F(74,3**n),"cube_moment")
 return M
cache={};dense_units=0;rounding_scale=10**18;dense_count=0
for p in primes:
 if not 1253<=p<switch:continue
 n=cube_depth(p)
 if n not in cache:cache[n]=cube_moment(n)
 fee=cache[n]/(p-n**4-2)**2
 dense_units+=ceildiv(fee.numerator*rounding_scale,fee.denominator);dense_count+=1
wdense=F(dense_units,rounding_scale)
# The sparse bands use every integer and exact infinite remainder.
# For every sparse band n>=11, n^4+2<=3^(n-1)/2.
check(2*(11**4+2)<=3**10)
# Positive coefficients of 3(n^4+2)-((n+1)^4+2), shifted n=11+t.
poly=[2,-4,-6,-4,3]
shifted=[sum(F(poly[4-j])*comb(j,k)*11**(j-k) for j in range(k,5)) for k in range(5)]
check(all(x>0 for x in shifted))
bands=[]
for n in range(SWITCH_POWER+1,21):
 A=3**(n-1)+1;B=3**n;c=n**4+2
 check(A-c-1>0,"sparse_band_domain")
 fee=F(74,3**n)*(F(1,A-c-1)-F(1,B-c))
 bands.append(dict(n=n,fee=str(fee)))
wsparse=sum((F(z['fee']) for z in bands),F(0))+F(999,2*9**21)
# Finite Euler products, upper/lower fixed denominator integer rounding.
scale=2**160;mlo=mhi=plo=phi=scale
capmax=F(0);counts=dict(head=0,finite=0,dense=0,sparse=0)
for p in primes:
 c=cap(p);capmax=max(capmax,c)
 counts['head' if p in head else 'finite' if p in finite else 'dense' if p<switch else 'sparse']+=1
 a,b=c.numerator,c.denominator
 den=b*(p-1)**2;num=den+a*(3*(p-1)+2)
 mlo=mlo*num//den;mhi=ceildiv(mhi*num,den)
 plo=plo*p//(p-1);phi=ceildiv(phi*p,p-1)
check(counts['head']==10);check(counts['finite']==193);check(counts['dense']==dense_count)
Mlo,Mhi,Plo,Phi=(F(v,scale) for v in (mlo,mhi,plo,phi))
# Exact fourth-power polynomial-geometric infinite sum.
mom=(F(3,2),F(3,4),F(3,2),F(33,8),F(15))
a=PRODUCT_POWER+1
Gamma=F(16,3**a)*(sum(F(comb(4,j)*a**(4-j))*mom[j] for j in range(5))+mom[0])
check(Gamma<1);check(5*(a**4+2)<=limit)
Ctail=1/(1-Gamma)
alpha=F(candidate['projection_alpha']);gate=F(candidate['head_gate']);wfinite=F(candidate['finite_unqueried_fee_upper']);typeI=F(1,65536)
basefee=wfinite+wdense+wsparse+typeI
check(basefee<gate)
A6=Mhi*Ctail/Plo**6
rs=[];elementary=[]
for K in (52,74):
 V=2**K
 poly6=sum(F(factorial(6),factorial(6-j))*F(7*K,10)**(6-j) for j in range(7))
 E=Mhi*Ctail*F(201,199)**6*F(V,V-3)**2*poly6/(2*(V-1)*F(263*PRODUCT_POWER,240)**6)
 raw=gate-basefee-E
 if K==52:
  check(raw>0,"RS_positive_margin")
  density=alpha*raw;denom=density.denominator//density.numerator+1
  check(density>F(1,denom))
  rs.append(dict(K=K,fee=str(E),raw_margin=str(raw),projected_margin=str(density),density_denominator=denom))
 ratio=F(1,2)*F(K+3,K+2)**6
 if K==74:
  check(ratio<1,"elementary_geometric_ratio")
  Ee=2*A6*(4*(K+2))**6/F(2**K)/(1-ratio)
  raw=gate-basefee-Ee
  if K==74:
   check(raw>0,"elementary_positive_margin")
   density=alpha*raw;denom=density.denominator//density.numerator+1
   check(density>F(1,denom))
   elementary.append(dict(K=K,fee=str(Ee),raw_margin=str(raw),projected_margin=str(density),density_denominator=denom))
check(len(rs)==1 and len(elementary)==1,'chosen_policy_count')
check(F(rs[0]['projected_margin'])>F(1,430000),'RS_clean_density')
check(F(elementary[0]['projected_margin'])>F(1,520000),'elementary_clean_density')
out=dict(status='PASS',scope='Exact coefficients for the fixed RS52 and elementary74 row policies; source and infinite-tail arguments are ordinary proofs',new_lean_verification=False,input_sha256=hashlib.sha256(candidate_bytes).hexdigest(),producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),switch=switch,product_endpoint=limit,counts=counts,check_count=checks,check_categories=check_categories,Gamma=str(Gamma),Ctail=str(Ctail),M0_lower=str(Mlo),M0_upper=str(Mhi),Podd_lower=str(Plo),Podd_upper=str(Phi),dense_fee=str(wdense),dense_moments={str(n):str(v) for n,v in cache.items()},sparse_bands=bands,sparse_infinite_remainder=str(F(999,2*9**21)),complete_sparse_fee=str(wsparse),finite_fee=str(wfinite),typeI=str(typeI),basefee=str(basefee),gate=str(gate),base_reserve=str(gate-basefee),RS_policy={**rs[0],'stated_density_denominator':430000},elementary_policy={**elementary[0],'stated_density_denominator':520000})
output=args.output or Path(__file__).with_suffix('.json');output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status=out['status'],check_count=checks,counts=counts,Gamma=float(Gamma),M0_upper=float(Mhi),dense_fee=float(wdense),sparse_fee=float(wsparse),base_reserve=float(gate-basefee),RS_first={**{k:v for k,v in rs[0].items() if k in ('K','density_denominator')},'raw_margin':float(F(rs[0]['raw_margin'])),'fee':float(F(rs[0]['fee']))},elementary_first={**{k:v for k,v in elementary[0].items() if k in ('K','density_denominator')},'raw_margin':float(F(elementary[0]['raw_margin'])),'fee':float(F(elementary[0]['fee']))}),indent=2))
