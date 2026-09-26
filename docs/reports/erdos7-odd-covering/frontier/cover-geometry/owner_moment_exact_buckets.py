#!/usr/bin/env python3
"""Exact full infinite moments by polynomial tail buckets; compare certified rows."""
from fractions import Fraction as F
from math import comb, gcd, prod
from itertools import product
import heapq, json, sys, hashlib, time
from pathlib import Path
sys.set_int_max_str_digits(0)
started=time.monotonic()
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--candidate',type=Path,default=Path(__file__).with_name('order_matched_owner_network_certificate.json'))
parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=parser.parse_args()
CANDIDATE=args.candidate
cand=json.loads(CANDIDATE.read_text())
checks={}
def check(group, ok):
    checks[group]=checks.get(group,0)+1
    if not ok: raise RuntimeError('FAIL '+group)
def lcm(a,b):return a//gcd(a,b)*b
P=(3,5,7); D=(F(2),F(4,3),F(7,5)); count=958
# Own increasing smooth-number enumeration; no candidate pattern list or program.
heap=[(1,0,0,0)]; seen={(0,0,0)}; pats=[]; values=[]
while len(pats)<count:
    val,*xs=heapq.heappop(heap);x=tuple(xs);pats.append(x);values.append(val)
    for i,p in enumerate(P):
        y=list(x);y[i]+=1;y=tuple(y)
        if y not in seen:
            seen.add(y);heapq.heappush(heap,(val*p,*y))
h=tuple(max(x[i] for x in pats) for i in range(3))
full=sorted((prod(P[i]**x[i] for i in range(3)),x) for x in product(*(range(a+1) for a in h)) if prod(P[i]**x[i] for i in range(3))<=values[-1])
check('independent complete smooth prefix',full==list(zip(values,pats)))
check('requested candidate prefix length',cand['prefix_count']==count)
check('Cartesian prefix box is complete',all(P[i]**(h[i]+1)>values[-1] for i in range(3)))
# Partition each infinite coordinate into 0,...,h-1 and its ENTIRE tail >=h.
# Exact moments of G with P(G=g)=(1-1/p)p^-g follow stationarity.
axis=[]; axisden=[]
for p,d,cut in zip(P,D,h):
    gm=[F(1)]
    for j in range(1,5):gm.append(sum(F(comb(j,k))*gm[k] for k in range(j))/F(p-1))
    raw=[]
    for ell in range(cut):
        mass=1-d/p if ell==0 else d*F(p-1,p**(ell+1))
        raw.append([mass*(ell+1)**j for j in range(5)])
    raw.append([d/F(p**cut)*sum(F(comb(j,k)*(cut+1)**(j-k))*gm[k] for k in range(j+1)) for j in range(5)])
    check('axis total probability',sum(x[0] for x in raw)==1)
    for j in range(5):
        whole=1-d/p+d/F(p)*sum(F(comb(j,k)*2**(j-k))*gm[k] for k in range(j+1))
        check('bucket moments equal whole geometric formula',sum(x[j] for x in raw)==whole)
    check('positive full tail moments',all(z>0 for z in raw[-1]))
    den=1
    for row in raw:
        for x in row:den=lcm(den,x.denominator)
    axisden.append(den);axis.append([[int(x*den) for x in row] for row in raw])
scale=prod(axisden)
coords=list(product(*(range(a+1) for a in h)))
weights=[[prod(axis[i][b[i]][j] for i in range(3)) for j in range(5)] for b in coords]
check('joint full probability',sum(w[0] for w in weights)==scale)
counts=[0]*len(coords)
cur3=sum(w[3] for w in weights);cur4=sum(w[4] for w in weights)
nums={3:[],4:[]}
# Adding one selected point increments exactly the boxes that dominate it.
for n,x in enumerate(pats):
    for ix,b in enumerate(coords):
        if all(b[i]>=x[i] for i in range(3)):
            c=counts[ix];w=weights[ix]
            cur3 += -3*w[2]+(6*c+3)*w[1]-(3*c*c+3*c+1)*w[0]
            cur4 += -4*w[3]+(12*c+6)*w[2]-(12*c*c+12*c+4)*w[1]+(4*c*c*c+6*c*c+4*c+1)*w[0]
            counts[ix]=c+1
    nums[3].append(cur3);nums[4].append(cur4)
    check('exact moments positive',cur3>0 and cur4>0)
    if n:check('exact moments strictly decrease',nums[3][-2]>cur3 and nums[4][-2]>cur4)
# Direct unit-complement formula checks the first moment value independently.
for r in (3,4):
    direct0=sum(comb(r,j)*(-1)**(r-j)*sum(w[j] for w in weights) for j in range(r+1))
    check('direct initial unit-complement formula',direct0==nums[r][0])
# Direct final bucket sum independently checks the incremental polynomial update.
for r in (3,4):
    direct=sum(sum(comb(r,j)*(-c)**(r-j)*w[j] for j in range(r+1)) for c,w in zip(counts,weights))
    check('direct final full-tail polynomial sum',direct==nums[r][-1])
# Independent finite prime window and literal head caps from625.
flags=[True]*971;flags[0]=flags[1]=False
for p in range(2,32):
    if flags[p]:
        for j in range(p*p,971,p):flags[j]=False
primes=[p for p in range(3,971) if flags[p]]
owners=[p for p in primes if p>=37]
head={3:F(2),5:F(4,3),7:F(7,5),11:F(11,9),13:F(13,11),17:F(17,15),19:F(19,17),23:F(5,3),29:F(20,11),31:F(2)}
check('complete owner prime window',len(owners)==152)
check('complete finite Euler prime window',len(primes)==162 and set(primes[:10])==set(head))
TAIL=F(512,9529569);TYPEI=F(1,65536);V=2**115
results={}
for r in (3,4):
    c=cand['results'][str(r)]
    check('candidate rows are complete ordered prime window',[z['owner_prime'] for z in c['rows']]==owners)
    check('candidate moment count',len(c['upper_moment_numerators'])==count)
    cscale=c['common_moment_denominator']
    errors=[]
    for n,val in enumerate(c['upper_moment_numerators']):
        exact=F(nums[r][n],scale); upper=F(val,cscale)
        check('all candidate moment uppers dominate exact full-tail moments',upper>=exact)
        errors.append(upper-exact)
    cap=dict(head); exact_finite=F(0);candidate_fee_rebuilt=F(0);rows=[];matches=0
    for v,cr in zip(owners,c['rows']):
        N=cr['selected_nonunit_patterns'];den=v-3-N
        check('row admissible selected count',0<=N<count and den>=5*r)
        cc=F(r*(v-1),den);cap[v]=cc
        check('row cap invariant',cc<F(v,5))
        check('candidate row D threshold cap consistency',cr['complement_D']==den and F(cr['threshold'])==F(r-1,r) and F(cr['conditional_Haar_cap'])==cc)
        mm=F(nums[r][N],scale);fee=mm/F(den**r);exact_finite+=fee
        upper=F(c['upper_moment_numerators'][N],cscale)
        cfee=upper/F(den**r);candidate_fee_rebuilt+=cfee
        check('candidate row moment and fee consistency',F(cr['complete_moment_upper'])==upper and F(cr['violation_fee'])==cfee)
        check('candidate row fee bounds exact fee',cfee>=fee)
        bestN=min(range(v-3-5*r+1),key=lambda n:F(nums[r][n],(v-3-n)**r))
        matches+=N==bestN
        rows.append({'v':v,'N':N,'r':r,'D':den,'cap':str(cc),'exact_moment':str(mm),'exact_fee':str(fee),'independent_minimizing_N':bestN})
    check('candidate finite fee sum consistency',candidate_fee_rebuilt==F(c['finite_owner_fee']))
    check('candidate full owner budget consistency',candidate_fee_rebuilt+TAIL==F(c['total_owner_fee']) and F(c['prime_tail_fee'])==TAIL)
    total=exact_finite+TAIL
    simple={3:F(8631,1000000),4:F(397,50000)}[r]
    check('independent owner fee simple bound',total<simple)
    check('candidate owner fee simple bound',candidate_fee_rebuilt+TAIL<simple and F(c['simple_total_owner_fee_upper'])==simple)
    minD=min(row['D'] for row in rows)
    check('candidate minimum D',minD==c['minimum_D'])
    euler=F(1);factors=[]
    for p in primes:
        mom=1+cap[p]*(F(3,p-1)+F(2,(p-1)**2))
        factor=mom*F(p-1,p)**12;euler*=factor
        factors.append({'prime':p,'cap':str(cap[p]),'moment2':str(mom),'euler_correction':str(factor)})
    check('all162 candidate Euler factors match independent rows',factors==c['finite_Euler_factors'])
    check('candidate Euler exact product matches',euler==F(c['finite_Euler_correction']))
    eu={3:F(3,1000),4:F(1,125)}[r]
    check('independent Euler strict target',0<euler<eu)
    check('candidate Euler target',F(c['finite_Euler_strict_upper'])==eu)
    large=5*eu*F((4*117)**12,V)
    check('candidate whole large tail rederived',F(c['complete_large_owner_tail'])==large and c['same_large_owner_threshold']==V)
    combined=total+large+TYPEI
    check('candidate all fees consistent',candidate_fee_rebuilt+TAIL+large+TYPEI==F(c['owner_plus_large_tail_plus_ordinary']))
    results[str(r)]={'moment_order':r,'exact_moment_denominator':scale,'exact_moment_numerators':nums[r],'rows':rows,'independently_exact_minimizing_rows':matches,'finite_owner_fee':str(exact_finite),'finite_owner_fee_decimal':float(exact_finite),'total_owner_fee':str(total),'total_owner_fee_decimal':float(total),'minimum_D':minD,'Euler_correction':str(euler),'Euler_correction_decimal':float(euler),'Euler_strict_upper':str(eu),'whole_large_owner_tail':str(large),'whole_large_owner_tail_decimal':float(large),'owner_large_ordinary_total':str(combined),'owner_large_ordinary_decimal':float(combined),'maximum_candidate_moment_overestimate':str(max(errors)),'minimum_candidate_moment_overestimate':str(min(errors))}
output={'status':'PASS','method':'Independent exact infinite tail buckets and geometric moments; no candidate producer read or imported. Candidate JSON supplies chosen N parameters and comparison targets only.','producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'candidate_json_sha256':hashlib.sha256(CANDIDATE.read_bytes()).hexdigest(),'prefix_count':count,'last_smooth_value':values[-1],'axis_tail_thresholds':h,'exact_bucket_count':len(coords),'checks':checks,'check_count':sum(checks.values()),'results':results,'elapsed_seconds':time.monotonic()-started,'new_lean_verification':False}
args.output.write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps({k:output[k] for k in ('status','axis_tail_thresholds','exact_bucket_count','check_count','elapsed_seconds')}))
for r,d in results.items():print(json.dumps({'order':r,**{k:d[k] for k in ('finite_owner_fee_decimal','total_owner_fee_decimal','minimum_D','Euler_correction_decimal','whole_large_owner_tail_decimal','owner_large_ordinary_decimal','independently_exact_minimizing_rows')}}))
