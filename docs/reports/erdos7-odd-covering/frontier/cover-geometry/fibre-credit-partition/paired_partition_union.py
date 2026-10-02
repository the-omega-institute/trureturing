"""Exact coupled row-budget optimization; arithmetic phases are not optimized."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from math import prod, lcm
from itertools import product
import json

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source',required=True)
ap.add_argument('--output',required=True)
ap.add_argument('--endpoint',required=True)
args=ap.parse_args()
source=Path(args.source).read_bytes();data=json.loads(source)
endpoint=Path(args.endpoint).read_bytes();source_ep=json.loads(endpoint)
checks=0

def need(ok,msg):
    global checks
    checks+=1
    if not ok:raise ValueError(msg)

def submasks(mask):
    sub=mask
    while True:
        yield sub
        if sub==0:break
        sub=(sub-1)&mask

def optimizer(X,Y,a,W,b,V):
    need(a>0 and b>0 and W>0 and V>0,'Positive head caps and carrier masses')
    n=len(X);full=(1<<n)-1
    need(n==len(Y) and all(x>=0 and y>=0 and x+y<1 for x,y in zip(X,Y)),'Subunit paired raw budgets')
    s=W/a;t=V/b;k=s.numerator//s.denominator;rho=s-k;ell=t.numerator//t.denominator;sigma=t-ell
    need(k==2 and ell>=1,'This enumerator has two first-head full rows')
    pstar=prod(1-x/(1-y) for x,y in zip(X,Y))
    need(pstar>=rho**k,'First-head fractional-row evacuation guard')
    den=[lcm(x.denominator,y.denominator) for x,y in zip(X,Y)]
    nx=[int(x*d) for x,d in zip(X,den)];ny=[int(y*d) for y,d in zip(Y,den)]
    D=prod(den);ra,rn=rho.denominator,rho.numerator;sa,sn=sigma.denominator,sigma.numerator
    py=[prod((den[q]-ny[q] if mask>>q&1 else den[q]) for q in range(n)) for mask in range(1<<n)]
    best=None;bestA=None;bestR=None;bestparts=None;partitions=0;transitions=0
    # Full rows are interchangeable. Fix coordinate0 in first row when n>0.
    for A in range(1<<n):
        if n and not A&1:continue
        AA=[A,full^A]
        cost=[]
        for S in range(1<<n):
            vv=[prod(den[q]-(nx[q] if I>>q&1 else 0)-(ny[q] if S>>q&1 else 0) for q in range(n)) for I in AA]
            cost.append(ra*sum(vv)+rn*py[S])
        # Identical full-row partition. Force first nonempty row to hold least bit;
        # also permit empty rows, so all partitions into at most ell cells appear.
        dp=[cost[m] for m in range(1<<n)]
        parent=[]
        for j in range(2,ell+1):
            nd=[];pa=[]
            for mask in range(1<<n):
                vv=cost[0]+dp[mask];ss=0
                if mask:
                    least=mask&-mask
                    for S in submasks(mask^least):
                        S|=least;v=cost[S]+dp[mask^S];transitions+=1
                        if v<vv:vv=v;ss=S
                nd.append(vv);pa.append(ss)
            dp=nd;parent.append(pa)
        # Fractional second row stays labeled and may carry private events.
        for R in (submasks(full) if sigma else [0]):
            v=sa*dp[full^R]+sn*cost[R]
            if best is None or v<best:
                best=v;bestA=A;bestR=R
                rem=full^R;parts=[]
                for pa in reversed(parent):
                    S=pa[rem];parts.append(S);rem^=S
                parts.append(rem);bestparts=parts
        partitions+=1
    comp=a*b*F(best,ra*sa*D)
    union=W*V-comp
    # Exact independent evaluation of final assignment.
    aw=[a,a]+([a*rho] if rho else [])
    am=[bestA,full^bestA]+([0] if rho else [])
    bw=[b]*ell+([b*sigma] if sigma else [])
    bm=bestparts+([bestR] if sigma else [])
    direct=sum((ww*vv*prod(1-(X[q] if I>>q&1 else 0)-(Y[q] if J>>q&1 else 0) for q in range(n)) for ww,I in zip(aw,am) for vv,J in zip(bw,bm)),F(0))
    need(direct==comp and sum(aw)==W and sum(bw)==V,'Optimizer witness exact reconstruction')
    need(sum(am)==full and sum(bm)==full,'Every coordinate allocated once per head')
    return {'union_upper':str(union),'complement_lower':str(comp),'first_partition_masks':[bestA,full^bestA],'second_full_partition_masks':bestparts,'second_fractional_mask':bestR,'first_fractional_budget_masks':[], 'first_fractional_weight_ratio':str(rho),'second_fractional_weight_ratio':str(sigma),'first_fractional_guard':str(pstar),'first_full_partitions':partitions,'dp_transitions':transitions,'decimal':float(union)}

# Independent small-model enumeration retains BOTH fractional rows and
# evaluates every raw-budget placement, rather than using the subset DP.
def brute_union(X,Y,a,W,b,V):
    sx=W/a;sy=V/b;k=sx.numerator//sx.denominator;ell=sy.numerator//sy.denominator
    ww=[a]*k+([a*(sx-k)] if sx!=k else [])
    vv=[b]*ell+([b*(sy-ell)] if sy!=ell else [])
    best=F(-1);assignments=0
    for aa in product(range(len(ww)),repeat=len(X)):
        for bb in product(range(len(vv)),repeat=len(Y)):
            z=sum((w*v*(1-prod(1-(X[q] if aa[q]==i else 0)-(Y[q] if bb[q]==j else 0) for q in range(len(X)))) for i,w in enumerate(ww) for j,v in enumerate(vv)),F(0))
            best=max(best,z);assignments+=1
    return best,assignments

small_controls=[]
for X,Y,ell,sigma in [
    ([F(1,10),F(1,8)],[F(1,6),F(1,7)],2,F(1,2)),
    ([F(0),F(1,10)],[F(1,3),F(1,5)],2,F(1,3)),
    ([F(0)],[F(0)],2,F(0)),
    ([F(1,20),F(1,15),F(1,12)],[F(1,9),F(1,8),F(1,7)],2,F(2,3)),
    ([F(1,100),F(1,100)],[F(4,5),F(4,5)],1,F(9,10))]:
    a=F(1,3);W=F(5,6);b=F(1,ell+1);V=b*(ell+sigma)
    solved=optimizer(X,Y,a,W,b,V)
    brute,count=brute_union(X,Y,a,W,b,V)
    need(F(solved['union_upper'])==brute,'Independent all-placement maximum equals compressed DP')
    small_controls.append({'X':list(map(str,X)),'Y':list(map(str,Y)),'second_full_rows':ell,'second_fraction':str(sigma),'max_union':str(brute),'raw_assignments_checked':count,'second_fractional_mask':solved['second_fractional_mask']})
need(small_controls[-1]['second_fractional_mask']!=0,'A real scalar optimum requires second fractional row')

need(data['endpoint_sha256']==sha256(endpoint).hexdigest(),'Source certificate bound to endpoint bytes')
q=sorted(int(q) for q in data['all_nonternary_heights']['T7'])
out={'small_controls':small_controls,'source_sha256':sha256(source).hexdigest(),'endpoint_sha256':sha256(endpoint).hexdigest(),'private_primes':q,'contract':'Exact paired scalar relaxation with subunit total private budgets; no original arithmetic phase realization or unrestricted cover conclusion.'}
for scope in ['finite','all_nonternary_heights']:
    if scope=='finite':
        X=[F(source_ep['group5']['T'][str(p)]) for p in q]
        Y=[F(source_ep['additional_disjoint_group7']['T'][str(p)]) for p in q]
        a=F(data['a5']);W=F(data['W']);b=F(data['a7']);V=F(1)
        d57=F(data['D57_safe_charge']);rem=F(data['direct_remaining_charge']);old=F(data['private_joint_upper'])
    else:
        d=data[scope];X=[F(d['T5'][str(p)]) for p in q];Y=[F(d['T7'][str(p)]) for p in q]
        a=F(4,15);W=F(2,3);b=F(6,35);V=F(1);d57=a*F(d['T5']['7']);rem=F(d['remaining_charge'])
        old=F(d['joint_upper'])-d57
    r=optimizer(X,Y,a,W,b,V)
    r['improvement_over_product_defect_upper']=str(old-F(r['union_upper']))
    r['survivor_lower']=str(W-d57-rem-F(r['union_upper']))
    r['survivor_decimal']=float(F(r['survivor_lower']))
    need(F(r['union_upper'])<=old,'Exact joint optimization strengthens defect envelope')
    r['first_full_partition_primes']=[[q[t] for t in range(len(q)) if m>>t&1] for m in r['first_partition_masks']]
    r['second_full_partition_primes']=[[q[t] for t in range(len(q)) if m>>t&1] for m in r['second_full_partition_masks']]
    r['second_fractional_primes']=[q[t] for t in range(len(q)) if r['second_fractional_mask']>>t&1]
    out[scope]=r
    print(scope, json.dumps(r),flush=True)
# Existing large-prime continuation applied to the improved actual Haar seed.
from math import factorial
delta=F(out['all_nonternary_heights']['survivor_lower'])
cap=F(data['all_nonternary_heights']['density_cap'])
need(delta>F(1,500) and delta/cap>F(1,4000),'Improved all-height mass and Haar density')
B=400000;ell=11;c=F(2*ell**2+1,2*ell**2-1)
moment=F(data['large_prime_tail']['M2_upper'])
poly=sum((F(factorial(7),factorial(7-j)*ell**j) for j in range(8)),F(0))
loss=moment*c**7/F(B)*F(B,B-3)**2*poly
need(3**ell<=B and ell>=4 and B>=286,'Inherited SH11--13 parameter scope')
need(loss<F(1,5000) and F(1,4000)-loss>F(1,20000),'Smaller large-prime threshold with positive supported mass')
out['large_prime_tail']={'B':B,'ell':ell,'c_ell':str(c),'M2_upper':str(moment),'polynomial':str(poly),'tail_loss_upper':str(loss),'head_Haar_mass_lower':'1/4000','final_supported_mass_lower':str(F(1,4000)-loss),'final_supported_mass_threshold':'1/20000','contract':'Specified191 head exponent palette, only5-stars on declared pure3-avoiding root, head-only v3<=1; arbitrary finite nonternary heights; fix3,5,7 and componentwise enlarge private primes. All primes outside designated head>400000; all tail-touching heights arbitrary finite. Uses existing SH11 analytic premise. Supported distorted mass, not natural density.'}
out['checks']=checks
Path(args.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
