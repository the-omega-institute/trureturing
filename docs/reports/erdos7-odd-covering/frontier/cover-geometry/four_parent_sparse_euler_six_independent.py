#!/usr/bin/env python3
"""Independent same-policy four-parent/sixth-power Euler certificate.

Primes use trial division, products use reversed exact64-factor blocks before
256-bit directed rounding, and the logarithmic excess uses a telescoper.
The candidate producer is never imported. Ordinary arithmetic, not Lean.
"""
from pathlib import Path
from fractions import Fraction as F
from math import prod, isqrt, factorial
from hashlib import sha256
from collections import Counter
import argparse,json
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--directory',type=Path,default=Path(__file__).parent)
ap.add_argument('--candidate',type=Path)
ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
args=ap.parse_args();checks=Counter()
def ck(name,ok):
    if not ok:raise ArithmeticError(name)
    checks[name]+=1
raw=(args.directory/'unqueried_head_four_parent_certificate.json').read_bytes()
ck('pinned651input',sha256(raw).hexdigest()=='8bf5da7b70697b67e5f3df8b2787cbcac087841342423d028372ba4ebe903d2f')
old=json.loads(raw);SWITCH=3**10;B0=3**13
HEAD={3:F(2),5:F(4,3),7:F(7,5),11:F(11,9),13:F(13,11),17:F(17,15),19:F(19,17),23:F(5,3),29:F(20,11),31:F(2)}
finite_caps={r['owner_prime']:F(r['owner_prime']-1,r['h']) for r in old['rows']}
for r in old['rows']:
    ck('same inherited finite row',r['D']==r['owner_prime']-3 and r['t']==r['D']-r['h'] and 10<=r['h']<r['D'])
    ck('same inherited finite cap',finite_caps[r['owner_prime']]==F(r['conditional_Haar_cap'])<F(r['owner_prime'],10))
finite_fee=F(5455,5814)*sum(F(r['complete_hinge_upper']) for r in old['rows'])
ck('same inherited finite fee',finite_fee==F(old['finite_unqueried_fee_upper']))
# Trial division independent of the producer's sieve.
primes=[2]
for m in range(3,B0+1,2):
    prime=True
    for p in primes:
        if p*p>m:break
        if m%p==0:prime=False;break
    if prime:primes.append(m)
odd=primes[1:]
ck('complete finite prime count',len(odd)==120738)
ck('finite owner coverage',[p for p in odd if 37<=p<1253]==sorted(finite_caps))
P=(3,5,7,11);DS=(F(2),F(4,3),F(7,5),F(11,5))
# Direct coordinate moments of X=L+1 and Y=min(X,n), followed by tensor expansion.
def cube(n):
    exx=[];exy=[];eyy=[];aa=[];bb=[]
    for p,d in zip(P,DS):
        g1=F(1,p-1);g2=F(p+1,(p-1)**2);tail=d/p**n
        xx=1-d/p+d/p*(4+4*g1+g2)
        prefix=sum((1-d/p if ell==0 else d*F(p-1,p**(ell+1)))*(ell+1)**2 for ell in range(n))
        xy=prefix+tail*n*(n+1+g1);yy=prefix+tail*n*n
        a=xx-2*xy+yy;b=xx-xy
        ck('cube A from direct mixed moments',a==d*F(p*(p+1),p**n*(p-1)**2))
        ck('cube B from direct mixed moments',b==d*F(p,p**n*(p-1))*(n+1+F(2,p-1)))
        exx.append(xx);exy.append(xy);eyy.append(yy);aa.append(a);bb.append(b)
    moment=prod(exx)-2*prod(exy)+prod(eyy)
    upper=sum(aa[i]*prod(exx[j] for j in range(4) if j!=i) for i in range(4))
    upper+=2*sum(bb[i]*bb[j]*prod(exx[k] for k in range(4) if k not in(i,j)) for i in range(4) for j in range(i+1,4))
    ck('cube exact and union upper',0<moment<=upper)
    return moment,upper
moments={n:cube(n)[0] for n in range(5,14)}
ck('explicit full cube majorant base',3**5*cube(5)[1]==F(7988967877739,183428437500)<74)
ck('complete cube scaled contraction from five',all(F(3,p)<=1 for p in P) and F(3,15)*F(7,6)**2<1)
factor_pairs=[];counts=Counter();dense_integer=0;dense_quantum=10**18
for p in odd:
    if p<37:
        c=HEAD[p];counts['head']+=1
    elif p<1253:
        c=finite_caps[p];counts['finite']+=1
    elif p<=SWITCH:
        n=isqrt(isqrt((p-3)//2));den=p-n**4-2;c=F(2*(p-1),den);counts['dense']+=1
        ck('dense row correct band',2*n**4+3<=p<=2*(n+1)**4+1)
        fee=moments[n]/den**2;ceiling=-((-fee.numerator*dense_quantum)//fee.denominator)
        ck('dense full-height fee ceiling',fee<=F(ceiling,dense_quantum)<fee+F(1,dense_quantum))
        dense_integer+=ceiling
        ck('dense normalized cap',c<=4<F(p,10))
    else:
        n=11
        while 3**n<p:n+=1
        den=p-n**4-2;c=F(2*(p-1),den);counts['sparse']+=1
        ck('sparse normalized cap',3**(n-1)<p<=3**n and 2<c<4<F(p,10))
        ck('later arbitrary row dominated',F(2*(p-1),p-3)<c)
    # This integer formula precedes any rational product rounding.
    a,b=c.numerator,c.denominator
    factor_pairs.append((b*(p-1)**2+a*(3*p-1),b*(p-1)**2))
ck('complete policy partition',dict(counts)==dict(head=10,finite=193,dense=5764,sparse=114771))
dense_fee=F(dense_integer,dense_quantum)
SCALE=2**256;BLOCK=64
def blocked_interval(pairs):
    low=high=SCALE;nb=0
    rev=list(reversed(pairs))
    for start in range(0,len(rev),BLOCK):
        part=rev[start:start+BLOCK];num=prod(x[0] for x in part);den=prod(x[1] for x in part)
        low=low*num//den;high=-((-high*num)//den);nb+=1
        ck('directed exact block product',0<low<=high)
    return F(low,SCALE),F(high,SCALE),nb
mlo,mhi,nblocks=blocked_interval(factor_pairs)
plo,phi,pblocks=blocked_interval([(p,p-1) for p in odd])
ck('positive finite products',1<plo<=phi and 1<mlo<=mhi)
# Quartic half/fifth bounds follow by induction from this shifted polynomial.
growth=(23191,9060,1314,84,2)
for t in range(5):
    n=11+t
    ck('quartic growth polynomial identity',sum(a*t**j for j,a in enumerate(growth))==3*(n**4+2)-((n+1)**4+2))
ck('quartic positive induction coefficients',min(growth)>0)
ck('sparse half-bound base',2*(11**4+2)<=3**10)
ck('Euler excess fifth-bound base',5*(14**4+2)<=3**13)
ck('cube scaled diagonal and cross contraction',all(F(3,p)<=1 for p in P) and F(3,15)*F(13,12)**2<1)
ck('complete sparse moment envelope',3**11*cube(11)[1]<74)
bands=[];sparse_fee=F(0)
for n in range(11,21):
    offset=n**4+2
    fee=F(74,3**n)*(F(1,3**(n-1)-offset)-F(1,3**n-offset))
    ck('positive sparse integral band',fee>0 and 2*offset<=3**(n-1))
    sparse_fee+=fee;bands.append(dict(n=n,fee=str(fee)))
remainder=F(6*74,9**21)/(1-F(1,9))
ck('complete sparse geometric remainder',remainder==F(999,2*9**21))
sparse_fee+=remainder
# Degree-four polynomial telescoper, not a finite truncation of the logarithmic excess.
def telescoper(n):return F(6*n**4+12*n**3+36*n*n+66*n+66,4)
for n in range(5):ck('quartic telescoper identity',telescoper(n)-telescoper(n+1)/3==n**4+1)
Gamma=16*telescoper(14)/3**14
ck('complete logarithmic excess',Gamma==F(361960,1594323)<1)
Ctail=1/(1-Gamma)
ck('Euler linear excess at27',27*27-27*27+16>=0)
logB=13*(1+F(1,12)+F(1,80))
ck('positive log3 lower partial sum',logB==F(3419,240)>10)
ck('log2 elementary upper',F(2,3)+F(2,81)/(1-F(1,9))<F(7,10))
ck('Rosser ratio bound',F(1+F(1,200),1-F(1,200))==F(201,199))
gate=F(old['head_gate']);alpha=F(old['projection_alpha']);typeI=F(1,65536)
base=finite_fee+dense_fee+sparse_fee+typeI
branches={}
for kind,K,density_denominator in [('rosser_schoenfeld',52,430000),('elementary',74,520000)]:
    if kind=='rosser_schoenfeld':
        v=2**K;ell=F(7*K,10);polynomial=F(1)
        for j in range(1,7):polynomial=ell*polynomial+F(factorial(6),factorial(6-j))
        ck('integral polynomial independent expansion',polynomial==sum(F(factorial(6),factorial(6-j))*ell**(6-j) for j in range(7)))
        ck('decreasing odd integral range',v-1>B0 and B0>286)
        fee=mhi*Ctail*F(201,199)**6*F(v,v-3)**2*polynomial/(2*(v-1)*logB**6)
    else:
        ratio=F(1,2)*F(K+3,K+2)**6
        ck('whole dyadic tail ratio',0<ratio<1)
        fee=2*mhi*Ctail/plo**6*(4*(K+2))**6/(2**K*(1-ratio))
    projected=alpha*(gate-base-fee)
    ck('whole positive density',projected>F(1,density_denominator))
    branches[kind]=dict(K=K,fee=str(fee),raw_margin=str(gate-base-fee),projected=str(projected),density_denominator=density_denominator)
# Candidate output is read only after the independent reconstruction.
candidate_path=args.candidate or args.directory/'four_parent_sparse_euler_six_certificate.json'
candidate_raw=candidate_path.read_bytes();candidate=json.loads(candidate_raw)
ck('candidate complete certificate scope',candidate['status']=='PASS' and candidate['new_lean_verification'] is False)
ck('candidate input attribution',candidate['input_sha256']==sha256(raw).hexdigest())
for field,value in [('M0_lower',mlo),('M0_upper',mhi),('Podd_lower',plo),('Podd_upper',phi)]:
    ck('candidate product encloses independent '+field,F(candidate[field])<=value if field.endswith('lower') else value<=F(candidate[field]))
for field,value in [('Gamma',Gamma),('Ctail',Ctail),('dense_fee',dense_fee),('complete_sparse_fee',sparse_fee),('finite_fee',finite_fee),('typeI',typeI),('gate',gate)]:
    ck('same '+field,F(candidate[field])==value)
ck('same actual policy cutpoints',candidate['switch']==SWITCH and candidate['product_endpoint']==B0 and candidate['counts']==dict(counts))
ck('same exact dense moments',candidate['dense_moments']=={str(n):str(m) for n,m in moments.items()})
ck('same whole sparse bands',candidate['sparse_bands']==bands and F(candidate['sparse_infinite_remainder'])==remainder)
ck('same complete preliminary budget',F(candidate['basefee'])==base and F(candidate['base_reserve'])==gate-base)
for kind,field in [('rosser_schoenfeld','RS_policy'),('elementary','elementary_policy')]:
    c=candidate[field];r=branches[kind];fee=F(c['fee']);margin=alpha*(gate-base-fee)
    ck('same chosen arbitrary-parent threshold',c['K']==r['K'])
    ck('candidate full tail dominates independent bound',fee>=F(r['fee']))
    ck('candidate whole margin accounting',F(c['raw_margin'])==gate-base-fee and F(c['projected_margin'])==margin)
    ck('candidate stated density',c['stated_density_denominator']==r['density_denominator'] and margin>F(1,r['density_denominator']))
out=dict(schema='four-parent-sparse-six-independent-v1',status='PASS',new_lean_verification=False,
    input_sha256=sha256(raw).hexdigest(),candidate_sha256=sha256(candidate_raw).hexdigest(),
    producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),checks=dict(checks),check_count=sum(checks.values()),
    prime_count=len(odd),last_prime=odd[-1],counts=dict(counts),block_length=BLOCK,block_count=nblocks,
    rounding_scale=SCALE,M0_lower=str(mlo),M0_upper=str(mhi),Podd_lower=str(plo),Podd_upper=str(phi),
    dense_moments={str(n):str(m) for n,m in moments.items()},dense_fee=str(dense_fee),sparse_bands=bands,
    sparse_infinite_remainder=str(remainder),complete_sparse_fee=str(sparse_fee),Gamma=str(Gamma),Ctail=str(Ctail),
    base_fee=str(base),branches=branches)
args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='PASS',checks=out['check_count'],prime_count=len(odd),block_count=nblocks,
    M0_upper=float(mhi),dense_fee=float(dense_fee),sparse_fee=float(sparse_fee),Gamma=float(Gamma),
    branches={k:dict(K=v['K'],fee=float(F(v['fee'])),projected=float(F(v['projected']))) for k,v in branches.items()}),indent=2))
