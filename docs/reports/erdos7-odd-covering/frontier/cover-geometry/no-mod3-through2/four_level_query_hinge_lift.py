#!/usr/bin/env python3
"""Exact certificate for the actual PA fourth-level fibre lift.

All infinite tails enter full first moments. Only count atoms below4
are needed. This does not enumerate or optimize original families.
"""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
from math import prod
from pathlib import Path
import json

ROWS=((11,2,F(5,3)),(13,2,F(3,2)),(17,4,F(2)),(19,4,F(9,5)))
checks={}
def check(name,condition):
    if name in checks or not condition: raise ValueError(name)
    checks[name]=True

def coordinate(p,mass,cap):
    return mass,mass+cap/(p-1),{1:mass-cap/p,2:cap*F(p-1,p*p),3:cap*F(p-1,p**3)}
def multiply(a,b):
    low=defaultdict(F)
    for i,w in a[2].items():
        for j,v in b[2].items():
            if i*j<4: low[i*j]+=w*v
    return a[0]*b[0],a[1]*b[1],dict(low)
def hinge(law,t):
    return law[1]-t*law[0]+sum(((t-i)*w for i,w in law[2].items() if i<t),F())
def suffix_law(start):
    law=(F(1),F(1),{1:F(1)})
    for p,_,cap in ROWS[start:]: law=multiply(law,coordinate(p,F(1),cap))
    return law
suffixes=[dict(start=i,zeta4=hinge(suffix_law(i),4),zeta3=hinge(suffix_law(i),3)) for i in range(5)]
expect_zeta=(F(20115643355127233,378396319677192960),F(711972268589,47382459263360),F(7295473,2695861360),F(1,68590),F())
for i,z in enumerate(expect_zeta):check('exact suffix threshold4 '+str(i),suffixes[i]['zeta4']==z)

def corner(x,y):
    law=multiply(coordinate(5,x,F(1)),coordinate(7,y,F(1)))
    alpha=x*y-F(1,12)
    deb4=suffixes[0]['zeta4']/12
    deb3=suffixes[0]['zeta3']/12
    stages=[]
    for i,(p,t,cap) in enumerate(ROWS):
        Fq=hinge(law,t)
        charge=2*cap/(p-1)*Fq
        alpha-=charge
        deb4+=suffixes[i+1]['zeta4']*charge
        deb3+=suffixes[i+1]['zeta3']*charge
        stages.append(dict(q=p,F=Fq,charge=charge))
        law=multiply(law,coordinate(p,F(1),cap))
    phi4=hinge(law,4)
    return dict(x=x,y=y,alpha=alpha,stages=stages,phi4=phi4,debit4=deb4,K=(phi4-deb4)/alpha,old_simple_query_bound=2+(hinge(law,3)-deb3)/alpha)
cs=[corner(x,y) for x,y in product((F(1,2),F(1)),(F(2,3),F(1)))]
K=max(c['K'] for c in cs)
B=F(432040125182653876501,86355045355449035400)
alpha_min=F(7575003978548161,73724315753088000)
check('exact common hinge bound K',K==F(12019840537595758779003,5715264751774801992890))
check('worst hinge corner is smallest actual pure masses',K==cs[0]['K'])
check('positive alpha and exact alpha_min',all(c['alpha']>0 for c in cs) and min(c['alpha'] for c in cs)==alpha_min)
for i,c in enumerate(cs):
    check('corner certificate '+str(i),K*c['alpha']-c['phi4']+c['debit4']>=0)
for i,suf in enumerate(suffixes):check('nonnegative actual deletion coefficient '+str(i),K>=suf['zeta4'])
check('old SD2 arithmetic recovered unchanged',max(c['old_simple_query_bound'] for c in cs)==F(137303605308635558323,27345764362558861210))
# Coefficients of each quantity are separately affine in x and y.
# These exact interior diagnostics complement that algebraic proof.
for ix in (1,2,3):
    for iy in (1,2,3):
        a=F(ix,4);b=F(iy,4)
        x=F(1,2)+a/2;y=F(2,3)+b/3
        row=corner(x,y)
        weights=((1-a)*(1-b),(1-a)*b,a*(1-b),a*b)
        cert=row['alpha']*K-row['phi4']+row['debit4']
        interpolated=sum(w*(c['alpha']*K-c['phi4']+c['debit4']) for w,c in zip(weights,cs))
        check('bilinear certificate diagnostic '+str(ix)+' '+str(iy),cert==interpolated and cert>=0)

theta=F(1,81);kappa=F(26,27)
s0=1-K/78
query_raw=B+(1+B)/kappa
R=query_raw/s0
T=F(566,49)
gate=566-49*R
haar9=gate*kappa*s0*alpha_min/F(11088)
check('h4 geometric tail and clipping threshold',kappa==1-3*theta)
check('positive raw joint mass',0<s0<1 and s0==F(144590270033612932222139,148596883546144851815140))
check('exact joint-query upper',R==F(100187189764192062038511763,8675416202016775933328340))
check('strict complete-query target',R<T)
check('exact target margin',T-R==F(1113271896084138376764053,425095393898822020733088660))
check('exact nine-prime Haar lower',haar9==F(1113271896084138376764053,999154089609171598809907200000))
check('nine-prime Haar lower exceeds one over 900000',haar9>F(1,900000))
check('old direct h4 loss certificate fails',566*(1-B/81)-49*(1+2*B)<0)
# Pointwise clipping-mass inequality for exact rational scalar inputs.
for y in (F(),F(1),F(3),F(4),F(10),F(81),F(100)):
    for c in (F(),F(1,4),F(1,2),F(26,27),F(1)):
        if 1-c<=theta*y:
            check('pointwise retained-mass diagnostic '+str(y)+' '+str(c),min(F(1),c/kappa)>=1-theta*max(y-3,F())/kappa)

# A finite actual witness: h4 holds, h5 fails, M2 fails on a live
# Q-point, and an essential Q-only triple avoids old rooted/star scope.
Q=(5,7,11,13,17,19)
def crt(pairs):
    value=0;mod=1
    for m,a in pairs:
        value+=mod*((a-value)*pow(mod,-1,m)%m)
        mod*=m
    return value%mod
originals=[dict(m=3,a=2,d=1,e=1,qphase=0,kind='pure3')]
for p in Q:
    for e,qphase in ((0,0),(1,1),(5,2),(6,3)):
        a=crt(((3**e,0),(p,qphase)))
        originals.append(dict(m=3**e*p,a=a,d=p,e=e,qphase=qphase,kind='prime_cofactor',p=p))
originals.append(dict(m=385,a=4,d=385,e=0,qphase=4,kind='q_triple'))
check('26 original numerical labels are distinct odd nonunits',len(originals)==len({r['m'] for r in originals})==26 and all(r['m']>1 and r['m']%2 for r in originals))
selected={p:{0,1} for p in Q};selected[385]={4}
check('two selected phases suffice through exponent4',all(r['d']==1 or r['e']>4 or r['qphase'] in selected[r['d']] for r in originals))
check('exponent5 adds third phases at small cofactors',all(len({r['qphase'] for r in originals if r['d']==p and r['e']<=5})==3 for p in Q))
check('one live Q point activates six residual cofactors',all(2%d not in a for d,a in selected.items()) and sum(any(r['d']==p and r['e']>=5 and r['qphase']==2 for r in originals) for p in Q)==6)
for i,row in enumerate(originals):
    roots={p:3 for p in Q}; t=1
    if row['kind']=='pure3':t=2
    elif row['kind']=='q_triple':
        roots.update({5:4,7:4,11:4})
    else:
        e=row['e'];p=row['p']
        roots[p]=row['qphase']
        if e==1:t=3
        elif e==5:t=243
        elif e==6:
            t=0;roots={q:4 for q in Q};roots[p]=3
            if p!=7:roots[7]=5
    witness=crt(((729,t),)+tuple((p,roots[p]) for p in Q))
    row['private_witness']=witness
    check('actual private witness '+str(i),[r['m'] for r in originals if witness%r['m']==r['a']]==[row['m']])
check('essential Q-only triple remains present',originals[-1]['m']==385 and originals[-1]['m']%3!=0)

def encode(x):
    if isinstance(x,F):return {'exact':str(x),'decimal':float(x)}
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x
result=dict(scope='Two globally fixed projected phases through ternary exponent4; arbitrary later phases and activation counts, actual distinct labels, one PA source, all query heights. No unrestricted Erdős #7 or Lean claim.',suffixes=suffixes,corners=cs,K=K,B=B,theta=theta,kappa=kappa,retained_mass_lower=s0,raw_query_upper=query_raw,complete_query_upper=R,target_margin=T-R,nine_prime_Haar_lower=haar9,actual_example=originals,checks=list(checks),check_count=len(checks))
out=Path(__file__).with_suffix('.json');out.write_text(json.dumps(encode(result),indent=2)+'\n')
print(json.dumps({'checks':len(checks),'K':str(K),'query_upper':str(R),'query_upper_decimal':float(R),'Haar_lower':str(haar9),'result':str(out)}))
