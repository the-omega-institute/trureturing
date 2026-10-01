"""Exact finite-cap N=2 endpoint; complete moments and all-depth comparison."""

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from hashlib import sha256
import json
from math import factorial, prod
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
LIMIT = 256
ORDERS = (0, 1, 2, 4)
PRIMES = (3,5,7,11,13,17,19,23,29,31,37,41)
NEXT = (43,47,53,59,61,67,71,73)
checks = []


def ck(v, name):
    if not v:
        raise ArithmeticError(name)
    checks.append(name)


def haar_moment(p, k):
    # Factorial moments of a geometric variable supported on 1,2,...:
    # E[(V)_j]=j!*p/(p-1)^j for j>=1. Stirling transforms give V^k.
    if k == 0:
        return F(1)
    row = [1]
    for n in range(1,k+1):
        row = [0] + [(row[j-1] if j-1<len(row) else 0)
                     + j*(row[j] if j<len(row) else 0)
                     for j in range(1,n+1)]
    return sum((F(row[j]*factorial(j)*p,(p-1)**j)
                for j in range(1,k+1)),F(0))


def append(atoms, moments, p, mass, cap):
    out = [F(0)]*(LIMIT+1)
    probabilities = [F(0),mass-F(cap,p)]
    probabilities.extend(F(cap*(p-1),p**v) for v in range(2,LIMIT+1))
    # Divisor-based convolution, independently of the author's implementation.
    for n in range(1,LIMIT+1):
        out[n] = sum((atoms[n//v]*probabilities[v]
                      for v in range(1,n+1) if n%v==0),F(0))
    out_moments = [moments[i]*(mass+cap*(haar_moment(p,k)-1))
                   for i,k in enumerate(ORDERS)]
    ck(all(v>=0 for v in out),'nonnegative convolved atoms at '+str(p))
    return out,out_moments


def atom_hash(atoms):
    content='\n'.join(str(n)+':'+str(atoms[n]) for n in range(1,LIMIT+1))
    return sha256(content.encode()).hexdigest()


def snapshot(atoms,moments):
    low = [sum((F(n**k)*atoms[n] for n in range(1,LIMIT+1)),F(0))
           for k in ORDERS]
    tail=[moments[i]-low[i] for i in range(4)]
    ck(all(v>=0 for v in tail),'complete infinite moment tail nonnegative')
    ck(tail[1]>=(LIMIT+1)*tail[0] and tail[2]>=(LIMIT+1)*tail[1]
       and tail[3]>=(LIMIT+1)**2*tail[2],'tail support above atom inventory')
    return {'moments':{str(k):str(moments[i]) for i,k in enumerate(ORDERS)},
            'low_moments':{str(k):str(low[i]) for i,k in enumerate(ORDERS)},
            'tail_moments':{str(k):str(tail[i]) for i,k in enumerate(ORDERS)},
            'atom_hash_1_through_256':atom_hash(atoms)}


def trim(atoms,moments,target):
    ck(0<target<=moments[0],'legal positive upper-mass target')
    remaining=moments[0]-target
    out=atoms[:]
    removals=[]
    cutoff=None
    for n in range(1,LIMIT+1):
        amount=min(out[n],remaining)
        out[n]-=amount
        remaining-=amount
        removals.append((n,amount))
        if remaining==0:
            cutoff=n
            break
    ck(remaining==0,'exact trim resolved within finite low inventory')
    removed=[sum((F(n**k)*v for n,v in removals),F(0)) for k in ORDERS]
    result=[moments[i]-removed[i] for i in range(4)]
    ck(result[0]==target and all(out[n]==0 for n in range(1,cutoff)),
       'exact target and upper-mass support')
    return out,result,{'cutoff':cutoff,
                       'removed':{str(k):str(removed[i]) for i,k in enumerate(ORDERS)},
                       'split_retained':str(out[cutoff])}


def decimal(v):
    with localcontext() as ctx:
        ctx.prec=40
        return str(Decimal(v.numerator)/Decimal(v.denominator))


N=2
mstar=F(36518862868606981,466438558966380000)
factors=[]
atoms=[F(0)]*(LIMIT+1)
atoms[1]=F(1)
moments=[F(1)]*4
for p in PRIMES:
    A=F(2,3) if p==3 else 1-sum((F(1,p**e) for e in range(1,N+1)),F(0))
    ck(A>=F(1,p),'finite-cap anchor atom nonnegative at '+str(p))
    factors.append({'p':p,'mass':str(A)})
    atoms,moments=append(atoms,moments,p,A,F(1))
raw=snapshot(atoms,moments)
A_total=moments[0]
h=mstar*A_total
ck(0<mstar<1,'fixed source m_star lies in probability domain')
ck(0<h<A_total,'tight initial h2 below complete raw mass')
ck(h>F(36518862868606981,1816999451688960000),'finite-cap initial mass improves uniform fixed-h bound')
atoms,moments,initial_trim=trim(atoms,moments,h)
initial=snapshot(atoms,moments)
records=[]
for p in NEXT:
    before=snapshot(atoms,moments)
    T=F(p-1,2)
    ck(F(2)<=p,'half clipping has legal cap at '+str(p))
    ck(T<=LIMIT,'exact stop-loss threshold inside low inventory')
    hinge=moments[1]-T*moments[0]+sum(((T-n)*atoms[n]
                                     for n in range(1,LIMIT+1) if n<T),F(0))
    charge=hinge/T
    target=moments[0]-charge
    ck(hinge>=0,'nonnegative complete hinge at '+str(p))
    record={'prime':p,'before':before,'threshold':str(T),'hinge':str(hinge),
            'charge':str(charge),'target':str(target),'positive':target>0,
            'mean_gate':str((p-1)*moments[0]-moments[1])}
    if target<=0:
        records.append(record)
        break
    atoms,moments=append(atoms,moments,p,F(1),F(2))
    record['appended']=snapshot(atoms,moments)
    atoms,moments,record['trim']=trim(atoms,moments,target)
    record['after']=snapshot(atoms,moments)
    records.append(record)
next73=next((r for r in records if r['prime']==73),None)
barrier=next73 is not None and F(next73['mean_gate'])<=0
result={'scope':'Single N=2 finite-cap optimistic comparison for actual N>=max(2,N_plus); physical N=2 existence not assumed; no author artifact inputs.',
        'N':N,'mstar':str(mstar),'A_total':str(A_total),'initial_mass':str(h),
        'limit':LIMIT,'orders':ORDERS,'factors':factors,'raw':raw,'initial_trim':initial_trim,
        'initial':initial,'stages':records,'final':snapshot(atoms,moments),
        'next73_all_constant_clip_mean_barrier':barrier,
        'exact_checks':len(checks),'checks':checks}
parser=argparse.ArgumentParser()
parser.add_argument('--output', type=Path, required=True)
output=parser.parse_args().output
output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'exact_checks':len(checks),'initial_mass':decimal(h),'initial_cutoff':initial_trim['cutoff'],
                  'stages':[{'p':r['prime'],'positive':r['positive'],'target':decimal(F(r['target'])),
                             'before_mean':decimal(F(r['before']['moments']['1'])/F(r['before']['moments']['0'])),
                             **({'cutoff':r['trim']['cutoff']} if r['positive'] else {})} for r in records],
                  'final_mass':decimal(moments[0]),'mean':decimal(moments[1]/moments[0]),
                  'M2':decimal(moments[2]),'M4':decimal(moments[3]),
                  'next73_all_constant_clip_mean_barrier':barrier,'output':str(output)},indent=2))
