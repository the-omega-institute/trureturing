"""Exact parameter bounds and a complete-period control for Report385 HC1--HC9.

Uses only the Python standard library. These are conditional ordinary arithmetic
checks, not a covering construction or a Lean verification.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from math import prod
from pathlib import Path
import json

def need(ok,msg):
    if not ok:raise ValueError(msg)

def forest(q,R,t):
    need(t*q>R*(q-1),'infeasible forest')
    exposed=R;N=0;layers=[]
    while exposed>t:
        layers.append(t);N+=t;exposed=q*(exposed-t)
    layers.append(exposed);N+=exposed
    if t>=R:closed=R
    else:
        delta=q*t-(q-1)*R;J=0
        while q**J*delta<t:J+=1
        rem=F(q*t-q**J*delta,q-1)
        need(rem.denominator==1 and 1<=rem<=t,'last layer')
        closed=t*J+int(rem)
    need(N==closed and N>=R,'forest count disagreement')
    return N,layers

def best(q,K,p,retained):
    full=q**(K+1)
    R=full-sum(q**(K+1-i) for i in range(1,K+1)) if retained else full
    threshold=F(R*(q-1),q)
    need(threshold.denominator==1,'integral threshold')
    amin=max(1,int(threshold));rows=[]
    for a in range(amin,R):
        N,layers=forest(q,R,a+1)
        rows.append((a+(N-2)//(p-1),a,N,layers))
    winner=min(rows)
    return dict(bound=winner[0],a=winner[1],N=winner[2],layers=winner[3],R=R,a_min=amin,candidate_a_count=len(rows))
ps=(3,5,7,11,13,17,19,23,29,31,43)
rows=[]
for q in (3,5,7):
    for K in ((0,1,2,3) if q==3 else (0,1,2)):
        row={'repair_prime':q,'repair_height':K,'targets':{}}
        for p in ps:
            if p==q:continue
            new=best(q,K,p,True);old=best(q,K,p,False)
            need(new['bound']<=old['bound'],'retained repair worse')
            row['targets'][str(p)]={'retained':new,'without_retained':old,'initial_support_compatible':K>0 or p<q}
        ex=next(iter(row['targets'].values()))['retained'];row.update(R=ex['R'],a_min=ex['a_min'],a_max=ex['R']-1)
        rows.append(row)
# Exact old/new profile comparison only, not an actual covering family.
heights={3:1,5:6,7:1,11:1}
n_lower=1+sum((p-1)*h for p,h in heights.items());n_upper=prod(h+1 for h in heights.values())-1
need(n_lower<=n_upper,'classical count comparison')
need(best(3,1,5,True)['bound']==5 and best(3,1,5,False)['bound']==8,'H5 concrete bound')
# CRT star control from the mixed-response source. Entire period is checked.
aps={3:0,5:0,25:6,125:7,625:8,15:1,75:52,375:253,1875:4};Q=1875
need(all(e in aps for d in aps for e in range(2,d+1) if d%e==0),'divisor closure')
need(all(a%e!=aps[e] for d,a in aps.items() for e in aps if e<d and d%e==0),'comparable disjointness')
private={d:[] for d in aps};holes=[]
for x in range(Q):
    owners=[d for d,a in aps.items() if x%d==a]
    if not owners:holes.append(x)
    if len(owners)==1:private[owners[0]].append(x)
need(all(private.values()),'irredundancy')
star=[]
for digit,label in zip((1,2,3,4),(15,75,375,1875)):
    y=next(x for x in range(Q) if x%625==digit and x%3==1)
    need(y%label==aps[label],'star phase')
    star.append({'digit':digit,'point':y,'label':label})
need(len(holes)>0,'noncover scope')
starout={'Q':Q,'aps':{str(d):a for d,a in aps.items()},'private_counts':{str(d):len(v) for d,v in private.items()},'private_witnesses':{str(d):v[0] for d,v in private.items()},'holes':len(holes),'first_hole':holes[0],'reciprocal_sum':str(sum((F(1,d) for d in aps),F(0))),'source_star':star,'boundary':'An actual divisor-closed comparable-disjoint irredundant noncover; no whole-cover or global-minimality premise.'}
bucket_rows=[{'support_count':s,'bounds':{str(p):2+(5*s-9)//(p-2) for p in (3,5,7,11,13,17,19,23,29,31,37)[:s] if p>3}} for s in (4,5,9,11)]
need(bucket_rows[2]['bounds']['23']==3 and bucket_rows[2]['bounds']['29']==3,'nine-prime bucket consequence')
need(all(bucket_rows[3]['bounds'][str(p)]==3 for p in (29,31,37)),'eleven-prime bucket consequence')
out={'bucket_rows':bucket_rows,'scope':'Exact parameter consequences of existing QC2 and RP2--RP4, conditional on one lexicographically minimum distinct odd whole cover. Ordinary proof/arithmetic, no Lean claim.','rows':rows,'classical_count_profile':{'heights':heights,'n_lower':n_lower,'n_upper':n_upper,'status':'Parameter comparison only; actual cover existence is not asserted.'},'finite_noncover_star':starout}
parser = ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
rendered = json.dumps(out, indent=2)+'\n'
if args.output:
    args.output.write_text(rendered)
else:
    print(rendered, end='')
