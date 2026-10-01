#!/usr/bin/env python3
"""Independent recursive Fibonacci reserve certificate; exact interval decisions."""
import sys
sys.dont_write_bytecode = True

import argparse
from bisect import bisect_left,bisect_right
import gzip
import hashlib
import importlib.util
import json
from math import isqrt
from pathlib import Path

ENGINE = Path(__file__).resolve().with_name('price_band.py')
spec = importlib.util.spec_from_file_location('integer_interval_engine',ENGINE)
e = importlib.util.module_from_spec(spec)
spec.loader.exec_module(e)
I,SCALE,ZERO,ONE = e.I,e.SCALE,e.ZERO,e.ONE
lograt,logiv = e.lograt,e.logiv
LOW,HIGH = 144,121393
GAMMA_M = 1000000
TARGET_NUM,TARGET_DEN = 9,100000000


def gamma_interval(m):
    h = I(sum(SCALE//j for j in range(1,m+1)),sum(e.ceildiv(SCALE,j) for j in range(1,m+1)))
    base = h-lograt(m)
    return I((base-I.rat(1,2*m)).lo,(base-I.rat(1,2*(m+1))).hi)


def prefix(values):
    ans = [ZERO]
    for v in values:
        ans.append(ans[-1]+v)
    return ans


def count_initial(items,predicate):
    lo,hi = 0,len(items)
    while lo<hi:
        mid = (lo+hi)//2
        if predicate(items[mid]):
            lo=mid+1
        else:
            hi=mid
    return lo


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    out=args.out
    out.mkdir(parents=True,exist_ok=True)
    gamma=gamma_interval(GAMMA_M)
    primes=e.prime_sieve(HIGH+1)
    logs=[];d1=[];c2=[];threshold=[];events=[]
    for p in primes:
        lp=lograt(p)
        logs.append(lp)
        d1.append(I.rat(1,p)-lograt(p+1,p))
        c2.append(I.rat(1,p)-lograt(p*p+p+1,p*p))
        threshold.append(lograt(p*p+p+1,p*p+p)/lp)
        power,k=p,1
        while power<=HIGH:
            events.append((power,p,k))
            power*=p;k+=1
    assert all(a.lo>b.hi for a,b in zip(threshold,threshold[1:])), 'second-layer thresholds not separated'
    events.sort()
    assert len(set(q for q,p,k in events))==len(events)
    event_values=[q for q,p,k in events]
    log_by_prime=dict(zip(primes,logs))
    psi_prefix=prefix([log_by_prime[p] for q,p,k in events])
    P_prefix=prefix([I.rat(1,k*q) for q,p,k in events])
    log_prefix,d1_prefix,c2_prefix=map(prefix,[logs,d1,c2])

    def b2(a,b,price):
        left=bisect_right(primes,isqrt(b))
        right=bisect_right(primes,a-1)
        if right<=left:
            return ZERO,{'eligible':[left,left],'d2':[left,left],'ambiguous':[left,left]}
        first_uncertain=count_initial(threshold,lambda t:t.lo>price.hi)
        first_d1=count_initial(threshold,lambda t:t.hi>=price.lo)
        assert first_uncertain<=first_d1
        split1=max(left,min(right,first_uncertain))
        split2=max(left,min(right,first_d1))
        ans=(c2_prefix[split1]-c2_prefix[left])+price*(log_prefix[split1]-log_prefix[left])
        ans=ans+(d1_prefix[right]-d1_prefix[split2])
        for j in range(split1,split2):
            other=c2[j]+price*logs[j]
            ans=ans+I(min(d1[j].lo,other.lo),min(d1[j].hi,other.hi))
        return ans,{'eligible':[left,right],'d2':[left,split1],'ambiguous':[split1,split2]}

    fib=[0,1]
    for k in range(2,27):
        fib.append(fib[-1]+fib[-2])
    roots=[(fib[j],fib[j+1],j-1) for j in range(12,26)]
    assert roots[0][0]==LOW and roots[-1][1]==HIGH
    assert all(a[1]==b[0] for a,b in zip(roots,roots[1:]))
    nodes=[];leaves=[];failures=[]

    def visit(a,b,m,depth,parent):
        assert b-a==fib[m] and a>=4
        index=len(nodes)
        psi_index=bisect_right(event_values,a)
        P_index=bisect_left(event_values,b)
        psi=psi_prefix[psi_index]
        pp=P_prefix[P_index]
        price=ONE/(lograt(b)*b)
        reserve,partition=b2(a,b,price)
        bound=gamma+logiv(logiv(psi))-pp+reserve
        row={'index':index,'a':a,'b':b,'fibonacci_length_index':m,
             'depth':depth,'parent':parent,'psi_event_index':psi_index,
             'P_leftlimit_event_index':P_index,'psi':psi.wire(),'P_leftlimit':pp.wire(),
             'price_at_b':price.wire(),'B2':reserve.wire(),
             'prime_partition':partition,'Gamma':bound.wire()}
        nodes.append(row)
        if bound.lo*TARGET_DEN>TARGET_NUM*SCALE:
            row['status']='leaf'
            leaves.append(index)
        elif m>2:
            row['status']='split'
            c=a+fib[m-1]
            left_index=visit(a,c,m-1,depth+1,index)
            right_index=visit(c,b,m-2,depth+1,index)
            row['children']=[left_index,right_index]
        else:
            row['status']='failed-unit-cell'
            failures.append(row)
        return index

    root_indices=[visit(a,b,m,0,None) for a,b,m in roots]
    ordered=[nodes[i] for i in leaves]
    assert not failures, ('unit cells failed',failures)
    assert ordered[0]['a']==LOW and ordered[-1]['b']==HIGH
    assert all(a['b']==b['a'] for a,b in zip(ordered,ordered[1:])), 'leaf coverage gap or overlap'
    assert len(nodes)==2*len(leaves)-len(roots)
    min_leaf=min(ordered,key=lambda row:int(row['Gamma'][0]))

    # Predetermined exact direct-sum audit against the prefix partition.
    audited=0
    for idx in sorted(set([0,len(nodes)-1]+list(range(0,len(nodes),251)))):
        row=nodes[idx]
        price=I(*map(int,row['price_at_b']))
        direct=ZERO
        for j,p in enumerate(primes):
            if p*p>row['b'] and p<=row['a']-1:
                d2=c2[j]+price*logs[j]
                direct=direct+I(min(d1[j].lo,d2.lo),min(d1[j].hi,d2.hi))
        got=I(*map(int,row['B2']))
        assert not(got.hi<direct.lo or direct.hi<got.lo), 'prefix/direct reserve intervals disjoint'
        audited+=1

    # Actual marginal optimum at the fixed diagnostic x=100000.
    x=100000
    price=ONE/(lograt(x)*x)
    contributions=[]
    R=ZERO
    RK={k:ZERO for k in [2,3,4]}
    old=ZERO
    for j,p in enumerate(primes):
        if p>x:
            break
        lp=logs[j]
        cost=price*lp
        v=0;power=p;qv=ZERO
        while power<=x:
            v+=1
            qv=qv+I.rat(1,v*power)
            power*=p
        a=0;power=1;psum=0;active=[]
        while True:
            power*=p;psum+=power
            gain=lograt(psum+1,psum)
            if gain.lo>cost.hi:
                a+=1;active.append(gain.wire())
            elif gain.hi<cost.lo:
                inactive=gain
                break
            else:
                raise AssertionError(('ambiguous marginal sign',p,a+1,gain.wire(),cost.wire()))
        # Sum 1+p+...+p^a divided by p^a is G_p(a).
        gp_num=(p**(a+1)-1)//(p-1)
        loggp=lograt(gp_num,p**a)
        rp=qv-cost*v-loggp+cost*a
        R=R+rp
        for K in RK:
            if p**K>x:
                RK[K]=RK[K]+rp
        if p*p>=2*x and p<=x-1:
            old=old+d1[j]
        if p*p>x:
            assert a in [1,2],('R2 optimizer outside two candidates',p,a)
        contributions.append({'p':p,'v':v,'a':a,'Q':qv.wire(),'cost':cost.wire(),
                              'active_marginals':active,'first_inactive_marginal':inactive.wire(),
                              'log_G':loggp.wire(),'R_p':rp.wire()})
    B2,part=b2(x,x,price)
    assert not(B2.hi<RK[2].lo or RK[2].hi<B2.lo)
    diag={'x':x,'price':price.wire(),'B_old':old.wire(),'B2':B2.wire(),
          'R2':RK[2].wire(),'R3':RK[3].wire(),'R4':RK[4].wire(),'R':R.wire(),
          'B2_partition':part,'contributions':contributions}
    cert={'schema':'recursive-fibonacci-reserve-v1','scale':str(SCALE),'atanh_terms':e.TERMS,
          'range':[LOW,HIGH],'gamma_m':GAMMA_M,'gamma':gamma.wire(),
          'target':[TARGET_NUM,TARGET_DEN],'fibonacci':fib,'roots':root_indices,
          'primes':[[p,logs[j].wire(),d1[j].wire(),c2[j].wire(),threshold[j].wire()] for j,p in enumerate(primes)],
          'events':[list(x) for x in events],'nodes':nodes,'leaves':leaves,
          'failures':failures,'diagnostic':diag}
    data=json.dumps(cert,separators=(',',':')).encode()
    path=out/'certificate.json.gz'
    path.write_bytes(gzip.compress(data,mtime=0))
    decimals={'B_old':old.decimal(),'B2':B2.decimal(),'R2':RK[2].decimal(),
              'R3':RK[3].decimal(),'R4':RK[4].decimal(),'R':R.decimal()}
    result={'status':'PASS','range':[LOW,HIGH],'prime_count':len(primes),'prime_power_event_count':len(events),
            'root_count':len(roots),'bound_evaluations':len(nodes),'leaf_count':len(leaves),
            'maximum_depth_root_zero':max(r['depth'] for r in nodes),
            'minimum_leaf_interval':[min_leaf['a'],min_leaf['b']],
            'minimum_leaf_Gamma_wire':min_leaf['Gamma'],
            'minimum_leaf_Gamma_decimal':I(*map(int,min_leaf['Gamma'])).decimal(),
            'gamma_interval':gamma.decimal(),'direct_prefix_audit_nodes':audited,
            'diagnostic_x':x,'diagnostic_intervals':decimals,
            'certificate_path':path.name,'certificate_sha256':hashlib.sha256(data).hexdigest(),
            'script':Path(__file__).name,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'engine':ENGINE.name,'engine_sha256':hashlib.sha256(ENGINE.read_bytes()).hexdigest(),
            'limitations':['Integer-interval arithmetic certificate, not Lean verification.',
                           'Analytic reserve and continuity bridges require the separate mathematical argument.',
                           'Only the finite range and x=100000 diagnostic are checked.']}
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
