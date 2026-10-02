#!/usr/bin/env python3
"""Exact three-kernel source-domain atlas counterexample.

Endpoint coverage is kept separate from continuous source-domain coverage.
No Lean claim or unrestricted covering result is made. Standard library only.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, factorial, isqrt, lcm, prod
from pathlib import Path
import json
from time import perf_counter

CHECKS = 0


def need(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ValueError(message)


def a4(q):
    t = F(1,q-1)
    return 15*t+50*t*t+60*t**3+24*t**4


def hinge_coefficients(primes,h):
    @lru_cache(None)
    def pmf(k,n):
        if k == 0:
            return F(n == 1)
        q=primes[k-1]
        C=F(q-1,q-2)
        def tail(e):
            return F(1) if e == 0 else C/q**e
        return sum(((tail(d-1)-tail(d))*pmf(k-1,n//d)
                    for d in range(1,n+1) if n%d == 0),F(0))
    mean=prod((1+F(1,q-2) for q in primes),start=F(1))
    H0,Hr,Hv=mean-h,mean,3*mean/2
    for n in range(1,h):
        p1=pmf(len(primes),n)
        p2=pmf(len(primes),n//2) if n%2 == 0 else F(0)
        pv=sum((F(2,3**(d-2))*pmf(len(primes),n//d)
                for d in range(3,n+1) if n%d == 0),F(0))
        H0+=(h-n)*p1
        Hr+=(h-n)*(p2-p1)
        Hv+=(h-n)*(pv-p2)
    need(all(x>=0 for x in (H0,Hr,Hv)),'nonnegative complete hinge')
    return H0,Hr,Hv


def exact_tail(tail):
    need((tail['lower'],tail['upper'],tail['ell'],tail['growth'])==(1600,3000,7,21),
         'Report804 full-tail bridge shape')
    delta=F(tail['delta'])
    scale=tail['scale']
    need(delta==F(2,7) and scale==10**30,'Report804 distortion and grid')
    C=F(27,256)/(delta**3*(1-delta))
    need(C==F(64827,10240),'analytic tail constant')
    need(all(F(x)/(1-delta)<=comb(21,i) for i,x in enumerate((15,50,60,24),1)),
         'complete quartic growth comparison')
    series=sum((F(factorial(21),factorial(21-j)*21**j) for j in range(22)),F(0))
    total=C/3*F(99,97)**21*F(3000,2999**4)*series
    ps=[p for p in range(1601,3001) if all(p%d for d in range(2,isqrt(p)+1))]
    need(ps==tail['primes'] and len(ps)==179,'complete prime bridge list')
    for p in reversed(ps):
        raw=C/(p-1)**4+(1+F(7,5)*a4(p))*total
        total=F(-((-raw.numerator*scale)//raw.denominator),scale)
        need(F(0)<=total-raw<F(1,scale),'upward bridge rounding')
    need(total==F(tail['expected_upper'])==F(4301685063112470380207,10**30),
         'Report804 source-independent tail')
    return total


def setup(c):
    primes=tuple(c['primes'])
    leaves=tuple(c['leaves'])
    need(primes==(5,7,11,13,17,19,23) and leaves==(4,7,2,5,8),'fixed source coordinates')
    parts=c['partitions']
    need(parts==[[[0],[1],[2,3,4]]]+[[[0],list(range(1,q))] for q in primes[1:]],
         'literal first-digit partitions')
    patterns=list(product(range(3),*[range(2) for _ in primes[1:]]))
    w=tuple(map(F,c['weights']))
    need(len(w)==5 and min(w)>=0 and sum(w)==1,'one normalized common weight vector')
    U=[[F(0)]*len(patterns) for _ in leaves]
    seen=set()
    for e in c['nonzero_u']:
        l,sid,value=e['leaf_index'],e['pattern_id'],F(e['u'])
        need(type(l)is int and type(sid)is int and 0<=l<5 and 0<=sid<len(patterns),
             'literal retained table index')
        need((l,sid)not in seen and 0<value<=w[l],'unique positive retained coefficient below full weight')
        seen.add((l,sid))
        U[l][sid]=value
    family=c['actual_family']
    need(len({m for m,a in family})==len(family),'globally distinct numerical family')
    need(all(type(m)is int and type(a)is int and m>1 and m%2 and 0<=a<m for m,a in family),
         'literal odd nonunit actual phases')
    actual=dict(family)
    need(actual[3]==0 and actual[9]==1 and actual[45]==11,'actual808 anchors and opposing colour')
    selected=c['selected_labels']
    need(len(selected)==len(set(selected))==23 and set(selected)==set(actual)-{3,9},
         'all23 selected mixed slots once')
    size=1<<len(primes)
    beta=[prod((F(1,q-2) for i,q in enumerate(primes) if D>>i&1),start=F(1))
          for D in range(size)]
    R=[[beta[D] if D and (h or D.bit_count()>1) else F(0)
        for D in range(size)] for h in range(3)]
    forced=set()
    for m in selected:
        a=actual[m]
        h,n=0,m
        while n%3==0:
            h,n=h+1,n//3
        D,leftover=0,n
        fixed={}
        for i,q in enumerate(primes):
            if leftover%q==0:
                D|=1<<i
                fixed[i]=next(j for j,p in enumerate(parts[i]) if a%q in p)
                while leftover%q==0:
                    leftover//=q
        need(leftover==1 and n>1 and h<=2 and (h or D.bit_count()>=2),'selected inventory membership')
        R[h][D]-=prod((F(q-1,q-2) for i,q in enumerate(primes) if D>>i&1),start=F(1))/n
        for l,leaf in enumerate(leaves):
            if leaf%3**h==a%3**h:
                for sid,s in enumerate(patterns):
                    if all(s[i]==colour for i,colour in fixed.items()):
                        forced.add((l,sid))
                        need(U[l][sid]==0,'literal selected K8 nullity')
    need(all(x>=0 for row in R for x in row),'complete nonnegative residual inventories')
    scale=lcm(*(x.denominator for row in U for x in row))
    UI=[[int(x*scale) for x in row] for row in U]
    projections=[]
    for D in range(size):
        inside=tuple(i for i in range(len(primes)) if D>>i&1)
        outside=tuple(i for i in range(len(primes)) if not D>>i&1)
        groupids={}
        ids=[]
        for s in patterns:
            key=tuple(s[i] for i in inside)
            if key not in groupids:
                groupids[key]=len(groupids)
            ids.append(groupids[key])
        projections.append((outside,ids,len(groupids)))
    return primes,leaves,patterns,w,U,UI,scale,beta,R,projections,len(forced)


def evaluate(pi,patterns,UI,scale,beta,R,projections,details=False):
    denoms=[lcm(*(x.denominator for x in row)) for row in pi]
    counts=[[int(x*d) for x in row] for row,d in zip(pi,denoms)]
    raw=[[counts[i][colour] for i,colour in enumerate(s)] for s in patterns]
    envelopes=[]
    for D,(outside,ids,ngroups) in enumerate(projections):
        outden=scale*prod(denoms[i] for i in outside)
        A=[[0]*ngroups for _ in range(5)]
        for sid,p in enumerate(raw):
            fac=prod(p[i] for i in outside)
            if not fac:
                continue
            k=ids[sid]
            for l in range(5):
                A[l][k]+=UI[l][sid]*fac
        f0=max(sum(A[l][k] for l in range(5)) for k in range(ngroups))
        f1=max(max(A[0][k]+A[1][k],A[2][k]+A[3][k]+A[4][k]) for k in range(ngroups))
        f2=max(max(row) for row in A)
        envelopes.append((F(f0,outden),F(f1,outden),F(f2,outden)))
    mass=envelopes[0][0]
    shallow=[sum((R[h][D]*envelopes[D][h] for D in range(len(beta))),F(0)) for h in range(3)]
    high=sum((beta[D]*envelopes[D][2]/2 for D in range(len(beta))),F(0))
    alpha=mass-sum(shallow,F(0))-high
    result=dict(mass=str(mass),shallow_losses=list(map(str,shallow)),high_loss=str(high),
                alpha=str(alpha),alpha_decimal=float(alpha))
    if details:
        result['envelopes']=[[str(x) for x in row] for row in envelopes]
    return alpha,result


def unique_object(pairs):
    out={}
    for key,value in pairs:
        if key in out:raise ValueError('duplicate JSON key: '+key)
        out[key]=value
    return out


def read_json(path):
    return json.loads(path.read_text(),object_pairs_hook=unique_object)


VERTICES5=((F(0),F(1,5),F(4,5)),(F(0),F(4,15),F(11,15)),
           (F(1,5),F(0),F(4,5)),(F(4,15),F(0),F(11,15)),
           (F(4,15),F(4,15),F(7,15)))


def vertex_probability(vi,mask,primes):
    return [VERTICES5[vi]]+[(F(q-1,q*(q-2)),1-F(q-1,q*(q-2)))if mask>>(i-1)&1 else(F(0),F(1))
                            for i,q in enumerate(primes[1:],1)]


def local_vertex_check(primes,parts):
    menus=[]
    for q,partition in zip(primes,parts):
        cap=[min(F(1),F(len(part)*(q-1),q*(q-2)))for part in partition]
        menu=set()
        for free in range(len(partition)):
            fixed=[i for i in range(len(partition))if i!=free]
            for bits in product((0,1),repeat=len(fixed)):
                p=[F(0)]*len(partition)
                for i,b in zip(fixed,bits):p[i]=b*cap[i]
                p[free]=1-sum(p)
                if 0<=p[free]<=cap[free]:menu.add(tuple(p))
        menus.append(menu)
    need(menus[0]==set(VERTICES5),'complete local5 cap polygon vertices')
    for q,menu in zip(primes[1:],menus[1:]):
        upper=F(q-1,q*(q-2))
        need(menu=={(F(0),F(1)),(upper,1-upper)},'complete binary cap segment vertices')
    need(prod(map(len,menus))==320,'complete320 product endpoints')


def main():
    parser=argparse.ArgumentParser()
    here=Path(__file__).resolve().parent
    parser.add_argument('--certificate',type=Path,default=here/'three_kernel_atlas_counterexample_certificate.json')
    parser.add_argument('--result',type=Path,default=here/'three_kernel_atlas_counterexample.json')
    parser.add_argument('--write-result',action='store_true')
    args=parser.parse_args()
    started=perf_counter()
    c=read_json(args.certificate)
    need(c['schema']=='e7-three-kernel-atlas-counterexample-v1','certificate schema')
    need(c['normalization']=='mu=lambda_w restricted to U / lambda_w(U)',
         'full-source normalization, same comparison as813')
    common=c['common'];primes=tuple(common['primes'])
    need(common['threshold']==16,'fixed h16 query gate')
    need(common['pattern_encoding']=='lex product: q5 colour0=0,1=1,2=other; otherq colour0=0,1=other',
         'literal categorical pattern encoding')
    local_vertex_check(primes,common['partitions'])
    H0,Hr,Hv=hinge_coefficients(primes,16)
    Kq=prod((1+F(q-1,q-2)*a4(q)for q in primes),start=F(1))*(1+F(28,27)*a4(29))
    T=exact_tail(common['tail'])
    for key,value in dict(H0=H0,Hr=Hr,Hv=Hv,Kq=Kq,T1600=T).items():
        need(F(common['expected_hinge'][key])==value,'complete inherited '+key)
    p5=tuple(map(F,c['interior_probability5']))
    fraction=F(c['interior_other_upper_fraction'])
    need(p5==(F(1,4),F(1,8),F(5,8))and fraction==F(99,100),'literal strict-interior counterexample')
    interior=[p5]+[(fraction*F(q-1,q*(q-2)),1-fraction*F(q-1,q*(q-2)))for q in primes[1:]]
    for q,pi,partition in zip(primes,interior,common['partitions']):
        caps=[min(F(1),F(len(part)*(q-1),q*(q-2)))for part in partition]
        need(sum(pi)==1 and all(0<x<cap for x,cap in zip(pi,caps)),
             'strict interior of every local capped simplex')
    need([k['name']for k in c['kernels']]==['point812','quarter','third'],'three fixed named tables')
    need(c['third_point']==[3,63],'literal third-candidate point')
    all_endpoint_gates=[];tables=[];gaps=[];third_point=None
    for ki,kernel in enumerate(c['kernels']):
        source=dict(common,weights=kernel['weights'],nonzero_u=kernel['nonzero_u'])
        geometry=setup(source)
        _,leaves,patterns,w,U,UI,scale,beta,R,projections,nforced=geometry
        r=max(sum(w[:2]),sum(w[2:]));v=max(w)
        charge=H0+Hr*r+Hv*v+27*Kq*(1+15*r+216*v)*T
        rows=[];faces=[]
        for vi in range(5):
            group=[]
            for mask in range(64):
                pi=vertex_probability(vi,mask,primes)
                alpha,_=evaluate(pi,patterns,UI,scale,beta,R,projections)
                gate=12*alpha-charge
                row=dict(vertex5=vi,binary_upper_mask=mask,alpha=str(alpha),gate=str(gate))
                rows.append(row);group.append(row)
                if ki==2 and(vi,mask)==(3,63):
                    reserve=gate/(27*alpha)
                    need(alpha==F(c['expected_third_alpha']),'exact third point source mass lower bound')
                    need(gate>F(c['third_gate_floor'])==F(3,20),'third point gate above0.15')
                    need(reserve>F(c['third_reserve_floor'])==F(13,100),'third point distorted reserve above0.13')
                    third_point=dict(**row,gate_decimal=float(gate),alpha_decimal=float(alpha),
                                     reserve=str(reserve),reserve_decimal=float(reserve))
            worst=min(group,key=lambda row:F(row['gate']))
            faces.append(dict(vertex5=vi,positive=sum(F(row['gate'])>0 for row in group),
                              worst=worst,minimum_gate_decimal=float(F(worst['gate']))))
        positives=sum(F(row['gate'])>0 for row in rows)
        need(positives==c['expected_endpoint_positive_counts'][ki],'exact per-table endpoint count')
        if ki==1:
            need(min(F(face['worst']['gate'])for face in faces[:3])>F(1,5),
                 'quarter table positive on conv(v0,v1,v2) times full six-interval box')
        all_endpoint_gates.append([F(row['gate'])for row in rows])
        alpha,_=evaluate(interior,patterns,UI,scale,beta,R,projections)
        gate=12*alpha-charge
        upper=F(c['interior_gate_upper_bounds'][ki])
        need(gate<upper<0,'strict negative interior gate for fixed table')
        gaps.append(dict(table=kernel['name'],alpha=str(alpha),gate=str(gate),gate_decimal=float(gate),strict_upper=str(upper)))
        tables.append(dict(name=kernel['name'],weights=list(map(str,w)),r=str(r),v=str(v),
                           allowed_entries=960-nforced,nonzero_entries=len(kernel['nonzero_u']),
                           full_entries=sum(x==w[l]for l,row in enumerate(U)for x in row),
                           partial_entries=sum(0<x<w[l]for l,row in enumerate(U)for x in row),
                           positive_endpoints=positives,faces=faces))
    union=sum(any(table[i]>0 for table in all_endpoint_gates)for i in range(320))
    missing_first_two=[(i//64,i%64)for i in range(320)if not any(table[i]>0 for table in all_endpoint_gates[:2])]
    need(union==c['expected_endpoint_union']==320,'all endpoints have at least one positive table')
    need(missing_first_two==[(3,63)],'third table repairs the unique missing endpoint')
    result=dict(schema='e7-three-kernel-atlas-counterexample-result-v1',tables=tables,
                third_point=third_point,endpoint_union=union,first_two_missing=[list(key)for key in missing_first_two],
                interior_probabilities=[[str(x)for x in pi]for pi in interior],interior_failures=gaps,
                T1600=str(T),Kq=str(Kq),H0=str(H0),Hr=str(Hr),Hv=str(Hv),checks=CHECKS,
                conclusion='These three fixed tables cover every product endpoint but fail at one strict interior point; therefore they do not form a continuous source-domain atlas under the specified full-source h16 gate.',
                scope='ordinary exact counterexample to endpoint-union sufficiency; no pointwise optimal-LP impossibility, no actual covering and no retained-source-moment claim')
    if args.write_result:args.result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(read_json(args.result)==result,'retained exact result replay')
    print(json.dumps(dict(endpoint_positive_counts=[x['positive_endpoints']for x in tables],
                          endpoint_union=union,third_gate=third_point['gate_decimal'],
                          interior_gates=[x['gate_decimal']for x in gaps],checks=CHECKS,
                          elapsed_seconds=perf_counter()-started),indent=2))


if __name__=='__main__':main()
