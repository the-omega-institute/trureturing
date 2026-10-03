#!/usr/bin/env python3
"""Exact uniform retained-head and fixed-h16 dual certificates for actual808.

Standard library only; no LP solver, external files or floating proof steps.
No Lean claim or unrestricted covering result is made.
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


def unique_object(pairs):
    out={}
    for key,value in pairs:
        if key in out:raise ValueError('duplicate JSON key: '+key)
        out[key]=value
    return out


def read_json(path):
    return json.loads(path.read_text(),object_pairs_hook=unique_object)


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


VERTICES5=((F(0),F(1,5),F(4,5)),(F(0),F(4,15),F(11,15)),
           (F(1,5),F(0),F(4,5)),(F(4,15),F(0),F(11,15)),
           (F(4,15),F(4,15),F(7,15)))


def vertex_probability(key,primes):
    need(len(key)==2 and all(type(x)is int for x in key) and 0<=key[0]<5 and 0<=key[1]<64,
         'literal categorical product vertex key')
    vi,mask=key
    return [VERTICES5[vi]]+[(F(q-1,q*(q-2)),1-F(q-1,q*(q-2)))if mask>>(i-1)&1 else(F(0),F(1))
                            for i,q in enumerate(primes[1:],1)]


def vertex_completeness(primes,partitions):
    # A vertex of a box intersected with one sum hyperplane has at most one
    # coordinate not at a box endpoint. Enumerate that finite local menu.
    menus=[]
    for q,parts in zip(primes,partitions):
        caps=[min(F(1),F(len(part)*(q-1),q*(q-2)))for part in parts]
        local=set()
        for free in range(len(parts)):
            fixed=[i for i in range(len(parts))if i!=free]
            for choices in product((0,1),repeat=len(fixed)):
                p=[F(0)]*len(parts)
                for i,b in zip(fixed,choices):p[i]=caps[i]*b
                p[free]=1-sum(p)
                if 0<=p[free]<=caps[free]:local.add(tuple(p))
        menus.append(local)
    need(menus[0]==set(VERTICES5),'all five local5 capped-simplex vertices')
    for q,menu in zip(primes[1:],menus[1:]):
        upper=F(q-1,q*(q-2))
        need(menu=={(F(0),F(1)),(upper,1-upper)},'complete binary capped-simplex vertices')
    need(prod(map(len,menus))==320,'complete320 product vertex menu')


def dual_layout(c,geometry):
    primes,leaves,patterns,_,_,_,_,beta,R,_,_=geometry
    forced=set()
    family=dict(c['actual_family'])
    for m in c['selected_labels']:
        a=family[m]
        h,n=0,m
        while n%3==0:h,n=h+1,n//3
        fixed={}
        for i,q in enumerate(primes):
            if n%q==0:
                fixed[i]=next(j for j,part in enumerate(c['partitions'][i])if a%q in part)
        for l,leaf in enumerate(leaves):
            if leaf%3**h==a%3**h:
                for sid,s in enumerate(patterns):
                    if all(s[i]==colour for i,colour in fixed.items()):forced.add((l,sid))
    names=[('w',l)for l in range(5)]+[('r',),('v',),('alpha',)]
    uid={}
    for l in range(5):
        for sid in range(len(patterns)):
            if(l,sid)not in forced:
                uid[l,sid]=len(names)
                names.append(('u',l,sid))
    loss={(D,h):R[h][D]+(beta[D]/2 if h==2 else 0)for D in range(128)for h in range(3)}
    loss={key:value for key,value in loss.items()if value>0}
    keys=c['dual']['vertex_keys']
    need(len(keys)==len({tuple(key)for key in keys})>0,'distinct selected dual vertices')
    probs=[vertex_probability(key,primes)for key in keys]
    zid={}
    for vi in range(len(keys)):
        for D,h in loss:
            zid[vi,D,h]=len(names)
            names.append(('z',vi,D,h))
    return names,uid,zid,loss,probs


def check_dual(c,geometry,H0,Hr,Hv,Kq,T):
    started=perf_counter()
    primes,leaves,patterns,_,_,_,_,_,_,_,_=geometry
    names,uid,zid,loss,probs=dual_layout(c,geometry)
    nvars=len(names)
    dual=c['dual']
    need(dual['threshold']==16 and F(dual['variable_upper_bound'])==1,
         'dual fixedh16 and universal variable box')
    aggregate=[F(0)]*nvars
    multipliers=[]
    def constraint(label):
        tag=label[0]
        if tag=='retained_cap':
            need(len(label)==3 and tuple(label[1:])in uid,'valid retained cap row')
            l,sid=label[1:]
            return[(uid[l,sid],F(1)),(l,F(-1))]
        if tag=='root_cap':
            root=tuple(label[1:])
            need(root in((0,1),(2,3,4)),'valid root cap row')
            return[(l,F(1))for l in root]+[(5,F(-1))]
        if tag=='leaf_cap':
            need(len(label)==2 and type(label[1])is int and 0<=label[1]<5,'valid leaf cap row')
            return[(label[1],F(1)),(6,F(-1))]
        if tag=='v_le_r':
            need(len(label)==1,'valid v<=r row')
            return[(6,F(1)),(5,F(-1))]
        if tag=='head':
            need(len(label)==2 and type(label[1])is int and 0<=label[1]<len(probs),
                 'valid common-head constraint')
            vi=label[1]
            pi=probs[vi]
            mass=[prod((pi[i][s[i]]for i in range(7)),start=F(1))for s in patterns]
            return[(7,F(1))]+[(zid[vi,D,h],value)for(D,h),value in loss.items()]+[
                    (idx,-mass[sid])for(l,sid),idx in uid.items()]
        need(tag=='epigraph'and len(label)==6,'valid epigraph row tag')
        _,vi,D,h,kappa,ls=label
        need(type(vi)is int and type(D)is int and type(h)is int and(vi,D,h)in zid,
             'valid epigraph vertex/support/type')
        inside=[i for i in range(7)if D>>i&1]
        outside=[i for i in range(7)if not D>>i&1]
        leafsets=(tuple(range(5)),)if h==0 else(((0,1),(2,3,4))if h==1 else tuple((l,)for l in range(5)))
        need(tuple(ls)in leafsets,'one permitted shared leaf/root query')
        need(len(kappa)==len(inside)and all(type(col)is int and 0<=col<len(c['partitions'][i])for i,col in zip(inside,kappa)),
             'one common literal query colour tuple')
        pi=probs[vi]
        terms=[(zid[vi,D,h],F(-1))]
        for sid,s in enumerate(patterns):
            if all(s[i]==col for i,col in zip(inside,kappa)):
                prob=prod((pi[i][s[i]]for i in outside),start=F(1))
                if prob:
                    terms.extend((uid[l,sid],prob)for l in ls if(l,sid)in uid)
        return terms
    for entry in dual['inequalities']:
        y=F(entry['multiplier'])
        need(y>=0,'nonnegative inequality dual multiplier')
        multipliers.append(y)
        for idx,coefficient in constraint(entry['row']):
            aggregate[idx]+=y*coefficient
    mu=F(dual['equality_multiplier'])
    for l in range(5):aggregate[l]+=mu
    objective=[F(0)]*nvars
    objective[7]=F(12)
    objective[5]=-Hr-405*Kq*T
    objective[6]=-Hv-5832*Kq*T
    residual=[d-a for d,a in zip(objective,aggregate)]
    correction=sum((max(x,F(0))for x in residual),F(0))
    constant=-H0-27*Kq*T
    # Every row above has RHS0, and the one equality is sumw=1.
    upper=constant+mu+correction
    need(upper<F(-1,25),'exact fixedh16 upper bound below-1/25')
    return dict(vertices=dual['vertex_keys'],variables=nvars,nonzero_multipliers=sum(x>0 for x in multipliers),
                equality_multiplier=str(mu),objective_constant=str(constant),
                positive_residual_count=sum(x>0 for x in residual),
                positive_residual_sum=str(correction),positive_residual_sum_decimal=float(correction),
                upper_bound=str(upper),upper_bound_decimal=float(upper),
                strict_upper_bound='-1/25',
                scope='every shared retained-kernel/weight certificate on these three probability vertices, fixedh16 and full inheritedT1600 comparator')


def all_threshold_bounds(primes,Kq,T,dual_upper):
    # The same variables obey r>=1/2 and v>=1/5 from sumw=1,
    # together with 0<=v<=r<=1. Linear corrections attain their maximum
    # at these four corners of that enclosing polygon.
    coarse=F(-1,25)
    need(dual_upper<coarse,'certified common h16 upper below coarse bound')
    corners=((F(1,2),F(1,5)),(F(1,2),F(1,2)),(F(1),F(1)),(F(1),F(1,5)))
    penalty=27*Kq*T
    def coeff(h):
        a,b,d=hinge_coefficients(primes,h)
        return(-a-penalty,-b-15*penalty,-d-216*penalty)
    c16=coeff(16)
    rows=[]
    for h in range(28):
        ch=coeff(h)
        s=F(28-h,12)
        delta=tuple(a-s*b for a,b in zip(ch,c16))
        candidates=[s*coarse+delta[0]+delta[1]*r+delta[2]*v for r,v in corners]
        upper=max(candidates)
        need(upper<0,'negative scaled dual for integer threshold'+str(h))
        rows.append(dict(h=h,scale=str(s),upper_bound=str(upper),upper_bound_decimal=float(upper),
                         maximizing_corner=candidates.index(upper)))
    need(max(F(row['upper_bound'])for row in rows)==coarse,'all integer thresholds bounded above by-1/25')
    return dict(integer_thresholds=rows,integer_maximum=str(coarse),
                real_extension='between integer knots the integer-valued-run hinge and gate are affine; at28 gate is strictlynegative',
                negative_thresholds='G_h=G_0+h*(1-alpha)<=G_0 for h<0 and alpha<=1',
                thresholds_at_least28='(28-h)*alpha<=0, hinge>=0, full moment-tail penalty>0',
                scope='all real thresholds for the same shared-kernel/global-alpha certificate and inherited full-source query/moment comparison')


def main():
    parser=argparse.ArgumentParser()
    here=Path(__file__).resolve().parent
    parser.add_argument('--certificate',type=Path,default=here/'retained_kernel_uniform_head_certificate.json')
    parser.add_argument('--result',type=Path,default=here/'retained_kernel_uniform_head.json')
    parser.add_argument('--write-result',action='store_true')
    args=parser.parse_args()
    started=perf_counter()
    c=read_json(args.certificate)
    need(c['schema']=='e7-uniform-retained-head-and-fixed-gate-dual-v1','certificate schema')
    need(c['normalization']=='mu=lambda_w restricted to U / lambda_w(U)',
         'one full-source survivor normalization')
    need(c['pattern_encoding']=='lex product: q5 colour0=0,1=1,2=other; otherq colour0=0,1=other',
         'literal retained pattern encoding')
    geometry=setup(c)
    primes,leaves,patterns,w,U,UI,scale,beta,R,projections,nforced=geometry
    vertex_completeness(primes,c['partitions'])
    need(c['threshold']==16,'fixed continuation threshold')
    H0,Hr,Hv=hinge_coefficients(primes,16)
    Kq=prod((1+F(q-1,q-2)*a4(q)for q in primes),start=F(1))*(1+F(28,27)*a4(29))
    T=exact_tail(c['tail'])
    for name,value in dict(H0=H0,Hr=Hr,Hv=Hv,Kq=Kq,T1600=T).items():
        need(F(c['expected_hinge'][name])==value,'exact inherited '+name)
    r=max(sum(w[:2]),sum(w[2:]))
    v=max(w)
    charge=H0+Hr*r+Hv*v+27*Kq*(1+15*r+216*v)*T
    rows=[]
    worst=None
    for vi in range(5):
        for mask in range(64):
            pi=vertex_probability((vi,mask),primes)
            alpha,_=evaluate(pi,patterns,UI,scale,beta,R,projections)
            row=dict(vertex5=vi,binary_upper_mask=mask,alpha=str(alpha),gate=str(12*alpha-charge))
            rows.append(row)
            if worst is None or alpha<F(worst['alpha']):worst=row
    alpha=F(worst['alpha'])
    need(len(rows)==320 and alpha==F(c['expected_uniform_alpha'])and alpha>F(249,10000),
         'complete uniform head lower bound above0.0249')
    need([worst['vertex5'],worst['binary_upper_mask']]==c['expected_uniform_worst'],
         'literal worst product vertex')
    dual=check_dual(c,geometry,H0,Hr,Hv,Kq,T)
    thresholds=all_threshold_bounds(primes,Kq,T,F(dual['upper_bound']))
    result=dict(schema='e7-uniform-retained-head-and-fixed-gate-dual-result-v1',
                weights=list(map(str,w)),r=str(r),v=str(v),H0=str(H0),Hr=str(Hr),Hv=str(Hv),
                Kq=str(Kq),T1600=str(T),
                full_u_entries=960,forced_zero_entries=nforced,
                nonzero_entries=len(c['nonzero_u']),
                full_weight_entries=sum(x==w[l]for l,row in enumerate(U)for x in row),
                partial_entries=sum(0<x<w[l]for l,row in enumerate(U)for x in row),
                uniform_head=dict(vertices=320,worst=worst,alpha=str(alpha),alpha_decimal=float(alpha),
                                  guaranteed_floor='249/10000',rows=rows),
                fixed_h16_dual=dual,all_threshold_obstruction=thresholds,
                checks=CHECKS,
                evidence='ordinary exact rational verification; no solver or Lean assertion',scope=c['scope'])
    if args.write_result:
        args.result.write_text(json.dumps(result,indent=2)+'\n')
    else:
        need(read_json(args.result)==result,'retained result exact replay')
    print(json.dumps(dict(alpha=str(alpha),alpha_decimal=float(alpha),dual_upper=dual['upper_bound'],
                          dual_upper_decimal=dual['upper_bound_decimal'],checks=CHECKS,
                          elapsed_seconds=perf_counter()-started),indent=2))


if __name__=='__main__':main()
