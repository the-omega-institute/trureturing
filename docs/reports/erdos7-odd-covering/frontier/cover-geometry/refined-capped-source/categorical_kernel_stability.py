#!/usr/bin/env python3
"""Exact retained-kernel point certificate and finite-pure-source TV transport.

One common weight/table has a positive cap-point gate, fails the full 320
vertices, and succeeds for the specified finite pure families at depths >=3.
No optimization, Lean claim or unrestricted covering result. Standard library.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, factorial, isqrt, lcm, prod
from pathlib import Path
import json

CHECKS = 0


def unique_object(pairs):
    out={}
    for key,value in pairs:
        if key in out:raise ValueError('duplicate JSON key: '+key)
        out[key]=value
    return out


def read_json(path):
    return json.loads(path.read_text(),object_pairs_hook=unique_object)


def keys(value,expected,label):
    need(type(value)is dict and set(value)==set(expected),label)


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
    keys(c,('schema','primes','leaves','actual_family','selected_labels','partitions','probabilities','pattern_encoding','weights','nonzero_u','threshold','tail','expected_hinge','normalization','expected_vertices','expected_stability'),'certificate complete shape')
    need(c['schema']=='e7-categorical-kernel-stability-v1','certificate schema')
    need(c['normalization']=='mu=lambda_w restricted to U / lambda_w(U)','one full-source survivor normalization')
    need(c['pattern_encoding']=='lex product: q5 colour0=0,1=1,2=other; otherq colour0=0,1=other','literal retained pattern encoding')
    keys(c['tail'],('lower','upper','ell','growth','delta','scale','expected_upper','primes'),'complete tail certificate shape')
    keys(c['expected_hinge'],('H0','Hr','Hv','Kq','T1600'),'hinge certificate shape')
    keys(c['expected_vertices'],('count','all_positive','worst_vertex5','worst_binary_upper_mask','worst_alpha'),'vertex countercontrol shape')
    keys(c['expected_stability'],('depth_lower','coordinate_lipschitz','tv_deltas_at_depth3','probabilities_at_depth3','source_debit_upper','alpha_floor','epsilon_floor','distorted_mass_floor','strict_floor'),'stability certificate shape')
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
        keys(e,('leaf_index','pattern_id','u'),'retained entry complete shape')
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
    need(set(selected)=={15,21,45,33,35,39,63,51,57,55,105,75,69,65,99,77,85,117,95,165,91,147,225},'fixed23 numerical slot contract')
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
    need(all(sum(row)==1 and all(x>=0 for x in row) for row in pi),'valid categorical source block')
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


def stability(c,primes,w,patterns,UI,scale,beta,R,projections,alpha,H,K,T):
    proposed=c['expected_stability']
    need(type(proposed['depth_lower'])is int and proposed['depth_lower']==3,'finite pure depth lower bound')
    need(proposed['strict_floor']=='13/1000','claimed strict finite-source reserve floor')
    r=max(sum(w[:2]),sum(w[2:]));v=max(w)
    ell=[];deltas=[];pis=[];pure=[]
    for i,q in enumerate(primes):
        coefficient=1+sum((R[0][D]+r*R[1][D]+v*(R[2][D]+beta[D]/2)
                          for D in range(len(beta)) if not D>>i&1),F(0))
        need(coefficient>=1,'nonnegative complete TV coefficient')
        ell.append(coefficient)
        classes=[(q,2 if q==5 else 1)]+[(q**j,(3 if q==5 else 2)+q**(j-1)) for j in (2,3)]
        for k,(m,a) in enumerate(classes):
            need(a%q!=0 and (q!=5 or a%q!=1),'pure inventory preserves its referenced colours')
            for n,b in classes[:k]:need(a%n!=b,'pure prefix cylinders pairwise disjoint')
        survivor=1-sum((F(1,m) for m,a in classes),F(0))
        a=F(1,q)/survivor;cap=F(q-1,q*(q-2))
        need(a==F(q-1,q*(q-2+F(1,q**3))) and 0<a<cap,'actual finite pure normalization')
        law=(a,a,1-2*a) if q==5 else (a,1-a)
        star=tuple(map(F,c['probabilities'][i]))
        delta=sum((abs(x-y) for x,y in zip(law,star)),F(0))/2
        need(delta==(2 if q==5 else 1)*(cap-a),'actual categorical total variation')
        pis.append(law);deltas.append(delta);pure.extend(classes)
    need(len(pure)==len({m for m,a in pure})==21,'distinct finite pure originals')
    need(all(m>1 and m%2 and m not in c['selected_labels'] and m not in (3,9) for m,a in pure),'same actual-source family pure addition')
    for name,values in [('coordinate_lipschitz',ell),('tv_deltas_at_depth3',deltas)]:
        need(list(map(str,values))==proposed[name],'exact '+name)
    need([list(map(str,row)) for row in pis]==proposed['probabilities_at_depth3'],'exact depth3 categorical law')
    debit=sum((a*b for a,b in zip(ell,deltas)),F(0))
    afloor=alpha-debit;efloor=12*afloor-H-27*K*T;reserve=efloor/(27*afloor)
    need(afloor>0 and efloor>F(1,100) and reserve>F(13,1000),'strict same-source finite-pure continuation')
    quantities=dict(source_debit_upper=debit,alpha_floor=afloor,epsilon_floor=efloor,distorted_mass_floor=reserve)
    for name,value in quantities.items():need(value==F(proposed[name]),'exact transported '+name)
    actual,details=evaluate(pis,patterns,UI,scale,beta,R,projections)
    need(abs(actual-alpha)<=debit and actual>=afloor,'literal depth3 certificate respects TV transport')
    return dict(depth_lower=3,coordinate_lipschitz=list(map(str,ell)),tv_deltas_at_depth3=list(map(str,deltas)),
                probabilities_at_depth3=[list(map(str,row)) for row in pis],depth3_pure_originals=[list(x) for x in pure],
                **{k:str(v) for k,v in quantities.items()},strict_floor='13/1000',
                depth3_actual_alpha=str(actual),depth3_actual_gate=str(12*actual-H-27*K*T),
                distorted_mass_floor_decimal=float(reserve),
                scope='Exactly the specified pure families with independently chosen finite E_q>=3; no arbitrary additional old pure deletions. The TV debit is monotone, not necessarily L itself.')


def calculate(c):
    global CHECKS
    CHECKS=0
    primes,leaves,patterns,w,U,UI,scale,beta,R,projections,nforced=setup(c)
    pi=[tuple(map(F,row)) for row in c['probabilities']]
    need(pi==[(F(4,15),F(4,15),F(7,15))]+[(F(q-1,q*(q-2)),1-F(q-1,q*(q-2)))for q in primes[1:]],
         'declared all-upper probability point')
    h=c['threshold'];need(type(h)is int and h==16,'fixed h16')
    H0,Hr,Hv=hinge_coefficients(primes,h)
    Kq=prod((1+F(q-1,q-2)*a4(q) for q in primes),start=F(1))*(1+F(28,27)*a4(29))
    T=exact_tail(c['tail'])
    for name,value in dict(H0=H0,Hr=Hr,Hv=Hv,Kq=Kq,T1600=T).items():
        need(F(c['expected_hinge'][name])==value,'exact proposed '+name)
    r=max(sum(w[:2]),sum(w[2:]));v=max(w)
    H=H0+Hr*r+Hv*v;K=Kq*(1+15*r+216*v)
    alpha,point=evaluate(pi,patterns,UI,scale,beta,R,projections,True)
    gate=(28-h)*alpha-H-27*K*T
    need(alpha>0 and gate>0,'positive fixed cap-point source and continuation gate')
    reserve=gate/(27*alpha)
    point.update(gate=str(gate),gate_decimal=float(gate),positive=True,reserve=str(reserve),reserve_decimal=float(reserve))
    partial=[];full=0
    for l,row in enumerate(U):
        for sid,x in enumerate(row):
            if x==w[l]:full+=1
            elif x>0:partial.append(dict(leaf_index=l,leaf=leaves[l],pattern_id=sid,colours=list(patterns[sid]),u=str(x),u_over_w=str(x/w[l])))
    out=dict(schema='e7-categorical-kernel-stability-result-v1',
             scope='One fixed table: positive point certificate; failed320-vertex robust certificate; positive actual finite pure E_q>=3 transport with selected23 phase contract, arbitrary29 and certified full prime tails>1600. Ordinary arithmetic, not Lean or unrestricted Erdős7.',
             weights=list(map(str,w)),r=str(r),v=str(v),H0=str(H0),Hr=str(Hr),Hv=str(Hv),H=str(H),Kq=str(Kq),K=str(K),T1600=str(T),
             full_u_entries=960,forced_zero_entries=nforced,nonzero_entries=len(c['nonzero_u']),full_weight_entries=full,partial_entries=len(partial),partial_rows=partial,point=point)
    vertices5=[(F(0),F(1,5),F(4,5)),(F(0),F(4,15),F(11,15)),(F(1,5),F(0),F(4,5)),(F(4,15),F(0),F(11,15)),(F(4,15),F(4,15),F(7,15))]
    worst=None;rows=[]
    for vi,p5 in enumerate(vertices5):
        for mask in range(64):
            pv=[p5]+[((F(q-1,q*(q-2)),1-F(q-1,q*(q-2)))if mask>>(i-1)&1 else(F(0),F(1)))for i,q in enumerate(primes[1:],1)]
            a,_=evaluate(pv,patterns,UI,scale,beta,R,projections)
            g=(28-h)*a-H-27*K*T
            row=dict(vertex5=vi,binary_upper_mask=mask,alpha=str(a),gate=str(g))
            rows.append(row)
            if worst is None or a<F(worst['alpha']):worst=row
    expected=c['expected_vertices']
    need(expected['count']==len(rows)==320 and expected['all_positive']is False,'same-candidate320 robust success is not claimed')
    need(worst['vertex5']==expected['worst_vertex5'] and worst['binary_upper_mask']==expected['worst_binary_upper_mask'] and F(worst['alpha'])==F(expected['worst_alpha'])<0,'exact same-candidate negative vertex')
    out['vertices']=dict(count=len(rows),same_u_and_w=True,worst=worst,all_positive=all(F(row['gate'])>0 for row in rows),rows=rows)
    need(not out['vertices']['all_positive'],'full categorical relaxation fails for this fixed candidate')
    out['finite_pure_stability']=stability(c,primes,w,patterns,UI,scale,beta,R,projections,alpha,H,K,T)
    out['checks']=CHECKS
    return out


def main():
    here=Path(__file__);parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=here.with_name(here.stem+'_certificate.json'))
    parser.add_argument('--result',type=Path,default=here.with_suffix('.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args();out=calculate(read_json(args.certificate))
    if args.write_result:args.write_result.write_text(json.dumps(out,indent=2)+'\n')
    else:need(out==read_json(args.result),'retained exact result replay')
    print(json.dumps(dict(checks=out['checks'],point_gate=out['point']['gate_decimal'],same_candidate320_all_positive=out['vertices']['all_positive'],finite_pure_mass_floor=out['finite_pure_stability']['distorted_mass_floor_decimal'])))


if __name__=='__main__':main()
