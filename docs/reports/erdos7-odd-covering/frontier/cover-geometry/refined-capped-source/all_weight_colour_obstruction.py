#!/usr/bin/env python3
"""Exact fixed-weight source optimum and complete first-query obstruction.

One two-colour core, original caps and complete max-residual certificate.
Ordinary rational algebra; not Lean or a covering/impossibility theorem.
"""
from fractions import Fraction as F
from math import prod
from pathlib import Path
import argparse
import json

Q=(5,7,11,13,17,19,23)
LEAVES=(4,7,2,5,8)
CAPS=tuple(F(q-1,q-2) for q in Q)
CHECKS=0


def need(ok,message):
    global CHECKS
    CHECKS+=1
    if not ok:raise ValueError(message)


def factors(m):
    n,es=m,[]
    for p in (3,)+Q:
        e=0
        while n%p==0:n//=p;e+=1
        es.append(e)
    need(n==1,'stated old numerical support')
    return es


def inventories(selected):
    beta=[prod((F(1,q-2) for i,q in enumerate(Q) if d>>i&1),start=F(1)) for d in range(128)]
    residual=[[beta[d] if d and (j>0 or d.bit_count()>=2) else F(0) for d in range(128)] for j in range(3)]
    need(len(selected)==len(set(selected)),'distinct selected slots')
    for m in selected:
        need(type(m) is int and m>1 and m%2==1,'odd nonunit selected label')
        es=factors(m);j=es[0];d=sum(1<<i for i,e in enumerate(es[1:]) if e)
        need(j<=2 and d and (j>0 or d.bit_count()>=2),'selected shallow mixed slot')
        residual[j][d]-=prod((CAPS[i] for i in range(7) if d>>i&1),start=F(1))/(m//3**j)
    need(all(x>=0 for row in residual for x in row),'nonnegative complete residual coefficients')
    return beta,residual


def source_rows(t,u,beta,residual):
    need(all(0<=t[i]<=CAPS[i]/q for i,q in enumerate(Q)) and 0<=u<=CAPS[0]/5
         and t[0]+u<=1,'valid one-coordinate categorical probabilities')
    rows=[]
    for d in range(128):
        zero,one=F(1),F(0)
        for i in range(1,7):
            if d>>i&1:continue
            p=t[i];zero,one=zero*(1-p),one*(1-p)+zero*p
        atmost=zero+one
        if d&1:S,T,B=zero,atmost,atmost
        else:S,T,B=(1-t[0])*zero,(1-t[0]-u)*atmost+t[0]*zero,(1-t[0])*atmost+t[0]*zero
        need(0<=S<=1 and 0<=T<=B<=1,'actual core response range')
        rows.append((S,T,B,residual[0][d],residual[1][d],beta[d]/2+residual[2][d]))
    return rows


def source_value(rows,weights):
    z=[w*A for w,A in zip(weights,(rows[0][0],rows[0][0],rows[0][1],rows[0][2],rows[0][2]))]
    value=sum(z,F(0))
    for S,T,B,r0,r1,r2 in rows:
        z=[w*A for w,A in zip(weights,(S,S,T,B,B))]
        value-=r0*sum(z,F(0))+r1*max(sum(z[:2]),sum(z[2:]))+r2*max(z)
    return value


def supporting_plane(rows,weights,dual):
    a,_,c,b,_=weights
    S,T,B,*_=rows[0]
    plane=[2*(S-T),2*(B-T),T]
    dual_map={(x['support'],x['kind']):x for x in dual}
    need(len(dual_map)==len(dual),'unique declared dual ties')
    branches_used=[];seen=set()
    for d,(S,T,B,r0,r1,r2) in enumerate(rows):
        for i,x in enumerate((2*(S-T),2*(B-T),T)):plane[i]-=r0*x
        root=[(2*S,F(0),F(0)),(-2*T,2*(B-T),T)]
        leaf=[(S,F(0),F(0)),(-2*T,-2*T,T),(F(0),B,F(0))]
        for kind,coef,branches in [('root',r1,root),('leaf',r2,leaf)]:
            if not coef:continue
            values=[x*a+y*b+z for x,y,z in branches]
            active=[i for i,x in enumerate(values) if x==max(values)]
            key=(d,kind)
            if len(active)==1:
                need(key not in dual_map,'no mixture claimed on a strict maximum')
                chosen=branches[active[0]]
                entry=dict(support=d,kind=kind,active=active)
            else:
                need(key in dual_map and active==dual_map[key]['active'],'declared tie is exact and complete')
                data=dual_map[key];theta=F(data['mix_second'])
                need(F(data['coefficient'])==coef,'declared tie loss coefficient equals the complete inventory')
                need(len(active)==2 and 0<=theta<=1,'convex mixture of the two active affine branches')
                x,y=(branches[i] for i in active)
                chosen=tuple((1-theta)*x[i]+theta*y[i] for i in range(3))
                entry=dict(support=d,kind=kind,active=active,mix_second=str(theta))
                seen.add(key)
            for i,x in enumerate(chosen):plane[i]-=coef*x
            branches_used.append(entry)
    need(seen==set(dual_map),'all declared dual mixtures are used')
    maximum=source_value(rows,weights)
    need(plane==[F(0),F(0),maximum],'global affine upper plane is the exact constant maximum')
    return maximum,plane,branches_used


def universal_gates():
    root,leaf=F(1,2),F(1,5)
    atoms={1:F(1)}
    for axis,q in enumerate((3,)+Q):
        def tail(j):
            if j==1:return F(1)
            if axis==0:return root if j==2 else leaf/3**(j-3)
            return CAPS[axis-1]/q**(j-1)
        new={}
        for n,mass in atoms.items():
            for j in range(1,27//n+1):
                z=tail(j)-tail(j+1)
                need(z>=0,'nonnegative universal lower-comparator atom')
                new[n*j]=new.get(n*j,F(0))+mass*z
        atoms=new
    mean=(1+root+3*leaf/2)*prod((1+C/(q-1) for q,C in zip(Q,CAPS)),start=F(1))
    gates=[]
    for h in range(28):
        hinge=mean-h+sum(((h-n)*mass for n,mass in atoms.items() if n<h),F(0))
        gate=hinge/(28-h)
        need(gate>F(1,50),'every universal first-query gate exceeds one fiftieth')
        gates.append(dict(h=h,hinge=str(hinge),gate=str(gate),gate_decimal=float(gate)))
    hinge28=mean-28+sum(((28-n)*mass for n,mass in atoms.items()),F(0))
    tail28=1-sum(atoms.values(),F(0))
    need(hinge28>0 and 0<tail28<=1,'positive terminal hinge makes the real-threshold gate increase on [27,28)')
    return mean,gates,dict(hinge28=str(hinge28),probability_at_least28=str(tail28))


def calculate(cert):
    global CHECKS
    CHECKS=0
    need(cert['schema']=='all-weight-colour-obstruction-v1','certificate schema')
    need(tuple(cert['primes'])==Q and tuple(cert['leaves'])==LEAVES,'declared coordinates')
    need(cert['core']=='short:no zero hits; long:at most one zero hit; leaf2:not colour1 at5',
         'one declared two-colour core')
    weights=tuple(map(F,cert['maximizing_weights']))
    need(len(weights)==5 and all(w>=0 for w in weights) and sum(weights)==1
         and weights[0]==weights[1] and weights[3]==weights[4],'symmetric feasible five-leaf weights')
    beta,residual=inventories(cert['selected_labels'])
    family=cert['actual_family']
    need(len({m for m,a in family})==len(family),'distinct actual numerical labels')
    need([45,11] in family,'declared changed actual45 phase')
    for m,a in family:
        need(type(m) is int and m>1 and m%2==1 and type(a) is int and 0<=a<m,'actual odd canonical class')
        es=factors(m)
        if m in (3,9):need(a==int(m==9),'common actual pure3/9 frame')
        if m not in cert['selected_labels']:continue
        for li,leaf in enumerate(LEAVES):
            for x5 in range(5):
                for hits in range(64):
                    n=hits.bit_count()+int(x5==0)
                    in_core=n==0 if li<2 else n<=1 and (li!=2 or x5!=1)
                    meets=(not es[0] or leaf%3**min(es[0],2)==a%3**min(es[0],2))
                    meets=meets and (not es[1] or x5==a%5)
                    meets=meets and all(not e or bool(hits>>i&1)==(a%q==0)
                                        for i,(q,e) in enumerate(zip(Q[1:],es[2:])))
                    need(not(in_core and meets),'one actual selected cylinder is core-null')
    allupper=source_rows(tuple(C/q for C,q in zip(CAPS,Q)),CAPS[0]/5,beta,residual)
    maximum,plane,branches=supporting_plane(allupper,weights,cert['dual_ties'])
    need(maximum==F(cert['expected_source_maximum']) and 0<maximum<F(3,400),
         'exact positive source optimum below three four-hundredths')
    vertices=[]
    for mask in range(256):
        t=tuple(C/q if mask>>i&1 else F(0) for i,(q,C) in enumerate(zip(Q,CAPS)))
        u=CAPS[0]/5 if mask>>7&1 else F(0)
        value=source_value(source_rows(t,u,beta,residual),weights)
        need(value>=maximum,'one fixed maximizing law attains the uniform full-box source optimum')
        vertices.append(dict(mask=mask,value=str(value),decimal=float(value)))
    worst=min(vertices,key=lambda v:F(v['value']))
    need(worst['mask']==255 and F(worst['value'])==maximum,'all-upper endpoint is a minimizing source vertex')
    # Symmetrization controls include nonsymmetric and zero-weight laws.
    symmetry_count=0
    for i in range(5):
        for j in range(5-i):
            for k in range(5-i-j):
                for ell in range(5-i-j-k):
                    w=tuple(F(x,4) for x in (i,j,k,ell,4-i-j-k-ell))
                    s=((w[0]+w[1])/2,)*2+(w[2],)+((w[3]+w[4])/2,)*2
                    need(source_value(allupper,w)<=source_value(allupper,s)<=maximum,
                         'fixed-row pair averaging and global plane control')
                    symmetry_count+=1
    mean,gates,terminal=universal_gates()
    least=min(gates,key=lambda row:F(row['gate']))
    need(least['h']==cert['expected_least_gate_h'],'least universal gate threshold')
    need(F(3,400)<F(1,50) and all(maximum<F(g['gate']) for g in gates),
         'all-weight full-hinge obstruction precedes every prime-tail debit')
    return dict(schema='all-weight-colour-obstruction-result-v1',check_count=CHECKS,
                scope='Exact maximum of the original-cap two-colour full-box source certificate, followed by a universal full-hinge29 obstruction. Not absence of actual survivors or impossibility of other sources.',
                maximizing_weights=list(map(str,weights)),source_maximum=str(maximum),source_maximum_decimal=float(maximum),
                dual_plane=list(map(str,plane)),dual_ties=cert['dual_ties'],branch_selections=branches,
                vertices=vertices,worst_source_vertex=worst,symmetry_controls=symmetry_count,
                lower_comparator=dict(root='1/2',leaf='1/5',complete_mean=str(mean)),gates=gates,least_gate=least,
                terminal_real_threshold=terminal,
                strict_bracket='source maximum < 3/400 < 1/50 < every first-query gate')


def main():
    here=Path(__file__)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=here.with_name(here.stem+'_certificate.json'))
    parser.add_argument('--result',type=Path,default=here.with_suffix('.json'))
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    result=calculate(json.loads(args.certificate.read_text()))
    if args.write_result:args.write_result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(result==json.loads(args.result.read_text()),'retained exact result replay')
    print(json.dumps(dict(check_count=result['check_count'],source_maximum=result['source_maximum_decimal'],
                         least_gate=result['least_gate']['gate_decimal'],bracket=result['strict_bracket'])))


if __name__=='__main__':main()
