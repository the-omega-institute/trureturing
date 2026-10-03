#!/usr/bin/env python3
"""Exact actual-pure source cells and a finite three-kernel source gap.

Uses the sibling Report814 evaluator and its literal table certificate.
No optimization, network, or finite-to-unbounded inference is performed.
"""
import argparse
from fractions import Fraction as F
import importlib.util
import json
from math import isqrt, prod
from pathlib import Path

CHECKS=0


def need(condition,label):
    global CHECKS
    CHECKS+=1
    if not condition:raise ValueError(label)


def unique_object(pairs):
    out={}
    for key,value in pairs:
        if key in out:raise ValueError('duplicate JSON key: '+key)
        out[key]=value
    return out


def read_json(path):
    return json.loads(path.read_text(),object_pairs_hook=unique_object)


def source_distribution(q,classes):
    need(type(q)is int and q>=3 and q%2==1 and all(q%d for d in range(2,isqrt(q)+1)),
         'odd prime coordinate')
    need(len({m for m,a in classes})==len(classes),'one original per numerical prime power')
    for m,a in classes:
        need(type(m)is int and type(a)is int and m>=q and 0<=a<m,'literal pure-prime integer data')
        cofactor=m
        while cofactor%q==0:cofactor//=q
        need(cofactor==1 and m>=q and 0<=a<m,'literal pure-prime cylinder')
    modulus=max([q]+[m for m,a in classes])
    survivor=[x for x in range(modulus)if all(x%m!=a for m,a in classes)]
    need(bool(survivor),'nonempty pure survivor')
    count=[0]*q
    for x in survivor:count[x%q]+=1
    deleted=next((a for m,a in classes if m==q),None)
    A=F(q-1,q)if deleted is not None else F(1)
    B=F(1,q*(q-1))
    deficits=[F(0)if i==deleted else F(1,q)-F(count[i],modulus)for i in range(q)]
    D=sum(deficits)
    need(all(d>=0 for d in deficits)and D<B,'actual union deficit below complete deeper budget')
    need(F(len(survivor),modulus)==A-D,'one actual normalization denominator')
    p=[F(n,len(survivor))for n in count]
    if deleted is None:
        lo,hi=F(q-2,q*q-q-1),F(q-1,q*q-q-1)
    else:
        lo,hi=F(1,q),F(q-1,q*(q-2))
    for i,value in enumerate(p):
        if i==deleted:
            need(value==0,'actual pure root is null')
        else:
            need(value==(F(1,q)-deficits[i])/(A-D),'same-source deficit identity')
            need(lo<=value<=hi and value>0,'live-root lower and upper probabilities')
    return dict(q=q,classes=[list(x)for x in classes],modulus=modulus,
                haar_survivor=str(F(len(survivor),modulus)),deleted_root=deleted,
                deficits=list(map(str,deficits)),total_deficit=str(D),first_digit=list(map(str,p)))


def projected_vertices(q,deleted,parts):
    B=F(1,q*(q-1))
    a=[F(len(part)-int(deleted in part),q)for part in parts]
    A=sum(a)
    live=[i for i,x in enumerate(a)if x]
    need(A>B and all(a[i]>B for i in live),'positive denominator and all live categories')
    vertices=[]
    for weak in live:
        p=tuple((x-(B if i==weak else 0))/(A-B)if x else F(0)for i,x in enumerate(a))
        need(min(p)>=0 and sum(p)==1,'normalized projected simplex vertex')
        vertices.append(p)
    # Zero-deficit source is already in their convex hull.
    bary=[a[i]/A for i in live]
    need(sum(bary)==1,'baseline barycentric weights')
    need(tuple(sum(bary[j]*vertices[j][i]for j in range(len(live)))for i in range(len(a)))
         ==tuple(x/A for x in a),'uniform baseline needs no extra vertex')
    return vertices


def main():
    parser=argparse.ArgumentParser()
    here=Path(__file__).resolve().parent
    parser.add_argument('--source-dir',type=Path,default=here.parent)
    parser.add_argument('--certificate',type=Path,default=here/'actual_pure_source_domains_certificate.json')
    parser.add_argument('--result',type=Path,default=here/'actual_pure_source_domains.json')
    parser.add_argument('--write-result',action='store_true')
    args=parser.parse_args()
    c=read_json(args.certificate)
    need(c['schema']=='e7-actual-pure-source-domains-v1','domain certificate schema')
    need(c['normalization']=='lambda_q=Haar restricted to actual pure survivor / Haar survivor mass',
         'natural actual Haar-conditioned source, not arbitrary capped law')
    spec=importlib.util.spec_from_file_location('actual_pure_source814',args.source_dir/'three_kernel_atlas_counterexample.py')
    api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
    source=api.read_json(args.source_dir/'three_kernel_atlas_counterexample_certificate.json')
    need(source['schema']==c['source_schema']=='e7-three-kernel-atlas-counterexample-v1','fixed814 source schema')
    need(source['normalization']==c['table_normalization']=='mu=lambda_w restricted to U / lambda_w(U)',
         'old table gates keep full-source survivor normalization')
    common=source['common'];primes=tuple(common['primes'])
    need(primes==tuple(c['primes'])==(5,7,11,13,17,19,23),'declared head primes')
    need(common['threshold']==16,'fixed old-table h16 gate')
    cells=[]
    need([x['name']for x in c['q5_cells']]==['pure0','pure1','pure_other','no_pure'],'four source cases')
    need([x['deleted_root']for x in c['q5_cells']]==[0,1,2,None],'literal deleted-root categories')
    for item in c['q5_cells']:
        vertices=projected_vertices(5,item['deleted_root'],common['partitions'][0])
        need(len(vertices)==len(item['vertices']) and
             set(vertices)=={tuple(map(F,row))for row in item['vertices']},'projected q5 cell vertices')
        cells.append(dict(name=item['name'],vertices=[list(map(str,row))for row in vertices]))
    need(F(8,19)<F(7,15),'no-pure and pure-other triangles separated')
    need(F(1,8)<F(3,19)<F(1,5),'Report814 relaxed counterexample is impossible for actual pure law')
    outer_vertices={tuple(map(F,row))for cell in cells for row in cell['vertices']}
    need(all(0<=p[0]<=F(4,15) and 0<=p[1]<=F(4,15) and p[0]+p[1]>=F(1,5)
             for p in outer_vertices),'every actual outer cell lies in old P5')
    need(set(api.VERTICES5)<=outer_vertices,'old P5 vertices remain in actual closed convex cells')
    binary=[]
    need([item['q']for item in c['binary_cells']]==list(primes[1:]),'complete six binary source coordinates')
    for item in c['binary_cells']:
        q=item['q'];lo=F(q-2,q*q-q-1);mid=F(q-1,q*q-q-1);hi=F(q-1,q*(q-2))
        need(lo<F(1,q)<mid<=hi,'positive structural intervals overlap')
        need(F(item['zero'])==0 and tuple(map(F,item['positive_interval']))==(lo,hi),'merged binary components')
        parts=([0],list(range(1,q)))
        for deleted in(None,0,1):
            values=projected_vertices(q,deleted,parts)
            expected={lo,mid}if deleted is None else({F(0)}if deleted==0 else{F(1,q),hi})
            need({p[0]for p in values}==expected,'binary projection from joint deficit simplex')
        binary.append(dict(q=q,components=[['0'],[str(lo),str(hi)]]))
    need(4*2**6==c['expected_product_cells']==256,'convex product cell count')
    need(sum(len(x['vertices'])for x in cells)*3**6==c['expected_product_vertices']==7290,'distinct product vertex menu count')
    controls=[source_distribution(x['q'],[tuple(y)for y in x['classes']])for x in c['small_families']]
    need(len(controls)==6,'bounded overlap and missing-label controls')
    # The two nested125 controls ensure actual UNION deficits are used.
    need(controls[2]['haar_survivor']==controls[1]['haar_survivor'],'nested pure125 adds no deletion')
    need(controls[4]['total_deficit']=='1/125','deep class inside removed root is not charged twice')
    need(c['pure_depth']==3 and(c['pure_root5'],c['deep_root5'],c['pure_root_other'],c['deep_root_other'])==(2,1,1,2),
         'literal finite-depth actual example')
    pi=[];actual=[];all_classes=[]
    for q in primes:
        f,d=(2,1)if q==5 else(1,2)
        classes=[(q,f)]+[(q**j,d+q**(j-1))for j in(2,3)]
        need(all(a%min(m,n)!=b%min(m,n)for i,(m,a)in enumerate(classes)for n,b in classes[i+1:]),
             'three actual pure cylinders are pairwise disjoint')
        record=source_distribution(q,classes)
        p=list(map(F,record['first_digit']))
        colour=(p[0],p[1],sum(p[2:]))if q==5 else(p[0],sum(p[1:]))
        pi.append(colour);record['colours']=list(map(str,colour));actual.append(record);all_classes+=classes
        need(F(record['haar_survivor'])==1-F(1,q)-F(1,q*q)-F(1,q**3),'actual complete finite pure source mass')
        if q>5:need(p[0]==F(q*q,q**3-q*q-q-1),'exact untouched zero-root probability')
    need(pi[0]==tuple(map(F,c['expected_probability5']))==(F(25,94),F(19,94),F(25,47)),
         'actual quinary categorical probabilities')
    family=[tuple(x)for x in common['actual_family']]+all_classes
    need(len(family)==c['expected_original_count']==46 and len({m for m,a in family})==46,
         'one actual46-original family with globally distinct numerical labels')
    need(all(m>1 and m%2 and 0<=a<m for m,a in family),'actual odd nonunit literal family')
    H0,Hr,Hv=api.hinge_coefficients(primes,16);T=api.exact_tail(common['tail'])
    Kq=prod((1+F(q-1,q-2)*api.a4(q)for q in primes),start=F(1))*(1+F(28,27)*api.a4(29))
    for key,value in dict(H0=H0,Hr=Hr,Hv=Hv,Kq=Kq,T1600=T).items():
        need(F(common['expected_hinge'][key])==value,'complete old comparison '+key)
    need([x['name']for x in source['kernels']]==['point812','quarter','third'],'fixed three old table identities')
    need(len(c['gate_upper_bounds'])==3,'one strict upper bound for every old table')
    gates=[]
    for kernel,upper in zip(source['kernels'],c['gate_upper_bounds']):
        _,leaves,patterns,w,U,UI,scale,beta,R,projections,_=api.setup(dict(common,weights=kernel['weights'],nonzero_u=kernel['nonzero_u']))
        alpha,_=api.evaluate(pi,patterns,UI,scale,beta,R,projections)
        r=max(sum(w[:2]),sum(w[2:]));v=max(w)
        gate=12*alpha-H0-Hr*r-Hv*v-27*Kq*(1+15*r+216*v)*T
        need(gate<F(upper)<0,'strict negative gate on the actual finite source')
        gates.append(dict(table=kernel['name'],alpha=str(alpha),gate=str(gate),gate_decimal=float(gate),strict_upper=upper))
    result=dict(schema='e7-actual-pure-source-domains-result-v1',q5_cells=cells,binary_cells=binary,
                product_cells=256,product_vertices=7290,small_actual_controls=controls,
                actual_sources=actual,actual_family=[list(x)for x in family],original_count=46,
                three_old_table_gates=gates,H0=str(H0),Hr=str(Hr),Hv=str(Hv),Kq=str(Kq),T1600=str(T),
                checks=CHECKS+api.CHECKS,
                scope='minimal closed convex outer cells for normalized Haar actual-pure sources; a literal finite source defeats three specified full-source h16 tables, not the optimal pointwise LP or new retained-moment gate')
    if args.write_result:args.result.write_text(json.dumps(result,indent=2)+'\n')
    else:need(read_json(args.result)==result,'exact saved result replay')
    print(json.dumps(dict(product_cells=256,product_vertices=7290,actual_probability5=list(map(str,pi[0])),
                          old_gates=[x['gate_decimal']for x in gates],checks=CHECKS+api.CHECKS),indent=2))


if __name__=='__main__':main()
