"""Exact source-adaptive atlas when an actual pure5 class kills a reference root.

Reuses the canonical814 common-source evaluator and fixed rational tables.
Every certified cell uses one table for all its vertices. No solver is used.
"""
import argparse
import importlib.util
import json
from fractions import Fraction as F
from math import prod
from pathlib import Path

def run():
    p=argparse.ArgumentParser()
    p.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--result',type=Path,default=Path(__file__).with_suffix('.json'))
    p.add_argument('--write-result',action='store_true')
    args=p.parse_args()
    spec=importlib.util.spec_from_file_location('reference_atlas_source814',args.source_dir/'three_kernel_atlas_counterexample.py')
    api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
    c=api.read_json(args.source_dir/'three_kernel_atlas_counterexample_certificate.json')
    api.need(c['schema']=='e7-three-kernel-atlas-counterexample-v1','fixed814 certificate schema')
    api.need(c['normalization']=='mu=lambda_w restricted to U / lambda_w(U)','same full-source normalization')
    common=c['common'];primes=tuple(common['primes'])
    api.need(common['threshold']==16,'fixed h16 threshold')
    api.local_vertex_check(primes,common['partitions'])
    H0,Hr,Hv=api.hinge_coefficients(primes,16)
    T=api.exact_tail(common['tail'])
    K=prod((1+F(q-1,q-2)*api.a4(q)for q in primes),start=F(1))*(1+F(28,27)*api.a4(29))
    for key,value in dict(H0=H0,Hr=Hr,Hv=Hv,Kq=K,T1600=T).items():
        api.need(F(common['expected_hinge'][key])==value,'complete inherited '+key)
    api.need([x['name']for x in c['kernels']]==['point812','quarter','third'],'fixed814 table identities')
    jobs=[('quarter','root0',(0,1)),('quarter','root1',(2,3)),('third','root1',(2,3))]
    faces={}
    for table,axis,vertices in jobs:
        k=next(x for x in c['kernels']if x['name']==table)
        _,leaves,patterns,w,U,UI,scale,beta,R,projections,_=api.setup(dict(common,weights=k['weights'],nonzero_u=k['nonzero_u']))
        r=max(sum(w[:2]),sum(w[2:]));v=max(w)
        charge=H0+Hr*r+Hv*v+27*K*(1+15*r+216*v)*T
        minima=[]
        for vi in vertices:
            rows=[]
            for mask in range(64):
                pi=api.vertex_probability(vi,mask,primes)
                L,_=api.evaluate(pi,patterns,UI,scale,beta,R,projections)
                G=12*L-charge
                rows.append(dict(mask=mask,gate=str(G),source_lower=str(L)))
            low=min(rows,key=lambda x:F(x['gate']))
            minima.append(dict(vertex5=vi,worst=low))
        faces[table+'_'+axis]=minima
    q0=[F(x['worst']['gate'])for x in faces['quarter_root0']]
    q1=[F(x['worst']['gate'])for x in faces['quarter_root1']]
    t1=[F(x['worst']['gate'])for x in faces['third_root1']]
    split_t=F(2,3)
    split=F(1,5)+(F(4,15)-F(1,5))*split_t
    api.need(split==F(11,45),'exact division of the actual root1 interval')
    left=(1-split_t)*q1[0]+split_t*q1[1]
    right=(1-split_t)*t1[0]+split_t*t1[1]
    lower=min(*q0,q1[0],left,right,t1[1])
    api.need(left>F(7,200)and right>F(1,25),'positive splice from fixed-table concavity')
    api.need(lower>F(7,200),'one uniform gate lower bound across all three cells')
    api.need(lower/27>F(1,800),'positive full-tail distorted mass reserve')
    # The scalar purity bounds are universal consequences of a complete deficit budget.
    A=F(4,5);B=F(1,20)
    api.need((F(1,5)-B)/(A-B)==F(1,5),'least live-root probability with pure5 present')
    api.need(F(1,5)/(A-B)==F(4,15),'greatest live-root probability with pure5 present')
    result=dict(schema='e7-reference-phase-atlas-v1',source='Report814 literal quarter and third tables',faces=faces,split=str(split),split_parameter=str(split_t),quarter_split_lower=str(left),third_split_lower=str(right),uniform_gate_lower=str(lower),uniform_gate_lower_decimal=float(lower),mass_lower=str(lower/27),mass_lower_decimal=float(lower/27),strict_mass_floor='1/800',source_range=['1/5','4/15'],checks=api.CHECKS,scope='Selected808 phase conditions and full804 support/tail; arbitrary actual finite pure-q families; actual pure5 phase0 or1 only. Each source selects one fixed table; no root-other, absent-pure5 or unrestricted Erdos7 claim.')
    if args.write_result:args.result.write_text(json.dumps(result,indent=2)+'\n')
    else:api.need(api.read_json(args.result)==result,'exact saved atlas result')
    print(json.dumps(dict(gate_lower=float(lower),quarter_splice=float(left),third_splice=float(right),mass_lower=float(lower/27),checks=api.CHECKS),indent=2))

if __name__=='__main__':run()
