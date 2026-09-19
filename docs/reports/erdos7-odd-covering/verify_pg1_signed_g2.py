#!/usr/bin/env python3
"""Signed original357 rebate for PG1's whole cost G2=(2L-5)+.

This verifier consumes the hash-bound pg1_joint_tail_certificate.json.  Its
geometry is certified by verify_pg1_joint_tail.py, not recomputed here.  Only
the added signed deletion bounds and complete shared-denominator criteria
are recomputed.  --write rebuilds the adjacent extension certificate.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import numpy as np

HERE=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:raise ArithmeticError(message)

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod

def evaluate(data,source_directory):
    prior_raw=read_artifact_bytes(source_directory/'certificates/pg1_joint_tail_certificate.json')
    require(sha256(prior_raw).hexdigest()==data['source_joint_sha256'],
            'hash-bound prior joint geometry certificate')
    prior=json.loads(prior_raw)
    require(prior['schema']=='erdos7-pg1-joint-tail-v1','prior certificate schema')
    c=prior['result'];source_hashes=prior['source_sha256']
    source_raw={name:read_artifact_bytes(source_directory/name) for name in source_hashes}
    require({name:sha256(raw).hexdigest() for name,raw in source_raw.items()}==source_hashes,
            'unchanged three original canonical inputs')
    source=json.loads(source_raw['certificates/mod3_conditioned_geometry_certificate.json'])
    m9=json.loads(source_raw['certificates/original9_conditioned_geometry_certificate.json'])
    require(c['source_sha256']==source_hashes,'prior result source identities')
    PG=load(source_directory/'verify_point_geometry.py','point_geometry')
    case=next(x for x in source['cases'] if x['name']=='PG1')
    pts=np.array(case['points'],dtype=np.int64);xs=np.array(case['old_points'],dtype=np.int64)
    w=np.array(case['weight_numerators'],dtype=np.int64);den=case['weight_denominator']
    require(np.all(w>=0) and sum(map(int,w))==den,'unchanged normalized PG1 probability')
    C=F(prior['floor_reference']);Wmax=C-1
    require(C==149 and c['depth_box']==[8,5,4],'same floor reference and source tail geometry')
    ds,ga,et,rem,depths,probs,beta,eo=PG.coeffs(tuple(c['depth_box']))
    rem[ds.index(35)]-=F(1,4)
    require(min(rem)>=0,'nonnegative complete higher357 deletion remainder')
    GD=PG.group_setup({'survivors':pts.tolist(),'points':xs.tolist()},(9,45),35)
    def deletion(v):
        require(np.all(v>=0) and 48*sum(map(int,v))<2**63,
                'nonnegative signed measure and bounded integer arithmetic')
        caps=[max(sum(int(a) for x,a in zip(pts,v) if x%d==r)
                  for r in range(d)) for d in ds]
        group,_,_=PG.group_oracle(v,GD)
        upper=F(group['value'],48*den)+sum((r*F(a,den) for r,a in zip(rem,caps)),F(0))
        return {'caps':caps,'group_numerator48':group['value'],'upper':str(upper)}
    ordinary=deletion(w);q0=1-F(ordinary['upper'])
    require(q0==F(c['source_survival_lower'])==F(m9['result']['survival_lower'])>0,
            'recomputed same independent source survival')
    def signed_cost(rows,factor,target):
        observations=[]
        for row in rows:
            i,j=row['charge_root3'],row['charge_root9']
            floor=((pts%3==i)&(pts%9==j)).astype(np.int64)
            charge_baseline=1+(pts%3==i).astype(np.int64)+(pts%9==j).astype(np.int64)
            require(np.array_equal(np.maximum(2*charge_baseline-5,0),floor),
                    'whole-cost original-root floor')
            loss=deletion(w*(target-factor*floor))
            U=F(row['costs']['n2']['lambda_upper'])
            excess=U+F(loss['upper'])-target
            observations.append({'charge_root3':i,'charge_root9':j,
                                 'target':str(target),'source_lambda_G2_upper':str(U),
                                 'weighted_deletion':loss,'criterion_excess':str(excess)})
        return observations
    base=signed_cost(c['unweighted_whole_cost']['records'],np.ones(len(w),dtype=np.int64),1)
    base_excess=max(F(r['criterion_excess']) for r in base)
    # The already certified H2 deletion has the same original-root floor.
    # Reuse each charge's deletion BEFORE taking a maximum over charges.
    require(F(m9['result']['hinge2']['target'])==3,'ordinary inherited H2 target')
    ordinary_hinge={(r['root3'],r['root9']):r for r in m9['result']['hinge2']['records']}
    def inherited_cost(rows,ordinary=False):
        observations=[]
        for row in rows:
            i,j=row['charge_root3'],row['charge_root9']
            hinge=ordinary_hinge[i,j] if ordinary else row['costs']['h2']
            target=F(3) if ordinary else F(hinge['signed_target'])
            require(target==(3 if ordinary else 3*Wmax),'same inherited signed target')
            UG=F(row['costs']['n2']['lambda_upper']);UH=F(hinge['lambda_upper'])
            EH=F(hinge['criterion_excess'])
            loss=F(hinge['weighted_deletion_upper']) if ordinary else F(hinge['weighted_deletion']['upper'])
            require(EH==UH+loss-target,'per-charge certified hinge deletion identity')
            observations.append({'charge_root3':i,'charge_root9':j,
                                 'source_lambda_G2_upper':str(UG),'source_lambda_H2_upper':str(UH),
                                 'source_H2_excess':str(EH),'inherited_G2_excess':str(UG-UH+EH)})
        require(len(observations)==len(ordinary_hinge)
                and {(r['charge_root3'],r['charge_root9']) for r in observations}==set(ordinary_hinge),
                'all independent charge roots retained in inherited costs')
        return observations
    base_inherited=inherited_cost(c['unweighted_whole_cost']['records'],ordinary=True)
    base_inherited_excess=max(F(r['inherited_G2_excess']) for r in base_inherited)
    P=F(1403,630);M=F(4,3);p1=F(28,33);p2=F(50,363)
    mt3=F(7,6)-p1-2*p2;k3=2*mt3-5*(1-p1-p2)
    require(mt3==F(31,726) and k3==F(2,121),'complete N>=3 multiplier tail')
    emax=max(F(r['criterion_excess']) for r in m9['result']['records'])
    square_excess={(r['root3'],r['root9']):F(r['criterion_excess'])
                   for r in m9['result']['records']}
    require(len(c['records'])==len(square_excess)
            and {(r['final_root3'],r['final_root9']) for r in c['records']}==set(square_excess),
            'all source final-root branches exactly once')
    records=[];count=len(base)
    for row in c['records']:
        i,j=row['final_root3'],row['final_root9']
        old_A=33*P-C+Wmax*(3*mt3+k3)/7
        old_B=((P-M)*emax+M*square_excess[i,j]+F(row['selected_lambda_H4'])/6+
               (p1*F(row['selected_lambda_G1'])+p2*F(row['selected_lambda_G2'])+
                mt3*F(row['selected_hinge2_excess'])-k3*F(row['positive_floor_residual']))/7)
        require(old_A==F(row['criterion_constant'])
                and old_B==F(row['criterion_inverse_Q_coefficient'])
                and old_A+old_B/q0==F(row['criterion_excess']),
                'reconstructed entire prior common-Q criterion')
        if row['method']=='weighted final-original-root floor':
            b=1+(pts%3==i).astype(np.int64)+(pts%9==j).astype(np.int64)
            factor=int(C)-b*b
            require(np.all(factor>=0) and int(factor.max())<=Wmax,'same final-root weight')
            observations=signed_cost(row['geometry']['records'],factor,int(Wmax))
            signed=max(F(r['criterion_excess']) for r in observations)
            inherited=inherited_cost(row['geometry']['records'])
            inherited_excess=max(F(r['inherited_G2_excess']) for r in inherited)
            method='weighted final-root G2'
        else:
            require(row['method']=='uniform final floor','known prior final-root method')
            observations=[];signed=Wmax*base_excess
            inherited=[];inherited_excess=Wmax*base_inherited_excess
            method='uniform weight times ordinary signed G2'
        count+=len(observations)
        # Each candidate is a complete globally valid criterion, with its
        # own common-Q coefficient.  Select only after bounding that whole
        # candidate over Q in [q0,1].
        new_A=old_A+p2*Wmax/7
        new_B=old_B+p2*(signed-F(row['selected_lambda_G2']))/7
        inherited_A=old_A+p2*(3*Wmax)/7
        inherited_B=old_B+p2*(inherited_excess-F(row['selected_lambda_G2']))/7
        require(old_B>0 and new_B>0 and inherited_B>0,'all complete criteria maximized at Q=q0')
        old_excess=old_A+old_B/q0;new_excess=new_A+new_B/q0
        inherited_bound=inherited_A+inherited_B/q0
        choices={'prior joint floor':old_excess,'signed G2':new_excess,'inherited H2 deletion':inherited_bound}
        selected_method=min(choices,key=choices.get);selected=choices[selected_method]
        records.append({'final_root3':i,'final_root9':j,'method':method,
                        'signed_G2_observations':observations,'signed_G2_excess':str(signed),
                        'prior_criterion_constant':str(old_A),'prior_criterion_inverse_Q':str(old_B),
                        'prior_criterion_excess':str(old_excess),
                        'signed_criterion_constant':str(new_A),'signed_criterion_inverse_Q':str(new_B),
                        'signed_criterion_excess':str(new_excess),
                        'inherited_G2_observations':inherited,'inherited_G2_excess':str(inherited_excess),
                        'inherited_criterion_constant':str(inherited_A),'inherited_criterion_inverse_Q':str(inherited_B),
                        'inherited_criterion_excess':str(inherited_bound),
                        'selected_complete_criterion':selected_method,
                        'criterion_excess':str(selected)})
        print(json.dumps({'final_roots':[i,j],'criterion_excess':float(selected)}),flush=True)
    worst=max(F(r['criterion_excess']) for r in records)
    require(worst<0,'strict negative final criterion')
    # For final retained mass r in (0,1], r*(Gamma-C)<=worst<0 implies
    # Gamma<=C+worst.  The prior independent positive survival is reused.
    require(F(c['independent_tail_survival_lower'])>0,'prior independent final survival')
    bound=C+worst
    require(bound<F(c['Gamma13_upper']) and bound<F(data['rounded_Gamma13_upper']),
            'strict improvement over the prior unchanged-law endpoint')
    require(count==40,'ten ordinary and thirty weighted signed G2 observations')
    return {'scope':'same PG1 law and physical kernels; prior geometry is a separately verified hash-bound prerequisite; full higher357 and multiplier tails',
            'source_joint_sha256':data['source_joint_sha256'],'original_source_sha256':source_hashes,
            'source_survival_lower':str(q0),'ordinary_deletion':ordinary,
            'ordinary_signed_G2_observations':base,'ordinary_signed_G2_excess':str(base_excess),
            'ordinary_inherited_G2_observations':base_inherited,
            'ordinary_inherited_G2_excess':str(base_inherited_excess),
            'signed_G2_observation_count':count,'records':records,
            'prior_Gamma13_upper':c['Gamma13_upper'],'maximum_criterion_excess':str(worst),
            'Gamma13_upper':str(bound)}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,default=HERE/'certificates/pg1_signed_g2_certificate.json')
    parser.add_argument('--source-directory',type=Path,default=HERE)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args();data=json.loads(read_artifact_text(args.certificate))
    require(data['schema']=='erdos7-pg1-signed-g2-v1','certificate schema')
    result=evaluate(data,args.source_directory)
    if args.write:
        data['result']=result;write_certificate_text(args.certificate, json.dumps(data,indent=2)+'\n')
    else:require(data['result']==result,'exact signed deletions and complete common-Q criteria')
    print(json.dumps({'Gamma13_upper':result['Gamma13_upper'],
                      'Gamma13_decimal':float(F(result['Gamma13_upper'])),
                      'signed_G2_observation_count':result['signed_G2_observation_count'],
                      'maximum_criterion_excess':result['maximum_criterion_excess']}),flush=True)

if __name__=='__main__':main()
