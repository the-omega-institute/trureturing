"""Replay SH20 at thresholds13..21 and consume the same-law observations.

The existing saturated convex and SH18 certificates are hash-bound verified
prerequisites. This reuses the existing SH21 convex-query implementation,
independently checks three full4480^2 maxima, and replays every integer
11/13/17/19/23 schedule through the existing obstruction evaluator.
Only the numerical strategy obstruction is claimed, not noncoverage.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import importlib.util,json,time
import numpy as np

THRESHOLDS=tuple(range(13,22))
DENSE=(((2,1,1),13),((3,0,2),17),((8,5,4),21))

def require(condition,message):
    if not condition:raise ArithmeticError(message)

def load_module(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'available prerequisite implementation')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def dense_checks(head,observations):
    # Independent full layouts: no reduced features or singleton identity.
    points=[x for x in range(45) if all(x%d!=a for d,a in head['family'] if 45%d==0)]
    survivors=[x for x in range(315) if all(x%d!=a for d,a in head['family'])]
    sizes=np.array([sum(y%45==x for y in survivors) for x in points],dtype=np.int64)
    weights=np.array(head['weight_numerators'],dtype=np.int64)
    require(points==head['points'] and sizes.tolist()==head['r'],'independent actual geometry')
    require(int(sizes@weights)==head['weight_denominator'],'independent same-law normalization')
    ds=(3,5,9,15,45)
    choices=product(*[sorted({x%d for x in points}) for d in ds])
    masks=np.array([[[int(x%d==a) for x in points] for d,a in zip(ds,row)]
                    for row in choices],dtype=np.int64)
    require(len(masks)==4480,'all full layouts including each singleton45 choice')
    output=[]
    for depth,threshold in DENSE:
        u3,u5,u7=[z+1 for z in depth]
        load=1+np.einsum('ijn,j->in',masks,np.array([1,u5,u3,u5,u3*u5],dtype=np.int64))
        limit=(1+u7)*(2+u3+2*u5+u3*u5)
        range_bound=4*head['weight_denominator']*limit
        require(range_bound<2**63,'all direct signed64 operations fit')
        base=np.maximum(load-threshold,0)@((sizes-1)*weights)
        best=0
        for lo in range(0,len(load),64):
            aa=load[lo:lo+64]
            values=np.broadcast_to(base[lo:lo+len(aa),None],(len(aa),len(load))).copy()
            for j,w in enumerate(weights):
                values+=w*np.maximum(aa[:,j,None]+u7*load[None,:,j]-threshold,0)
            best=max(best,int(values.max()))
        require(best==observations[depth][threshold],'independent dense maximum agrees')
        output.append({'depth':list(depth),'threshold':threshold,'full_layout_pairs':len(load)**2,
                       'hinge_numerator':best,'integer_range_bound':range_bound})
    return output

def compute(profile_path,head_path,convex_verifier,obstruction_verifier):
    raw=read_artifact_bytes(profile_path);data=json.loads(raw)
    head_raw=read_artifact_bytes(head_path);head=json.loads(head_raw)
    require(sha256(head_raw).hexdigest()==data['head_certificate_sha256'],'same SH18 prerequisite')
    require(data['schema']==1 and data['scope']=='SH18 carrier and law; arbitrary finite original357 heights',
            'specified initial law and profile contract')
    require(head['depth_box']==[8,5,4],'specified all-height comparison box')
    depths=set(product(range(9),range(6),range(5)))
    require(len(head['records'])==270 and {tuple(r['depth']) for r in head['records']}==depths,
            'all and only the270 geometric depths')
    convex=load_module(convex_verifier,'saturated_convex_prerequisite')
    _,sizes,nums,den,features=convex.prepare(head)
    totals={t:F(0) for t in THRESHOLDS};observations={};records=[]
    mass=F(0);square=F(0);largest_range=0
    for row in head['records']:
        z=tuple(row['depth'])
        pr=F(2,3**(z[0]+1))*F(4,5**(z[1]+1))*F(6,7**(z[2]+1))
        require(pr==F(row['probability']),'exact geometric atom')
        mass+=pr;square+=pr*F(row['square_numerator'],den)
        values=[];observations[z]={}
        for t in THRESHOLDS:
            value,bound=convex.exact_cost(features,sizes,nums,den,z,t)
            values.append(value);observations[z][t]=value;totals[t]+=pr*F(value,den)
            largest_range=max(largest_range,bound)
        records.append({'depth':list(z),'hinge_numerators':values})
    outside=F(head['U_B'])-square-(1-mass);q=F(head['survival_lower'])
    require(mass==F(head['beta']) and outside==F(data['outside_square_excess'])>=0,
            'complete same-law outside square-minus-one budget')
    require(q==F(data['survival_lower']) and 0<q<=1,'same-law survival denominator')
    hinges={}
    for t in THRESHOLDS:
        coefficient=F(t,4*t*t-1);remainder=coefficient*outside
        hinges[str(t)]={'integer_square_coefficient':str(coefficient),'finite_box':str(totals[t]),
                        'geometric_remainder':str(remainder),'nu_upper':str((totals[t]+remainder)/q)}
    dense=dense_checks(head,observations)
    obstruction=load_module(obstruction_verifier,'combined_schedule_prerequisite')
    enhanced=obstruction.compute(profile_path,
                                 additional_hinges={int(t):F(v['nu_upper']) for t,v in hinges.items()})
    require(enhanced['schedule_count']==530145,'complete unchanged schedule domain')
    require(enhanced['argmin_charge_grid_bound']==[4,4,8,8,12],'minimum grid-charge witness unchanged')
    return {'schema':1,'scope':'SH20 high hinges on the exact SH18 law; same bounded SH27 schedule obstruction',
            'profile_certificate_sha256':sha256(raw).hexdigest(),
            'head_certificate_sha256':sha256(head_raw).hexdigest(),'thresholds':list(THRESHOLDS),
            'records':records,'outside_square_excess':str(outside),'survival_lower':str(q),
            'hinges':hinges,'dense_independent_checks':dense,'reduced_integer_range_bound':largest_range,
            'extended_schedule_obstruction':enhanced}

def main():
    here=Path(__file__).parent
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',type=Path,default=here/'certificates/saturated_convex_profile_certificate.json')
    parser.add_argument('--head',type=Path,default=here/'certificates/saturated_joint_head_certificate.json')
    parser.add_argument('--convex-verifier',type=Path,default=here/'verify_saturated_convex_profile.py')
    parser.add_argument('--obstruction-verifier',type=Path,default=here/'verify_combined_schedule_obstruction.py')
    parser.add_argument('--certificate',type=Path,default=here/'certificates/saturated_high_hinges_certificate.json')
    parser.add_argument('--write-certificate',action='store_true')
    args=parser.parse_args();start=time.perf_counter()
    if not args.write_certificate:
        expected=json.loads(read_artifact_text(args.certificate))
        require(sha256(read_artifact_bytes(args.profile)).hexdigest()==expected['profile_certificate_sha256'],
                'exact profile prerequisite hash')
        require(sha256(read_artifact_bytes(args.head)).hexdigest()==expected['head_certificate_sha256'],
                'exact head prerequisite hash')
    result=compute(args.profile,args.head,args.convex_verifier,args.obstruction_verifier)
    if args.write_certificate:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
    else:require(result==expected,'complete high-hinge and enhanced-obstruction certificate replay')
    print(json.dumps({'thresholds':result['thresholds'],'queries':len(result['records'])*len(THRESHOLDS),
                      'dense_pairs':sum(r['full_layout_pairs'] for r in result['dense_independent_checks']),
                      'schedules':result['extended_schedule_obstruction']['schedule_count'],
                      'minimum_charge_lower':result['extended_schedule_obstruction']['minimum_charge_coefficient_lower'],
                      'seconds':time.perf_counter()-start}))

if __name__=='__main__':main()
