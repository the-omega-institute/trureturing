#!/usr/bin/env python3
"""One exact fixed-q p11/T4 scalar majorant on the existing SH18 probability.

Run from any cwd with Python3+NumPy. The adjacent directory, or --source-dir,
contains the three hash-bound canonical prerequisites. No optimizer or scratch import is used.
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
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from math import lcm
import argparse,importlib.util,json
import numpy as np

def require(value,message):
    if not value:raise ArithmeticError(message)

P,T,W=11,4,F(10000)
A=F(3*P-1,(P-1)**2);DEN=P-1-T;CAP=F(P-1,DEN)
KNOTS=(F(0),F(56,315),F(128,315),F(512,315))
FILES=('verify_saturated_whole_cost.py','certificates/saturated_joint_head_certificate.json',
       'certificates/saturated_convex_profile_certificate.json')

def kappa(k):return F(P-1,P-1-min(k,T))

def compute(source,expected=None):
    raw={name:read_artifact_bytes(source/name) for name in FILES}
    hashes={name:sha256(data).hexdigest() for name,data in raw.items()}
    if expected is not None:
        require(expected.get('schema')=='erdos7-fixed-q-p11-v1','schema')
        require(expected.get('source_sha256')==hashes,'all prerequisite source bytes')
        require(expected.get('p')==P and expected.get('T')==T and expected.get('W')==str(W),
                'prescribed p11/T4/W10000')
        require(expected.get('q')==list(map(str,KNOTS)),'prescribed exact candidate')
    spec=importlib.util.spec_from_file_location('canonical_whole',source/FILES[0])
    whole=importlib.util.module_from_spec(spec);spec.loader.exec_module(whole)
    head=json.loads(raw[FILES[1]]);profile=json.loads(raw[FILES[2]])
    require(profile['head_certificate_sha256']==hashes[FILES[1]],'profile binds same head')
    prepared=whole.prepare(head);features,sizes,nums,weight_den,outside=prepared
    survival=F(head['survival_lower'])
    require(survival==F(profile['survival_lower']) and survival>0,'same conditioned probability')
    h11=A*kappa(1)
    slopes=[KNOTS[j+1]-KNOTS[j] for j in range(T-1)]
    require(0<=slopes[0]<=slopes[1]<=slopes[2]<=W/DEN,'convex increasing knot slopes')
    require(all(KNOTS[j]>=A*(kappa(j+1)-kappa(1)) for j in range(T)),'constant lower energy center')

    def p_cost(k):return KNOTS[k-1] if k<=T else KNOTS[-1]+W*(k-T)/DEN
    def v_cost(k):return max(A*kappa(j)*k*k-KNOTS[j-1] for j in range(1,T+1))
    require(v_cost(1)==h11,'Vq1 fixed')

    def quadratic_observation(name,cost):
        center=cost(1);values=[F(0)]+[cost(k)-center for k in range(1,463)]
        increments=[values[k]-values[k-1] for k in range(1,len(values))]
        require(all(0<=x<=y for x,y in zip([F(0)]+increments,increments)),
                'increasing convex exact cost')
        require(all(values[k]<=A*CAP*(k*k-1) for k in range(1,463)),
                'quadratic outside coefficient on finite table')
        scale=lcm(*(v.denominator for v in values))
        integer=[v*scale for v in values]
        require(all(v.denominator==1 and 0<=v<2**63 for v in integer),'exact integer cost table')
        require(weight_den*int(integer[-1])<2**63,'pre-arithmetic whole intermediate bound')
        table=np.array(list(map(int,integer)),dtype=np.int64)
        total=F(0);largest=0
        for row in head['records']:
            value,bound=whole.maximum_cost(features,sizes,nums,weight_den,row['depth'],table)
            total+=F(row['probability'])*F(value,weight_den*scale);largest=max(largest,bound)
        tail=A*CAP*outside
        return {'name':name,'conditioning_center':str(center),'exact_cost_denominator':scale,
                'integer_range_bound':largest,'square_majorant_coefficient':str(A*CAP),
                'finite_box':str(total),'geometric_remainder':str(tail),
                'nu_cost_upper':str(center+(total+tail)/survival)}

    def affine_observation(name,cost):
        result=whole.whole_observation(name,cost,T,head,prepared,survival)
        result.pop('records')
        return result

    chosen_p=affine_observation('fixed_q_P',p_cost)
    chosen_v=quadratic_observation('fixed_q_V',v_cost)
    # Recompute the original diagonal construction as an independent same-law
    # comparator. It is a bound, not an asserted optimum among potentials.
    diagonal=[F(0)]*(T+1)
    for j in range(1,T):diagonal[j+1]=diagonal[j]+A*j*j*(kappa(j+1)-kappa(j))
    def diagonal_u(k):return diagonal[k] if k<=T else diagonal[T]+W*(k-T)/DEN
    def diagonal_energy(k):
        return A*kappa(1)+sum((A*kappa(j+1)*(2*j+1) for j in range(1,min(k,T))),F(0))\
               +A*CAP*max(0,k*k-T*T)
    prior_p=affine_observation('diagonal_u',diagonal_u)
    prior_v=quadratic_observation('H11_plus_diagonal_v',diagonal_energy)
    chosen=F(chosen_p['nu_cost_upper'])+F(chosen_v['nu_cost_upper'])
    prior=F(prior_p['nu_cost_upper'])+F(prior_v['nu_cost_upper'])
    require(chosen<prior,'strict improvement of the same-law p11 contribution')
    result={'schema':'erdos7-fixed-q-p11-v1','source_sha256':hashes,'p':P,'T':T,'W':str(W),
            'scope':'one fixed potential before comparison; actual77-point SH18 law; all finite357 heights; p11 has no earlier-prime multiplier',
            'q':list(map(str,KNOTS)),'survival_lower':str(survival),
            'queries':[chosen_p,chosen_v,prior_p,prior_v],'Cp_upper':str(chosen),
            'diagonal_Cp_upper':str(prior),'strict_improvement':str(prior-chosen),
            'whole_depth_queries':1080,'rounding':'none',
            'maximum_integer_range':max(x['integer_range_bound'] for x in (chosen_p,chosen_v,prior_p,prior_v))}
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--certificate',type=Path,default=(Path(__file__).resolve().parent / 'certificates/fixed_q_p11_certificate.json'))
    ap.add_argument('--write',action='store_true')
    args=ap.parse_args();expected=None if args.write else json.loads(read_artifact_text(args.certificate))
    if expected is not None:
        def strict_types(value):
            require(type(value) in (dict,list,str,int),'exact certificate types; no floats or bools')
            if type(value) is dict:
                require(all(type(k) is str for k in value),'string certificate keys')
                for child in value.values():strict_types(child)
            elif type(value) is list:
                for child in value:strict_types(child)
        strict_types(expected)
    result=compute(args.source_dir,expected)
    if args.write:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
    else:require(result==expected,'complete exact certificate equality')
    print(json.dumps({'verified':True,'Cp_upper':result['Cp_upper'],
                      'Cp_upper_decimal':float(F(result['Cp_upper'])),
                      'strict_improvement':result['strict_improvement'],
                      'improvement_decimal':float(F(result['strict_improvement'])),
                      'maximum_integer_range':result['maximum_integer_range'],'rounding':'none'},indent=2))
