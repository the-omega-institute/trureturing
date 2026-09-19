#!/usr/bin/env python3
"""Exact fixed-mod3 square and deleted-energy bounds on actual315 carriers.

Usage: python3 -I -O verify_mod3_conditioned_geometry.py [certificate.json]
Requires Python3 and NumPy. Reuses the two adjacent geometry algorithms,
retaining the original mod3 test root in each one. All certificate arithmetic
is integer/Fraction. No optimization or external service is used.
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
from itertools import product
from pathlib import Path
import importlib.util
import json
import sys
import numpy as np

HERE=Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location('point_geometry',HERE/'verify_point_geometry.py')
PG=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PG)
require=PG.require


def evaluate(case):
    family=case['family'];rawpoints=case['points'];raww=case['weight_numerators']
    require(type(family) is list and all(type(row) is list and len(row)==2
            and all(type(v) is int for v in row) for row in family),'integer low family')
    require(len(family)==len({d for d,a in family})==11
            and {d for d,a in family}=={d for d in range(2,316) if 315%d==0},
            'complete distinct original low labels')
    require(all(0<=a<d for d,a in family),'canonical forbidden residues')
    require(type(rawpoints) is list and all(type(x) is int for x in rawpoints)
            and rawpoints==[x for x in range(315) if all(x%d!=a for d,a in family)],
            'complete actual low carrier')
    require(type(raww) is list and len(raww)==len(rawpoints)
            and all(type(w) is int and 0<=w<2**63 for w in raww),'nonnegative integer weights')
    den=sum(raww)
    require(type(case['weight_denominator']) is int and den==case['weight_denominator']>0,
            'same normalized actual law')
    pts=np.array(rawpoints,dtype=np.int64);w=np.array(raww,dtype=np.int64)
    xs=np.array(sorted(set(int(x%45) for x in pts)),dtype=np.int64)
    require(xs.tolist()==case['old_points'],'actual old projection')
    roots=np.unique(xs%3)
    require(roots.tolist()==[1,2] and set(int(x%7) for x in pts)<=set(range(1,7)),
            'the specified normalization omits root0 at3 and7')
    ri=np.array([xs.tolist().index(int(x%45)) for x in pts],dtype=np.int64)
    cut=case['depth_box']
    require(cut==[8,5,4],'complete specified270-depth box')
    ds,ga,eta,rem,depths,probs,beta,eo=PG.coeffs(cut)
    rem[ds.index(35)]-=F(1,4)
    require(min(rem)>=0 and min(eo)>=0 and 0<beta<1,'complete nonnegative geometric remainder')
    mods=(3,5,9,15)
    choices=list(product(*(sorted(set(int(x%d) for x in xs)) for d in mods)))
    features=np.array([[[int(x%d==a) for x in xs] for d,a in zip(mods,row)]
                       for row in choices],dtype=np.int64)
    lowroots=np.array([row[0] for row in choices],dtype=np.int64)
    loads={(z3,z5):1+np.einsum('ajn,j->an',features,
           np.array([1,1+z5,1+z3,1+z5],dtype=np.int64),dtype=np.int64)
           for z3,z5 in product(range(cut[0]+1),range(cut[1]+1))}
    bmax=[1,1,1+cut[1],1+cut[0],1+cut[1],(1+cut[0])*(1+cut[1])]
    safety=(2+cut[2])**2*sum(bmax)**2*den
    require(safety<2**63,'every square intermediate fits signed64')
    prec,_,_,_=PG.exact_squares(w,pts,ri,loads,depths,low_roots=lowroots)
    dp=PG.FixedADP(pts,xs,ri)
    drec=[dp.query(w,z,root_values=True) for z in depths]
    caps=[max(sum(int(v) for x,v in zip(pts,w) if int(x%d)==a) for a in range(d)) for d in ds]
    tail=sum((e*F(m,den) for e,m in zip(eo,caps)),F(0))
    grouped=PG.group_setup({'survivors':rawpoints,'points':xs.tolist()},(9,45),35)
    best,_,_=PG.group_oracle(w,grouped)
    q=1-F(best['value'],48*den)-sum((e*F(m,den) for e,m in zip(rem,caps)),F(0))
    require(q>0,'independent positive mass for the actual higher survivor event')
    K=F(case['target'])
    require(K>=4,'nonnegative signed deletion weight on both roots')
    results=[]
    for root in roots:
        r=str(int(root))
        pure=[v['root_numerators'][r] for v in prec]
        fixed=[v[r] for v in drec]
        num=list(map(min,zip(pure,fixed)))
        U=(1-beta)*F(num[0],den)+sum((p*F(v,den) for p,v in zip(probs,num)),F(0))+tail
        # No renormalization: h_i mu is a positive finite measure.
        factor=K.numerator-K.denominator*(1+3*(pts%3==root))
        require(int(factor.min())>=0 and int(factor.max())*den*48<2**63,
                'weighted group arithmetic fits signed64')
        weighted=w*factor
        weighted_caps=[max(sum(int(v) for x,v in zip(pts,weighted) if int(x%d)==a)
                           for a in range(d)) for d in ds]
        wb,_,_=PG.group_oracle(weighted,grouped)
        R=F(wb['value'],48*den*K.denominator)+sum(
            (e*F(m,den*K.denominator) for e,m in zip(rem,weighted_caps)),F(0))
        margin=K-U-R
        results.append({'root':int(root),'pure7_numerators':pure,'fixedA_numerators':fixed,
                        'U':str(U),'weighted_caps':weighted_caps,'weighted_group48':wb['value'],
                        'weighted_deletion_upper':str(R),'margin':str(margin)})
    unsigned=[min(v['numerator'],max(dr.values())) for v,dr in zip(prec,drec)]
    unsigned_U=(1-beta)*F(unsigned[0],den)+sum(
        (p*F(v,den) for p,v in zip(probs,unsigned)),F(0))+tail
    old=1+(unsigned_U-1)/q
    return {'divisors':ds,'cap_numerators':caps,'group_numerator48':best['value'],
            'survival_lower':str(q),'unrestricted_root_square_upper':str(unsigned_U),
            'unit_loss_Gamma_upper':str(old),'target':str(K),
            'improvement_from_unit_loss':str(old-K),'roots':results,
            'minimum_margin':str(min(F(r['margin']) for r in results)),
            'maximum_square_integer_bound':safety}


def main():
    args=[a for a in sys.argv[1:] if a!='--write']
    path=Path(args[0]) if args else HERE/'certificates/mod3_conditioned_geometry_certificate.json'
    data=json.loads(read_artifact_text(path))
    require(data['schema']=='erdos7-mod3-conditioned-geometry-v1','certificate schema')
    require(len(data['cases'])==2,'two specified actual carriers')
    for case in data['cases']:
        result=evaluate(case)
        require(F(result['minimum_margin'])>=0,'both original mod3 branches satisfy the signed criterion')
        if '--write' in sys.argv:case['result']=result
        else:require(case['result']==result,'exact finite maxima, weighted deletions, and full tails')
        print(json.dumps({'case':case['name'],'target':case['target'],
                          'survival_lower':result['survival_lower'],
                          'minimum_margin':result['minimum_margin'],
                          'unit_loss_Gamma_upper':result['unit_loss_Gamma_upper']}),flush=True)
    if '--write' in sys.argv:write_certificate_text(path, json.dumps(data,indent=2)+'\n')


if __name__=='__main__':main()
