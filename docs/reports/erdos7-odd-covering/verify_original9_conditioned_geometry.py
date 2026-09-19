#!/usr/bin/env python3
"""Retain original mod9 separately from its higher saturated descendants.

The fixed PG1 probability is inherited from the hash-bound adjacent source.
All ten original3/original9 branches, full geometric tails, weighted actual
deletion groups and the independent positive survival bound are recomputed.
Requires Python3 and NumPy. Run with python3 -I -O; --write creates the result.
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
from itertools import product
from pathlib import Path
import importlib.util
import json
import sys
import numpy as np

HERE=Path(__file__).resolve().parent
SPEC=importlib.util.spec_from_file_location('point_geometry',HERE/'verify_point_geometry.py')
PG=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(PG)
require=PG.require


def hinge2_observation(pts,xs,w,den,ri,cut,ds,ga,rem,depths,probs,beta,caps,GD,q):
    """Bound H2 on the same lifted law and actual deletion event as the square.

    Original roots i,j remain fixed across every auxiliary depth. Only the
    higher projected mod9 cylinder varies. R_E consumes (3-g(b_ij))*mu
    without renormalizing; q is the independently established survival bound.
    """
    R=np.array([sum(int(v) for v,k in zip(w,ri) if int(k)==row)
                for row in range(len(xs))],dtype=np.int64)
    v=np.array([max(int(v) for v,k in zip(w,ri) if int(k)==row)
                for row in range(len(xs))],dtype=np.int64)
    require(np.all(R>=v) and np.all(v>=0),'nonnegative row hinge relaxation')
    _,features=PG.geometry(xs)
    roots=np.array([int(xs[np.flatnonzero(row[1])[0]]%3) for row in features],dtype=np.int64)
    load_limit=3+2*(cut[1]+1)+(cut[0]+1)+(cut[0]+1)*(cut[1]+1)
    safety=((cut[2]+2)*load_limit+2)*den
    require(safety<2**63 and 3*48*den<2**63,'hinge and weighted deletion arithmetic fits signed64')
    outside=[]
    for d,gamma in zip(ds,ga):
        inside=F(1)
        for p,h,k in zip((3,5,7),(2,1,1),cut):
            exponent,quotient=0,d
            while quotient%p==0:
                exponent+=1;quotient//=p
            inside*=sum((F(p-1,p**(z+1))*(z+1)**int(exponent==h)
                         for z in range(k+1)),F(0))
        outside.append(1+gamma-inside-1+beta)
    require(min(outside)>=0,'complete nonnegative first-moment geometric remainder')
    tail=sum((e*F(m,den) for e,m in zip(outside,caps)),F(0))
    cache={}
    for z3,z5 in product(range(cut[0]+1),range(cut[1]+1)):
        b=np.array([1,1,1+z5,1+z3,1+z5,(1+z3)*(1+z5)],dtype=np.int64)
        full=np.einsum('aer,e->ar',features,b,dtype=np.int64)
        cache[z3,z5]=(full,int((full@v).max()))
    records=[]
    for root9 in sorted(set(int(x%9) for x in xs)):
        for root3 in (1,2):
            per_depth={}
            for z, (full,mb) in cache.items():
                A=(full-features[:,3,:]+(xs%9==root9).astype(np.int64))[roots==root3]
                require(int(A.min())>=1 and int(full.min())>=1,'A+(1+z7)B is at least2')
                # Exact maximum of the row relaxation: the high hinge is
                # linear, so A and B separate. Only A carries original3.
                base=int((np.maximum(A-2,0)@(R-v)+A@v).max())
                per_depth[z]=(base,mb)
            nums=[per_depth[z3,z5][0]+(1+z7)*per_depth[z3,z5][1]-2*int(v.sum())
                  for z3,z5,z7 in depths]
            require(min(nums)>=0,'nonnegative full-A hinge maxima')
            U=(1-beta)*F(nums[0],den)+sum((p*F(n,den) for p,n in zip(probs,nums)),F(0))+tail
            baseline=((pts%3==root3)&(pts%9==root9)).astype(np.int64)
            weighted=w*(3-baseline)
            require(int(weighted.min())>=0,'nonnegative target3 deletion weights')
            wcaps=[max(sum(int(vv) for x,vv in zip(pts,weighted) if x%d==a)
                       for a in range(d)) for d in ds]
            wg,_,_=PG.group_oracle(weighted,GD)
            deletion=F(wg['value'],48*den)+sum((e*F(m,den) for e,m in zip(rem,wcaps)),F(0))
            records.append({'root3':root3,'root9':root9,'hinge_numerators':nums,
                            'lambda_upper':str(U),'weighted_caps':wcaps,'weighted_group48':wg['value'],
                            'weighted_deletion_upper':str(deletion),'criterion_excess':str(U+deletion-3)})
    require(len(records)==10 and q>0,'all fixed original roots and independent positive survival')
    margin=min(-F(r['criterion_excess']) for r in records)
    require(margin>0,'same-law H2 target3 strictly passes every branch')
    return {'target':'3','depth_box':list(cut),'full_A_layouts':len(features),
            'outside_mean_coefficients':list(map(str,outside)),'outside_mean_increment':str(tail),
            'records':records,'minimum_margin':str(margin),'H2_upper':'3','mean_upper':'5',
            'maximum_hinge_integer_bound':safety}


def evaluate(data):
    source=HERE/'certificates/mod3_conditioned_geometry_certificate.json'
    require(sha256(read_artifact_bytes(source)).hexdigest()==data['source_sha256'],'inherited probability source')
    parent=json.loads(read_artifact_text(source))
    require(parent['schema']=='erdos7-mod3-conditioned-geometry-v1','source schema')
    case=next(c for c in parent['cases'] if c['name']==data['source_case'])
    require(case['name']=='PG1' and data['reference_target']=='33'
            and data['rounded_Gamma_upper']=='135/4','specified original9 endpoint')
    family=case['family'];raw=case['points'];den=case['weight_denominator']
    require(len(family)==len({d for d,a in family})==11
            and {d for d,a in family}=={d for d in range(2,316) if 315%d==0},'original low labels')
    require(all(type(d) is int and type(a) is int and 0<=a<d for d,a in family),
            'canonical integer forbidden residues')
    require(raw==[x for x in range(315) if all(x%d!=a for d,a in family)],'actual full low carrier')
    pts=np.array(raw,dtype=np.int64);xs=np.array(case['old_points'],dtype=np.int64)
    weights=case['weight_numerators']
    require(all(type(v) is int and v>=0 for v in weights)
            and len(weights)==len(raw) and sum(weights)==den>0,'unchanged probability')
    require(xs.tolist()==sorted(set(int(x%45) for x in pts)),'actual old projection')
    w=np.array(weights,dtype=np.int64);ri=np.array([xs.tolist().index(int(x%45)) for x in pts])
    require(set(int(x%3) for x in pts)=={1,2}
            and set(int(x%7) for x in pts)<=set(range(1,7)),'empty-root replacement domain')
    cut=(8,5,4)
    ds,ga,eta,rem,depths,probs,beta,eo=PG.coeffs(cut);rem[ds.index(35)]-=F(1,4)
    require(min(rem)>=0 and min(eo)>=0,'nonnegative exact tail coefficients')
    mods=(3,5,9,15)
    choices=list(product(*(sorted(set(int(x%d) for x in xs)) for d in mods)))
    features=np.array([[[int(x%d==a) for x in xs] for d,a in zip(mods,row)]
                       for row in choices],dtype=np.int64)
    lowroots=np.array([row[0] for row in choices],dtype=np.int64)
    high={(z3,z5):1+np.einsum('ajn,j->an',features,np.array([1,1+z5,1+z3,1+z5],dtype=np.int64),dtype=np.int64)
          for z3,z5 in product(range(9),range(6))}
    caps=[max(sum(int(v) for x,v in zip(pts,w) if x%d==a) for a in range(d)) for d in ds]
    tail=sum((e*F(m,den) for e,m in zip(eo,caps)),F(0))
    GD=PG.group_setup({'survivors':raw,'points':xs.tolist()},(9,45),35)
    group,_,_=PG.group_oracle(w,GD)
    q=1-F(group['value'],48*den)-sum((e*F(m,den) for e,m in zip(rem,caps)),F(0))
    require(q==F(case['result']['survival_lower'])>0,'same-law independent survival')
    safety=7**2*(2+2*6+9+9*6)**2*den
    require(safety<2**63,'split-label square arithmetic fits signed64')
    dp=PG.FixedADP(pts,xs,ri);K=F(data['reference_target']);records=[]
    for root9 in sorted(set(int(x%9) for x in xs)):
        # A's d9 slot now contains only higher labels, with coefficient z3.
        # The original mod9 cylinder is restored at its fixed root9.
        low={z:L-features[:,2,:]+(xs%9==root9).astype(np.int64) for z,L in high.items()}
        prec,_,_,_=PG.exact_squares(w,pts,ri,low,depths,low_roots=lowroots,high_loads=high)
        drec=[dp.query(w,z,root_values=True,original_nine=root9) for z in depths]
        for root3 in (1,2):
            key=str(root3);pure=[r['root_numerators'][key] for r in prec];fixed=[r[key] for r in drec]
            nums=list(map(min,zip(pure,fixed)))
            U=(1-beta)*F(nums[0],den)+sum((p*F(n,den) for p,n in zip(probs,nums)),F(0))+tail
            baseline=1+(pts%3==root3).astype(np.int64)+(pts%9==root9).astype(np.int64)
            factor=K.numerator-K.denominator*baseline*baseline
            require(int(factor.min())>=0 and int(factor.max())*den*48<2**63,'nonnegative bounded deletion weights')
            weighted=w*factor
            wcaps=[max(sum(int(v) for x,v in zip(pts,weighted) if x%d==a) for a in range(d)) for d in ds]
            wg,_,_=PG.group_oracle(weighted,GD)
            R=F(wg['value'],48*den*K.denominator)+sum((e*F(m,den*K.denominator) for e,m in zip(rem,wcaps)),F(0))
            records.append({'root3':root3,'root9':root9,'pure7_numerators':pure,'fixedA_numerators':fixed,
                            'U':str(U),'weighted_caps':wcaps,'weighted_group48':wg['value'],
                            'weighted_deletion_upper':str(R),'criterion_excess':str(U+R-K)})
    require(len(records)==10,'all nonempty original3/original9 root pairs')
    excess=max(F(0),*(F(r['criterion_excess']) for r in records))
    bound=K+excess/q
    require(bound<F(data['rounded_Gamma_upper']),'strict all-height upper bound')
    result={'cap_numerators':caps,'group_numerator48':group['value'],'survival_lower':str(q),
            'records':records,'maximum_nonnegative_excess':str(excess),'Gamma_upper':str(bound),
            'rounding_margin':str(F(data['rounded_Gamma_upper'])-bound),
            'maximum_square_integer_bound':safety}
    result['hinge2']=hinge2_observation(pts,xs,w,den,ri,cut,ds,ga,rem,depths,probs,beta,caps,GD,q)
    return result


def main():
    args=[a for a in sys.argv[1:] if a!='--write']
    path=Path(args[0]) if args else HERE/'certificates/original9_conditioned_geometry_certificate.json'
    data=json.loads(read_artifact_text(path))
    require(data['schema']=='erdos7-original9-conditioned-geometry-v1','schema')
    result=evaluate(data)
    if '--write' in sys.argv:
        data['result']=result;write_certificate_text(path, json.dumps(data,indent=2)+'\n')
    else:require(data['result']==result,'all exact split-label geometry and deletion data')
    print(json.dumps({'Gamma_upper':result['Gamma_upper'],'rounded_Gamma_upper':data['rounded_Gamma_upper'],
                      'survival_lower':result['survival_lower'],'branches':len(result['records']),
                      'H2_upper':result['hinge2']['H2_upper'],'mean_upper':result['hinge2']['mean_upper'],
                      'H2_minimum_margin':result['hinge2']['minimum_margin']}),flush=True)


if __name__=='__main__':main()
