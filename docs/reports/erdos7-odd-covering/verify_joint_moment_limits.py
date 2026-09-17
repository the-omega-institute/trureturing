#!/usr/bin/env python3
"""Exact primal/dual limits for joint integer-load moments in two SH27 costs.

Only two fixed W483 schedules are checked, not a new255-schedule search.
The infinite load tail is covered by an exact affine identity. No solver
or floating-point value is needed for certificate generation or replay.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import prod
from pathlib import Path
import runpy

HERE=Path(__file__).resolve().parent
PINS={
    'certificates/supported13_hinges_certificate.json':'b34a86ff533a3d1fc9c3de0c0ab3894f5648326eaf8e6602f0b176f350330442',
    'verify_pg1_scalar_schedule.py':'9f7be4b430abbf631a0958e96eaf860f56948d680078fe842c90c308e663289b',
}
W=F(483)


def require(condition,message):
    if not condition:raise ArithmeticError(message)


def unique(pairs):
    out={}
    for k,v in pairs:
        require(k not in out,'duplicate JSON key: '+k)
        out[k]=v
    return out


def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [encode(v) for v in x]
    return x


def current_cost(x,p,t,future,n):
    d=p-1-t;c=F(p-1,d);a=F(3*p-1,(p-1)**2)
    return W*F(max(n*x-t,0),d)+future*a*(F(p-1,p-1-min(n*x,t))-c)


def dual_value(x,constant,hinges):
    return constant+sum((coefficient*max(x-h,0) for h,coefficient in hinges.items()),F())


def route(source,helper,name):
    if name=='restart':
        obs=source['supported13_profile']
        hs={int(k):F(v) for k,v in obs['hinge_upper'].items()}
        M=F(obs['mean_upper']);G=F(obs['source_square'])
        schedule=[(17,6),(19,8)]
        r=(hs[6]-hs[8])/2
        p13=hs[8]-4*r
        law={6:1-r,12:r-p13,13:p13}
        constant=-F(7,135)
        coefficients={6:F(7,270),8:F(6517,135)}
        old_scan=source['restart17_19']
    else:
        hs={int(k):F(v) for k,v in source['source_integer_hinges'].items()}
        M=F(source['source_mean']);G=F(source['source_square'])
        schedule=[(11,4),(13,6),(17,6),(19,8)]
        q=hs[3]-hs[4];v=(hs[4]-hs[6])/2;r=(hs[6]-hs[8])/2
        p12=hs[8]-3*r
        law={3:1-q,4:q-v,6:v-r,11:r-p12,12:p12}
        constant=-F(14,135)
        coefficients={3:F(2,135),4:F(1,270),6:F(1,135),8:F(6517,135)}
        old_scan=source['once_conditioned11_13_17_19']
    require(min(law.values())>=0 and sum(law.values())==1,'abstract load law is a probability')
    mean=sum((p*x for x,p in law.items()),F())
    square=sum((p*x*x for x,p in law.items()),F())
    moments={h:sum((p*max(x-h,0) for x,p in law.items()),F()) for h in range(1,18)}
    require(mean==M and square<=G and all(moments[h]<=hs[h] for h in moments),
            'one abstract law satisfies every mean, square and H1--H17 constraint')
    require(all(c>=0 for c in coefficients.values()),'nonnegative dual upper-moment coefficients')
    dual_bound=constant+sum((c*hs[h] for h,c in coefficients.items()),F())
    # For x>=8 both functions are affine. Equality of their value at8
    # and slope proves the entire unbounded tail, not a finite cutoff.
    tail_slope=sum(coefficients.values(),F())
    require(tail_slope==F(483,10) and dual_value(8,constant,coefficients)==0,
            'dual and19/T8/N1 cost have identical affine tails on[8,infinity)')
    for x in range(1,9):
        require(dual_value(x,constant,coefficients)>=current_cost(x,19,8,F(1),1),
                'all remaining positive integer loads satisfy the exact majorant')
    require(sum((p*current_cost(x,19,8,F(1),1) for x,p in law.items()),F())==dual_bound,
            'matching primal and dual for the complete integer moment problem')
    growth=[1+F(3*p-1,(p-1)*(p-1-t)) for p,t in schedule]
    hinge7_excess=hs[7]-(hs[6]+hs[8])/2
    require(hinge7_excess>0,'strict discrete-convexity improvement at hinge7')
    prefix=[];old_total=F();new_total=F();records=[];tails=[]
    for i,(p,t) in enumerate(schedule):
        future=prod(growth[i+1:])
        row,features=helper['build_step'](p,t,future,prefix,hs,M,F())
        require(row['whole_n2_charge_improvement']==0,'no different-law PG1 observation')
        verified,_=helper['verify_at'](row,features,W,hs,M)
        old_total+=verified
        tail=W*row['tail_A']
        primal_tail=W*(mean*row['tail_mean']-t*row['tail_probability'])/row['d']
        require(primal_tail==tail,'same law attains the complete auxiliary tail cost')
        tails.append(dict(prime=p,threshold=t,full_mean=row['auxiliary_mean'],
                          tail_probability=row['tail_probability'],tail_mean=row['tail_mean'],
                          exact_tail_cost=tail,primal_tail_cost=primal_tail))
        subtotal=tail
        for n,probability,end,charge,energy,improvement in features:
            values=[None]+[W*charge[k]+energy[k] for k in range(1,end+2)]
            baseline,_=helper['feature_value'](values,hs,M,True)
            selected=dual_bound if (p,t,n)==(19,8,1) else baseline
            if (p,t,n)==(19,8,1):
                require(baseline-selected==F(7,1485)*hinge7_excess,
                        'all improvement is precisely the hinge7 convexity correction')
            primal=sum((mass*current_cost(x,p,t,future,n) for x,mass in law.items()),F())
            require(primal==selected,'same abstract law attains every retained cost bound')
            require(selected<=baseline,'joint-moment refinement never increases a cost')
            subtotal+=probability*selected
            records.append(dict(prime=p,threshold=t,auxiliary_multiplier=n,
                                probability=probability,old_bound=baseline,
                                exact_joint_moment_bound=selected,
                                weighted_saving=probability*(baseline-selected)))
        # Every omitted n>=T gives W(n*x-T)/d. The witness mean equals M,
        # so it also attains the exact full mass/mean auxiliary tail.
        new_total+=subtotal
        prefix.append((p,row['cap']))
    offset=prod(growth)*G-1-W
    old_defect=offset+old_total;new_defect=offset+new_total
    require(old_scan['least_defect_schedule']==[list(x) for x in schedule]
            and old_defect==F(old_scan['minimum_residual_at483']),
            'exactly the two existing least-defect schedules, no new scan')
    require(0<new_defect<old_defect,'strict but insufficient exact W483 improvement')
    require(sum((r['weighted_saving'] for r in records),F())==old_defect-new_defect,
            'all savings accounted for')
    return dict(name=name,schedule=schedule,source_mean=M,source_square_bound=G,
                source_hinge_bounds=hs,abstract_primal_law=law,
                primal_mean=mean,primal_square=square,square_slack=G-square,
                primal_hinges=moments,
                dual=dict(constant=constant,mean_coefficient=F(),square_coefficient=F(),
                          hinge_coefficients=coefficients,exact_bound=dual_bound,
                          infinite_tail_start=8,infinite_tail_slope=tail_slope),
                hinge7_excess_over_neighbor_average=hinge7_excess,
                cost_terms=records,complete_auxiliary_tails=tails,old_W483_defect=old_defect,
                exact_joint_moment_W483_defect=new_defect,
                exact_saving=old_defect-new_defect,
                scope='Exact optimum for the SH27 cost terms under the listed positive-integer load moments. The separate SH26 physical-square bound is held fixed. The abstract witness is not an actual covering family or BBMST-generated load law.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,default=HERE/'certificates/joint_moment_limits_certificate.json')
    parser.add_argument('--source-directory',type=Path,default=HERE)
    parser.add_argument('--profile-certificate',type=Path)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    profile_path=args.profile_certificate or args.source_directory/'certificates/supported13_hinges_certificate.json'
    helper_path=args.source_directory/'verify_pg1_scalar_schedule.py'
    for path,name in [(profile_path,'certificates/supported13_hinges_certificate.json'),(helper_path,'verify_pg1_scalar_schedule.py')]:
        require(sha256(read_artifact_bytes(path)).hexdigest()==PINS[name],'source SHA-256: '+name)
    source=json.loads(read_artifact_text(profile_path),object_pairs_hook=unique)
    helper=runpy.run_path(str(helper_path))
    rows=[route(source,helper,name) for name in ('restart','fourstep')]
    result=encode(dict(schema='erdos7-joint-integer-moment-limits-v1',source_sha256=PINS,
        W=W,routes=rows,
        scope='Two fixed existing schedules, all load moments together and complete unbounded load/auxiliary tails. No repeated255 scan. Exact dual upper bounds and matching abstract primal probabilities certify the limited gain from this moment relaxation; actual joint geometry remains outside it.'))
    if args.write:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
    else:
        actual=json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique)
        require(actual==result,'entire certificate equals exact recomputation')
    print('PASS exact joint moments: '+', '.join(r['name']+' defect='+str(float(r['exact_joint_moment_W483_defect']))+
                                               ', saving='+str(float(r['exact_saving'])) for r in rows))


if __name__=='__main__':main()
