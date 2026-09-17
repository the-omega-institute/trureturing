#!/usr/bin/env python3
"""Complete generic AP13 hinge transfer and exact AP/SH27 continuations.

The source is the same actual AP(4,6) law. Exact auxiliary probability
and first-moment tails remain full at every step. Default validates a
saved certificate; --write regenerates it. No Lean status is asserted.
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
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import json
from math import prod
from pathlib import Path
import runpy

HERE=Path(__file__).resolve().parent
PINS={
    'certificates/pure_root_profile_certificate.json':'b1ba6c871d993fd43152351c2b823a7955d93ce4500fbe29f9420c38f7f72196',
    'certificates/shared_cell_hinges_certificate.json':'585fd5cc59e7c121e64141aec6717ead06b3d5dfd00e2a40a2278e796f7f8845',
    'verify_pg1_scalar_schedule.py':'9f7be4b430abbf631a0958e96eaf860f56948d680078fe842c90c308e663289b',
}
LIMIT=17


def require(condition,message):
    if not condition: raise ArithmeticError(message)


def unique(pairs):
    out={}
    for k,v in pairs:
        require(k not in out,'duplicate JSON key: '+k)
        out[k]=v
    return out


def encode(value):
    if isinstance(value,F): return str(value)
    if isinstance(value,dict): return {str(k):encode(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)): return [encode(v) for v in value]
    return value


def auxiliary(prefix,T):
    probabilities={1:F(1)};mean=F(1)
    for p,c in prefix:
        require(0<c<=p,'capped auxiliary factor is a probability')
        following=defaultdict(F)
        for n,w in probabilities.items():
            for v in range(1,(T-1)//n+1):
                following[n*v]+=w*(1-c/p if v==1 else c*F(p-1,p**v))
        probabilities=dict(following)
        mean*=1+c/F(p-1)
    if T==1: probabilities={}
    tail_mass=1-sum(probabilities.values(),F())
    tail_mean=mean-sum((n*v for n,v in probabilities.items()),F())
    require(tail_mass>=0 and tail_mean>=T*tail_mass,'full auxiliary mass and mean tail')
    return probabilities,mean,tail_mass,tail_mean


def source_profile(j,shared):
    knots={int(h):F(v) for h,v in shared['generic_integer_hinges'].items()}
    M=F(shared['complete_test_first_moment']);G=F(j['source_inputs']['G'])
    require(M==1+knots[1],'same complete-load mean and hinge-one observation')
    extension=[]
    for h in range(13,LIMIT+1):
        values=[]
        for branch in j['branches']:
            u=list(map(F,branch['reference_pure_masses']))
            D=F(branch['uniform357_Haar_density_bound'])
            _,mean,tail_mass,tail_mean=auxiliary(list(zip((3,5,7),(1/x for x in u))),h)
            values.append(D*prod(u)*(tail_mean-h*tail_mass))
        root=max(values)
        square=(G-1)*F(h,4*h*h-1)
        knots[h]=min(root,square)
        extension.append(dict(h=h,root_bound=root,unit_floor_square_bound=square,
                              selected=knots[h]))
    return knots,M,G,extension


def interpolate(knots,mean,t):
    if t<=1: return mean-t
    n=t.numerator//t.denominator
    return knots[n] if t==n else (n+1-t)*knots[n]+(t-n)*knots[n+1]


def supported_profile(shared,knots,M,G):
    law=shared['same_actual_AP13_consumer']
    rho=F(law['survival_lower']);g=F(law['supported_square'])
    raw={};physical={};aux_rows=[]
    for h in range(1,LIMIT+1):
        probs,mean,tail_mass,tail_mean=auxiliary([(11,F(5,3)),(13,F(2))],h)
        require(mean==F(49,36),'same11/13 full comparison mean')
        value=sum((pn*n*interpolate(knots,M,F(h,n)) for n,pn in probs.items()),F())
        value+=M*tail_mean-h*tail_mass
        physical[h]=value;raw[h]=value/rho
        aux_rows.append(dict(h=h,probability_below_cutoff=probs,full_mean=mean,
                             tail_probability=tail_mass,tail_mean=tail_mean))
    mean_witness=min(range(1,LIMIT+1),key=lambda a:a+raw[a])
    mean13=F(mean_witness)+raw[mean_witness]
    profile={};witnesses={}
    for h in range(1,LIMIT+1):
        witness=min(range(h,LIMIT+1),key=lambda a:a-h+raw[a])
        shifted=F(witness-h)+raw[witness]
        square=(g-1)*F(h,4*h*h-1)
        profile[h]=min(shifted,square)
        witnesses[h]=dict(shift_threshold=witness,shifted_hinge=shifted,
                           unit_floor_square_bound=square)
    require(mean_witness==6 and profile[1]==mean13-1,'same supported13 mean and hinges')
    return dict(survival_lower=rho,source_square=g,physical_hinges=physical,
                raw_conditioned_hinges=raw,mean_upper=mean13,mean_threshold=mean_witness,
                hinge_upper=profile,shift_witnesses=witnesses,auxiliary_tails=aux_rows)


def schedule_row(schedule,hinges,mean,G,helper,verify_W=F(483)):
    growth=[1+F(3*p-1,(p-1)*(p-1-t)) for p,t in schedule]
    P=prod(growth);prefix=[];steps=[];feature_sets=[]
    for i,(p,t) in enumerate(schedule):
        row,features=helper['build_step'](p,t,prod(growth[i+1:]),prefix,hinges,mean,F())
        # No PG1-specific13/T5 whole-N2 branch is present in either schedule.
        require(row['whole_n2_charge_improvement']==0,'no different-law PG1 observation used')
        steps.append(row);feature_sets.append(features);prefix.append((p,row['cap']))
    A=sum((r['A'] for r in steps),F());B=sum((r['B'] for r in steps),F())
    intercept=P*G-1+B
    minimum_W=max(r['minimum_W'] for r in steps)
    values=[helper['verify_at'](r,fs,verify_W,hinges,mean)
            for r,fs in zip(steps,feature_sets)]
    direct=P*G-1+sum((value for value,_ in values),F())-verify_W
    require(direct==intercept+(A-1)*verify_W,'same final-W affine functional')
    output=dict(schedule=schedule,A=A,B=B,positive_intercept=intercept,minimum_W=minimum_W,
                residual_at483=direct,physical_square_multiplier=P,
                minimum_verified_feature_coefficient=min(v for _,v in values),
                Gamma_upper=None)
    if A<1:
        W=max(minimum_W,intercept/(1-A))
        final=[helper['verify_at'](r,fs,W,hinges,mean)
               for r,fs in zip(steps,feature_sets)]
        require(P*G-1+sum((value for value,_ in final),F())<=W,'final SH28 criterion')
        output['Gamma_upper']=1+W
        output['W']=W
    return output


def scan(initial,hinges,mean,G,helper,expected_finite):
    rows=[schedule_row(initial+[(17,a),(19,b)],hinges,mean,G,helper)
          for a,b in product(range(1,16),range(1,18))]
    require(len(rows)==255 and all(r['positive_intercept']>0 and r['residual_at483']>0 for r in rows),
            'all255 integer schedules have a positive affine deficit at W483')
    finite=[r for r in rows if r['Gamma_upper'] is not None]
    require(len(finite)==expected_finite,'complete finite-sufficient schedule count')
    best_bound=min(finite,key=lambda r:r['Gamma_upper'])
    best=min(rows,key=lambda r:r['residual_at483'])
    return dict(schedule_count=255,finite_sufficient_bound_count=len(finite),
                best_sufficient_bound=best_bound,
                minimum_A=min(r['A'] for r in rows),
                minimum_positive_intercept=min(r['positive_intercept'] for r in rows),
                minimum_residual_at483=best['residual_at483'],
                least_defect_schedule=best['schedule'],outcomes=rows,
                scope='Only this fixed complete-profile SH27 scalar-feature upper functional and the255 stated integer17/19 schedules. Failure is not a lower bound on actual moments or a no-covering obstruction.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,default=HERE/'certificates/supported13_hinges_certificate.json')
    parser.add_argument('--source-directory',type=Path,default=HERE)
    parser.add_argument('--shared-cell-certificate',type=Path)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    shared_path=args.shared_cell_certificate or args.source_directory/'certificates/shared_cell_hinges_certificate.json'
    for name,pin in PINS.items():
        path=shared_path if name=='certificates/shared_cell_hinges_certificate.json' else args.source_directory/name
        require(sha256(read_artifact_bytes(path)).hexdigest()==pin,'source SHA-256: '+name)
    j=json.loads(read_artifact_text(args.source_directory/'certificates/pure_root_profile_certificate.json'),object_pairs_hook=unique)
    shared=json.loads(read_artifact_text(shared_path),object_pairs_hook=unique)
    require(shared['source_sha256']['certificates/pure_root_profile_certificate.json']==PINS['certificates/pure_root_profile_certificate.json'],
            'same prior actual law in the shared-cell source')
    helper=runpy.run_path(str(args.source_directory/'verify_pg1_scalar_schedule.py'))
    knots,M,G,extension=source_profile(j,shared)
    supported=supported_profile(shared,knots,M,G)
    hs=supported['hinge_upper'];ms=supported['mean_upper'];gs=supported['source_square']
    single=[schedule_row([(17,t)],hs,ms,gs,helper) for t in range(1,16)]
    finite=[r for r in single if r['Gamma_upper'] is not None]
    best17=min(finite,key=lambda r:r['Gamma_upper'])
    require(best17['schedule']==[(17,8)] and best17['Gamma_upper']==F(
        71411032739803777721269,176909701938094610544),
        'same-law actual AP17/T8 supported-square improvement')
    restart=scan([],hs,ms,gs,helper,72)
    four_step=scan([(11,4),(13,6)],knots,M,G,helper,59)
    require(restart['best_sufficient_bound']['Gamma_upper']==F(
            14309324828593686784688579,6107986643845861414296),
            'same-law actual17/19 positive continuation')
    result=encode(dict(schema='erdos7-supported13-hinges-v1',source_sha256=PINS,
        scope='Full actual generic AP(4,6) supported13 law with the shared-cell source profile; complete original labels and arbitrary finite heights. Universal hinge transfer uses exact full comparison means. Positive AP17 and17/19 continuations, plus510 exact schedule outcomes. Ordinary mathematics, not Lean or unrestricted Erdos7 resolution.',
        source_mean=M,source_square=G,source_integer_hinges=knots,
        source_profile_extension=extension,supported13_profile=supported,
        single17=dict(schedule_count=15,outcomes=single,best=best17),
        restart17_19=restart,once_conditioned11_13_17_19=four_step,
        universal_formula='U(t)=sum_(n<t)P(N=n)*n*H357(t/n)+M357*E[N;N>=t]-t*P(N>=t), N=N11*N13 and E N=49/36. For t>=1, H13(t)<=inf_(a>=t)[a-t+U(a)/rho13]. Only the listed witnesses are numerically evaluated.',
        open_mathematical_obligations='Every one of the255 supported13-restart schedules and255 four-step once-conditioned schedules has positive W483 defect for this specific upper functional. Some yield larger finite positive-survival bounds. Actual kernels or richer joint observations may perform better.'))
    if args.write: write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
    else:
        actual=json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique)
        require(actual==result,'entire certificate equals exact recomputation')
    print('PASS full AP13 profile: mean<='+str(float(ms))+'; AP17 Gamma<='+str(float(best17['Gamma_upper']))+
          '; AP19 Gamma<='+str(float(restart['best_sufficient_bound']['Gamma_upper']))+
          '; restart/four-step minimum W483 defects='+str(float(restart['minimum_residual_at483']))+
          '/'+str(float(four_step['minimum_residual_at483'])))


if __name__=='__main__':main()
