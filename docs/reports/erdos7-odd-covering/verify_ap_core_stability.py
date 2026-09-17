#!/usr/bin/env python3
"""Exact full-law AP(4,6) finite-core stability and the complete W483 reduction."""

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

HERE=Path(__file__).resolve().parent
PINS={
    'certificates/shared_cell_hinges_certificate.json':'585fd5cc59e7c121e64141aec6717ead06b3d5dfd00e2a40a2278e796f7f8845',
    'certificates/pure_root_profile_certificate.json':'b1ba6c871d993fd43152351c2b823a7955d93ce4500fbe29f9420c38f7f72196',
    'certificates/weighted_kernel_tails_certificate.json':'373b6a441a027f0e6fd7b4c9b718e90b8dcbf6382ecbbf87633a7bcec9741d48',
}

def require(c,m):
    if not c: raise ArithmeticError(m)

def unique(pairs):
    d={}
    for k,v in pairs:
        require(k not in d,'duplicate JSON key: '+k);d[k]=v
    return d

def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x

def phi(p,a):return F((a+1)**2)+F(2*(a+1),p-1)+F(p+1,(p-1)**2)
def sigma(p):return F(p*(p*p+4*p+1),(p-1)**3)
def prob_tail(p,b):return F(1,(p-1)*p**b)
def energy_tail(p,b):
    return F(1,p**b)*(F((b+2)**2,p-1)+F(4*b+7,(p-1)**2)+F(3*(p+1),(p-1)**3))

def factors(ps,b,weighted):
    if weighted:
        full=prod(sigma(p) for p in ps)
        head=prod(sigma(p)-energy_tail(p,b) for p in ps)
        unit=prod(phi(p,0) for p in ps)
        for p in ps:
            require(sigma(p)-energy_tail(p,b)==sum((F(1,p**a)*phi(p,a) for a in range(b+1)),F()),
                    'closed weighted tail vs literal finite head')
    else:
        full=prod(F(p,p-1) for p in ps)
        head=prod(F(p,p-1)-prob_tail(p,b) for p in ps)
        unit=F(1)
    return dict(full=full,head=head,unit=unit,tail=full-head,head_nonunit=head-unit)

def step(p,T,ps,D,J,b,weighted):
    s=F(p-2,p-1);delta=F(T-1,p-2);C=1/(1-delta);lip=max(C*C,C/delta)
    a=factors(ps,b,weighted)
    z=phi(p,0) if weighted else F(1)
    full=sigma(p)-z if weighted else F(1,p-1)
    tail=energy_tail(p,b) if weighted else prob_tail(p,b)
    t=prob_tail(p,b)
    old=D*a['tail']*(C/s*full+lip/(s*s)*z/F(p-1))
    mixed=D*a['head_nonunit']*(C/s*tail+lip/(s*s)*z*t)
    pure=J*(C/s*tail+(lip+C)/(s*s)*z*t)
    return dict(prime=p,threshold=T,delta=delta,C=C,pure_floor=s,Lipschitz=lip,
                old_primes=ps,D=D,J=J,weighted=weighted,factors=a,
                old_error=old,mixed_error=mixed,pure_error=pure,total=old+mixed+pure)

def test_tail(ps,b,D):
    full=prod(F(p*(p+1),(p-1)**2) for p in ps)
    head=prod(1+sum((F(2*a+1,p**a) for a in range(1,b+1)),F()) for p in ps)
    return D*(full-head)

def evaluate(b,G0,D0,G13,D13,rho):
    a=factors([3,5,7],b,False);w=factors([3,5,7],b,True)
    initial_w=D0*(G0*a['tail']+w['tail']);initial_m=2*D0*a['tail']
    w11=step(11,4,[3,5,7],D0,G0,b,True)
    m11=step(11,4,[3,5,7],D0,F(1),b,False)
    w13=step(13,6,[3,5,7,11],F(5,3)*D0,F(23,15)*G0,b,True)
    m13=step(13,6,[3,5,7,11],F(5,3)*D0,F(1),b,False)
    ew=F(55,36)*(F(23,15)*initial_w+w11['total'])+w13['total']
    em=initial_m+m11['total']+m13['total']
    normalized_w=(ew+G13*em)/rho
    normalized_m=2*em/rho
    test=test_tail([3,5,7,11,13],b,D13)
    return dict(box=b,initial_weighted=initial_w,initial_L1=initial_m,
                steps=[w11,m11,w13,m13],physical_and_killed_weighted_error=ew,
                physical_and_killed_L1_error=em,normalized_weighted_error=normalized_w,
                normalized_L1_error=normalized_m,complete_test_tail=test,
                full_to_finite_Gamma_error=normalized_w+test)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,default=HERE/'certificates/ap_core_stability_certificate.json')
    parser.add_argument('--source-directory',type=Path,default=HERE)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args();sources={}
    for n,h in PINS.items():
        raw=read_artifact_bytes(args.source_directory/n)
        require(sha256(raw).hexdigest()==h,'source SHA-256 '+n)
        sources[n]=json.loads(raw,object_pairs_hook=unique)
    src=sources['certificates/pure_root_profile_certificate.json']
    law=sources['certificates/shared_cell_hinges_certificate.json']['same_actual_AP13_consumer']
    G0=F(src['source_inputs']['G']);D0=1/F(src['source_inputs']['survivor_density_lower'])
    G13=F(law['supported_square']);D13=F(law['supported_Haar_density']);rho=F(law['survival_lower'])
    require((G0,D0)==(F(3849,106),F(432,53)),'same actual uniform357 source')
    require((law['T11'],law['T13'])==(4,6),'same actual AP law')
    rows=[evaluate(b,G0,D0,G13,D13,rho) for b in [10,11,13,14,15,16,20]]
    by_b={r['box']:r for r in rows}
    tolerances={11:F(1),14:F(1,10),16:F(1,100)}
    for b,t in tolerances.items():
        require(by_b[b]['full_to_finite_Gamma_error']<t,'full law and test approximation')
        require(by_b[b-1]['full_to_finite_Gamma_error']>=t,'previous uniform box fails this sufficient bound')
    r20=by_b[20]
    old_wt=sources['certificates/weighted_kernel_tails_certificate.json']
    require(old_wt['W']==483,'original full-mask criterion coefficient')
    D_ratio=D13/F(old_wt['incoming_law']['Haar_density_bound'])
    G_ratio=G13/F(old_wt['incoming_law']['complete_square_bound'])
    eps=[D_ratio*(F(row['old_cofactor_tail_error'])+F(row['mixed_current_depth_tail_error']))
         +G_ratio*F(row['pure_current_depth_tail_error']) for row in old_wt['steps']]
    mask=F(59,45)*eps[0]+eps[1]+483*(2*eps[0]+eps[1])
    incoming=F(5251,2880)*r20['normalized_weighted_error']+483*r20['normalized_L1_error']
    test19=test_tail([3,5,7,11,13,17,19],20,F(18,5)*D13)
    allowance=mask+incoming+test19;safe=F(263,1000)
    require(allowance<safe,'complete finite-reference allowance below .263')
    require(F(5251,2880)==F(89,64)*F(59,45),'normalized-kernel weighted propagation')
    result=encode(dict(
        schema='erdos7-actual-ap-core-stability-v1',source_sha256=PINS,
        scope='Every finite actual distinct family on3,5,7,11,13; full uniform357 source and actual pure-base11/4,13/6 kernels, one final conditioning. The core deletes original forbidden labels outside the exponent box; every test tail is paid. No AO-law substitution, no computed finite-core maximum, no unrestricted Erdos7 or Lean endpoint.',
        source_inputs=dict(G357=G0,D357=D0,Gamma13=G13,D13=D13,rho13=rho),
        rows=rows,certified_tolerances=tolerances,
        full_finite_reference=dict(incoming_box=20,future_old_cofactor_box=20,
            future_current_forbidden_depth=8,test_box=20,primes=[3,5,7,11,13,17,19],
            weighted_incoming_propagation=F(5251,2880),W=483,
            complete_mask_allowance=mask,mask_source_D_ratio=D_ratio,mask_source_G_ratio=G_ratio,mask_step_epsilons=eps,
            incoming_law_allowance=incoming,test_tail_allowance=test19,
            total_allowance=allowance,safe_allowance=safe,safety_slack=safe-allowance,
            criterion='For every complete box20 test: E_finite[L_box^2-1]+483*B_finite <=483-.263.',
            implication='If the finite criterion holds for every original finite core pattern, the corresponding full actual17/19 law has positive survivor mass and supported Gamma19<=484. The finite maximum is not computed and the later-prime continuation is not supplied.',
            actual_reference='Actual AP13 law of the retained original core, then original17/19 kernels with only box20 cofactors/currentdepth8/puredepth8 constraints; all law and test periods are lifted uniformly to the common box20 period.')))
    if args.write:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
    else:require(json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique)==result,'entire certificate equality')
    print('PASS actual AP finite-core: errors '+str({b:float(by_b[b]['full_to_finite_Gamma_error']) for b in tolerances})+
          '; complete W483 allowance '+str(float(allowance))+' < .263')

if __name__=='__main__':main()
