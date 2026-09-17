#!/usr/bin/env python3
"""Exact generic uniform357 pure-root profile and unchanged AP(4,6) continuation.

All missing-prime and missing/ineffective-modulus9 branches are retained.
The proof is ordinary mathematics; no finite enumeration proves arbitrary heights.
Default: validate the existing certificate. Use --write to regenerate it.
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

HERE=Path(__file__).resolve().parent
P=(3,5,7)
PINS={
    'certificates/uniform_gamma_cofactor_certificate.json':'c443ac33dab710c3651c7785135e8b47f69511c3418727afec446b07934fff48',
    'certificates/star_block_obstruction_certificate.json':'a378fed7d44cb1dd77fa81b9d9888cc248014011bf8a25aafeeceab8166a1907',
    'certificates/joint_density_certificate.json':'de89179f6a15e78501c7568f3df125c3af53cb9d176066e6937eca9932878b9c',
    'certificates/arbitrary_head_profile_certificate.json':'afd62721adaa0800421ea3fbcc9ce99c76ad6e7fda7526ac73194a9e6aeae65e',
    'certificates/weighted_kernel_tails_certificate.json':'c1e64e46884a7a4e226222aea4394fae98e5f159fe4e2e366a5b17fbbc95f240',
}


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


def branch(case,present5,present7,G0,R0,s0,fallback):
    present=(case!='modulus3_absent',present5,present7)
    lower3={'modulus3_absent':F(5,6),'modulus9_absent_or_ineffective':F(11,18),
            'modulus9_effective':F(1,2)}[case]
    lower5=F(3,4) if present5 else F(19,20)
    lower7=F(5,6) if present7 else F(41,42)
    upper3={'modulus3_absent':F(1),'modulus9_absent_or_ineffective':F(2,3),
            'modulus9_effective':F(5,9)}[case]
    reference_masses=[upper3,F(4,5) if present5 else F(1),
                      F(6,7) if present7 else F(1)]
    G=G0 if case=='modulus9_effective' else F(fallback[case]['three_prime_square'])
    R35=F(15,7) if case=='modulus9_effective' else F(fallback[case]['old_cylinder_cap'])
    s35=lower3*lower5-F(1,8)
    require(s35>0 and lower7-R35/6>0,'positive pair recurrence inputs')
    density_candidates=dict(
        CM8=s0,
        absent_prime_union=-F(3,16)+sum((F(1,p) for p,on in zip(P,present) if not on),F()),
        CM1_actual_pure_product=F(53,135)*lower3*lower5*lower7,
        same_uniform_pair_recurrence=s35*(lower7-R35/6),
        CM2_linear_numerator=F(53,162)*lower3*lower5+(lower7-F(5,6))*s35)
    density=max(density_candidates.values())
    D=1/density
    reference_mass=prod(reference_masses)
    mean=prod(1+1/u/F(p-1) for p,u in zip(P,reference_masses))
    # Exact product probabilities only at product values <=12. The full
    # mean supplies every omitted product tail in each hinge evaluation.
    dist={1:F(1)}
    for p,u in zip(P,reference_masses):
        c=1/u
        require(c<=p,'valid geometric tail domination')
        new=defaultdict(F)
        for n,w in dist.items():
            for v in range(1,13//n+1):
                probability=1-c/p if v==1 else c*F(p-1,p**v)
                new[n*v]+=w*probability
        dist=dict(new)
    raw={h:D*reference_mass*(mean-h+sum(((h-n)*w for n,w in dist.items() if n<h),F()))
         for h in range(1,13)}
    profile=dict(raw)
    profile[1]=min(profile[1],R0)
    profile[2]=min(profile[2],(G-1+17*R0)/30)
    profile[3]=min(profile[3],(G-1+2*R0)/15)
    return dict(ternary_case=case,modulus5_present=present5,modulus7_present=present7,
                actual_pure_density_lowers=[lower3,lower5,lower7],
                reference_pure_masses=reference_masses,reference_mass=reference_mass,
                pair_survivor_lower=s35,pair_R_upper=R35,
                density_candidates=density_candidates,survivor_density_lower=density,
                uniform357_Haar_density_bound=D,uniform357_square_bound=G,
                product_mean=mean,product_distribution_through12=dist,
                raw_root_hinges=raw,profile=profile)


def continuation(profile,G,R,D0):
    M=1+R
    def H(t):
        if t<=1: return M-t
        n=t.numerator//t.denominator
        return profile[n] if t==n else (n+1-t)*profile[n]+(t-n)*profile[n+1]
    c11,c13=F(5,3),F(2)
    b11=H(F(4))/6
    cost=F()
    for n in range(1,7):
        pn=1-c11/11 if n==1 else c11*F(10,11**n)
        cost+=pn*n*H(F(6,n))
    tail_mass=c11/F(11**6)
    tail_mean=tail_mass*(7+F(1,10))
    cost+=M*tail_mean-6*tail_mass
    b13=cost/6
    # Different exact decomposition, with n>=6 all in the affine tail.
    closed=(F(28,33)*profile[6]+F(100,363)*profile[3]
            +F(19300,483153)*profile[2]+F(887,322102)*R+F(1,966306))/6
    require(b13==closed,'independent closed13 charge identity')
    rho=1-b11-b13
    physical=G*(1+F(32,100)*c11)*(1+F(38,144)*c13)
    require(rho>0,'actual final conditioning is justified')
    return dict(T11=4,T13=6,c11=c11,c13=c13,b11=b11,b13=b13,
                survival_lower=rho,physical_square=physical,
                supported_square=1+(physical-1)/rho,
                supported_Haar_density=D0*c11*c13/rho)


def prefix_fixtures():
    # Enumerate every one-coordinate layout at these finite heights,
    # independently of the capped-tail distribution construction.
    cases=[(3,3,set(range(27))),
           (3,3,{x for x in range(27) if x%3!=0}),
           (3,3,{x for x in range(27) if x%3!=0 and x%9!=4}),
           (5,2,{x for x in range(25) if x%5!=0}),
           (7,2,{x for x in range(49) if x%7!=0})]
    count=0
    for p,height,allowed in cases:
        N=p**height;u=F(len(allowed),N);c=1/u
        for layout in product(*(range(p**e) for e in range(1,height+1))):
            counts=defaultdict(int)
            for x in allowed:
                value=1+sum(x%(p**e)==a for e,a in enumerate(layout,1))
                counts[value]+=1
            for h in range(1,height+2):
                actual=sum(F(n,len(allowed))*max(0,v-h) for v,n in counts.items())
                # Finite K tail c*p^-e for1<=e<=height, zero afterwards.
                cap=sum((F(1,p**e)*c for e in range(max(1,h),height+1)),F())
                require(actual<=cap,'literal pure-prefix convex comparison fixture')
            count+=1
    return count


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',nargs='?',type=Path,default=HERE/'certificates/pure_root_profile_certificate.json')
    parser.add_argument('--source-directory',type=Path,default=HERE)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    source={}
    for name,pin in PINS.items():
        raw=read_artifact_bytes(args.source_directory/name)
        require(sha256(raw).hexdigest()==pin,'source SHA-256: '+name)
        source[name]=json.loads(raw,object_pairs_hook=unique)
    cofactor=source['certificates/uniform_gamma_cofactor_certificate.json']['signed_two_level_three_prime_parameters']
    G=F(cofactor['Gamma357_upper'])
    fallback={row['case']:row for row in cofactor['missing_pure_cases']}
    R=F(source['certificates/joint_density_certificate.json']['improved_R_bound'])
    s0=F(source['certificates/star_block_obstruction_certificate.json']['cm1_actual_head_sharpness']['infimum_ambient_uncovered_density'])
    require((G,R,s0)==(F(3849,106),F(1649,360),F(53,432)),'same uniform357 source bounds')
    cases=('modulus3_absent','modulus9_absent_or_ineffective','modulus9_effective')
    rows=[branch(case,p5,p7,G,R,s0,fallback) for case in cases for p5,p7 in product((False,True),repeat=2)]
    envelope={h:max(row['profile'][h] for row in rows) for h in range(1,13)}
    worst=rows[-1]
    require(envelope==worst['profile'],'all twelve branches dominated at every retained hinge')
    require(envelope[3]==F(6759,2597) and envelope[4]==F(776841,454475)
            and envelope[6]==F(1501750547,1670195625),'new exact generic hinges')
    law=continuation(envelope,G,R,1/s0)
    require(law['supported_square']==F(8416748733302130673,43949004608153173),
            'new same-law supported13 square bound')
    require(law['survival_lower']==F(43949004608153173,99601923308580000),
            'new same-law supported13 survival lower')
    old=source['certificates/arbitrary_head_profile_certificate.json']['selected_actual_law']
    require(law['supported_square']<F(old['supported_square']) and
            law['survival_lower']>F(old['survival_lower']), 'strict same-law improvement')
    Kphysical=F(source['certificates/arbitrary_head_profile_certificate.json']['physical_fourth13'])
    fourth13=1+(Kphysical-1)/law['survival_lower']
    g13=law['supported_square']
    charge17=g13/256
    survival17=1-charge17
    require(survival17>0,'separate full-Haar17 survivor normalization')
    physical17=F(89,64)*g13
    supported17=1+(physical17-1)/survival17
    old_wt=source['certificates/weighted_kernel_tails_certificate.json']
    require(F(old_wt['incoming_law']['Haar_density_bound'])==F(old['supported_Haar_density'])
            and F(old_wt['incoming_law']['complete_square_bound'])==F(old['supported_square']),
            'WT source is the same old supported AP(4,6) law')
    D_ratio=law['supported_Haar_density']/F(old['supported_Haar_density'])
    G_ratio=g13/F(old['supported_square'])
    tail_rows=[]
    for row in old_wt['steps']:
        errors=dict(old_cofactor_tail_error=D_ratio*F(row['old_cofactor_tail_error']),
                    mixed_current_depth_tail_error=D_ratio*F(row['mixed_current_depth_tail_error']),
                    pure_current_depth_tail_error=G_ratio*F(row['pure_current_depth_tail_error']))
        tail_rows.append(dict(prime=row['prime'],epsilon=sum(errors.values()),**errors))
    require([row['prime'] for row in tail_rows]==[17,19], 'same WT steps and order')
    e17,e19=[row['epsilon'] for row in tail_rows]
    wt_square=F(59,45)*e17+e19
    wt_charge=2*e17+e19
    allowance=wt_square+483*wt_charge
    safe_allowance=F(294,1000)
    require(allowance<safe_allowance,'same-law mask allowance below .294')
    result=encode(dict(
        schema='erdos7-generic-pure-root-profile-v1',source_sha256=PINS,
        scope='Same actual uniform357 law and unchanged AP(4,6)11/13 kernels. All arbitrary finite heights, actual residue choices and missing classes retained. Twelve ternary/root branches; original tests are complete. Ordinary proof and exact numerical certificate, not Lean or unrestricted Erdos7 noncoverage.',
        source_inputs=dict(G=G,R=R,survivor_density_lower=s0),branches=rows,
        generic_integer_hinges=envelope,selected_actual_law=law,
        previous_same_law=old,
        supported_square_improvement=F(old['supported_square'])-law['supported_square'],
        same_law_fourth=dict(physical_fourth13=Kphysical,supported_fourth13=fourth13),
        separate_full_Haar17=dict(kernel='full-Haar T4, delta=1/2; separate from WT AP17/8',
             assigned_bad_upper=charge17,survival_lower=survival17,
             physical_square=physical17,supported_square=supported17),
        same_law_weighted_mask_tails=dict(
             kernel='Pure-base AP17/8 and AP19/8; fixed old box20 and current depth8',
             D_ratio=D_ratio,G_ratio=G_ratio,steps=tail_rows,
             physical_and_final_killed_weighted_error=wt_square,
             assigned_charge_sum_error=wt_charge,total_criterion_allowance=allowance,
             safe_allowance=safe_allowance,safety_slack=safe_allowance-allowance,
             reference_criterion='For every complete original L: E_ref[L^2-1]+483*B_ref <=483-.294.',
             scope='Only17/19 forbidden masks reduced; incoming actual AP13 law and all original test labels remain full. Reference correlation criterion is not supplied.'),
        literal_one_coordinate_layout_fixtures=prefix_fixtures(),
        open_mathematical_obligations='No 17/19 joint correlation certificate or later-prime continuation is supplied here.'))
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
    else:
        actual=json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique)
        require(actual==result,'entire saved certificate equals exact recomputation')
    print('PASS generic 12-branch pure-root profile: Gamma13='+str(law['supported_square'])+
          ' = '+str(float(law['supported_square']))+'; rho13='+str(float(law['survival_lower'])))


if __name__=='__main__': main()
