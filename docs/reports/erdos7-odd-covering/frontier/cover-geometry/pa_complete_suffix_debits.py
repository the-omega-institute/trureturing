#!/usr/bin/env python3
"""Exact complete-suffix deletion and joint-penalty PA query bounds.

Report569 proves the arbitrary-family comparison. Full geometric first
moments retain all heights; only atoms below thresholds need enumeration.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


ROWS = ((11,2,F(5,3)),(13,2,F(3,2)),(17,4,F(2)),(19,4,F(9,5)))
checks = {}


def check(name, condition):
    if name in checks or not condition:
        raise ValueError(name)
    checks[name] = True


def coordinate(p, mass, cap):
    return mass, mass+cap/(p-1), {
        1:mass-cap/p, 2:cap*F(p-1,p*p), 3:cap*F(p-1,p**3)}


def multiply(a,b):
    low = defaultdict(F)
    for i,w in a[2].items():
        for j,v in b[2].items():
            if i*j < 4:
                low[i*j] += w*v
    return a[0]*b[0],a[1]*b[1],dict(low)


def hinge(law, threshold):
    return law[1]-threshold*law[0]+sum(
        ((threshold-i)*w for i,w in law[2].items() if i < threshold),F())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    suffixes = []
    for start in range(5):
        law = (F(1),F(1),{1:F(1)})
        for p,_,cap in ROWS[start:]:
            law = multiply(law,coordinate(p,F(1),cap))
        suffixes.append(dict(mass=law[0],mean=law[1],low=law[2],zeta=hinge(law,3)))
    expected_zeta = (F(208872886945,1638469417728),F(554975819,11284224640),
                     F(120619,8346320),F(1,3610),F())
    for i,row in enumerate(suffixes):
        check('suffix_hinge_'+str(i),row['zeta'] == expected_zeta[i])
    coefficients = []
    for i,(q,t,cap) in enumerate(ROWS):
        future = suffixes[i+1]
        eta = future['mean']/(q-1)-F(q+1,q*q)*future['low'][1]-future['low'].get(2,F())/q
        check('suffix_cap_slope_identity_'+str(q),suffixes[i]['zeta'] == future['zeta']+cap*eta)
        check('positive_eta_'+str(q),eta > 0)
        coefficients.append(dict(q=q,t=t,cap=cap,a=2*cap/(q-1),eta=eta,zeta=future['zeta']))
    corners = []
    for index,(x,y) in enumerate(product((F(1,2),F(1)),(F(2,3),F(1)))):
        law = multiply(coordinate(5,x,F(1)),coordinate(7,y,F(1)))
        prefix = x*y-F(1,12)
        deletion = suffixes[0]['zeta']/12
        joint = F()
        stages = []
        for row in coefficients:
            q,t,cap,a,eta = (row[k] for k in ('q','t','cap','a','eta'))
            full_hinge = hinge(law,t)
            charge = a*full_hinge
            d = {n:eta*(cap-F(q-1,q-1-2*n)) for n in range(1,t)}
            credit = sum((d[n]*law[2].get(n,F()) for n in d),F())-d[1]*(law[0]-prefix)
            check(f'positive_joint_{index}_{q}',credit > 0)
            stages.append(dict(q=q,prefix_lower=prefix,auxiliary_mass=law[0],
                               low_atoms=law[2],F=full_hinge,charge=charge,
                               d=d,J=credit,deletion=row['zeta']*charge))
            deletion += row['zeta']*charge
            joint += credit
            prefix -= charge
            check(f'positive_prefix_{index}_{q}',prefix > 0)
            law = multiply(law,coordinate(q,F(1),cap))
        phi = hinge(law,3)
        alpha = prefix
        simple_bound = 2+(phi-deletion)/alpha
        joint_bound = 2+(phi-deletion-joint)/alpha
        check('strict_target_simple_'+str(index),simple_bound < F(257,51))
        check('strict_target_joint_'+str(index),joint_bound < simple_bound)
        corners.append(dict(x=x,y=y,stages=stages,alpha=alpha,Phi=phi,
                            deletion=deletion,J=joint,
                            simple_bound=simple_bound,joint_bound=joint_bound,
                            simple_bound_decimal=float(simple_bound),
                            joint_bound_decimal=float(joint_bound),
                            target_margin=F(155,51)*alpha-phi+deletion,
                            joint_target_margin=F(155,51)*alpha-phi+deletion+joint))
    simple = max(row['simple_bound'] for row in corners)
    joint = max(row['joint_bound'] for row in corners)
    check('worst_corner_simple',simple == corners[0]['simple_bound'])
    check('worst_corner_joint',joint == corners[0]['joint_bound'])
    check('exact_simple_target_margin',corners[0]['target_margin'] ==
          F(25377570437213856497,13573383773301031680000))
    check('exact_joint_target_margin',corners[0]['joint_target_margin'] ==
          F(53066757345018132083,14287772392948454400000))
    for label,bound in (('simple',simple),('joint',joint)):
        lam = bound-2
        check(label+'_anchor_slope',lam >= suffixes[0]['zeta'])
        for i,row in enumerate(corners):
            gain = row['deletion']+(row['J'] if label == 'joint' else 0)
            check(label+'_corner_certificate_'+str(i),lam*row['alpha']-row['Phi']+gain >= 0)
        for row in coefficients:
            check(label+'_row_slope_'+str(row['q']),lam-row['zeta'] >= row['cap']*row['eta'])
    # Convex branch and actual-row equality checks at interior rational
    # points supplement (and do not replace) the analytic derivative proof.
    lam = joint-2
    for row in coefficients:
        q,t,cap,a,eta,zeta = (row[k] for k in ('q','t','cap','a','eta','zeta'))
        weight = lam-zeta
        def psi(u):
            if u < t:
                return eta*(F(q-1)/(q-1-2*u)-cap)
            return weight*a*(u-t)
        check('threshold_match_'+str(q),psi(F(t)) == 0)
        for i in range(17):
            g = F(i,16)
            loss = max(F(),1-cap*g)
            kappa = cap if not g else min(cap,1/g)
            check(f'actual_penalty_{q}_{i}',weight*loss-eta*(cap-kappa) ==
                  psi(F(q-1,2)*(1-g)))
    seven_bound = 1+2*joint
    outside_charge = (1+seven_bound)*F(51,616)
    reserve = 1-outside_charge
    haar_lower = reserve*min(row['alpha'] for row in corners)/18
    check('restricted_seven_query_target',seven_bound < F(565,51))
    check('restricted_nine_positive_reserve',reserve > 0)
    check('restricted_nine_haar_bound',haar_lower > F(1,30000))
    # Reuse Report463's actual pure23/29 conditioning. After a residual
    # P-only deletion of mass delta, retain both mass s and unnormalized
    # query sum A: the unit old cofactor then costs s, not one.
    extension_density = F(22,21)*F(28,27)
    pure_extension_charge = (49*seven_bound+1)/567
    residual_limit = 1-49*seven_bound/566
    check('positive_residual_budget',residual_limit > 0)
    check('pure_extension_improves_free_extension',pure_extension_charge < outside_charge)
    phase_tails = []
    for h in range(1,9):
        delta = joint/3**h
        live = (566*(1-delta)-49*seven_bound)/567
        direct_live = 1-delta-pure_extension_charge
        haar = live*min(row['alpha'] for row in corners)/(18*extension_density)
        check('unit_mass_credit_'+str(h),live-direct_live == delta/567)
        check('phase_tail_sign_'+str(h),(live > 0) == (h >= 5))
        phase_tails.append(dict(head_height=h,residual_upper=delta,
                               survivor_reserve=live,haar_lower=haar))
    check('five_level_exact_haar',phase_tails[4]['haar_lower'] ==
          F(15786622554865812862151,113225721562358906941440000))
    check('five_level_haar_bound',phase_tails[4]['haar_lower'] > F(1,8000))
    weighted_projection = dict(
        scope='For each nonunit Q cofactor, at most two projected phases through ternary exponent5; all deeper projected phases and all23/29 originals arbitrary. More generally, the same-law residual deletion bound must be below residual_limit.',
        seven_query_bound=seven_bound,pure_extension_charge=pure_extension_charge,
        residual_limit=residual_limit,extension_density=extension_density,
        phase_tails=phase_tails)
    result = dict(scope='Arbitrary finite two-copy family on Q={5,7,11,13,17,19}; one actual PA law, complete queries at every height. Restricted nine-prime consumer requires at most two distinct projected residues per nonunit Q cofactor after removing powers of3 from P-only originals. Not unrestricted Erdos7 or an arbitrary ternary-prefix transfer.',
                  suffixes=suffixes,coefficients=coefficients,corners=corners,
                  simple_bound=simple,joint_bound=joint,
                  simple_bound_decimal=float(simple),joint_bound_decimal=float(joint),
                  target=F(257,51),strict_gap_to_target=F(257,51)-joint,
                  restricted_nine=dict(seven_query_bound=seven_bound,outside_charge=outside_charge,
                                       survivor_reserve=reserve,haar_lower=haar_lower),
                  weighted_projection=weighted_projection,
                  checks=checks,check_count=len(checks))
    args.output.write_text(json.dumps(result,default=str,indent=2)+'\n')
    print('simple_bound',simple,float(simple))
    print('joint_bound',joint,float(joint))
    print('gap_to_target',F(257,51)-joint)
    print('checks',len(checks))


if __name__ == '__main__':
    main()
