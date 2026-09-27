#!/usr/bin/env python3
"""Exact complete-suffix deletion and joint-penalty PA query bounds.

Report569 proves the arbitrary-family comparison. Full geometric first
moments retain all heights; only atoms below thresholds need enumeration.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial, prod
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


def shared_ternary_union(bound):
    """Actual irredundant input refuting automatic additive certification."""
    primes = (5,7,11,13,17,19)
    pure = ((3,2),(9,4),(27,19),(81,37))

    def crt(coordinates):
        value,modulus = 0,1
        for m,a in coordinates:
            value += modulus*((a-value)*pow(modulus,-1,m)%m)
            modulus *= m
        return value%modulus

    originals = [dict(m=m,a=a,kind='pure3') for m,a in pure]
    for p in primes:
        for e,old,phase in ((0,0,0),(1,0,1),(3,1,2)):
            originals.append(dict(m=3**e*p,a=crt(((3**e,old),(p,phase))),
                                  kind='mixed',p=p,e=e,old=old,phase=phase))
    survivor = [x for x in range(81) if all(x%m != a for m,a in pure)]
    check('shared_union_22_distinct_originals',len(originals) == len({r['m'] for r in originals}) == 22)
    check('shared_union_pure_survivor',len(survivor) == 41)
    check('shared_union_pure_disjoint',all(not set(range(a,81,m))&set(range(b,81,n))
          for i,(m,a) in enumerate(pure) for n,b in pure[i+1:]))
    check('shared_union_untouched_root',all(x in survivor for x in range(0,81,3)))
    check('shared_union_untouched_cylinder',all(x in survivor for x in range(1,81,27)))
    for row in originals:
        roots = {p:3 for p in primes}
        old = row['a'] if row['kind'] == 'pure3' else row['old']
        if row['kind'] == 'mixed':
            roots[row['p']] = row['phase']
        witness = crt(((81,old),)+tuple((p,roots[p]) for p in primes))
        check('shared_union_private_'+str(row['m']),
              [r['m'] for r in originals if witness%r['m'] == r['a']] == [row['m']])
        row['private_witness'] = witness
    weights = (F(1),F(27,41),F(3,41))
    local_minima = {}
    for p in primes:
        candidates = []
        for k in range(3):
            for chosen in combinations(range(3),k):
                residual = sum((weights[i] for i in range(3) if i not in chosen),F())
                candidates.append((residual/(p-k),chosen))
        optimum = min(v for v,_ in candidates)
        check('shared_union_selector_'+str(p),optimum == F(3,41*(p-2)) and
              [a for v,a in candidates if v == optimum] == [(0,1)])
        local_minima[p] = optimum
    for q,_,cap in ROWS:
        check('shared_union_actual_pa_cap_'+str(q),F(q,q-2) <= cap)
    r3 = F(81,82)
    rq = prod(1+F(p,(p-1)*(p-2)) for p in primes)-1
    envelope = sum(local_minima.values(),F())
    gate = 1-F(49,566)*(1+2*bound)
    refined_gate = 1-F(49,566)*(r3+(1+r3)*bound)
    loss = F(3,41)*(1-prod(F(p-3,p-2) for p in primes))
    mass = (566*(1-loss)-49*(1+2*bound))/567
    density = F(81,41)*prod(F(p,p-2) for p in primes)
    haar = mass/density*F(21,22)*F(27,28)
    check('shared_union_law_has_full_query_budget',rq < bound)
    check('shared_union_exact_envelope',envelope == F(7244,115005))
    check('shared_union_exact_loss',loss == F(47063,1035045))
    check('shared_union_envelope_fails_both_gates',loss < gate < refined_gate < envelope)
    check('shared_union_exact_density',density == F(1729,205))
    check('shared_union_nine_head_haar',haar > F(1,5500))
    return dict(scope='Twenty-two fixed actual originals; limitation of the weighted-max additive sufficient certificate, repaired by their actual union under the same law. Not an odd covering.',
                originals=originals,period=81*prod(primes),ternary_weights=weights,
                ternary_query=r3,q_query=rq,local_envelope_minima=local_minima,
                envelope_minimum=envelope,universal_gate=gate,refined_gate=refined_gate,
                actual_union=loss,source_density=density,nine_head_mass=mass,nine_head_haar=haar)


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
    # A finite cofactor window: only small d need the five-level phase
    # restriction. For larger d, select e=0,1 and pay the remaining tower
    # with the SAME PA law's Haar density bound.
    primes = (5,7,11,13,17,19)
    reciprocal_total = prod(F(p,p-1) for p in primes)-1
    density = 9/min(row['alpha'] for row in corners)
    windows = []
    for cutoff,expected_count in ((200000,399),(500000,534)):
        values = [1]
        for p in primes:
            extended = []
            for n in values:
                while n <= cutoff:
                    extended.append(n)
                    n *= p
            values = extended
        nonunit = sorted(n for n in values if n > 1)
        check('window_unique_'+str(cutoff),len(nonunit) == len(set(nonunit)) == expected_count)
        reciprocal_tail = reciprocal_total-sum((F(1,n) for n in nonunit),F())
        delta = joint/243+F(80,243)*density*reciprocal_tail
        live = (566*(1-delta)-49*seven_bound)/567
        haar = live/(2*density*extension_density)
        check('window_tail_positive_'+str(cutoff),reciprocal_tail > 0)
        check('window_residual_positive_'+str(cutoff),0 < delta < residual_limit)
        check('window_haar_positive_'+str(cutoff),haar > F(1,150000))
        windows.append(dict(cofactor_cutoff=cutoff,nonunit_count=len(nonunit),
                            cofactors=nonunit,reciprocal_tail=reciprocal_tail,
                            residual_upper=delta,survivor_reserve=live,haar_lower=haar))
    tail_cutoff,ell = 1000000,12
    head_primes = (3,)+primes+(23,29)
    moment2 = prod(F(p*(p+1),(p-1)**2) for p in head_primes)
    c = F(2*ell*ell+1,2*ell*ell-1)
    polynomial = sum((F(factorial(7),factorial(7-j)*ell**j) for j in range(8)),F())
    tau = c**7/tail_cutoff*F(tail_cutoff,tail_cutoff-3)**2*polynomial
    tail_charge = moment2*tau
    check('nine_head_second_moment',moment2 == F(14003665,540672))
    check('large_tail_analytic_parameters',tail_cutoff >= 286 and ell >= 4 and 3**ell <= tail_cutoff)
    check('large_tail_full_five_level_margin',phase_tails[4]['haar_lower']-tail_charge > F(1,12000))
    check('large_tail_finite_window_margin',windows[1]['haar_lower']-tail_charge > F(1,60000))
    large_tail = dict(scope='Chapter33 joint-load transfer, with its inherited analytic prime-product premise. All outside primes strictly above cutoff, arbitrary finite heights and original supports. Remaining mass is distorted, not Haar.',
                      cutoff=tail_cutoff,ell=ell,c=c,head_primes=head_primes,
                      moment2=moment2,tau=tau,tail_charge=tail_charge,
                      full_five_level_remaining=phase_tails[4]['haar_lower']-tail_charge,
                      finite_window_remaining=windows[1]['haar_lower']-tail_charge)
    joint_union_example = shared_ternary_union(joint)
    result = dict(scope='Arbitrary finite two-copy family on Q={5,7,11,13,17,19}; one actual PA law, complete queries at every height. Nine-prime consumers impose explicit projection or residual conditions; finite-window and large-prime-tail versions retain their stated restrictions. Not unrestricted Erdos7 or an arbitrary ternary-prefix transfer.',
                  suffixes=suffixes,coefficients=coefficients,corners=corners,
                  simple_bound=simple,joint_bound=joint,
                  simple_bound_decimal=float(simple),joint_bound_decimal=float(joint),
                  target=F(257,51),strict_gap_to_target=F(257,51)-joint,
                  restricted_nine=dict(seven_query_bound=seven_bound,outside_charge=outside_charge,
                                       survivor_reserve=reserve,haar_lower=haar_lower),
                  weighted_projection=weighted_projection,
                  finite_cofactor_windows=windows,large_prime_tail=large_tail,
                  shared_ternary_union=joint_union_example,
                  checks=checks,check_count=len(checks))
    args.output.write_text(json.dumps(result,default=str,indent=2)+'\n')
    print('simple_bound',simple,float(simple))
    print('joint_bound',joint,float(joint))
    print('gap_to_target',F(257,51)-joint)
    print('checks',len(checks))


if __name__ == '__main__':
    main()
