#!/usr/bin/env python3
"""Exact AP(4,6) restart: weighted 17/19 forbidden-mask tails, not old-law truncation.

The universal inequalities are ordinary mathematics in the adjacent proof.
This program checks their exact constants and finite coefficient fixtures.
By default validate the existing certificate. Writing requires --write.
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

HERE = Path(__file__).resolve().parent
SOURCE_NAME = 'certificates/arbitrary_head_profile_certificate.json'
SOURCE_SHA256 = 'afd62721adaa0800421ea3fbcc9ce99c76ad6e7fda7526ac73194a9e6aeae65e'


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate certificate key: ' + key)
        result[key] = value
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def phi(p, a):
    return F((a + 1)**2) + F(2 * (a + 1), p - 1) + F(p + 1, (p - 1)**2)


def sigma(p):
    return F(p * (p*p + 4*p + 1), (p - 1)**3)


def sigma_head(p, b):
    return sum((F(1, p**a) * phi(p, a) for a in range(b + 1)), F())


def params(p):
    delta = F(7, p - 2)
    C = 1 / (1 - delta)
    s = F(p - 2, p - 1)
    lip = max(C*C, C/delta)
    return delta, C, s, lip


def coefficients(alpha, delta):
    good = 1 / (1 - min(alpha, delta))
    bad = max(F(), alpha-delta) / (alpha*(1-delta)) if alpha else F()
    return good, bad


def coefficient_fixtures():
    mixed_count = 0
    pure_count = 0
    for p in (17, 19):
        delta, C, s, lip = params(p)
        grid = sorted({F(i, 48) for i in range(49)} | {delta})
        for alpha in grid:
            good, bad = coefficients(alpha, delta)
            require(0 <= bad <= good <= C, 'coefficient range')
            require((1-alpha)*good + alpha*bad == 1, 'physical row normalization')
            for alpha0 in grid:
                if alpha0 > alpha:
                    continue
                g0, b0 = coefficients(alpha0, delta)
                d = alpha-alpha0
                require(abs(good-g0) <= lip*d and abs(bad-b0) <= lip*d,
                        'common-region coefficient Lipschitz')
                require(abs(bad-g0) <= C + lip*d and g0 <= C + lip*d,
                        'changed-region physical and killed bounds')
                mixed_count += 1
        # Literal uniform spaces; k <= k0 are nested pure-survivor sizes.
        # r and t count raw mixed-bad points in the common and extra regions.
        for n in range(1, 25):
            sizes = [k for k in range(1, n+1) if F(k, n) >= s]
            for k0 in sizes:
                for k in sizes:
                    if k > k0:
                        continue
                    lam, lam0, kappa = F(k,n), F(k0,n), F(k0-k,n)
                    for r in range(k+1):
                        for t in range(k0-k+1):
                            alpha, alpha0 = F(r,k), F(r+t,k0)
                            require(abs(alpha-alpha0) <= kappa/lam0,
                                    'nested pure-law total variation')
                            good, bad = coefficients(alpha,delta)
                            g0, b0 = coefficients(alpha0,delta)
                            bound = (lip+C)*kappa/(s*s)
                            require(abs(good/lam-g0/lam0) <= bound and
                                    abs(bad/lam-b0/lam0) <= bound,
                                    'common pure-region density bound')
                            require(max(g0,b0)/lam0 <= C/s,
                                    'changed pure-region density bound')
                            pure_count += 1
    return dict(mixed_nested_mask_cases=mixed_count, pure_nested_base_cases=pure_count,
                meaning='Finite regression fixtures only; universal bounds use the ordinary proof.')


def prefix_fixtures():
    count = 0
    for p in (3,5,7,11,13,17,19):
        for a in range(7):
            for h in range(a, a+4):
                literal = sum((F(1,p**max(a,i,j)) for i in range(h+1)
                               for j in range(h+1)), F())
                omitted = F(1,p**h) * (F(2*h+3,p-1) + F(2,(p-1)**2))
                require(literal + omitted == F(1,p**a)*phi(p,a),
                        'localized pair sum including its full infinite tail')
                count += 1
        # A nonrecursive exact identity checks the infinite third sum.
        x = F(1,p)
        geometric = (1+x)/(1-x)**3 + F(2,p-1)/(1-x)**2 + F(p+1,(p-1)**2)/(1-x)
        require(geometric == sigma(p), 'full localized energy series')
    return count


def step(p, old_primes, D, J, b=20, h=8):
    delta, C, s, lip = params(p)
    factors = {q:dict(phi0=phi(q,0), sigma=sigma(q), head=sigma_head(q,b))
               for q in old_primes}
    all_old = prod(factors[q]['sigma'] for q in old_primes)
    head_old = prod(factors[q]['head'] for q in old_primes)
    unit_old = prod(factors[q]['phi0'] for q in old_primes)
    old_tail = all_old-head_old
    nonunit = all_old-unit_old
    head_nonunit = head_old-unit_old
    tail0 = F(1,(p-1)*p**h)
    tail_phi = sigma(p)-sigma_head(p,h)
    theta = (C/s)*(sigma(p)-phi(p,0)) + (lip/(s*s))*phi(p,0)/F(p-1)
    old_error = D*old_tail*theta
    mixed_error = D*head_nonunit*((C/s)*tail_phi + (lip/(s*s))*phi(p,0)*tail0)
    pure_error = J*((C/s)*tail_phi + ((lip+C)/(s*s))*phi(p,0)*tail0)
    total = old_error+mixed_error+pure_error
    require(min(old_tail,nonunit,tail0,tail_phi,total) > 0, 'positive tail quantities')
    return dict(prime=p, old_primes=old_primes, old_Haar_density_bound=D,
                old_complete_square_bound=J, threshold=8, delta=delta,
                pure_density_cap=C, pure_survivor_Haar_floor=s,
                full_Haar_density_cap=C/s, coefficient_Lipschitz=lip,
                old_exponent_box=b, current_depth_cutoff=h,
                old_prime_factors=factors, old_energy_product=all_old,
                old_energy_head_product=head_old, old_energy_tail=old_tail,
                old_unit_cofactor_energy=unit_old, old_nonunit_cofactor_energy=nonunit,
                old_head_nonunit_cofactor_energy=head_nonunit,
                current_probability_tail=tail0, current_energy_tail=tail_phi,
                theta=theta, old_cofactor_tail_error=old_error,
                mixed_current_depth_tail_error=mixed_error,
                pure_current_depth_tail_error=pure_error, epsilon=total)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=HERE/'certificates/weighted_kernel_tails_certificate.json')
    parser.add_argument('--source-certificate', type=Path, default=HERE/SOURCE_NAME)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    raw = read_artifact_bytes(args.source_certificate)
    require(sha256(raw).hexdigest() == SOURCE_SHA256, 'source certificate SHA-256')
    source = json.loads(raw, object_pairs_hook=unique)
    require(source['schema'] == 'erdos7-arbitrary-head-profile-v1', 'source certificate schema')
    law = source['selected_actual_law']
    require((F(law['T11']),F(law['T13'])) == (4,6), 'same AP(4,6) actual incoming law')
    D, J = F(law['supported_Haar_density']), F(law['supported_square'])
    require(D == F(13530827317392000000,171474522380088889) and
            J == F(42035473165849976389,171474522380088889), 'same supported13 constants')
    p17 = step(17, [3,5,7,11,13], D, J)
    propagation17 = 1+F(2)*(phi(17,0)-1)
    require(propagation17 == F(89,64), 'unconditioned AP17 physical square multiplier')
    p19 = step(19, [3,5,7,11,13,17], 2*D, propagation17*J)
    require(p17['theta'] == F(6613,7168) and p19['theta'] == F(2869,3780),
            'all-current-depth mixed coefficients')
    require(params(17) == (F(7,15),F(15,8),F(15,16),F(225,56)) and
            params(19) == (F(7,17),F(17,10),F(17,18),F(289,70)), 'typed pure/Haar constants')
    eps17,eps19 = p17['epsilon'],p19['epsilon']
    propagation19 = 1+F(9,5)*(phi(19,0)-1)
    require(propagation19 == F(59,45), 'normalized zero-block propagation')
    square_error = propagation19*eps17+eps19
    charge_error = 2*eps17+eps19
    allowance = square_error+483*charge_error
    margin = F(377,1000)
    require(allowance < margin, 'full weighted allowance below .377')
    physical_density = F(18,5)*D
    result = encode(dict(
        schema='erdos7-weighted-kernel-tails-v1', source_sha256={SOURCE_NAME:SOURCE_SHA256},
        scope='Ordinary proof and exact constants for truncating only forbidden masks at AP17/8 and AP19/8, from the full actual supported AP(4,6) law on3571113. Arbitrary original heights/residues and every original test label remain. Neither the incoming13 law nor test inventories are made finite by this certificate. No unrestricted Erdos7 or Lean-kernel conclusion.',
        incoming_law=dict(name='supported actual AP(4,6)13',Haar_density_bound=D,
                          complete_square_bound=J,survival_lower=F(law['survival_lower'])),
        steps=[p17,p19], propagation19=propagation19,
        physical_and_final_killed_weighted_error=square_error,
        assigned_charge_sum_error=charge_error, W=483,
        total_criterion_allowance=allowance, safe_allowance=margin,
        safety_slack=margin-allowance,
        reference_criterion='For every complete original test L: E_ref[L^2-1]+483*B_ref <= 483-377/1000.',
        resulting_criterion='For every complete original test L: E_actual[L^2-1]+483*B_actual <= 483-safety_slack < 483; hence B_actual<1 and SH28 gives positive final survival and supported complete-square bound484.',
        remaining_inputs=['A valid reference criterion for every complete original test.',
                          'Full actual incoming13 law; its needed finite joint marginals are external inputs.',
                          'Any desired test truncation requires a separate paid test-tail error.',
                          'Any incoming-law truncation needs continuity for this AP law; the existing AO finite-core certificate is a different law.'],
        optional_test_tail=dict(physical19_Haar_density_bound=physical_density,
             formula_description='E[L^2-L_h^2] <= (18D13/5)*(product_p sum_(a>=0)(2a+1)/p^a - product_p sum_(0<=a<=h_p)(2a+1)/p^a).',
             primes=[3,5,7,11,13,17,19], used_in_377_allowance=False),
        fixtures=dict(localized_prefix_pair_cases=prefix_fixtures(),**coefficient_fixtures())))
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n')
    else:
        actual = json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique)
        require(actual == result, 'entire certificate equals exact recomputation')
    print('PASS mask-only AP(4,6) restart: epsilon17='+str(float(eps17))+
          '; epsilon19='+str(float(eps19))+'; full W483 allowance='+str(float(allowance))+' < .377')


if __name__ == '__main__':
    main()
