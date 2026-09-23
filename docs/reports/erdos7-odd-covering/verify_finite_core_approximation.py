#!/usr/bin/env python3
"""Exact finite-core approximation bounds for the actual supported law through13.

CM8, SD1--SD6 and T1--T5 are ordinary inputs. Finite fixtures and exact
rational inequalities below do not replace their universal proofs. Existing
FI moment helpers and numerical source certificates are hash-bound and read;
their experiments are not rerun. Python standard library only.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb, lcm
from pathlib import Path
import argparse
import importlib.util
import json
import sys

HERE = Path(__file__).resolve().parent
CERTIFICATE = 'certificates/finite_core_approximation_certificate.json'
PRIMES = (3, 5, 7, 11, 13)
PINS = {
    'verify_pg1_lifted_global_cap.py': '2c437c90cbc390e0dff5b759ac5341078e2ba3a7fe4b3316ed83e54a0c4bdefb',
    'certificates/uniform_gamma_cofactor_certificate.json': '1739213682c47464c2d0a4e72f90ef98fb0813dcddae96bea250b355fbaea366',
    'certificates/star_block_obstruction_certificate.json': 'a378fed7d44cb1dd77fa81b9d9888cc248014011bf8a25aafeeceab8166a1907',
}


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate certificate key: '+key)
        result[key] = value
    return result


def load_inputs(directory):
    data = {}
    for filename, expected in PINS.items():
        raw = read_artifact_bytes(directory/filename)
        require(sha256(raw).hexdigest() == expected, 'source SHA-256: '+filename)
        if filename.endswith('.json'):
            data[filename] = json.loads(raw, object_pairs_hook=unique)
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('fi_helpers', directory/'verify_pg1_lifted_global_cap.py')
    fi = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fi)
    return fi, data


def finite_factor(p, b):
    return F(p, p-1)*(1-F(1, p**(b+1)))


def reciprocal_tails(fi, box):
    D3 = F(35, 16)
    B3 = fi.multiply(finite_factor(p, b) for p, b in zip(PRIMES[:3], box[:3]))
    T3 = D3-B3
    T11 = D3/10-B3*(1-F(1, 11**box[3]))/10
    B4 = B3*finite_factor(11, box[3])
    T13 = D3*F(11, 10)/12-B4*(1-F(1, 13**box[4]))/12
    T5 = F(1001, 384)-B4*finite_factor(13, box[4])
    require(min(T3, T11, T13) >= 0 and T3+T11+T13 == T5,
            'complete original forbidden tails partition by largest prime')
    return T3, T11, T13, T5


def error_bounds(fi, box, D0, survivor, D, H2, H4):
    T3, T11, T13, T5 = reciprocal_tails(fi, box)
    initial_L1 = 4*D0*T3
    physical_L1 = D0*(4*T3+8*T11+16*T13)
    killed_L1 = physical_L1+8*D0*T5
    final_L1 = 2*killed_L1/survivor
    require(final_L1 == D*(6*T3+8*T11+12*T13), 'normalization and event-difference constants')
    box_H2 = fi.multiply(fi.fixed_finite_moment(p, 0, b, 2) for p, b in zip(PRIMES, box))
    test_tail = D*(H2-box_H2)
    law_error_squared = D*H4*final_L1
    require(test_tail >= 0, 'all omitted original ordered test pairs remain as a nonnegative tail')
    return dict(box=box, T357=T3, T11=T11, T13=T13, full_old_reciprocal_tail=T5,
                initial_357_L1=initial_L1, physical_13_L1=physical_L1,
                killed_13_L1=killed_L1, final_supported_L1=final_L1,
                final_supported_TV=final_L1/2, omitted_test_square_upper=test_tail,
                same_test_law_error_squared=law_error_squared)


def finite_checks(fi):
    pairs = []
    for heights, cut in [((2, 1, 1, 0, 0), (1, 0, 1, 0, 0)),
                         ((2, 1, 1, 1, 1), (1, 1, 0, 1, 0)),
                         ((1, 1, 0, 0, 0), (2, 2, 2, 2, 2))]:
        ds = fi.original_divisors(heights)
        clipped = tuple(min(a, b) for a, b in zip(heights, cut))
        inside = set(fi.original_divisors(clipped))
        direct = sum((F(1, lcm(d, e)) for d in ds for e in ds
                      if d not in inside or e not in inside), F(0))
        formula = (fi.multiply(fi.fixed_finite_moment(p, 0, a, 2) for p, a in zip(PRIMES, heights))
                   -fi.multiply(fi.fixed_finite_moment(p, 0, b, 2) for p, b in zip(PRIMES, clipped)))
        require(direct == formula, 'literal full original ordered-pair tail equals the product formula')
        pairs.append(dict(physical_heights=heights, cutoff=cut, original_test_labels=len(ds),
                          original_ordered_pairs=len(ds)**2, inside_labels=len(inside), exact_Haar_tail=direct))
    geometric = []
    for p in PRIMES:
        for b in (0, 2, 20, 28, 64):
            difference = fi.fixed_low_moment(p, 0, 2)-fi.fixed_finite_moment(p, 0, b, 2)
            tail = F(1, p**b)*(F(2*b+1, p-1)+F(2*p, (p-1)**2))
            require(difference == tail > 0, 'exact positive second-moment geometric tail fixture')
            geometric.append(dict(prime=p, cutoff=b, tail=tail))
    # AM2's nested-mask proof also holds for the T4 value delta=1/2, C=2.
    def coeff(alpha):
        c = 1/(1-min(alpha, F(1, 2)))
        bad = 2*max(F(0), alpha-F(1, 2))/alpha if alpha else F(0)
        require((1-alpha)*c+alpha*bad == 1 and 0 <= bad <= 1 <= c <= 2,
                'T4 full-Haar clipping normalization and caps')
        return c, bad
    n, pair_count, types = 8, 0, 0
    for a in range(n+1):
        ca, ba = coeff(F(a, n))
        for b in range(n+1):
            cb, bb = coeff(F(b, n))
            for intersection in range(max(0, a+b-n), min(a, b)+1):
                aa, ab, neither = a-intersection, b-intersection, n-a-b+intersection
                d = F(aa+ab, n)
                physical = (intersection*abs(ba-bb)+aa*abs(ba-cb)+ab*abs(ca-bb)+neither*abs(ca-cb))/n
                killed = (aa*cb+ab*ca+neither*abs(ca-cb))/n
                require(max(physical, killed) <= 4*d, 'delta1/2 physical and killed mask Lipschitz fixtures')
                pair_count += comb(n, a)*comb(a, intersection)*comb(n-a, b-intersection)
                types += 1
    require(pair_count == 65536 and types == 165, 'all ordered eight-atom mask pairs retained')
    return dict(original_test_pair_fixtures=pairs, geometric_tail_fixtures=geometric,
                BB_delta_half_mask_checks=dict(atoms=n, all_ordered_mask_pairs=pair_count, intersection_types=types))


def admissible_moments_and_cylinders(fi, D0, survivor, D, H4):
    factors = {p: fi.fixed_low_moment(p, 0, 4) for p in PRIMES}
    H4_357 = fi.multiply(factors[p] for p in PRIMES[:3])
    K0 = 1+D0*(H4_357-1)
    Kphysical = K0*(2*factors[11]-1)*(2*factors[13]-1)
    Kfinal = 1+(Kphysical-1)/survivor
    require(H4_357 == F(16625, 12) and K0 == F(598121, 53)
            and Kphysical == F(3530785420609, 14310000)
            and Kfinal == F(7061548613243, 6392025) < D*H4,
            'AO4--AO6 ordered quartic transfer with both actual-conditioning unit floors')
    literal = []
    for p in PRIMES:
        for h in (0, 1, 2):
            size = p**h
            loads = [sum(x % p**e == 0 for e in range(h+1)) for x in range(size)]
            for k in (2, 3, 4):
                direct = F(sum(L**k for L in loads), size)
                finite = fi.fixed_finite_moment(p, 0, h, k)
                tail = fi.fixed_low_moment(p, 0, k)-finite
                require(direct == finite and tail > 0, 'literal coherent complete-prefix moments and positive tail')
                literal.append(dict(prime=p, height=h, power=k, direct=direct, infinite_tail=tail))
    require(len(literal) == 45, 'all45 AO literal prefix fixtures')
    power_tails, cylinders = [], []
    for box in ((8, 5, 4, 3, 3), (12, 8, 7, 6, 6), (16, 11, 9, 8, 7)):
        row = dict(box=box)
        for k in (2, 4):
            tail = (fi.multiply(fi.fixed_low_moment(p, 0, k) for p in PRIMES)
                    -fi.multiply(fi.fixed_finite_moment(p, 0, h, k) for p, h in zip(PRIMES, box)))
            require(tail > 0, 'AO7 complete original-label power tail')
            row['power'+str(k)+'_tail_upper'] = D*tail
        power_tails.append(row)
    for exponents in ((0, 0, 0, 0, 0), (2, 1, 1, 1, 1), (8, 5, 4, 3, 3), (16, 11, 9, 8, 7)):
        modulus = int(fi.multiply(p**a for p, a in zip(PRIMES, exponents)))
        upper = D/modulus*fi.multiply(fi.fixed_low_moment(p, a, 2) for p, a in zip(PRIMES, exponents))
        for p, a in zip(PRIMES, exponents):
            height = a+2
            direct = sum((F(1, p**max(i, j, a))
                          for i in range(height+1) for j in range(height+1)), F(0))
            finite = F(1, p**a)*fi.fixed_finite_moment(p, a, 2, 2)
            require(direct == finite < F(1, p**a)*fi.fixed_low_moment(p, a, 2),
                    'AO8 one queried cylinder with both original test axes retained')
        cylinders.append(dict(queried_old_exponents=exponents, original_old_modulus=modulus,
                              square_energy_in_cylinder_upper=upper))
    return dict(initial_Haar_fourth_357=H4_357, initial_fourth_after_unit_floor=K0,
                physical_fourth13=Kphysical, supported_fourth_after_unit_floor=Kfinal,
                quartic_transfer='K_new<=K_old*(1+c*(F4(p)-1)); c=2 for the full-Haar11 and13 steps.',
                literal_prefix_fixtures=literal, original_label_power_tails=power_tails,
                cylinder_bound='E_nu[L_T^2*1_(a mod d)] <= (D/d)*product_p F2(p,v_p(d)).',
                queried_cylinder_fixtures=cylinders)


def cubic_coordinate_tail(p, b):
    return F(1, p**b)*(F((b+2)**2, p-1)+F(4*b+7, (p-1)**2)+F(3*(p+1), (p-1)**3))


def cubic_weighted_tail(fi, D, H2):
    factors = {p: fi.fixed_low_moment(p, 0, 3) for p in PRIMES}
    total = fi.multiply(factors.values())
    require(total == F(10110619519, 44236800)
            and total-H2 == F(9464854399, 44236800),
            'full old three-label max-exponent sum and exact removal of queried unit')
    coordinate_checks = []
    for p in PRIMES:
        for b in (0, 1, 2, 8, 16, 28):
            inside = sum((F(1, p**a)*fi.fixed_low_moment(p, a, 2)
                          for a in range(b+1)), F(0))
            tail = cubic_coordinate_tail(p, b)
            alternate = (fi.fixed_finite_moment(p, 0, b, 3)
                         +(b+1)*(fi.fixed_low_moment(p, 0, 2)-fi.fixed_finite_moment(p, 0, b, 2)))
            require(inside == alternate and inside+tail == factors[p] and tail > 0,
                    'only queried-label exponent is truncated; both test exponents remain unbounded')
            coordinate_checks.append(dict(prime=p, queried_cutoff=b, inside=inside, exact_tail=tail))
    current17 = fi.fixed_low_moment(17, 0, 3)-fi.fixed_low_moment(17, 0, 2)
    require(current17 == F(595, 2048), 'all current test depths and positive queried current depths retained')
    rows = []
    for box in ((8, 5, 4, 3, 3), (12, 8, 7, 6, 6), (16, 11, 9, 8, 7), (20,)*5, (28,)*5):
        tail = total-fi.multiply(factors[p]-cubic_coordinate_tail(p, b) for p, b in zip(PRIMES, box))
        all_axis_tail = total-fi.multiply(fi.fixed_finite_moment(p, 0, b, 3) for p, b in zip(PRIMES, box))
        reciprocal = F(1001, 384)-fi.multiply(finite_factor(p, b) for p, b in zip(PRIMES, box))
        require(0 < tail <= all_axis_tail and reciprocal > 0,
                'third-label-only tail is bounded by the all-axis cubic tail')
        rows.append(dict(queried_old_box=box, Haar_weighted_tail=tail,
                         sum_old_square_cylinder_energy_upper=D*tail,
                         old_square_times_alpha17_high_upper=D*tail/16,
                         full_current_square_on_BB_bad_high_upper=D*tail*current17,
                         BB_bad_high_mass_first_moment_upper=D*reciprocal/16,
                         total_charge_increment_upper_delta_half=D*reciprocal/8,
                         old_square_weighted_charge_increment_upper_delta_half=D*tail/8))
    finite = []
    for heights, box in [((2, 1, 1, 0, 0), (1, 0, 1, 0, 0)),
                         ((1, 1, 1, 1, 0), (0, 1, 0, 0, 0))]:
        ds = fi.original_divisors(heights)
        inside = set(fi.original_divisors(tuple(min(a, b) for a, b in zip(heights, box))))
        direct = sum((F(1, lcm(d1, d2, q)) for d1 in ds for d2 in ds for q in ds if q not in inside), F(0))
        full = fi.multiply(fi.fixed_finite_moment(p, 0, a, 3) for p, a in zip(PRIMES, heights))
        limited = fi.multiply(sum((F(1, p**max(i, j, k))
                                   for i in range(a+1) for j in range(a+1) for k in range(min(a, b)+1)), F(0))
                              for p, a, b in zip(PRIMES, heights, box))
        bound = total-fi.multiply(factors[p]-cubic_coordinate_tail(p, b) for p, b in zip(PRIMES, box))
        require(direct == full-limited <= bound, 'literal complete original two-test/one-query tuples')
        finite.append(dict(physical_heights=heights, queried_box=box, test_labels=len(ds),
                           queried_tail_labels=len(ds)-len(inside), exact_Haar_weighted_tail=direct))
    # On actual bad points the T4 full-Haar BB density is at most1, even when its good cap is2.
    for alpha, delta in product((F(0), F(1, 4), F(1, 2), F(3, 4), F(1)), (F(1, 4), F(7, 15), F(1, 2))):
        bad_density = max(F(0), alpha-delta)/(alpha*(1-delta)) if alpha else F(0)
        require(0 <= bad_density <= 1, 'full-Haar BB bad-subset domination')
        for enlarged in (alpha, (1+alpha)/2, F(1)):
            difference = (max(F(0), enlarged-delta)-max(F(0), alpha-delta))/(1-delta)
            require(0 <= difference <= (enlarged-alpha)/(1-delta),
                    'whole BB charge increment has coefficient1/(1-delta)')
    return dict(scope='One AO law nu<=D*Haar, one complete original test, independently selected queried cylinders at each original old modulus. Query residues need not equal the old forbidden residues and may depend on the subsequent current depth.',
                full_old_three_label_Haar_sum=total, nonunit_queried_sum=total-H2,
                coordinate_formula='T_p=F3_Haar(p); U_p(b)=p^(-b)*[(b+2)^2/(p-1)+(4b+7)/(p-1)^2+3*(p+1)/(p-1)^3].',
                complete_tail_formula='sum_(q outside box) E_nu[L_T^2*1_Cq] <= D*[product_p T_p-product_p(T_p-U_p(b_p))]. Only the queried old label is restricted.',
                positive_current17_three_label_factor=current17,
                weighted_alpha17_bound='E_nu[L_old^2*alpha17_high] <= D*tail/16.',
                actual_BB_bad_energy_bound='For the full-Haar T4 kernel at17, E[L_full^2*1_B_high] <= D*tail*(595/2048), using bad density<=1. A generic Haar cap c instead gives c times this bound.',
                whole_charge_increment='With beta_delta(alpha)=(alpha-delta)_+/(1-delta), E_nu[L_old^2*(beta_delta(alpha_full)-beta_delta(alpha_core))] <= D*tail/[16*(1-delta)]; the unweighted bound uses the reciprocal tail instead. This compares normalized kernels and includes redistribution on old bad points.',
                limitation='This controls the weighted high-cofactor energy tail. Bad mass alone uses the smaller first-moment tail. No improved finite low-cofactor17 charge, complete Gamma bound or unrestricted continuation is asserted.',
                coordinate_checks=coordinate_checks, weighted_tail_rows=rows, literal_original_tuple_fixtures=finite)


def actual_BB_continuity_obstruction(fi):
    fixtures = []
    for N in (2, 3, 4, 8, 16, 32, 64, 128):
        n = N+1
        B2 = 4-F(N+2, 2*3**(N-1))
        require(B2 == fi.nonzero_finite_moment(3, N, 2), 'same complete old-prefix base moment')
        u = (5-B2)/(n*n-B2)
        w = u+(1-u)/F(2*3**(N-1))
        Gbase = F(95, 16)
        gap = w*n*n/80
        Gnew = Gbase+gap
        L1 = w/8
        require(0 < u < w < 1 and (1-u)*B2+u*n*n == 5
                and gap > F(1, 80) and gap/L1 == F(n*n, 10),
                'actual BB-current Gamma gap survives vanishing joint L1')
        require(L1 < (F(2, n*n-4)+F(1, 2*3**(N-1)))/8,
                'explicit joint L1 bound tends to zero')
        require(F(1, 17) <= F(1, 2) and F(2, 17) <= F(1, 2),
                'both full-Haar BB kernels have actual zero bad charge')
        fixtures.append(dict(N=N, original_old_test_labels=n, uniform_old_second=B2,
                             mixture_spike_mass=u, actual_old_mass_at_zero=w,
                             old_complete_Gamma2=F(5), current_Gamma_base=Gbase,
                             current_Gamma_new=Gnew, current_Gamma_gap=gap,
                             joint_L1=L1, Gamma_gap_over_L1=F(n*n, 10),
                             changed_original_modulus=3**N*17))
    return dict(scope='Arbitrary supported old laws with exact Gamma2=5; the old source is not asserted to be BBMST-generated. Both current transitions are actual full-Haar BB kernels at17, delta=1/2, with zero charge.',
                old_family='Every original old class is 1 modulo 3^j, 1<=j<=N; law is the uniform actual survivors mixed with a spike at0.',
                current_family='Pure17 forbids0; all mixed original current labels initially forbid current0. Only label3^N*17 changes from old0/current0 to old0/current3.',
                actual_rows='The reference current law is uniform on16 points. The changed law is uniform on15 points only at old0; all other rows agree.',
                exact_complete_maxima='Gamma_base=95/16; Gamma_new=95/16+w*(N+1)^2/80. Coherent old0 and one common good current root attain all pair bounds.',
                conclusion='Joint L1 tends to0 while the complete current Gamma2 gap is strictly greater than1/80. A uniform old Gamma2 bound alone does not give uniform Gamma continuity.',
                fixtures=fixtures)


def evaluate(directory):
    fi, data = load_inputs(directory)
    signed = data['certificates/uniform_gamma_cofactor_certificate.json']['signed_two_level_three_prime_parameters']
    cm8 = data['certificates/star_block_obstruction_certificate.json']['cm1_actual_head_sharpness']
    G = F(signed['Gamma357_upper'])
    density_lower = F(cm8['infimum_ambient_uncovered_density'])
    require(G == F(3849, 106) and density_lower == F(53, 432), 'CM8 and same-law SD numerical inputs')
    D0 = 1/density_lower
    J11, J13 = G*F(41, 25), G*F(41, 25)*F(55, 36)
    beta11, beta13 = G/100, J11/144
    survivor = 1-beta11-beta13
    D = 4*D0/survivor
    G2_final = 1+(J13-1)/survivor
    H2 = fi.multiply(fi.fixed_low_moment(p, 0, 2) for p in PRIMES)
    H4_factors = [fi.fixed_low_moment(p, 0, 4) for p in PRIMES]
    H4 = fi.multiply(H4_factors)
    require(survivor == F(28409, 127200) > 0 and D == F(4147200, 28409)
            and G2_final == F(11473869, 28409), 'actual supported law normalizer, density and unit-floor Gamma2')
    require(H4_factors == [F(30), F(285, 32), F(140, 27), F(1914, 625), F(2275, 864)]
            and H4 == F(19304285, 1728), 'complete five-prime original Haar fourth moment')
    cutoffs = []
    for tolerance, cutoff in [(F(1), 20), (F(1, 10), 24), (F(1, 100), 28)]:
        row = error_bounds(fi, (cutoff,)*5, D0, survivor, D, H2, H4)
        tail, square = row['omitted_test_square_upper'], row['same_test_law_error_squared']
        require(tail < tolerance and square < (tolerance-tail)**2,
                'exact squared comparison certifies total Gamma2 error at the stated cutoff')
        previous = error_bounds(fi, (cutoff-1,)*5, D0, survivor, D, H2, H4)
        require(previous['omitted_test_square_upper'] >= tolerance or
                previous['same_test_law_error_squared'] >= (tolerance-previous['omitted_test_square_upper'])**2,
                'previous uniform cutoff fails this particular sufficient bound')
        row.update(certified_Gamma2_absolute_error=tolerance,
                   strict_squared_margin=(tolerance-tail)**2-square,
                   finite_core_test_label_count=(cutoff+1)**5,
                   first_uniform_cutoff_for_this_bound=cutoff)
        cutoffs.append(row)
    return fi.encode(dict(
        schema='erdos7-finite-core-actual-old-law-v1', source_sha256=PINS,
        ordinary_source_commit='0355c3cc98f5bd10e03b6d71108d820f56ebbf89',
        scope='Every arbitrary finite original forbidden family on primes3,5,7,11,13, at most one residue per original modulus. Start from uniform complete actual357 survivors, apply full-Haar T4 kernels at11 and13 with delta=1/2, then condition on complete actual survival. All original test labels remain present in the target Gamma2.',
        verification_scope='Exact constants and finite fixtures; ordinary CM8/SD/T4 and the adjacent continuity proof carry universal heights and layouts. The family-specific finite core law and its maximum are not enumerated by this certificate.',
        construction=dict(Gamma357=G, ambient_357_density_lower=density_lower,
                          source_Haar_density_upper=D0, physical_J11=J11, physical_J13=J13,
                          charge11_upper=beta11, charge13_upper=beta13,
                          actual_survivor_mass_lower=survivor, physical_density_upper=4*D0,
                          final_supported_density_upper=D, final_supported_Gamma2_upper=G2_final),
        Haar_moments=dict(prime_order=PRIMES, fourth_factors=H4_factors, complete_second=H2,
                          complete_fourth=H4, final_law_fourth_from_density=D*H4,
                          plus_current17_Haar_fourth=H4*fi.fixed_low_moment(17, 0, 4),
                          final_law_plus_current17_fourth_from_density=D*H4*fi.fixed_low_moment(17, 0, 4)),
        admissible_law_moments=admissible_moments_and_cylinders(fi, D0, survivor, D, H4),
        cubic_weighted_cylinder_tail=cubic_weighted_tail(fi, D, H2),
        actual_BB_current_continuity_obstruction=actual_BB_continuity_obstruction(fi),
        law_comparison='For two families agreeing on the exponent box, L1(final laws)<=D*(6*T357+8*T11+12*T13). The finite-core family omits only high forbidden classes and its law is lifted with uniform suffixes. This approximating law is not asserted to avoid the full family tail.',
        Gamma_comparison='|Gamma_full(nu_full)-Gamma_box(nu_core)|<=D*(H2_Haar-H2_box)+sqrt(D*H4_Haar*L1_bound). Unit and every inside original test are retained; all other original pairs are included in the explicit tail.',
        cutoffs=cutoffs, finite_checks=finite_checks(fi)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE/CERTIFICATE)
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = evaluate(args.source_directory)
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2)+'\n')
    else:
        require(json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique) == result,
                'entire certificate equals exact recomputation')
    print(json.dumps(dict(survivor_lower=result['construction']['actual_survivor_mass_lower'],
                          final_density_upper=result['construction']['final_supported_density_upper'],
                          certified_Gamma_errors=[r['certified_Gamma2_absolute_error'] for r in result['cutoffs']],
                          uniform_cutoffs=[r['first_uniform_cutoff_for_this_bound'] for r in result['cutoffs']],
                          certificate_action='written' if args.write else 'verified')))


if __name__ == '__main__':
    main()
