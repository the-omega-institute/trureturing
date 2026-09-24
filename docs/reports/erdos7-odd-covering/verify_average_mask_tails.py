#!/usr/bin/env python3
"""Exact complete-original-divisor tails for averaged current-mask changes.

This is arithmetic supporting the adjacent ordinary tail proof and AM1--AM7.
Finite mask checks do not replace those universal ordinary proofs. Existing
FI source and moment constants are imported with exact SHA-256 binding.
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
from pathlib import Path
from math import comb
import argparse
import importlib.util
import json
import sys

HERE = Path(__file__).resolve().parent
CERTIFICATE = 'certificates/average_mask_tails_certificate.json'
SOURCE_PINS = {
    'verify_pg1_lifted_global_cap.py': '2c437c90cbc390e0dff5b759ac5341078e2ba3a7fe4b3316ed83e54a0c4bdefb',
    'certificates/pg1_lifted_global_cap_certificate.json': 'cf365032f6447be1fe010fdca00d90444a09bbf19b3654a1b089c7d06f2fe35d',
    'certificates/mod3_conditioned_geometry_certificate.json': '9a0e265a456ab133389202abd5ef91ac6826957f74c24b1e8bd055a97cea0a0a',
}
PRIMES = (3, 5, 7, 11, 13)
BOX = (65, 65, 65, 65, 65, 65)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def load_fi(directory):
    for filename, pin in SOURCE_PINS.items():
        require(sha256(read_artifact_bytes(directory/filename)).hexdigest() == pin,
                'exact dependency SHA-256: '+filename)
    spec = importlib.util.spec_from_file_location('pinned_fi', directory/'verify_pg1_lifted_global_cap.py')
    module = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    spec.loader.exec_module(module)
    stored = json.loads(read_artifact_text(directory/'certificates/pg1_lifted_global_cap_certificate.json'),
                        object_pairs_hook=module.unique_object)
    return module, stored


def finite_old_factor(p, a):
    return F(p, p-1)*(1-F(1, p**(a+1)))


def finite_current_factor(H):
    return (1-F(1, 17**H))/16


def finite_fixtures(fi):
    rows = []
    for heights, cut in [((2, 1, 1, 1, 1, 2), (1, 1, 0, 1, 0, 1)),
                         ((3, 2, 1, 1, 1, 3), (2, 1, 1, 0, 1, 2)),
                         ((2, 1, 1, 0, 0, 1), (4, 4, 4, 4, 4, 4))]:
        all_labels = list(product(*(range(a+1) for a in heights[:-1]), range(1, heights[-1]+1)))
        all_tail = mixed_tail = F(0)
        count = mixed_count = 0
        for exponents in all_labels:
            if all(e <= b for e, b in zip(exponents, cut)):
                continue
            value = 1/(fi.multiply(p**e for p, e in zip(PRIMES, exponents[:-1]))*17**exponents[-1])
            all_tail += value
            count += 1
            if any(exponents[:-1]):
                mixed_tail += value
                mixed_count += 1
        old_all = fi.multiply(finite_old_factor(p, a) for p, a in zip(PRIMES, heights[:-1]))
        old_inside = fi.multiply(finite_old_factor(p, min(a, b))
                                 for p, a, b in zip(PRIMES, heights[:-1], cut[:-1]))
        current_all = finite_current_factor(heights[-1])
        current_inside = finite_current_factor(min(heights[-1], cut[-1]))
        require(all_tail == old_all*current_all-old_inside*current_inside,
                'literal finite full-original-label tail equals product subtraction')
        require(mixed_tail == (old_all-1)*current_all-(old_inside-1)*current_inside,
                'literal finite mixed-label tail retains every nonunit old divisor')
        require(all_tail-mixed_tail == current_all-current_inside,
                'pure labels are removed exactly, not silently truncated')
        rows.append(dict(physical_heights=heights, inclusive_cut=cut, original_labels=len(all_labels),
                         outside_labels=count, outside_mixed_labels=mixed_count,
                         all_tail=all_tail, mixed_tail=mixed_tail))
    return rows


def bb_coefficients(alpha):
    delta, cap = F(7, 15), F(15, 8)
    good = 1/(1-min(alpha, delta))
    bad = cap*max(F(0), alpha-delta)/alpha if alpha else F(0)
    charge = max(F(0), alpha-delta)/(1-delta)
    require((1-alpha)*good+alpha*bad == 1 and alpha*bad == charge
            and 0 <= bad <= 1 <= good <= cap, 'actual clipping normalization, charge and caps')
    return good, bad


def uniform_mask_pair_fixtures():
    n, cap = 8, F(15, 8)
    types = pairs = 0
    max_physical_ratio = max_killed_ratio = F(0)
    for a in range(n+1):
        ca, ba = bb_coefficients(F(a, n))
        for b in range(n+1):
            cb, bb = bb_coefficients(F(b, n))
            for intersection in range(max(0, a+b-n), min(a, b)+1):
                neither, onlya, onlyb = n-a-b+intersection, a-intersection, b-intersection
                d = F(onlya+onlyb, n)
                physical = (intersection*abs(ba-bb)+onlya*abs(ba-cb)
                            +onlyb*abs(ca-bb)+neither*abs(ca-cb))/n
                killed = (onlya*cb+onlyb*ca+neither*abs(ca-cb))/n
                require(physical <= 2*cap*d and killed <= 2*cap*d,
                        'all uniform eight-atom mask pairs satisfy physical and killed L1 bounds')
                if d:
                    max_physical_ratio = max(max_physical_ratio, physical/d)
                    max_killed_ratio = max(max_killed_ratio, killed/d)
                types += 1
                pairs += comb(n, a)*comb(a, intersection)*comb(n-a, b-intersection)
    require(pairs == 2**(2*n), 'symmetry classes retain every ordered mask pair')
    return dict(atoms=n, ordered_mask_pairs=pairs, intersection_types=types,
                physical_L1_over_symmetric_mass_max=max_physical_ratio,
                killed_L1_over_symmetric_mass_max=max_killed_ratio,
                common_upper=2*cap)


def bb_row(n, pure_forbidden, raw_bad):
    base = set(range(n))-set(pure_forbidden)
    bad = set(raw_bad)&base
    c, b = bb_coefficients(F(len(bad), len(base)))
    physical = [F(0) if y not in base else (b if y in bad else c)/len(base) for y in range(n)]
    killed = [w if y not in bad else F(0) for y, w in enumerate(physical)]
    require(sum(physical, F(0)) == 1, 'literal row normalized')
    return physical, killed, base-bad


def repair_row(n, pure, raw_bad, t, retained):
    physical, killed, good = bb_row(n, pure, raw_bad)
    if retained:
        donors = (12, 13, 14, 16)
        for root, mass in [(2, t)]+[(root, -t/4) for root in donors]:
            cells = [y for y in good if y % 17 == root]
            require(cells, 'every selected root has new good support')
            for y in cells:
                physical[y] += mass/len(cells)
                killed[y] += mass/len(cells)
    require(sum(physical, F(0)) == 1 and min(physical) >= 0
            and max(physical) <= F(15, 8)/F(n-len(pure)), 'literal repaired normalization and global cap')
    require(sum(killed, F(0)) == sum(bb_row(n, pure, raw_bad)[1], F(0)),
            'literal repair preserves actual survivor mass')
    require(all(physical[y] == bb_row(n, pure, raw_bad)[0][y] for y in set(raw_bad)-set(pure)),
            'repair leaves every actual bad atom unchanged')
    return physical, killed


def control_fixtures(fi, t):
    cap = F(15, 8)
    A = 4+F(2176, 15)*t
    Apure = 9+136*t
    require(A == F(7864337, 1966080) < 5 and Apure == F(18874385, 2097152) < 10,
            'fixed-pure and changing-pure candidate L1 constants')
    require(F(136, 117)+F(68, 3)*t < cap and 1-F(17, 3)*t > 0
            and F(1, 15)+F(1, 68) < F(7, 15), 'uniform repair capacity, donors and zero charge')
    require(cap+F(225, 112) == F(435, 112) < 4
            and F(128, 15) < 9, 'change-of-base BB coefficient bounds')
    n = 17**2
    pure = {y for y in range(n) if y % 17 == 0 or y == 15}
    bad = {y for y in range(n) if y % 17 == 1 or y == 32}
    require(not pure&bad, 'actual H2 pure comb and transferred-row spoke are disjoint')
    base_bb, base_killed, _ = bb_row(n, pure, bad)
    base_transfer, base_transfer_killed = repair_row(n, pure, bad, t, True)
    row_results = []
    for name, new_bad in [('good-row', (bad-{1})|{2, 12}),
                          ('skipped-row', bad|{2+17*j for j in range(5)})]:
        h = F(len(new_bad^bad), n)
        d = h/F(n-len(pure), n)
        retained = d <= F(1, 68)
        require(retained == (name == 'good-row'), 'both repair and skip branches exercised')
        new_bb, new_killed, good = bb_row(n, pure, new_bad)
        candidate, candidate_killed = repair_row(n, pure, new_bad, t, retained)
        bb_L1 = sum((abs(x-y) for x, y in zip(new_bb, base_bb)), F(0))
        killed_L1 = sum((abs(x-y) for x, y in zip(new_killed, base_killed)), F(0))
        repair_L1 = sum((abs(x-y) for x, y in zip(candidate, base_transfer)), F(0))
        repair_killed_L1 = sum((abs(x-y) for x, y in zip(candidate_killed, base_transfer_killed)), F(0))
        require(max(bb_L1, killed_L1) <= 4*h and max(repair_L1, repair_killed_L1) <= A*h,
                'literal H2 physical and killed BB/repair L1 bounds')
        if retained:
            require(all(F(sum(y % 17 == root for y in good), n) >= F(3, 68)
                        for root in (2, 12, 13, 14, 16)), 'new selected roots retain uniform good mass')
        row_results.append(dict(case=name, Haar_symmetric_mass=h, pure_base_symmetric_mass=d,
                                repaired=retained, BB_L1=bb_L1, killed_BB_L1=killed_L1,
                                repair_L1=repair_L1, killed_repair_L1=repair_killed_L1,
                                survivor_mass=sum(candidate_killed, F(0))))
    changing_base = []
    n = 32
    old_pure, new_pure = {0}, {1}
    kappa = F(2, n)
    for name, raw in [('empty', set()), ('one-changed-base-atom', {0}),
                      ('crosses-clipping-threshold', {0}|set(range(2, 16))),
                      ('charged', set(range(24))), ('all-bad', set(range(32)))]:
        q, killed, _ = bb_row(n, old_pure, raw)
        qnew, killednew, _ = bb_row(n, new_pure, raw)
        r = F(2, 31)
        L1 = sum((abs(x-y) for x, y in zip(q, qnew)), F(0))
        killed_L1 = sum((abs(x-y) for x, y in zip(killed, killednew)), F(0))
        require(F(31, 32) >= F(15, 16) and r <= F(32, 15)*kappa
                and max(L1, killed_L1) <= F(435, 112)*r <= 9*kappa,
                'literal changed pure base with fixed raw mixed mask')
        changing_base.append(dict(case=name, current_atoms=n, raw_bad_atoms=len(raw), pure_symmetric_mass=kappa,
                                  pure_probability_L1=r, physical_L1=L1, killed_L1=killed_L1))
    for q in (F(1, 8), F(1, 2), F(1, 2**100)):
        require(q/(1-q) <= 1 and (1-q)*q/(1-q)+q == 2*q,
                'conditioning density coefficient bounded by1 and exact old-law L1=2q')
    return dict(fixed_pure_candidate_L1_coefficient=A, arbitrary_pure_candidate_L1_coefficient=Apure,
                selected_root_good_Haar_lower=F(3, 68), good_row_Haar_density_upper=F(136, 117),
                recipient_capacity_margin=cap-F(136, 117)-F(68, 3)*t,
                donor_density_margin=1-F(17, 3)*t,
                pure_probability_change_coefficient=F(32, 15), BB_base_change_coefficient=F(435, 112),
                uniform_mask_pairs=uniform_mask_pair_fixtures(), actual_H2_rows=row_results,
                changed_pure_base_fixtures=changing_base,
                old_conditioning='q<=1/2: joint physical/killed density difference<=2 and L1<=2q')


def full_projection_example(fi, case):
    k = 66
    upper = 2*(F(1, 17**k)+F(1, 17**(k+1)))
    require(upper < F(1, 2**100) and k > BOX[-1], 'two changed labels lie beyond the finite core')
    labels = []
    for e, old_residue in [(k, 1), (k+1, 2)]:
        labels.append(dict(original_modulus=3*17**e, old_cofactor=3, current_exponent=e,
                           new_old_residue=old_residue, new_current_residue=12,
                           CRT_residue=fi.crt(old_residue, 3, 12, 17**e)))
    require(all(x % 3 in (1, 2) for x in case['points']), 'every positive old row has a new bad point')
    # Literal H2 instance of the same two-label pattern, with all low315 labels retained.
    ds = fi.original_divisors((2, 1, 1, 0, 0))
    pure = {y for y in range(289) if y % 17 == 0 or y == 15}
    epsilon = F(0)
    changed_rows = 0
    for x, w in zip(case['points'], case['weight_numerators']):
        before, after = set(), set()
        for e in (1, 2):
            for j, d in enumerate(ds[1:], 1):
                old_points = {y for y in range(289) if y % 17**e == fi.prefix(e, j)}
                if x % d == 2 % d:
                    before |= old_points
                    if d != 3:
                        after |= old_points
                if d == 3 and x % 3 == e:
                    after |= {y for y in range(289) if y % 17**e == 12}
        require(12 not in before and 12 in after and 12 not in pure,
                'every actual old support row changes on a formerly clean root')
        difference = (before^after)-pure
        changed_rows += bool(difference)
        epsilon += F(w, case['weight_denominator'])*F(len(difference), 289)
    require(changed_rows == 75 and epsilon <= 2*(F(1, 17)+F(1, 17**2)),
            'full old projection coexists with the exact two-label averaged bound')
    return dict(reference='FI2 redundant stable family before the optional rare-cylinder changes',
                selected_current_exponents=[k, k+1], changed_original_labels=labels,
                Haar_joint_symmetric_mass_upper=upper, old_projection_mass=F(1),
                no_small_old_event_contains_difference=True,
                literal_H2=dict(old_rows=75, changed_rows=changed_rows, averaged_symmetric_mass=epsilon,
                                 original_current_labels=24, changed_original_labels=[51, 867]))


def fixed_second_moment_obstruction(fi):
    rows = []
    for N in (2, 3, 8, 64, 128):
        B2 = fi.nonzero_finite_moment(3, N, 2)
        B4 = fi.nonzero_finite_moment(3, N, 4)
        require(B2 == 4-F(N+2, 2*3**(N-1)) < 4, 'existing finite prefix factor for shifted survivor roots')
        spike = (5-B2)/((N+1)**2-B2)
        G2 = (1-spike)*B2+spike*(N+1)**2
        G4 = (1-spike)*B4+spike*(N+1)**4
        require(0 < spike < 1 and spike > F(1, (N+1)**2)
                and G2 == 5 and G4 > (N+1)**2, 'fixed complete Gamma2 and unbounded Gamma4 family')
        row = dict(N=N, base_second_moment=B2, base_fourth_moment=B4,
                   spike_mass=spike, complete_Gamma2=G2, complete_Gamma4=G4,
                   strict_fourth_moment_lower=(N+1)**2)
        if N <= 3:
            period = 3**N
            moduli = [3**j for j in range(1, N+1)]
            support = [x for x in range(period) if x % 3 != 1]
            require(support == [x for x in range(period) if all(x % d != 1 for d in moduli)],
                    'all distinct original forbidden moduli have exact actual survivor support')
            weights = [(1-spike)/len(support)+(spike if x == 0 else 0) for x in support]
            require(min(weights) > 0 and sum(weights, F(0)) == 1, 'positive normalized actual supported law')
            maximum2 = maximum4 = F(0)
            count = 0
            for residues in product(*(range(d) for d in moduli)):
                loads = [1+sum(x % d == a for d, a in zip(moduli, residues)) for x in support]
                second = sum((w*L**2 for w, L in zip(weights, loads)), F(0))
                fourth = sum((w*L**4 for w, L in zip(weights, loads)), F(0))
                maximum2, maximum4 = max(maximum2, second), max(maximum4, fourth)
                count += 1
            require(count == 3**(N*(N+1)//2) and maximum2 == G2 and maximum4 == G4,
                    'every independent original old test layout attains the predicted exact maxima')
            row['literal'] = dict(period=period, actual_survivors=len(support),
                                  all_independent_test_layouts=count, maximum2=maximum2, maximum4=maximum4)
        rows.append(row)
    return dict(scope='Arbitrary probabilities supported on actual old survivors; these laws are not claimed to be BBMST-derived.',
                family='M=3^N; every original forbidden class is 1 modulo 3^j, 1<=j<=N.',
                law='(1-spike_N)*uniform(x mod3 !=1)+spike_N*delta_0',
                original_test_inventory='One independently selectable residue for every divisor 3^j, including the unit.',
                exact_maximum='Gamma_k=(1-spike_N)*B_(k,N)+spike_N*(N+1)^k, attained with all residues0.',
                conclusion='The fixed exact value Gamma2=5 cannot uniformly bound Gamma4 over arbitrary supported old laws.',
                fixtures=rows)


def evaluate(directory):
    fi, prior = load_fi(directory)
    source = json.loads(read_artifact_text(directory/'certificates/mod3_conditioned_geometry_certificate.json'),
                        object_pairs_hook=fi.unique_object)
    case = next(c for c in source['cases'] if c['name'] == 'PG1')
    maximum = max(case['weight_numerators'])
    maximum_mu = F(maximum, case['weight_denominator'])
    maximum_points = [x for x, w in zip(case['points'], case['weight_numerators']) if w == maximum]
    C_old = 315*maximum_mu*F(11, 10)*F(13, 12)
    require(maximum_mu == F(16622259, 1000000007)
            and maximum_points == [164, 269, 299, 314]
            and C_old == F(49916643777, 8000000056), 'exact density domination constant')
    old_sum = fi.multiply(F(p, p-1) for p in PRIMES)
    total = old_sum/16
    total_mixed = (old_sum-1)/16
    require(old_sum == F(1001, 384) and total == F(1001, 6144)
            and total_mixed == F(617, 6144), 'complete original-divisor reciprocal sums')
    excluded_fractions = [F(1, p**(b+1)) for p, b in zip(PRIMES, BOX[:-1])]+[F(1, 17**BOX[-1])]
    inside_old = fi.multiply(finite_old_factor(p, b) for p, b in zip(PRIMES, BOX[:-1]))
    inside_current = finite_current_factor(BOX[-1])
    all_tail = total-inside_old*inside_current
    mixed_tail = total_mixed-(inside_old-1)*inside_current
    pure_tail = F(1, 16*17**BOX[-1])
    product_tail = total*(1-fi.multiply(1-r for r in excluded_fractions))
    union_tail = total*sum(excluded_fractions, F(0))
    require(0 < mixed_tail < all_tail == product_tail <= union_tail
            and all_tail-mixed_tail == pure_tail, 'exact complete outside-box tails')
    target = F(1, 2**100)
    eps_all, eps_mixed = 2*C_old*all_tail, 2*C_old*mixed_tail
    old_tail = old_sum-inside_old
    old_loss = C_old*old_tail
    pure_change = 2*pure_tail
    zeta = pure_change+eps_mixed
    require(0 < old_loss < target and eps_mixed < zeta < eps_all < target,
            'uniform exponent65 core controls every old, pure-current and mixed-current tail')
    old64 = old_sum-fi.multiply(finite_old_factor(p, 64) for p in PRIMES)
    require(C_old*old64 > target, 'uniform exponent64 fails this old-tail sufficient bound')
    K4 = F(prior['rare_family_stability']['K4_Haar'])
    epsilon0 = F(prior['uniform_comparisons']['physical_V_decrease_at_least'])
    t = F(prior['transfer']['t'])
    require(676*K4*target < epsilon0**2 and 400*K4*target < epsilon0**2,
            'both fixed-pure and arbitrary-pure AM square-error criteria')
    require(4*8*10 <= (36-8-10)**2 and 4*18*20 <= (81-18-20)**2,
            'exact squared checks for sqrt8+sqrt10<=6 and sqrt18+sqrt20<=9')
    rho_bound = (F(4, 17)-zeta-old_loss)/(1-old_loss)
    require(rho_bound > 0 and old_loss < F(1, 2), 'actual old conditioning and positive survivor lower bound')
    label_count = int(fi.multiply(b+1 for b in BOX[:-1]))*BOX[-1]
    return fi.encode(dict(
        schema='erdos7-average-mask-tails-v1',
        scope='Fixed FI2 finite exponent65 core on primes3,5,7,11,13,17; every old, pure-current and mixed-current forbidden residue beyond that core may be chosen independently at arbitrary finite physical heights. One actual old law conditions the reference PG1 product law on all new old survivors. All original labels remain present.',
        verification_scope='Exact source binding, rational constants, complete reciprocal tail formulas, and finite BB/repair fixtures. AM1--AM7 and the adjacent ordinary tail proof handle arbitrary heights and tests; finite checks are not formal Lean verification or exhaustive infinite-domain validation.',
        source_sha256=SOURCE_PINS,
        reused_FI=dict(K2=prior['moments']['K2'], K3=prior['moments']['K3'],
                       K4_Haar=prior['rare_family_stability']['K4_Haar'],
                       FI_epsilon=prior['uniform_comparisons']['physical_V_decrease_at_least']),
        old_law=dict(maximum_low_mass=maximum_mu, maximizing_points=maximum_points,
                     full_Haar_density_cap=C_old, cylinder_bound='nu(a mod d)<=C_old/d'),
        mask_measure='Fixed pure case: epsilon=E_nu0 Haar(B symmetric_difference B0) after restricting to the common pure base. Changing pure case: kappa=Haar(P symmetric_difference Pprime), eta=E_nu0 Haar(raw_D symmetric_difference raw_Dprime), zeta=kappa+eta. All budgets use nu0 before conditioning.',
        mask_bound='q<=C_old*T_old; kappa<=2*T_pure; eta<=2*C_old*T_mixed; zeta<=2*C_old*T_all',
        reciprocal_sums=dict(old_all=old_sum, current_positive=F(1, 16),
                             all_positive_current_labels=total, all_mixed_labels=total_mixed),
        box=dict(prime_order=list(PRIMES)+[17], inclusive_maximum_exponents=BOX,
                 current_minimum_exponent=1, all_inside_original_labels=label_count,
                 mixed_inside_original_labels=label_count-BOX[-1],
                 old_nonunit_inside_original_labels=int(fi.multiply(b+1 for b in BOX[:-1]))-1,
                 first_uniform_cutoff_meeting_old_tail_bound=65),
        exact_tails=dict(coordinate_excluded_fractions=excluded_fractions,
                         old_original=old_tail,
                         all_original_positive_current=all_tail,
                         fixed_pure_current= pure_tail, mixed_original=mixed_tail,
                         coordinate_union_upper=union_tail,
                         formula_all='(1001/6144)*(1-product_old(1-p^(-b_p-1))*(1-17^(-b17)))',
                         formula_mixed='all_tail-17^(-b17)/16'),
        mask_mass_bounds=dict(old_loss_q_upper=old_loss, pure_change_kappa_upper=pure_change,
                              raw_mixed_eta_upper=eps_mixed, total_zeta_upper=zeta,
                              all_label_upper=eps_all, mixed_label_upper=eps_mixed, threshold=target,
                              all_label_fraction_of_threshold=eps_all/target,
                              old_loss_fraction_of_threshold=old_loss/target,
                              zeta_fraction_of_threshold=zeta/target,
                              strict_margin=target-eps_all,
                              normalized_pure_base_upper=F(16, 15)*eps_all),
        AM_constants=dict(theta=target, K4_Haar=K4, epsilon0=epsilon0,
                          fixed_pure_squared_margin=epsilon0**2-400*K4*target,
                          arbitrary_pure_squared_margin=epsilon0**2-676*K4*target,
                          fixed_pure_error_squared_fraction=400*K4*target/epsilon0**2,
                          arbitrary_pure_error_squared_fraction=676*K4*target/epsilon0**2,
                          physical_and_killed_gain_lower=epsilon0/2,
                          conditioned_Gamma_gain='epsilon0/(2*rho_S)', actual_survivor_mass_lower=rho_bound),
        finite_label_fixtures=finite_fixtures(fi), controls=control_fixtures(fi, t),
        full_old_projection_example=full_projection_example(fi, case),
        fixed_second_moment_obstruction=fixed_second_moment_obstruction(fi)))


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
        def unique(pairs):
            obj = {}
            for key, value in pairs:
                require(key not in obj, 'duplicate certificate key: '+key)
                obj[key] = value
            return obj
        require(json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique) == result,
                'entire certificate equals exact recomputation')
    print(json.dumps(dict(C_old=result['old_law']['full_Haar_density_cap'],
                          box=result['box']['inclusive_maximum_exponents'],
                          epsilon_below_threshold=True,
                          certificate_action='written' if args.write else 'verified')))


if __name__ == '__main__':
    main()
