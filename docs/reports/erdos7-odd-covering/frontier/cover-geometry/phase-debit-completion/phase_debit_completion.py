#!/usr/bin/env python3
"""Independent exact N=K=4 check of the finite phase-debit gadget.

No repository producer is imported or run. Cylinder intersections are checked
by congruence, sequential row masses by the finite 5-adic carrier, and the
countable final-query tails by geometric sums. The actual all-label norm is
also reconstructed from conditional cylinder maxima and the constant-density
5-adic tail. Missing-slot completions are comparison choices only.
"""

from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import comb, prod, lcm
from pathlib import Path
import json


N = K = 4
ROWS = ((11, 2, (4, 0)), (13, 2, (4, 1)),
        (17, 4, (4, 2, 0, 0)), (19, 4, (4, 3, 0, 0)))
PRIMES = (5, 7, 11, 13, 17, 19)
OUTPUT = Path(__file__).with_suffix('.json')
checks = {}


def check(name, condition):
    if name in checks:
        raise RuntimeError('duplicate check: ' + name)
    if not condition:
        raise RuntimeError('failed: ' + name)
    checks[name] = True


def encode(digits):
    return sum(d * 5**i for i, d in enumerate(digits))


def hit(cylinder, point):
    return all(point.get(p, 0) % (p**e) == r for p, (e, r) in cylinder.items())


def meets(left, right):
    return all((left[p][1] - right[p][1]) % p**min(left[p][0], right[p][0]) == 0
               for p in left.keys() & right.keys())


def volume(cylinder):
    return F(1, prod(p**e for p, (e, _) in cylinder.items()))


def crt(cylinder):
    modulus = prod(p**e for p, (e, _) in cylinder.items())
    residue = sum(r * (modulus // p**e) * pow(modulus // p**e, -1, p**e)
                  for p, (e, r) in cylinder.items()) % modulus
    return modulus, residue


originals = []


def add(kind, cylinder, private, **metadata):
    modulus, residue = crt(cylinder)
    originals.append(dict(kind=kind, cylinder=cylinder, modulus=modulus,
                          residue=residue, private=private, **metadata))


for p in (5, 7):
    for e in range(1, N + 1):
        for c in (1, 2):
            r = c * p**(e - 1)
            add('pure' + str(p), {p: (e, r)}, {p: r}, prime=p, depth=e, digit=c)

for a in range(1, N + 1):
    for b in range(1, N + 1):
        for c in (3, 4):
            x5, x7 = 3 * 5**(a - 1), c * 7**(b - 1)
            add('mixed57', {5: (a, x5), 7: (b, x7)}, {5: x5, 7: x7},
                depth5=a, depth7=b, digit7=c)

for q, t, path in ROWS:
    for e in range(1, K + 1):
        for i in range(1, t + 2):
            for c in (2*i - 1, 2*i):
                cylinder = {q: (e, c*q**(e - 1))}
                x5 = 4
                if i > 1:
                    x5 = encode(path[:i-1])
                    cylinder[5] = (i-1, x5)
                add('later', cylinder, {5: x5, q: c*q**(e - 1)},
                    prime=q, depth=e, slot=i, digit=c)

pure = {p: [r for r in originals if r['kind'] == 'pure' + str(p)] for p in (5, 7)}
mixed = [r for r in originals if r['kind'] == 'mixed57']
labels = Counter(r['modulus'] for r in originals)
check('176_actual_original_classes', len(originals) == 176)
check('88_labels_with_exactly_two_occurrences', len(labels) == 88 and set(labels.values()) == {2})
check('odd_nonunit_labels', all(d > 1 and d % 2 for d in labels))
check('all_zero_is_actual_survivor', not any(hit(r['cylinder'], {}) for r in originals))
check('all_176_explicit_private_points', all(hit(r['cylinder'], r['private']) and
      sum(hit(s['cylinder'], r['private']) for s in originals) == 1 for r in originals))
check('CRT_encoding_preserves_all_coordinate_phases', all(
    r['residue'] % (p**e) == a for r in originals for p, (e, a) in r['cylinder'].items()))
for p in (5, 7):
    check('pure_%d_prefixes_disjoint' % p, all(not meets(r['cylinder'], s['cylinder'])
          for r, s in combinations(pure[p], 2)))
check('32_mixed_rectangles_pairwise_disjoint', len(mixed) == 32 and
      all(not meets(r['cylinder'], s['cylinder']) for r, s in combinations(mixed, 2)))
check('mixed_rectangles_avoid_all_pure_5_7_classes', all(
    not meets(r['cylinder'], s['cylinder']) for r in mixed for p in (5, 7) for s in pure[p]))
check('mixed_5_roots_are_only_0_or_3', {r['cylinder'][5][1] % 5 for r in mixed} == {0, 3})
check('mixed_7_roots_are_only_0_3_4', {r['cylinder'][7][1] % 7 for r in mixed} == {0, 3, 4})
check('nested_25_and_125_originals', all(r['residue'] % 5 == 0 for r in pure[5] if r['depth'] == 2)
      and all(r['residue'] % 25 == 0 for r in pure[5] if r['depth'] == 3))

u = {p: sum((volume(r['cylinder']) for r in pure[p]), F(0)) for p in (5, 7)}
w = {p: 1-u[p] for p in (5, 7)}
d5, d7 = F(1, 2)-u[5], F(1, 3)-u[7]
m = sum((volume(r['cylinder']) for r in mixed), F(0))
m5 = sum((F(1, 5**a) for a in range(1, N+1)), F(0))
m7 = 2*sum((F(1, 7**b) for b in range(1, N+1)), F(0))
check('mixed_mass_product_formula', m == m5*m7 == F(1, 12)*(1-F(1, 5**N))*(1-F(1, 7**N)))
check('reported_finite_anchor_values', (m, F(1, 12)-m, d5, d7, w[7]) ==
      (F(4992, 60025), F(121, 720300), F(1, 1250), F(1, 7203), F(1601, 2401)))

deep = {q: {5: (t, encode(path))} for q, t, path in ROWS}
check('four_deep_cells_pairwise_disjoint', all(not meets(x, y) for x, y in combinations(deep.values(), 2)))
check('all_deep_cells_in_root_4', all(c[5][1] % 5 == 4 for c in deep.values()))
check('deep_cells_avoid_pure_5_and_mixed_anchor_originals', all(
    not meets(c, r['cylinder']) for c in deep.values() for r in originals
    if r['kind'] in ('pure5', 'mixed57')))
# A 5-cell is not disjoint from the pure-7 cylinders. Their remaining mass
# is the factor w7 retained in every predeep mass and row-loss formula.

# Exact finite history marginal: sum the 7-coordinate analytically on each of
# the 625 residue classes. No complete multidimensional period is enumerated.
carrier5 = 5**N
mixed5 = [{5: (a, 3*5**(a-1))} for a in range(1, N+1)]
weights = []
removed_weights = []
for x in range(carrier5):
    point = {5: x}
    live5 = not any(hit(r['cylinder'], point) for r in pure[5])
    in_mixed5 = any(hit(c, point) for c in mixed5)
    weights.append((w[7]-m7*in_mixed5)/carrier5 if live5 else F(0))
    removed_weights.append(m7/carrier5 if in_mixed5 else F(0))
anchor_mass = sum(weights, F(0))
check('history_marginal_is_exact_anchor_mass', anchor_mass == w[5]*w[7]-m == F(53759, 214375))
check('removed_history_marginal_is_exact_mixed_mass', sum(removed_weights, F(0)) == m)

row_results = {}
row_history_factors = {}
ratios_expected = {11: F(7319, 7320), 13: F(14279, 14280),
                   17: F(20879, 20880), 19: F(32579, 32580)}
completed_removed_weights = list(removed_weights)
for q, t, path in ROWS:
    C = F(q-1, q-1-2*t)
    a = F(2, q-1-2*t)
    rows = [r for r in originals if r['kind'] == 'later' and r['prime'] == q]
    check('q%d_forbidden_q_prefixes_pairwise_disjoint' % q, all(
        not meets({q: r['cylinder'][q]}, {q: s['cylinder'][q]}) for r, s in combinations(rows, 2)))
    check('q%d_original_digits_nonzero_and_below_query_digit' % q,
          all(0 < r['digit'] < q-1 for r in rows))
    kvals, smass, local_forbidden = [], [], []
    for x in range(carrier5):
        k = 1 + sum(x % 5**depth == encode(path[:depth]) for depth in range(1, t+1))
        # Sum the volumes of the actual, explicitly listed q cylinders that
        # are active at this 5-history. Prefix disjointness makes this exact.
        b = sum((F(1, q**r['depth']) for r in rows
                 if 5 not in r['cylinder'] or x % 5**r['cylinder'][5][0] == r['cylinder'][5][1]), F(0))
        kvals.append(k)
        local_forbidden.append(b)
        smass.append(min(F(1), C*(1-b)))
    check('q%d_actual_fibre_fraction_formula' % q, all(
        b == F(2*k, q-1)*(1-F(1, q**K)) for k, b in zip(kvals, local_forbidden)))
    ell = a*(1-F(t+1, q**K))
    check('q%d_loss_only_on_deepest_cell' % q, all(
        1-s == (ell if hit(deep[q], {5: x}) else 0) for x, s in enumerate(smass)))
    predeep = sum((weight for x, weight in enumerate(weights) if hit(deep[q], {5: x})), F(0))
    check('q%d_previous_rows_preserve_current_deep_mass' % q, predeep == w[7]/5**t)
    actual_loss = sum((weight*(1-s) for weight, s in zip(weights, smass)), F(0))
    check('q%d_sequential_loss_formula' % q, actual_loss == w[7]/5**t*ell)
    old_hinge = sum((weight*max(k-t, 0) for weight, k in zip(weights, kvals)), F(0))
    charge = a*(1-F(1, q**K))*old_hinge
    check('q%d_exact_local_Jensen_charge' % q, charge == w[7]/5**t*a*(1-F(1, q**K)))
    check('q%d_Jensen_ratio' % q, actual_loss/charge == ratios_expected[q])
    check('q%d_charge_slack' % q, charge-actual_loss == w[7]/5**t*a*t/q**K)
    check('q%d_completed_rows_equal_actual_rows_on_removed_set' % q, all(
        kvals[x] == 1 and smass[x] == 1 for x, weight in enumerate(removed_weights) if weight))
    stage_debit = (1-F(1, q**K))*sum((weight*max(k-t, 0)
                    for weight, k in zip(completed_removed_weights, kvals)), F(0))
    check('q%d_stage_debit_zero_with_declared_completion' % q, stage_debit == 0)
    # Missing query phases are placed in forbidden pure roots. On actual
    # support and on transported eta each such root has density zero.
    check('q%d_missing_old_5_7_phases_are_forbidden' % q,
          any(r['cylinder'] == {5: (1, 1)} for r in pure[5]) and
          any(r['cylinder'] == {7: (1, 1)} for r in pure[7]))
    preceding = [p for p, _, _ in ROWS if p < q]
    check('q%d_missing_later_only_phases_are_forbidden_on_eta' % q, all(
        any(r['kind'] == 'later' and r['prime'] == p and r['slot'] == 1
            and r['depth'] == 1 and r['digit'] == 1 for r in originals) for p in preceding))
    weights = [weight*s for weight, s in zip(weights, smass)]
    # Completed kernels are probability kernels and do not change x5.
    g_on_removed = 1-F(2, q-1)*(1-F(1, q**K))
    r_query = F(1, q-1)/g_on_removed
    check('q%d_all_depth_query_probability_formula' % q,
          r_query == F(q**K, (q-3)*q**K+2))
    row_results[q] = dict(threshold=t, cap=C, coefficient=a,
                         deepest_residue=encode(path), deepest_depth=t,
                         mass_before_on_deepest_cell=predeep, pointwise_deep_loss=ell,
                         actual_loss=actual_loss, local_Jensen_charge=charge,
                         loss_charge_ratio=actual_loss/charge, stage_debit=stage_debit,
                         g_on_removed_set=g_on_removed, final_query_probability=r_query)
    row_history_factors[q] = dict(
        density=[min(C, 1/(1-b)) for b in local_forbidden], mass=smass)

final_mass = sum(weights, F(0))
check('one_unnormalized_sequential_mass_identity',
      final_mass == anchor_mass-sum((r['actual_loss'] for r in row_results.values()), F(0)))
check('actual_final_mass_positive', final_mass > 0)
check('stage_debits_all_zero', all(r['stage_debit'] == 0 for r in row_results.values()))

# Prefix-free cylinders 0^(n-1)(q-1) for ALL n are disjoint from each
# original 0^(e-1)c: if n=e digits differ, otherwise the first nonzero
# digit of the shorter word faces zero. Their Haar mass is 1/(q-1).
# On eta all rows have k=1 and depend on no other later coordinate,
# so the four resulting indicators are independent Bernoulli variables.
rs = [row_results[q]['final_query_probability'] for q, _, _ in ROWS]
check('reported_query_probabilities', rs == [F(14641, 117130), F(28561, 285612),
      F(83521, 1169296), F(130321, 2085138)])
elementary = {j: sum((prod(part) for part in combinations(rs, j)), F(0)) for j in (2, 3, 4)}
direct_hinge = F(0)
bernoulli_results = []
for bits in product((0, 1), repeat=4):
    probability = prod(r if bit else 1-r for bit, r in zip(bits, rs))
    kappa = sum(bits)
    payoff = max(2**kappa-3, 0)
    check('hinge_polynomial_at_k%d_pattern%s' % (kappa, ''.join(map(str, bits))),
          payoff == comb(kappa, 2)+2*comb(kappa, 3)-comb(kappa, 4))
    direct_hinge += probability*payoff
    bernoulli_results.append(dict(bits=bits, probability=probability, load=2**kappa, hinge=payoff))
check('16_pattern_probability_is_one', sum((r['probability'] for r in bernoulli_results), F(0)) == 1)
check('final_hinge_elementary_symmetric_formula',
      direct_hinge == elementary[2]+2*elementary[3]-elementary[4])
check('reported_final_hinge', direct_hinge == F(4273900631016651774307, 81565003794396764378880))
JL = m*direct_hinge
check('reported_JL', JL == F(610557233002378824901, 140108154554677935606750))

c0 = F(6168733163201163811, 542935350932041267200)
A5 = F(44887686823492905683, 27146767546602063360)
A7 = F(20281636668601030051, 20313907687933516800)
A57 = F(585035299774741193, 203139076879335168)
pure_credit = A5*d5+A7*d7+A57*d5*d7
mixed_credit = (F(257, 51)-2)*(F(1, 12)-m)
gap = c0-pure_credit-mixed_credit-JL
check('reported_pure_credit', pure_credit == F(1909679866745396595103, 1306438188180224299200000))
check('reported_mixed_credit', mixed_credit == F(3751, 7347060))
check('reported_positive_gap', gap == F(389314337271786978910446370296350517,
      77371208531501661979950475298771200000) and gap > 0)
limrs = [F(1, q-3) for q, _, _ in ROWS]
limhinge = sum((prod(part) for part in combinations(limrs, 2)), F(0)) \
    +2*sum((prod(part) for part in combinations(limrs, 3)), F(0))-prod(limrs)
limloss = sum((F(2, 3*5**t)*F(2, q-1-2*t) for q, t, _ in ROWS), F(0))
check('reported_limiting_hinge', limhinge == F(939, 17920))
check('reported_limiting_JL', limhinge/12 == F(313, 71680))
check('reported_limiting_row_loss_sum', limloss == F(451, 28125))
check('reported_limiting_gap', c0-limhinge/12 == F(1898967831309504083, 271467675466020633600))

# Independent actual all-depth norm. A safe later query q-1 modulo q^e
# attains h_q(x5)/q^e at EVERY old history, while an unqueried coordinate
# contributes its row mass s_q(x5). A queried 7-coordinate uses safe root 5,
# so its factor is 7^-b instead of the integrated surviving 7 mass. Aggregate
# the 625 constant-density cells bottom-up in the residue-prefix tree.
norm_profiles = []
complete_raw_query_sum = F(0)
for mask in range(16):
    selected = {q for i, (q, _, _) in enumerate(ROWS) if mask & (1 << i)}
    weighted_depth_totals = []
    for has7 in (False, True):
        leaves = []
        for x in range(carrier5):
            live5 = not any(hit(r['cylinder'], {5: x}) for r in pure[5])
            in_mixed5 = any(hit(c, {5: x}) for c in mixed5)
            conditional_factor = prod(row_history_factors[q][
                'density' if q in selected else 'mass'][x] for q, _, _ in ROWS)
            seven_factor = F(1) if has7 else w[7]-m7*in_mixed5
            leaves.append(seven_factor*conditional_factor/carrier5 if live5 else F(0))
        tree = {N: leaves}
        for depth in range(N-1, -1, -1):
            count = 5**depth
            children = tree[depth+1]
            tree[depth] = [sum((children[r+j*count] for j in range(5)), F(0))
                           for r in range(count)]
        maxima = [max(tree[depth]) for depth in range(N+1)]
        roots = [sorted({r % 5 for r, mass in enumerate(tree[depth]) if mass == maxima[depth]})
                 for depth in range(N+1)]
        # At a>N each 5-cylinder lies inside one original depth-N cell,
        # where every factor is constant. Summing all further maxima gives
        # max_N * sum_{j>=1}5^-j = max_N/4 exactly.
        all_depths = sum(maxima, F(0))+maxima[N]/4
        weighted_depth_totals.append(all_depths)
        norm_profiles.append(dict(later_mask=mask, contains7=has7,
                                  depth_maxima=maxima, maximizing_roots=roots,
                                  complete_5_depth_sum=all_depths))
        if not has7:
            check('actual_norm_mask%d_positive_5_depths_admit_root4' % mask,
                  all(4 in roots[depth] for depth in range(1, N+1)))
        if not selected and has7:
            check('actual_norm_5_7_control_root3_strictly_beats_root4', 3 in roots[1] and 4 not in roots[1])
        if not selected and not has7:
            check('actual_norm_unit_is_final_unnormalized_mass', maxima[0] == final_mass)
    later_exponent_sum = prod(F(1, q-1) for q in selected)
    complete_raw_query_sum += later_exponent_sum*(weighted_depth_totals[0]+weighted_depth_totals[1]/6)
actual_norm = complete_raw_query_sum/final_mass-1
check('actual_all_depth_norm_matches_independent_root_result', actual_norm == F(
    28910445817468311387876570938125683440809953920799874748454507061303396366140761311,
    12819829015616627078469015194714652014097027856899937287868470899215252808291827200))
check('actual_all_depth_norm_strictly_below_target', actual_norm < F(257, 51))

# Nested safe later cylinders give Nq=1+number of active nested exponents.
# E product(Nq) is a product of first moments. Since product(Nq) is a
# positive integer, only its values 1 and 2 need correction in E(X-3)+.
h_eta = {q: 1/row_results[q]['g_on_removed_set'] for q, _, _ in ROWS}
p_one = {q: 1-h_eta[q]/q for q, _, _ in ROWS}
p_two = {q: h_eta[q]*(q-1)/q**2 for q, _, _ in ROWS}
nested_mean = prod(1+h_eta[q]/(q-1) for q, _, _ in ROWS)
nested_hinge = nested_mean-3+2*prod(p_one.values())+sum((
    p_two[q]*prod(p_one[p] for p, _, _ in ROWS if p != q) for q, _, _ in ROWS), F(0))
nested_JL = m*nested_hinge
nested_gap = c0-pure_credit-mixed_credit-nested_JL
check('nested_final_hinge_exact', nested_hinge == F(4841508204833317525789, 81565003794396764378880))
check('nested_final_JL_matches_analytic_maximizer_formula', nested_JL == F(
    4841508204833317525789, 980757081882745549247250))
check('zero_completion_nested_maximizer_gap_positive', nested_gap == F(
    1033608573342003864932556253000744351,
    232113625594504985939851425896313600000) and nested_gap > 0)

# Completion repair: no original full 11-label has cofactor 7 or 35.
# At EVERY exponent, retain actual phases and add missing 7/35 phases.
# Empty exponents beyond K still have unit and both comparison phases.
first11 = [r for r in originals if r['kind'] == 'later' and r['prime'] == 11]
check('all_actual_first11_cofactors_are_1_5_25',
      {r['modulus']//11**r['depth'] for r in first11} == {1, 5, 25})
check('no_actual_7_times_11_power_or_35_times_11_power',
      all(7 not in r['cylinder'] for r in first11))
check('first11_occupied_old_5_25_phases_retained', all(
    r['cylinder'][5] == (r['slot']-1, 4) for r in first11 if r['slot'] > 1))
repair_R = {5: (1, 3), 7: (1, 3)}
check('repair_R_is_one_whole_actual_mixed_rectangle',
      sum(r['cylinder'] == repair_R for r in mixed) == 1)
repair_eta_R = F(0)
repair_hinge_integral = F(0)
repair_hinges = []
for r in mixed:
    root5, root7 = r['cylinder'][5][1] % 5, r['cylinder'][7][1] % 7
    in_R = root5 == 3 and root7 == 3
    old_load = 1+int(root7 == 3)+int(in_R)
    hinge = max(old_load-2, 0)
    check('repaired_hinge_rectangle_%d_%d_%d' % (r['depth5'], r['depth7'], r['digit7']),
          hinge == int(in_R))
    repair_eta_R += volume(r['cylinder'])*in_R
    repair_hinge_integral += volume(r['cylinder'])*hinge
    repair_hinges.append(dict(depth5=r['depth5'], depth7=r['depth7'], digit7=r['digit7'],
                              completed_load=old_load, hinge=hinge))
beta_head = sum((F(10, 2*11**e) for e in range(1, K+1) for _ in range(2)), F(0))
beta_tail = F(1, 11**K)
check('both_slot_beta_weights_head_plus_full_tail', beta_head+beta_tail == 1)
check('repair_removed_R_mass_exact', repair_eta_R == repair_hinge_integral == F(1, 35))
repair_J11 = (beta_head+beta_tail)*repair_hinge_integral
repair_credit = (F(257, 51)-2)*repair_J11/3
repair_margin = repair_credit-c0
check('repair_J11_includes_absent_exponent_tail', repair_J11 == F(1, 35))
check('repair_credit_exact', repair_credit == F(31, 1071))
check('repair_margin_positive', repair_margin == F(9546482409995175389, 542935350932041267200)
      and repair_margin > 0)

# Separate numerical checks for the general Gamma / phase-sensitive theorem.
# These constants are independent of the fixed gadget and do not assume
# eta(R)=1/35: the ordinary proof supplies eta(C)>=1/35-delta.
T = F(257, 51)
gamma_crit = 105*c0/(T-2)
general_margin = (T-2)*F(5, 11)/105-c0
check('general_Gamma_threshold_exact_and_below_5_over_11',
      gamma_crit == F(6168733163201163811, 15715215573196339200) and gamma_crit < F(5, 11))
check('general_5_over_11_margin_positive',
      general_margin == F(974546642797172189, 542935350932041267200) and general_margin > 0)
check('every_pair_of_5_7_35_has_lcm_35', all(lcm(a, b) == 35 for a, b in combinations((5, 7, 35), 2)))
count_pattern_checks = []
for counts in product(range(3), repeat=3):
    at_most_one_full = sum(n == 2 for n in counts) <= 1
    usable_pair = any(counts[i] <= 1 and counts[j] <= 1 for i, j in combinations(range(3), 2))
    count_pattern_checks.append(at_most_one_full == usable_pair)
check('all_27_numerical_two_of_three_patterns', len(count_pattern_checks) == 27 and all(count_pattern_checks))
slot_cases = [(n, r) for n in range(3) for r in range(n+1)]
slot_guard_results = []
for case in product(slot_cases, repeat=3):
    active = []
    valid = True
    for n, r in case:
        slots = ['matching']*r+['empty']*(2-n)+['nonmatching']*(n-r)
        s = 2-n+r
        active.append(s)
        valid = valid and len(slots) == 2 and all(
            (entry in ('matching', 'empty')) == (i < s) for i, entry in enumerate(slots))
    k1, k2 = sum(s >= 1 for s in active), sum(s == 2 for s in active)
    M = max(k1-1, 0)+max(k2-1, 0)
    slot_guard_results.append(valid and ((M >= 1) == (sum(s > 0 for s in active) >= 2)))
check('all_216_matching_empty_slot_alignment_patterns',
      len(slot_guard_results) == 216 and all(slot_guard_results))


def rationalize(value):
    if isinstance(value, F):
        return str(value.numerator) + '/' + str(value.denominator)
    if isinstance(value, dict):
        return {str(key): rationalize(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [rationalize(item) for item in value]
    return value


result = dict(
    scope='N=K=4 actual two-copy six-prime family; zero-debit and repaired legal completions; prefix-free and nested query hinges; exact actual all-depth norm; rational constants and finite slot guards for the general criterion',
    arithmetic='exact integer congruences and Fraction; no floating-point decisions; no old producer import',
    N=N, K=K, prime_support=PRIMES, original_count=len(originals), numerical_label_count=len(labels),
    originals=originals, pure_forbidden_masses=u, pure_survivor_masses=w,
    pure_deficits={5:d5, 7:d7}, mixed_mass=m, mixed_mass_saving=F(1, 12)-m,
    initial_actual_mass=anchor_mass, rows=row_results, final_actual_subprobability_mass=final_mass,
    slot_completion='Keep actual old phases. Missing labels containing 5 use pure forbidden root 1 at 5; otherwise labels containing 7 use root 1 at 7; later-only labels use root 1 at one previous later prime. Unit is 1. Empty later exponent slots have zero hinge.',
    final_query_layout='Any label containing 5 uses 5-root 4; otherwise any label containing 7 uses 7-root 5. Each positive later exponent n uses prefix 0^(n-1)(q-1); absent coordinates are unrestricted. These choices are fixed globally and are not asserted maximal.',
    countable_query_justification='Prefix-free later query cylinders avoid every original q digit; their geometric Haar sum is 1/(q-1). On transported eta all completed kernels equal actual normalized rows and depend only on the fixed value k=1, giving the four independent Bernoulli indicators. Finite inventories increase to the displayed all-depth load.',
    elementary_symmetric=elementary, bernoulli_patterns=bernoulli_results,
    final_hinge=direct_hinge, J_L=JL,
    actual_query_norm=dict(value=actual_norm, complete_raw_sum_including_unit=complete_raw_query_sum,
        profiles=norm_profiles, later_masks=16, old5_cells=carrier5,
        exact_tail='Beyond 5-depth four every density is constant on its old cell; sum of maxima equals depth-four maximum / 4. Positive 7 and later exponents contribute geometric factors 1/6 and 1/(q-1).'),
    nested_query=dict(first_moment=nested_mean, hinge=nested_hinge, J_L=nested_JL,
        zero_completion_gap=nested_gap,
        scope='Checks the exact nested safe-query value in the analytic maximizer theorem; the universal maximality proof is not replaced by this finite arithmetic.'),
    repaired_completion=dict(old_cofactors=(7,35), fixed_R=repair_R,
        declaration='At every first11 exponent and in both slots, retain actual phases, include the unit, complete cofactor 7 to root 3 and cofactor 35 to roots (3,3). Put all other missing phases in pure forbidden prefixes. This includes every absent exponent beyond K.',
        removed_R_mass=repair_eta_R, head_beta=beta_head, tail_beta=beta_tail,
        J11=repair_J11, credit=repair_credit, margin=repair_margin, rectangle_hinges=repair_hinges),
    general_criterion=dict(Gamma_critical=gamma_crit, exponent_one_weight=F(5,11),
        margin=general_margin, numerical_count_patterns=27, matching_empty_slot_patterns=216,
        scope='Rational constants and finite slot logic only; the same-family eta(C)>=1/35-delta bound and general all-depth theorem are ordinary proofs.'),
    NC4_constants=dict(c0=c0, A5=A5, A7=A7, A57=A57),
    credits=dict(pure=pure_credit, mixed_mass=mixed_credit, stage=F(0), final_query=JL),
    remaining_gap=gap,
    limits=dict(row_loss_sum=limloss, final_hinge=limhinge, J_L=limhinge/12, gap=c0-limhinge/12),
    verification_counts=dict(mixed_pair_intersections=comb(len(mixed), 2),
        mixed_pure_intersections=len(mixed)*sum(map(len, pure.values())),
        private_point_class_incidence_checks=len(originals)**2,
        five_adic_histories=carrier5, bernoulli_patterns=16),
    checks=checks, passed_count=len(checks), complete=True,
    boundaries=['No Lean verification.', 'Nested all-maximizer classification is an ordinary analytic theorem, not implied by fixed-instance tests.',
        'No all-laws lower witness.', 'The actual PA query norm is strictly below 257/51.',
        'No transfer from this two-copy six-prime family to unrestricted Erdos #7.'])
OUTPUT.write_text(json.dumps(rationalize(result), indent=2, ensure_ascii=False) + '\n')
print(json.dumps(dict(output=str(OUTPUT), passed_count=len(checks), original_count=len(originals),
                     final_mass=str(final_mass), J_L=str(JL), gap=str(gap),
                     output_sha256=sha256(OUTPUT.read_bytes()).hexdigest())))
