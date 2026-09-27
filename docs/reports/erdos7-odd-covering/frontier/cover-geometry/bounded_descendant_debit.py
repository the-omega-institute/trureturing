#!/usr/bin/env python3
"""Exact finite witness for a missing first-eleven descendant-slot debit.

The 1225 descendants are measured under Haar restricted to one 35-cylinder,
not under the actual removed measure eta. Transfer to eta uses the bounded
payoff defect estimate from the ordinary proof. No family scan, repository
producer, external input, or floating-point decision is used.
"""

from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod, lcm
from pathlib import Path
import json


checks = {}


def check(name, condition):
    if name in checks or not condition:
        raise RuntimeError('failed or duplicate check: ' + name)
    checks[name] = True


def hit(cylinder, point):
    return all(point[p] % p**e == residue for p, (e, residue) in cylinder.items())


def crt(cylinder):
    modulus = prod(p**e for p, (e, _) in cylinder.items())
    residue = sum(a*(modulus//p**e)*pow(modulus//p**e, -1, p**e)
                  for p, (e, a) in cylinder.items()) % modulus
    return modulus, residue


# Fix C once. Descendant choices are harmless translations; both slots use
# these same choices. The original C and every other original phase are fixed.
C = {5: (1, 3), 7: (1, 4)}
A1 = {5: (2, 8)}
A2 = {5: (3, 58)}
B1 = {7: (2, 18)}
B2 = {7: (3, 165)}
queries = {
    25: A1, 125: A2, 49: B1, 343: B2,
    175: {**A1, 7: C[7]}, 875: {**A2, 7: C[7]},
    245: {5: C[5], **B1}, 1715: {5: C[5], **B2},
}
D = (25, 125, 49, 343, 175, 875, 245, 1715)
check('eight_distinct_missing_cofactors', set(queries) == set(D) and len(queries) == 8)
check('all_query_CRT_moduli_are_declared_labels', all(crt(q)[0] == d for d, q in queries.items()))
check('all_full_labels_have_exactly_one_factor_eleven', all((11*d) % 121 for d in D))
check('no_conflict_between_full_labels_or_unit', len({11*d for d in D}) == 8 and 1 not in D)
check('nested_five_descendants_preserve_C_phase', 58 % 25 == 8 and 8 % 5 == 3)
check('nested_seven_descendants_preserve_C_phase', 165 % 49 == 18 and 18 % 7 == 4)
check('mixed_companions_preserve_both_C_roots', all(
    all(residue % p == C[p][1] for p, (_, residue) in queries[d].items())
    for d in (175, 875, 245, 1715)))

# Hypothesis is absence of the eight FULL labels at first 11 exponent only.
# In particular it imposes no restriction at 11^e*d when e>=2.
occupancy = {11*d: 0 for d in D}
check('both_slots_available_at_every_selected_full_label', all(2-n == 2 for n in occupancy.values()))
slot_queries = [dict(queries), dict(queries)]
check('one_fixed_completion_in_both_slots', slot_queries[0] == slot_queries[1])

hist5 = {s: 0 for s in range(3)}
hist7 = {s: 0 for s in range(3)}
for j in range(25):
    point = {5: C[5][1]+5*j}
    hist5[int(hit(A1, point))+int(hit(A2, point))] += 1
for j in range(49):
    point = {7: C[7][1]+7*j}
    hist7[int(hit(B1, point))+int(hit(B2, point))] += 1
distribution5 = {s: F(count, 25) for s, count in hist5.items()}
distribution7 = {s: F(count, 49) for s, count in hist7.items()}
check('five_Haar_conditional_count_distribution', distribution5 == {0:F(4,5), 1:F(4,25), 2:F(1,25)})
check('seven_Haar_conditional_count_distribution', distribution7 == {0:F(6,7), 1:F(6,49), 2:F(1,49)})

joint_counts = {(s5, s7): 0 for s5 in range(3) for s7 in range(3)}
payoff_counts = {0: 0, 1: 0, 3: 0}
cell_payoffs = []
load_identity_ok = bounded_hinge_ok = True
for j5, j7 in product(range(25), range(49)):
    point = {5: C[5][1]+5*j5, 7: C[7][1]+7*j7}
    s5 = int(hit(A1, point))+int(hit(A2, point))
    s7 = int(hit(B1, point))+int(hit(B2, point))
    joint_counts[s5, s7] += 1
    actual_selected_load = 1+sum(hit(query, point) for query in queries.values())
    hinge = max(actual_selected_load-2, 0)
    payoff = min(3, max(2*s5+2*s7-1, 0))
    load_identity_ok &= actual_selected_load == 1+2*s5+2*s7
    bounded_hinge_ok &= 0 <= payoff <= 3 and payoff <= hinge
    payoff_counts[payoff] += 1
    cell_payoffs.append(payoff)
check('all_1225_literal_CRT_loads_match_companion_formula', load_identity_ok)
check('all_1225_payoffs_are_nonnegative_bounded_hinge_lower_witnesses', bounded_hinge_ok)
check('joint_Haar_distribution_is_product', all(
    count == hist5[s5]*hist7[s7] for (s5, s7), count in joint_counts.items()))
check('payoff_histogram', payoff_counts == {0:840, 1:288, 3:97})
conditional_expectation = sum((F(value*count, 1225) for value, count in payoff_counts.items()), F(0))
raw_integral = F(1,35)*conditional_expectation
check('conditional_payoff_expectation', conditional_expectation == F(579,1225))
check('raw_C_payoff_integral', raw_integral == F(579,42875))

# Most damaging deletion removes high-payoff cells first. Equal masses make
# this exact by the elementary exchange argument. Check every whole-cell
# deletion and every half-cell deletion. At the three payoff transitions,
# the piecewise linear formula gives the entire fractional-mass envelope.
denominator = 35*1225
descending = sorted(cell_payoffs, reverse=True)
check('extremal_deletion_order_is_nonincreasing', all(a >= b for a,b in zip(descending,descending[1:])))
removed_payoff = 0
whole_checks = half_checks = 0
extreme_ok = True
for k in range(1226):
    epsilon = F(k,denominator)
    retained = raw_integral-F(removed_payoff,denominator)
    extreme_ok &= retained >= raw_integral-3*epsilon
    whole_checks += 1
    if k < 1225:
        epsilon_half = F(2*k+1,2*denominator)
        retained_half = raw_integral-F(2*removed_payoff+descending[k],2*denominator)
        extreme_ok &= retained_half >= raw_integral-3*epsilon_half
        half_checks += 1
        removed_payoff += descending[k]
check('all_extreme_whole_and_half_cell_deletions_obey_defect_bound', extreme_ok)
check('extreme_deletion_checks_cover_all_cells', (whole_checks,half_checks) == (1226,1225))
breakpoints = []
removed_payoff = 0
removed_count = 0
for payoff in (3,1,0):
    removed_count += payoff_counts[payoff]
    removed_payoff += payoff*payoff_counts[payoff]
    breakpoints.append(dict(deleted_mass=F(removed_count,denominator),
                            remaining_integral=raw_integral-F(removed_payoff,denominator)))
check('bounded_loss_constant_three_is_sharp_before_first_breakpoint',
      breakpoints[0]['remaining_integral'] == raw_integral-3*breakpoints[0]['deleted_mass'])

# Pointwise model of the raw-cap defect: count original memberships with
# multiplicity, then subtract the indicator of their union inside the pure
# survivor. This is >=1_C outside that actual removed union. The ordinary
# argument holds for any membership count; these 32 cells guard signs and
# the placement of the pure-survivor restriction.
pointwise_defect_ok = True
for memberships in product((0,1), repeat=4):
    for pure_survives in (0,1):
        in_U = int(pure_survives and any(memberships))
        defect = sum(memberships)-in_U
        loss_C = memberships[0]*(1-in_U)
        pointwise_defect_ok &= defect >= loss_C
check('32_pointwise_raw_defect_cells_have_correct_direction', pointwise_defect_ok)

beta_per_slot = F(5,11)
beta_two_slots = 2*beta_per_slot
constant = beta_two_slots*raw_integral/3
delta_coefficient = 1-beta_two_slots
check('both_first_exponent_beta_weights', beta_two_slots == F(10,11))
check('delta_after_bounded_debit_has_positive_coefficient', delta_coefficient == F(1,11))
check('uniform_mass_credit_constant', constant == F(386,94325))
check('large_delta_branch_already_supplies_same_credit', F(1,35) > constant)

T = F(257,51)
c0 = F(6168733163201163811,542935350932041267200)
credit = (T-2)*constant
margin = credit-c0
check('claimed_exact_total_credit', credit == F(11966,962115))
check('total_credit_strictly_exceeds_PA_gap', margin > 0)
check('missing_modulus35_branch_closes_directly', (T-2)*F(1,35) > c0)

# A literal separation family for the earlier single-pair/PS1 criteria.
# Its arithmetic is reconstructed here, not read from a previous producer.
fixture = []
support = (5,7,11,13,17,19)


def add_original(kind,cylinder,private):
    coordinates = {p:private.get(p,0) for p in support}
    modulus,residue = crt(cylinder)
    fixture.append(dict(kind=kind,cylinder=cylinder,modulus=modulus,
                        residue=residue,private=coordinates))


for p in (5,7):
    for depth in range(1,5):
        for digit in (1,2):
            residue=digit*p**(depth-1)
            add_original('pure'+str(p),{p:(depth,residue)},{p:residue})
for a,b in product(range(1,5),repeat=2):
    for digit7 in (3,4):
        x5,x7=3*5**(a-1),digit7*7**(b-1)
        add_original('mixed57',{5:(a,x5),7:(b,x7)},{5:x5,7:x7})
for old,digits in (({5:(1,4)},(1,2)),({7:(1,5)},(3,4)),
                   ({5:(1,4),7:(1,5)},(5,6))):
    for digit in digits:
        add_original('first11',{**old,11:(1,digit)},
                     {**{p:r for p,(_,r) in old.items()},11:digit})
for p in (13,17,19):
    add_original('laterpure',{p:(1,1)},{p:1})
label_counts = {}
for original in fixture:
    d=original['modulus']
    label_counts[d]=label_counts.get(d,0)+1
check('separation_fixture_has_57_originals_30_labels', len(fixture)==57 and len(label_counts)==30)
check('separation_fixture_multiplicity_at_most_two', max(label_counts.values())==2)
check('separation_fixture_full_six_prime_support',
      set().union(*(r['cylinder'].keys() for r in fixture))==set(support))
check('separation_fixture_all_zero_survives', not any(hit(r['cylinder'],dict.fromkeys(support,0)) for r in fixture))
check('separation_fixture_all_57_private_points', all(
    hit(r['cylinder'],r['private']) and sum(hit(s['cylinder'],r['private']) for s in fixture)==1
    for r in fixture))
check('separation_fixture_satisfies_all_eight_missing_full_labels', all(11*d not in label_counts for d in D))
check('separation_fixture_only_first11_labels_are_55_77_385',
      {r['modulus'] for r in fixture if 11 in r['cylinder']}=={55,77,385})
check('separation_fixture_all_three_small_full_labels_are_double', all(label_counts[d]==2 for d in (55,77,385)))

mixed_fixture=[r for r in fixture if r['kind']=='mixed57']
def meets(left,right):
    return all((left[p][1]-right[p][1]) % p**min(left[p][0],right[p][0])==0
               for p in left.keys() & right.keys())
check('separation_fixture_mixed_rectangles_pairwise_disjoint', all(
    not meets(left['cylinder'],right['cylinder'])
    for i,left in enumerate(mixed_fixture) for right in mixed_fixture[i+1:]))
check('separation_fixture_mixed_avoids_pure57', all(
    not meets(left['cylinder'],right['cylinder']) for left in mixed_fixture
    for right in fixture if right['kind'] in ('pure5','pure7')))
fixture_m=sum((F(1,r['modulus']) for r in mixed_fixture),F(0))
fixture_delta=F(1,12)-fixture_m
fixture_d5=F(1,2)-sum((F(1,r['modulus']) for r in fixture if r['kind']=='pure5'),F(0))
fixture_d7=F(1,3)-sum((F(1,r['modulus']) for r in fixture if r['kind']=='pure7'),F(0))
check('separation_fixture_same_actual_old_source_values',
      (fixture_m,fixture_delta,fixture_d5,fixture_d7)==
      (F(4992,60025),F(121,720300),F(1,1250),F(1,7203)))

# For a pair touching {5,7,35}, e=1 has max occupancy two and all later
# occupancies vanish. For other pairs the lcm is >=125: among nonunit
# 5/7-smooth cofactors below 125 only 25 and 49 remain after removing that
# triple, and their lcm is 1225. Higher exponents cannot enter this range.
gamma_touching = 1-F(5,11)*2
small_remaining=sorted({5**a*7**b for a,b in product(range(3),repeat=2)
                        if 1<5**a*7**b<125 and 5**a*7**b not in (5,7,35)})
check('all_low_nontriple_cofactors_are_25_49',small_remaining==[25,49])
check('only_small_remaining_pair_has_large_lcm',lcm(*small_remaining)==1225 and 5**3>=125 and 7**3>=125)
check('every_touching_pair_Gamma_mass_below_uniform_cap',
      gamma_touching==F(1,11) and gamma_touching*fixture_m<=F(1,132)<F(1,125))

A5=F(44887686823492905683,27146767546602063360)
A7=F(20281636668601030051,20313907687933516800)
A57=F(585035299774741193,203139076879335168)
old_test_upper=A5*fixture_d5+A7*fixture_d7+A57*fixture_d5*fixture_d7\
    +(T-2)*fixture_delta+(T-2)/375
old_test_gap=c0-old_test_upper
check('all_single_pair_PD8_upper_bound_exact',old_test_upper==F(
    92153606998216691157721,9145067317261570094400000))
check('BP7_single_pair_failure_margin_positive',old_test_gap==F(
    921646448584542100691,717260181746005497600000) and old_test_gap>0)
ps1_usable=[]
for target in fixture:
    if target['modulus']!=35:
        continue
    counts={}
    for d in (5,7,35):
        actual=[r for r in fixture if r['modulus']==11*d]
        matching=sum(meets({p:data for p,data in r['cylinder'].items() if p!=11},target['cylinder'])
                     for r in actual)
        counts[d]=2-len(actual)+matching
    ps1_usable.append(dict(C_CRT=crt(target['cylinder']),usable=counts))
check('both_actual_35_classes_have_all_PS1_usable_counts_zero',
      len(ps1_usable)==2 and all(all(s==0 for s in item['usable'].values()) for item in ps1_usable))
check('uniform_norm_bound_matches_report545',T-margin==F(
    19147691388545460496117,3800547456524288870400))


def json_exact(value):
    if isinstance(value,F):
        return str(value.numerator)+'/'+str(value.denominator)
    if isinstance(value,dict):
        return {str(k):json_exact(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [json_exact(v) for v in value]
    return value


result = dict(
    scope='Numerical and literal-cylinder support for the ordinary same-PA-law eight-missing-label descendant-slot theorem; not a complete Lean proof or unrestricted Erdos #7 result.',
    missing_old_cofactors=D, missing_full_first11_labels=[11*d for d in D],
    original_C=C, original_C_CRT=crt(C),
    fixed_comparison_queries={d:dict(cylinder=q,CRT=crt(q)) for d,q in queries.items()},
    completion_scope='Only absent full labels 11*d at exponent one are filled in both comparison slots. Original phases, all actual kernels, eta, and final normalization are unchanged. Later exponent and all other original labels are arbitrary.',
    conditional_measure='Haar conditional on C, not eta conditional on C',
    distribution5=distribution5, distribution7=distribution7,
    joint_descendant_counts=joint_counts, payoff_counts=payoff_counts,
    conditional_payoff_expectation=conditional_expectation, raw_payoff_integral=raw_integral,
    payoff='1_C * min(3, (2*S5+2*S7-1)_+)',
    bounded_transfer='Integral_eta f >= integral_H f - 3*H(C without U) >= 579/42875-3*delta; f is a nonnegative bounded LOWER witness for the actual completed hinge.',
    worst_deletion_breakpoints=breakpoints,
    extreme_deletion_checks=dict(whole_cells=whole_checks,half_cells=half_checks),
    first11_debit='J11 >= (10/11)*(579/42875-3*delta)',
    uniform_mass_credit=constant, remaining_delta_coefficient=delta_coefficient,
    T=T,c0=c0,total_credit=credit,strict_margin=margin,
    uniform_norm_bound=T-margin,
    separation_fixture=dict(originals=fixture,label_counts=label_counts,
        original_count=len(fixture),label_count=len(label_counts),mixed_mass=fixture_m,
        delta=fixture_delta,d5=fixture_d5,d7=fixture_d7,
        all_single_pair_Gamma_eta_upper=F(1,125),touching_pair_Gamma=gamma_touching,
        all_single_pair_PD8_upper=old_test_upper,old_test_gap=old_test_gap,
        PS1_usable_counts=ps1_usable,
        scope='One actual family is certified by the new condition and by no old single-pair PD8 or PS1 test. This is not inclusion of all old regions, failure of the general debit identity, or a lower witness.'),
    scope_notes=['The actual 35 class is chosen once when delta<1/35; if delta>=1/35 the direct packing credit closes instead.',
                 'No independence of the actual deleted measure eta is assumed.',
                 'Only the finite Haar descendant distribution factorizes.',
                 'The clipped payoff is used from below pointwise, never as a convex upper comparison.',
                 'The arbitrary-family transfer and all-depth PA implication are ordinary proofs, not consequences of finite checking alone.'],
    checks=checks,passed_count=len(checks),complete=True)
output=Path(__file__).with_suffix('.json')
output.write_text(json.dumps(json_exact(result),indent=2,ensure_ascii=False)+'\n')
print(json.dumps(dict(output=str(output),checks=len(checks),credit=str(credit),margin=str(margin),
                     output_sha256=sha256(output.read_bytes()).hexdigest())))
