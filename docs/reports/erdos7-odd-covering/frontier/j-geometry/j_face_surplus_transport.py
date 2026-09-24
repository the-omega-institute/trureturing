#!/usr/bin/env python3
"""Exact J-source-face surplus transport and one genuine seven-class collision."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_surplus_transport.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/source-budgets/sharp_source_mass_endpoints.py': '79bb947d96c36895069f58568d7a5de2c22aa561753f03352e9eb741313147d9',
}
DEFECTS = ('E5', 'E15', 'E5d', 'E15d', 'E3', 'omega')
ROOT = (0, 0, 1, 1, 1)
CARRIERS = tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rational(value):
    require(isinstance(value, (int, F)) and not isinstance(value, bool), 'Exact rational input')
    return F(value)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable exact input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def complete_G(e, H, prime, start):
    """The entire sum(n>=start)min(e,H*p^-n), including its infinite tail."""
    e, H = map(rational, (e, H))
    require(e >= 0 and H >= 0 and isinstance(prime, int) and prime > 1
            and isinstance(start, int) and start >= 0, 'Nonnegative complete geometric family')
    if e == 0 or H == 0:
        return {'value': F(0), 'crossing': None, 'constant_terms': 0, 'geometric_tail': F(0)}
    N = start
    while H > e*prime**N:
        N += 1
    tail = H*F(prime, (prime-1)*prime**N)
    return {'value': (N-start)*e+tail, 'crossing': N,
            'constant_terms': N-start, 'geometric_tail': tail}


def domain(epsilon, kappa):
    epsilon, kappa = map(rational, (epsilon, kappa))
    require(0 <= epsilon < F(1, 250) and 0 <= kappa <= 1,
            'Numerical domain of the ordinary exact-J-source-face theorem')
    return epsilon, kappa


def complete_load_upper(epsilon, kappa, defects):
    """Assumes the ordinary theorem's exact actual source face and pi condition."""
    epsilon, kappa = domain(epsilon, kappa)
    require(set(defects) == set(DEFECTS), 'One complete named defect vector')
    defects = {k: rational(defects[k]) for k in DEFECTS}
    require(min(defects.values()) >= 0 and sum(defects.values()) <= epsilon, 'One shared residual budget')
    E = defects['E5']+defects['E5d']+2*(defects['E15']+defects['E15d'])+defects['omega']
    e5 = defects['E3']+defects['omega']
    linear = sum(price*defects[k] for k, price in zip(DEFECTS, (22, 14, 2, 4, 1, 4)))
    S = F(3, 20)+epsilon
    G3, G5 = complete_G(E, F(1, 5), 3, 3), complete_G(e5, F(1, 15), 5, 2)
    upper = S+F(49, 100)+linear+F(13, 120)*kappa+G3['value']+G5['value']
    return {'survivor_mass': S, 'upper': upper, 'linear_defect_cost': linear,
            'ternary_error': E, 'five_error': e5, 'complete_G3': G3, 'complete_G5': G5}


def surplus_margin(epsilon, kappa):
    epsilon, kappa = domain(epsilon, kappa)
    G3 = complete_G(2*epsilon, F(1, 5), 3, 3)
    G5 = complete_G(epsilon, F(1, 15), 5, 2)
    margin = F(13, 50)-17*epsilon-F(13, 120)*kappa-G3['value']-G5['value']
    old_upper = F(10661, 48600)+F(17, 150)*kappa
    return {'margin_lower': margin, 'old49_fixed_layout_upper': old_upper,
            'old49_replacement_reserve': margin-old_upper, 'complete_G3': G3, 'complete_G5': G5}


def coefficient_checks():
    errors = {'test3': (1, 2, 1, 2, 0, 1), 'test9': (1, 2, 1, 2, 0, 1),
              'test5': (10, 5, 0, 0, 1, 1), 'test15': (10, 5, 0, 0, 0, 1)}
    prices = tuple(sum(row[j] for row in errors.values()) for j in range(6))
    require(prices == (22, 14, 2, 4, 1, 4), 'Same six defects, no independent residual allowances')
    kappa_prices = tuple(map(F, ('1/24', '1/30', '1/90', '1/90', '1/120', '1/360')))
    require(sum(kappa_prices) == F(13, 120) and F(13, 120)+F(17, 150) == F(133, 600),
            'Exact shallow, tail and old-layout carrier perturbation coefficients')
    categories = tuple(map(F, ('11/120', '2/45', '11/360', '4/75', '13/600',
                              '1/25', '1/60', '1/36', '1/72', '3/20')))
    require(sum(categories) == F(49, 100) and 5*F(3, 20)-sum(categories) == F(13, 50),
            'Complete nonunit and positive-seven load constants')
    eta = (F(1, 18),)+(F(1, 9),)*4
    h, h1 = sum(eta), sum(eta[2:])
    gap5 = (h/5, h1/5, eta[2]/5, h/25)
    gap15 = (h1/5, h1/5, eta[2]/5, h1/25, (h1-sum(eta[:2]))/5)
    require(min(gap5) == F(1, 50) and min(gap15) == F(1, 75)
            and min(gap5)/5 == F(1, 250), 'Strict surplus threshold and wrong-carrier prices')
    weighted_H = sum(eta[l]*(1-F(int(l < 2)+int(l == 1)+1+int(l >= 2), 5)) for l in range(5))
    require(weighted_H == F(5, 18) and weighted_H-F(1, 90) == F(4, 15),
            'H pure5 source loss pays its changed q(H)/90 subtraction')
    carrier_checks = []
    for beta_cell, late_cell in product(range(2, 5), repeat=2):
        beta = tuple(F(1, 4) if l == beta_cell else F(0) for l in range(5))
        late = tuple(F(1, 72) if l == late_cell else F(0) for l in range(5))
        a = (F(7, 45), F(37, 180))+tuple(F(7, 30)-F(5, 9)*beta[l]-5*late[l] for l in range(2, 5))
        A = tuple(sum(a[l]*(int(ROOT[l] == u)+int(l == v)) for l in range(5)) for u, v in CARRIERS)
        require(min(a) >= F(1, 40) and min(A) >= 0 and A[CARRIERS.index((0, 1))] == F(17, 30),
                'All18 original carrier coefficients are nonnegative on every affine product-simplex vertex')
        carrier_checks.append({'beta_cell': beta_cell, 'late_cell': late_cell, 'a': a, 'carrier_coefficients': A})
    kappas = []
    for kappa in (F(0), F(1, 40), F(1, 2), F(1)):
        c3, c5 = F(11, 20)+F(3, 20)*kappa, F(13, 30)+kappa/18
        require(F(2, 5)+F(3, 10)*kappa <= c3 <= F(3, 4)
                and 0 <= F(3, 4)-c3 <= F(1, 5)
                and 0 <= F(1, 2)-c5 <= F(1, 15), 'Positive raw-minus-reference envelopes on the full kappa interval')
        kappas.append({'kappa': kappa, 'pure3_reference': c3, 'pure5_reference': c5})
    return {'linear_prices': dict(zip(DEFECTS, prices)), 'family_error_rows': errors,
            'kappa_prices': kappa_prices, 'complete_constant_categories': categories,
            'other_five_slot_gaps': gap5, 'other_fifteen_carrier_gaps': gap15,
            'H_weighted_pure5_loss': weighted_H, 'H_net_improvement_coefficient': F(4, 15),
            'old_carrier_vertices': carrier_checks, 'reference_envelope_checks': kappas}


def series_checks():
    checks, digest = 0, sha256()
    for prime, start, H in ((3, 3, F(1, 5)), (5, 2, F(1, 15))):
        for e in (F(0), F(1, 1000000), F(1, 1000), F(1, 500), F(1, 20), H/F(prime**start)):
            value = complete_G(e, H, prime, start)
            for extra in (0, 1, 4):
                M = start+extra if e == 0 else value['crossing']+extra
                finite = sum((min(e, H/F(prime**n)) for n in range(start, M)), F(0))
                tail = F(0) if e == 0 else H/F(prime**M)/(1-F(1, prime))
                require(finite+tail == value['value'], 'Independent finite-piece plus full geometric-tail evaluation')
                checks += 1
                digest.update(str((prime, start, H, e, M, finite, tail)).encode())
    lower = surplus_margin(F(1, 1000), F(1, 40))
    require(lower['complete_G3']['value'] == F(53, 10125) and lower['complete_G5']['value'] == F(1, 600)
            and lower['old49_replacement_reserve'] == F(21763, 1944000)
            and lower['old49_replacement_reserve']-F(1, 100) == F(2323, 1944000),
            'Exact worst corner of the epsilon/kappa box has strictly more than1/100 replacement reserve')
    # Monotonicity of min(e,H*p^-n) makes this corner control the whole box.
    allocations, minimum_slack = 0, None
    for epsilon, kappa in product((F(0), F(1, 10000), F(1, 1000)), (F(0), F(1, 40), F(1))):
        for split in tuple(tuple(int(i == j) for i in range(6)) for j in range(6))+((F(1, 6),)*6,):
            defects = {k: epsilon*w for k, w in zip(DEFECTS, split)}
            detailed = complete_load_upper(epsilon, kappa, defects)
            uniform = surplus_margin(epsilon, kappa)
            observed_margin = 6*detailed['survivor_mass']-detailed['upper']
            slack = observed_margin-uniform['margin_lower']
            require(slack >= 0, 'The detailed one-budget inequality implies the stated uniform margin')
            minimum_slack = slack if minimum_slack is None else min(minimum_slack, slack)
            allocations += 1
    return {'complete_series_checks': checks, 'complete_series_digest': digest.hexdigest(),
            'uniform_budget_checks': allocations, 'minimum_budget_slack': minimum_slack,
            'box_epsilon_max': F(1, 1000), 'box_kappa_max': F(1, 40),
            'box_margin': lower, 'box_reserve_excess_over_one_hundredth': F(2323, 1944000)}


def collision_fixture(constructor, N=3, changed_depth=3):
    require(N == changed_depth == 3, 'Specified small actual original-label fixture')
    A, B, C = 3**N, 5**N, 7**N
    full5 = (1 << B)-1
    state, old_source_labels = [full5]*A, []
    for a, b in product(range(N+1), repeat=2):
        if a+b == 0:
            continue
        aa, ra, bb, rb = constructor.source(a, b, 'off-diagonal')
        remove = sum(1 << y for y in range(rb, B, 5**bb))
        for x in range(ra, A, 3**aa):
            state[x] &= full5 ^ remove
        old_source_labels.append(constructor.crt(aa, ra, bb, rb, 0, 0))
    source_mask = sum(row << (B*x) for x, row in enumerate(state))
    source_mass = F(source_mask.bit_count(), A*B)
    t = sum((F(1, 3**a) for a in range(3, N+1)), F(0))
    q = sum((F(1, 5**b) for b in range(1, N+1)), F(0))
    require(source_mass == F(5, 9)-t-q, 'Actual off-diagonal source from every original old modulus')
    seven_masks, occupied = {}, 0
    for e, j in product(range(1, N+1), range(1, 7)):
        mask = sum(1 << z for z in range(j*7**(e-1), C, 7**e))
        require(not occupied & mask, 'G(j,e) are disjoint for distinct depth/class pairs')
        occupied |= mask
        seven_masks[e, j] = mask
    pure7 = sum(seven_masks[e, 6] for e in range(1, N+1))
    seven_survivors = C-pure7.bit_count()
    pure7_mass = F(seven_survivors, C)
    require(pure7_mass == (5+F(1, 7**N))/6, 'Exact finite pure7 survivor normalization')
    labels_before = dict(old_source_labels)
    for e in range(1, N+1):
        m, r = constructor.crt(0, 0, 0, 0, e, 6*7**(e-1))
        require(m not in labels_before, 'Distinct pure7 original modulus')
        labels_before[m] = r
    labels_after = dict(labels_before)
    groups_before = {(e, j): 0 for e, j in product(range(1, N+1), range(1, 6))}
    groups_after = dict(groups_before)
    family_virtual = dict.fromkeys(DEFECTS[:-1], F(0))
    virtual_total, old_mass_total = F(0), F(0)
    changed, target_old, target_modulus = [], None, None
    for a, b in product(range(N+1), repeat=2):
        if a+b == 0:
            continue
        j, aa, ra, bb, rb = constructor.mixed(a, b, 'off-diagonal')
        old = sum(1 << (B*x+y) for x in range(ra, A, 3**aa) for y in range(rb, B, 5**bb))
        mass = F((old & source_mask).bit_count(), A*B)
        old_mass_total += mass
        family = ('E5' if a == 0 and b == 1 else 'E15' if a == 1 and b == 1 else
                  'E5d' if a == 0 and b >= 2 else 'E15d' if a == 1 and b >= 2 else
                  'E3' if a >= 3 and b == 0 else None)
        for e in range(1, N+1):
            new_j = 3 if (a, b, e) == (1, 1, changed_depth) else j
            groups_before[e, j] |= old
            groups_after[e, new_j] |= old
            m, before = constructor.crt(aa, ra, bb, rb, e, j*7**(e-1))
            m_after, after = constructor.crt(aa, ra, bb, rb, e, new_j*7**(e-1))
            require(m == m_after and m not in labels_before and m not in labels_after,
                    'Every original modulus remains unique after the single collision')
            labels_before[m], labels_after[m] = before, after
            require(all(m % p == 0 and before % p == r % p and after % p == r % p
                        for p, r in ((3**aa, ra), (5**bb, rb)) if p > 1), 'Original old CRT components are unchanged')
            virtual = F(6, 5*7**e)*mass
            virtual_total += virtual
            if family is not None:
                family_virtual[family] += virtual
            if new_j != j:
                require(j == 1 and new_j == 3, 'Only the named original15 label changes its seven class')
                changed.append({'modulus': m, 'before': before, 'after': after, 'depth': e})
                target_old, target_modulus = old, m
    require(len(labels_before) == len(labels_after) == (N+1)**3-1 == 63
            and set(labels_before) == set(labels_after)
            and all(m > 1 and m % 2 == 1 for m in labels_before), 'All63 distinct original odd moduli are preserved')
    require(len(changed) == 1 and [m for m in labels_before if labels_before[m] != labels_after[m]] == [target_modulus],
            'Exactly one original residue changed')
    target_active = target_old & source_mask
    require(F(target_active.bit_count(), A*B) == F(1, 15), 'The old root1 H cylinder has its full source-free mass')
    require(target_active & groups_before[changed_depth, 3] == target_active,
            'Changed15 carrier is already contained in the existing5 carrier in its new seven class')
    differences = []
    for pair in groups_before:
        before, after = groups_before[pair] & source_mask, groups_after[pair] & source_mask
        if before != after:
            differences.append(pair)
            require(pair == (changed_depth, 1) and not after & target_active
                    and before == after | target_active, 'Only the old unique class1 union loses the target cylinder')
    require(differences == [(changed_depth, 1)], 'Class3 union and every other seven pair are unchanged')
    normalizer = A*B*seven_survivors
    deleted_before = sum((F((source_mask & mask).bit_count()*seven_masks[pair].bit_count(), normalizer)
                          for pair, mask in groups_before.items()), F(0))
    deleted_after = sum((F((source_mask & mask).bit_count()*seven_masks[pair].bit_count(), normalizer)
                         for pair, mask in groups_after.items()), F(0))
    loss = deleted_before-deleted_after
    expected = F(2, 5*7**changed_depth)/(5+F(1, 7**N))
    require(loss == expected == F(1, 4290), 'Exact normalized finite collision loss from grouped unions')
    require(old_mass_total == F(1, 3)+2*q/3
            and deleted_before == (1-F(1, 7**N))/(5+F(1, 7**N))*old_mass_total,
            'Original disjoint construction agrees before the collision')
    omega_before, omega_after = virtual_total-deleted_before, virtual_total-deleted_after
    require(omega_before >= 0 and omega_after-omega_before == loss,
            'Old virtual capacities unchanged while the single union-error mass increases')
    h, h1, D = F(5, 9)-t, F(1, 3), 1-q
    capacities = dict(zip(DEFECTS[:-1], (h/25, h1/25, h/100, h1/100, D/90)))
    family_defects = {k: capacities[k]-family_virtual[k] for k in DEFECTS[:-1]}
    require(min(family_defects.values()) > 0, 'Finite absent-label tails remain positive; zero family defects are a limiting claim only')
    limiting_loss = F(2, 25*7**changed_depth)
    require(limiting_loss == F(2, 8575) and limiting_loss < F(1, 1000), 'A positive limiting all-omega example lies in the reserve box')
    digest = sha256(json.dumps({'before': sorted(labels_before.items()), 'after': sorted(labels_after.items())}, separators=(',', ':')).encode()).hexdigest()
    return {'height': N, 'changed_depth': changed_depth, 'old_grid': (A, B), 'seven_period': C,
            'original_odd_labels': len(labels_before), 'changed_label': changed[0], 'label_digest': digest,
            'source_mass': source_mass, 'pure7_survivor_mass': pure7_mass,
            'target_source_points': target_active.bit_count(), 'target_old_mass': F(1, 15),
            'changed_union_pairs': differences, 'deleted_before': deleted_before, 'deleted_after': deleted_after,
            'survivor_before': source_mass-deleted_before, 'survivor_after': source_mass-deleted_after,
            'normalized_union_loss': loss, 'virtual_total_before_and_after': virtual_total,
            'omega_before': omega_before, 'omega_after': omega_after,
            'complete_family_defects_before_and_after': family_defects,
            'shallow_good_carrier_weight': 1-F(1, 7**N), 'empty_carrier_weight': F(1, 7**N),
            'limiting_positive_epsilon_and_omega': limiting_loss,
            'scope': 'Actual finite original-label collision. Exact source face, pi_A=1 and zero capacity defects hold only in the complete limiting family.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('j_surplus_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    constructor = module('j_surplus_constructor', base/'frontier/source-budgets/sharp_source_mass_endpoints.py')
    return encode({'schema': 'erdos7-j-face-surplus-transport-v1', 'source_sha256': PINS,
                   'coefficients': coefficient_checks(), 'complete_series_and_reserve': series_checks(),
                   'actual_finite_collision': collision_fixture(constructor),
                   'scope': 'Ordinary exact-J-source-face surplus theorem arithmetic, complete unbounded geometric sums and a genuine finite collision. The finite fixture is not on the exact limiting source face. No source-perturbation theorem, new global K, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j_surplus_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact semantic J-face surplus certificate')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: full J-face surplus coefficients, complete tails, positive reserve box and one actual independent-label collision.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
