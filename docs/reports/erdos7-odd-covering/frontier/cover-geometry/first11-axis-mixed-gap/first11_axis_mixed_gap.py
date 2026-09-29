#!/usr/bin/env python3
"""Exact same-source first11 axis/mixed decomposition and complete-query consumer.

The universal proof is ordinary mathematics, not inferred from the fixtures.
Complete auxiliary tails are evaluated through exact moments. Actual fixtures
use fixed CRT projections, unnormalized old Haar, and literal 11-fibre unions.
No old producer or result data is imported. No Lean verification is claimed.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
from itertools import product
from math import prod
from pathlib import Path
import json

CHECKS = {}
ROWS = ((11, 2, F(5, 3), F(1, 3)), (13, 2, F(3, 2), F(1, 4)),
        (17, 4, F(2), F(1, 4)), (19, 4, F(9, 5), F(1, 5)))


def check(name, value):
    if name in CHECKS or not value:
        raise ValueError(name)
    CHECKS[name] = True


def coordinate(p, mass, cap=F(1)):
    return {'p': p, 'mass': mass, 'mean': mass + cap / (p - 1),
            'atoms': {1: mass - cap / p,
                      2: cap * F(p - 1, p ** 2),
                      3: cap * F(p - 1, p ** 3)}}


def full_product_hinge(cs, t):
    # Only products below t need point masses. Every higher value is kept
    # in the complete first moment, rather than a finite-tail approximation.
    low = {1: F(1)}
    for c in cs:
        out = {}
        for n, v in low.items():
            for m, w in c['atoms'].items():
                if n * m < t:
                    out[n * m] = out.get(n * m, F()) + v * w
        low = out
    return (prod(c['mean'] for c in cs) - t * prod(c['mass'] for c in cs)
            + sum((t - n) * v for n, v in low.items()))


def ledger(x, y):
    cs = [coordinate(5, x), coordinate(7, y)]
    alpha = x * y - F(1, 12)
    hinges = {}
    for q, t, cap, a in ROWS:
        hinges[q] = full_product_hinge(cs, t)
        alpha -= a * hinges[q]
        cs.append(coordinate(q, F(1), cap))
    return {'alpha': alpha, 'Phi': full_product_hinge(cs, 3), 'hinges': hinges}


def constants():
    T = F(257, 51)
    corners = {(x, y): ledger(x, y) for x in (F(1, 2), F(1))
               for y in (F(2, 3), F(1))}
    base = corners[F(1, 2), F(2, 3)]
    c0 = base['Phi'] - (T - 2) * base['alpha']
    kreq = c0 / (T - 2)
    check('complete_baseline_alpha', base['alpha'] == F(7575003978548161, 73724315753088000))
    check('complete_baseline_Phi', base['Phi'] == F(22496082952171, 69510823782400))
    check('complete_required_mass', kreq == F(6168733163201163811, 1650097635185615616000))
    for (x, y), row in corners.items():
        tag = str(x) + '_' + str(y)
        # E(A+B-1)+ for A=N5-1, B=N7-1: complete means minus
        # total mass plus the single zero-count atom.
        J = F(1, 4) * y + F(1, 6) * x - x * y + (x - F(1, 5)) * (y - F(1, 7))
        check('axis_formula_' + tag, J == x / 42 + y / 20 + F(1, 35))
        check('grid_difference_' + tag, row['hinges'][11] - J == F(1, 24))
        check('positive_mass_' + tag, row['alpha'] >= base['alpha'] > 0)
    margin = lambda z: (T - 2) * z['alpha'] - z['Phi']
    A5 = 2 * (margin(corners[F(1), F(2, 3)]) - margin(base))
    A7 = 3 * (margin(corners[F(1, 2), F(1)]) - margin(base))
    A57 = 6 * (margin(corners[F(1), F(1)]) - margin(base) - A5 / 2 - A7 / 3)
    check('positive_NC4_coefficients', min(A5, A7, A57) > 0)
    check('grid_pointwise_identity', all(max(n * m - 2, 0) - max(n + m - 3, 0)
                                       == (n - 1) * (m - 1)
                                       for n in range(1, 31) for m in range(1, 31)))
    check('axis_pointwise_identity', all(max(n + m - 3, 0) ==
                                       max(n - 2, 0) + max(m - 2, 0) + (n >= 2 and m >= 2)
                                       for n in range(1, 31) for m in range(1, 31)))
    slot = F(5, 11)
    saving = slot / 72
    delta = (T - 2) * (saving - kreq)
    query = T - delta
    check('root_slot_beats_threshold', slot > 72 * kreq)
    check('exact_slot_saving', saving == F(5, 792))
    check('exact_query_bound', query == F(910573262387495024737, 180978450310680422400))
    check('strict_query_success', query < T)
    check('complete_beta_weight', 2 * F(5) * F(1, 10) == 1)
    check('complete_mixed_occupancy', F(1, 4) * F(1, 6) == F(1, 24))
    full_mixed_inventory = F(1, 24) * 2 * 5 * F(1, 10)
    restricted_mixed_inventory = F(1, 24) * (F(5, 11) + 2 * 5 * F(1, 110))
    check('full_mixed_inventory_cap', full_mixed_inventory == F(1, 24))
    check('restricted_mixed_inventory_cap', restricted_mixed_inventory == F(1, 44))
    check('inventory_recovers_root_saving', (F(1, 24) - restricted_mixed_inventory) / 3 == saving)
    check('restricted_inventory_beats_threshold', restricted_mixed_inventory < F(1, 24) - 3 * kreq)
    for H in (1, 2, 3, 10):
        used = 2 * sum((F(5, 11 ** e) for e in range(1, H + 1)), F())
        check('absent_slot_tail_' + str(H), used + F(1, 11 ** H) == 1)
    # Dense pure inventories need not satisfy the earlier pure-union
    # sufficient region, while the new mixed-root condition is compatible.
    dense_pure_credit = sum((a * a * base['hinges'][q] * F(1, q ** 3)
                            / (1 + a * F(1, q ** 3)) for q, t, cap, a in ROWS), F())
    check('dense_pure_criterion_not_implied', dense_pure_credit < kreq)
    return {'target': T, 'baseline': base, 'c0': c0, 'kreq': kreq,
            'A5': A5, 'A7': A7, 'A57': A57,
            'mixed_free_weight_threshold': 72 * kreq,
            'root_slot_weight': slot, 'source_gap_lower': slot / 24,
            'absolute_saving_lower': saving, 'target_margin_lower': delta,
            'query_upper': query, 'hard_zeta_lower': F(1, 24) - 3 * kreq,
            'hard_fraction_lower': 1 - 72 * kreq,
            'full_mixed_inventory_cap': full_mixed_inventory,
            'restricted_mixed_inventory_cap': restricted_mixed_inventory,
            'mixed_inventory_sufficient_threshold': F(1, 24) - 3 * kreq,
            'dense_pure_credit_height3': dense_pure_credit}


def old_originals(kind):
    out = []
    if kind == 'none':
        return out
    for p in (5, 7):
        for e in (1, 2):
            for c in (1, 2):
                r = c * p ** (e - 1) if kind == 'comb' else c
                out.append((e if p == 5 else 0, e if p == 7 else 0,
                            r if p == 5 else 0, r if p == 7 else 0))
    for a, b in product((1, 2), repeat=2):
        for c7 in (4, 5):
            out.append((a, b, 4 * 5 ** (a - 1), c7 * 7 ** (b - 1)))
    return out


def first_originals(kind, seed):
    out = []
    if kind == 'empty':
        return out
    if kind == 'isolated_mixed':
        return [(0, 0, 1, 0, 0, 0, 0), (0, 0, 1, 1, 0, 0, 1),
                (1, 1, 1, 0, 0, 0, 2)]
    for a, b, e, j in product(range(3), range(3), (1, 2), (0, 1)):
        if kind == 'mixed_free' and e == 1 and j == 1 and a * b > 0:
            continue
        if kind == 'forbidden_fibre':
            if e != 1:
                continue
            r5, r7, r11 = 0, 0, ((3 * a + b) * 2 + j) % 11
        else:
            r5 = (2 * a + 3 * b + e + 4 * j + seed) % (5 ** a)
            r7 = (3 * a + 5 * b + 2 * e + j + 2 * seed) % (7 ** b)
            r11 = (a + 2 * b + 3 * j + 7 * e + seed) % (11 ** e)
        out.append((a, b, e, j, r5, r7, r11))
    return out


def fixture(name, old_kind, first_kind, seed=0):
    old = old_originals(old_kind)
    first = first_originals(first_kind, seed)
    M5, M7, M11 = 25, 49, 121
    old_den = M5 * M7
    check(name + '_two_copy_labels', max(Counter((a, b) for a, b, _, _ in old).values(), default=0) <= 2
          and max(Counter((a, b, e) for a, b, e, _, _, _, _ in first).values(), default=0) <= 2)
    check(name + '_fixed_unique_slots', len(first) == len(set((a, b, e, j) for a, b, e, j, _, _, _ in first)))
    pure5 = {r for r in range(M5) if not any(b == 0 and r % 5 ** a == r5 for a, b, r5, _ in old)}
    pure7 = {r for r in range(M7) if not any(a == 0 and r % 7 ** b == r7 for a, b, _, r7 in old)}
    x, y = F(len(pure5), M5), F(len(pure7), M7)
    source = [(r5, r7) for r5, r7 in product(pure5, pure7)
              if not any(a and b and r5 % 5 ** a == s5 and r7 % 7 ** b == s7
                         for a, b, s5, s7 in old)]
    source_mass = F(len(source), old_den)
    m = x * y - source_mass
    check(name + '_actual_anchor', x >= F(1, 2) and y >= F(2, 3) and 0 <= m <= F(1, 12))
    F11, J11 = x / 42 + y / 20 + F(59, 840), x / 42 + y / 20 + F(1, 35)
    slots = {(e, j): [] for e in (1, 2) for j in (0, 1)}
    pure_mask = 0
    for a, b, e, j, r5, r7, r11 in first:
        mask = sum(1 << r for r in range(M11) if r % 11 ** e == r11)
        if a == b == 0:
            pure_mask |= mask
        else:
            slots[e, j].append((a, b, r5, r7, mask))
    delta = 1 - 5 * F(pure_mask.bit_count(), M11)
    sums = {(e, j): [0, 0, 0, 0] for e, j in slots}
    loss, local_valid, fully_forbidden = F(), True, 0
    for r5, r7 in source:
        forbidden = pure_mask
        G = F()
        for (e, j), items in slots.items():
            A = B = C = 0
            for a, b, s5, s7, mask in items:
                if r5 % 5 ** a == s5 and r7 % 7 ** b == s7:
                    forbidden |= mask
                    if b == 0:
                        A += 1
                    elif a == 0:
                        B += 1
                    else:
                        C += 1
            h, g = max(A + B - 1, 0), max(A + B + C - 1, 0)
            sums[e, j] = [u + v for u, v in zip(sums[e, j], (h, g, g - h, C))]
            G += F(5, 11 ** e) * g
        allowed = F(M11 - forbidden.bit_count(), M11)
        ell = max(1 - F(5, 3) * allowed, F())
        loss += ell / old_den
        fully_forbidden += allowed == 0
        local_valid &= (3 + delta) * ell <= G
    check(name + '_literal_row_loss_inequality', local_valid)
    chi_bar, zeta_bar, mu_bar, I11 = J11, F(), F(), F()
    profile = {}
    for (e, j), values in sums.items():
        H, I, zeta, mu = (F(v, old_den) for v in values)
        check(name + '_slot_bounds_' + str(e) + '_' + str(j), H <= J11 and 0 <= zeta <= mu <= F(1, 24))
        beta = F(5, 11 ** e)
        chi_bar -= beta * H
        zeta_bar += beta * zeta
        mu_bar += beta * mu
        I11 += beta * I
        profile[str(e) + '_' + str(j)] = {'H': H, 'I': I, 'zeta': zeta, 'mu': mu}
    check(name + '_source_gap_identity', F11 - I11 == F(1, 24) + chi_bar - zeta_bar)
    check(name + '_source_gap_lower', F11 - I11 >= F(1, 24) - mu_bar >= 0)
    E, S = I11 / 3 - loss, F11 / 3 - loss
    check(name + '_coupled_saving_identity', 3 * S == F(1, 24) + chi_bar - zeta_bar + 3 * E)
    check(name + '_shortage_credit', E >= delta * I11 / (3 * (3 + delta)))
    B_mix = sum((F(5, 5 ** a * 7 ** b * 11 ** e)
                 for a, b, e, _, _, _, _ in first if a and b), F())
    check(name + '_actual_mixed_inventory_cap', mu_bar <= B_mix <= F(1, 24))
    check(name + '_inventory_saving', S >= (F(1, 24) - B_mix) / 3)
    # Absent e>=3 slots contribute their WHOLE beta tail. This is not a
    # finite-slot normalization and does not insert new actual originals.
    omega = F(1, 121) + sum((F(5, 11 ** e) for (e, j), items in slots.items()
                            if not any(a and b for a, b, _, _, _ in items)), F())
    check(name + '_mixed_free_weight_gain', F11 - I11 >= omega / 24 and S >= omega / 72)
    if first_kind == 'mixed_free':
        check(name + '_mixed_root_label_condition', all(c <= 1 for (a, b, e), c in
              Counter((a, b, e) for a, b, e, _, _, _, _ in first).items() if a and b and e == 1))
        check(name + '_both_pure11_retained', sum(a == b == 0 and e == 1 for a, b, e, _, _, _, _ in first) == 2)
        check(name + '_both_axis_root_retained', all(sum((a, b, e) == wanted for a, b, e, _, _, _, _ in first) == 2
                                                    for wanted in ((1, 0, 1), (0, 1, 1))))
        check(name + '_new_restricted_saving', S >= F(5, 792))
    if first_kind == 'isolated_mixed':
        check(name + '_occupancy_not_overload', mu_bar > 0 and zeta_bar == 0)
    if first_kind == 'forbidden_fibre':
        check(name + '_zero_allowed_fibre_present', fully_forbidden > 0)
    return {'name': name, 'old_originals': old, 'first11_originals': first,
            'x': x, 'y': y, 'mixed_old_mass': m, 'actual_old_mass': source_mass,
            'root_delta': delta, 'F11': F11, 'J11': J11, 'I11': I11,
            'chi_bar': chi_bar, 'zeta_bar': zeta_bar, 'mu_bar': mu_bar,
            'B_mix': B_mix,
            'Loss11': loss, 'E11': E, 'S11': S, 'mixed_free_weight': omega,
            'fully_forbidden_old_points': fully_forbidden, 'slot_profiles': profile}


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    data = constants()
    fixtures = [fixture('empty', 'none', 'empty'),
                fixture('mixed_alone', 'none', 'isolated_mixed'),
                fixture('forbidden_fibre', 'none', 'forbidden_fibre')]
    for k, old in enumerate(('none', 'comb', 'nested')):
        fixtures.append(fixture(old + '_mixed_free', old, 'mixed_free', k))
        fixtures.append(fixture(old + '_full', old, 'full', k + 4))
    result = {'scope': __doc__, 'constants': data, 'fixtures': fixtures,
              'checks': CHECKS, 'passed_checks': len(CHECKS), 'Lean': 'not run'}
    args.output.write_text(json.dumps(result, default=encode, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'passed_checks': len(CHECKS), 'fixture_count': len(fixtures),
                      'query_upper': data['query_upper'],
                      'json_sha256': hashlib.sha256(args.output.read_bytes()).hexdigest()}, default=encode))


if __name__ == '__main__':
    main()
