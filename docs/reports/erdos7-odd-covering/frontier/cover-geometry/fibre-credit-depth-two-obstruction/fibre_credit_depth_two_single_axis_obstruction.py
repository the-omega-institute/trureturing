"""Exact separation of one fixed-scale300 envelope from the original372 envelope.

Standard-library rational verifier. Every mathematical guard survives -O.
The supplied dual excludes all common nonnegative row laws for fixed scales
(10,12,16,18,22); it does not exclude other scales or refute Erdos #7.
"""
import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from math import prod
from pathlib import Path

D = tuple(d for d in range(1, 316) if 315 % d == 0)
P = (11, 13, 17, 19, 23)
S = tuple(p - 1 for p in P)
INPUT_SHA256 = '3233f1c82a405ae6018bcad76b0274f14bce7f19a2bcf3bac741657452eec630'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def kappa(d):
    return prod((F(p, p - 1) for p, h in ((3, 9), (5, 5), (7, 7))
                 if d % h == 0), start=F(1)) - 1


def axis_coefficient(j, k):
    return F(S[j] ** (k - 1), k) * sum(
        (prod((F(1, S[i]) for i in term), start=F(1))
         for term in combinations([i for i in range(5) if i != j], k - 1)), F(0))


def verify(data):
    need(set(data) == {'divisor_order', 'scales', 'core_phases',
                      'singleton_old_phases', 'dual_scale', 'dual_entries',
                      'joint_row_weights'}, 'Complete literal schema')
    need(data['divisor_order'] == list(D[1:]) and data['scales'] == list(S),
         'Fixed labeled divisor order and fixed scales')
    core, phases = data['core_phases'], data['singleton_old_phases']
    need(len(core) == 11 and len(phases) == 5 and all(len(row) == 11 for row in phases),
         'One core and five complete actual phase dictionaries')
    need(all(type(a) is int and 0 <= a < d
             for row in [core] + phases for d, a in zip(D[1:], row)),
         'Each original label has one legal globally fixed phase')
    rows = [x for x in range(315) if all(x % d != a for d, a in zip(D[1:], core))]
    hits = {x: [sum(x % d == a for d, a in zip(D[1:], row))
                for row in phases] for x in rows}
    lower = {x: [S[j] - hits[x][j] for j in range(5)] for x in rows}
    live = [x for x in rows if min(lower[x]) > 0]
    need(rows == live and len(rows) == 75, 'Literal75 actual rows all admissible')
    slots = [(d, -1, 0, kappa(d)) for d in D if kappa(d)]
    slots += [(d, j, k, axis_coefficient(j, k) * (kappa(d) + (k >= 2)))
              for j in range(5) for k in range(1, 6) for d in D
              if kappa(d) or k >= 2]
    need(len(slots) == 300, 'Complete300 single-axis slots')
    scale = data['dual_scale']
    need(type(scale) is int and scale > 0, 'Positive integer dual scale')
    entries = data['dual_entries']
    need(all(type(entry) is list and len(entry) == 3 for entry in entries),
         'Three coordinates per dual entry')
    budgets = [F(0)] * len(slots)
    loads = {x: F(0) for x in live}
    seen = set()
    incidence_checks = 0
    for slot, a, numerator in entries:
        need(type(slot) is int and 0 <= slot < len(slots)
             and type(a) is int and type(numerator) is int and numerator > 0,
             'Exact nonnegative dual multiplier at a valid slot')
        need((slot, a) not in seen, 'No duplicate dual query')
        seen.add((slot, a))
        d, j, k, coefficient = slots[slot]
        need(0 <= a < d, 'Valid cylinder residue')
        value = F(numerator, scale)
        budgets[slot] += value
        for x in live:
            if x % d == a:
                loads[x] += value if j == -1 else value / lower[x][j] ** k
                incidence_checks += 1
    need(all(budget <= slot[3] for budget, slot in zip(budgets, slots)),
         'Every exact dual slot budget is respected')
    bound = min(loads.values())
    need(bound == F(302528624050627203408353, 297327183003648000000000)
         and bound > F(1017, 1000), 'Every common row law has300 cost above1017/1000')
    pairs = data['joint_row_weights']
    need(all(type(pair) is list and len(pair) == 2
             and type(pair[0]) is int and type(pair[1]) is int and pair[1] >= 0
             for pair in pairs), 'Exact nonnegative integer primal weights')
    need([pair[0] for pair in pairs] == rows, 'One ordered weight for every actual row')
    weights = [pair[1] for pair in pairs]
    mass = sum(weights)
    need(mass == 305, 'Literal positive mass305')
    joint, joint_caps = F(0), []
    for mask in range(32):
        axes = [j for j in range(5) if mask & (1 << j)]
        values = [F(w, prod(lower[x][j] for j in axes)) for x, w in pairs]
        for d in D:
            coefficient = kappa(d) + (len(axes) >= 2)
            if coefficient:
                bins = [F(0)] * d
                for x, value in zip(rows, values):
                    bins[x % d] += value
                cap = max(bins)
                joint += coefficient * cap
                joint_caps.append([d, mask, str(cap), bins.index(cap)])
    ratio = joint / mass
    need(len(joint_caps) == 372 and ratio == F(3287121421692746843, 3306522202663680000)
         and ratio < F(199, 200), 'All372 primal maxima give strict feasibility')
    # Concrete actual numerical realization, distinct from conservative ell.
    # Each pure outside original uses root1; every mixed singleton uses root0.
    numerical = [[d, a] for d, a in zip(D[1:], core)]
    actual_counts = {x: [] for x in rows}
    fibre_checks, strict_improvements = 0, 0
    for j, p in enumerate(P):
        numerical.append([p, 1])
        mixed = []
        for d, a in zip(D[1:], phases[j]):
            residue = a + d * ((-a * pow(d, -1, p)) % p)
            need(residue % d == a and residue % p == 0 and 0 <= residue < d * p,
                 'CRT realization preserves the fixed old phase and actual new root')
            mixed.append((d * p, residue))
        numerical.extend(map(list, mixed))
        for x in rows:
            count = 0
            for t in range(p):
                point = x + 315 * (((t - x) * pow(315, -1, p)) % p)
                count += t != 1 and all(point % m != a for m, a in mixed)
                fibre_checks += 1
            need(count == p - 1 - (hits[x][j] > 0) and count >= lower[x][j],
                 'Actual root membership dominates conservative label count')
            actual_counts[x].append(count)
            strict_improvements += count > lower[x][j]
    need(len(numerical) == len({m for m, _ in numerical}) == 71
         and all(m > 1 and m % 2 for m, _ in numerical),
         'Exactly71 distinct odd numerical originals')
    point_cap = max(F(w, prod(lower[x])) for x, w in pairs)
    haar = (mass - joint) / (315 * prod(P) * point_cap)
    return {
        'scope': 'One actual complete dictionary. Fixed scales(10,12,16,18,22): '
                 'all common nonnegative laws fail300. One integer common law succeeds372. '
                 'Not an obstruction to other scales, universal372, or Erdos7.',
        'scales': list(S), 'core_rows': rows, 'core_row_count': len(rows),
        'minimum_conservative_denominators': [min(lower[x][j] for x in rows) for j in range(5)],
        'hit_histograms': [{str(h): sum(hits[x][j] == h for x in rows)
                            for h in sorted({hits[x][j] for x in rows})} for j in range(5)],
        'dual_nonzero_entries': len(entries), 'dual_incidence_checks': incidence_checks,
        'dual_slot_budget_checks': len(slots), 'dual_row_inequalities': len(rows),
        'dual_slot_budgets': [[d, j, k, str(c), str(b), str(c - b)]
                              for (d, j, k, c), b in zip(slots, budgets)],
        'dual_row_loads': [[x, str(loads[x])] for x in rows],
        'dual_lower_bound': str(bound), 'dual_lower_bound_row': min(loads, key=loads.get),
        'simple_dual_lower_bound': '1017/1000',
        'primal_total_mass': mass, 'primal_positive_rows': sum(w > 0 for w in weights),
        'joint_primal_ratio': str(ratio), 'joint_primal_margin': str(mass - joint),
        'joint_primal_caps': joint_caps, 'conservative_point_mass_cap': str(point_cap),
        'joint_Haar_lower': str(haar),
        'actual_numerical_classes': numerical, 'actual_fibre_checks': fibre_checks,
        'actual_minimum_root_counts': [min(actual_counts[x][j] for x in rows) for j in range(5)],
        'strict_root_count_improvements': strict_improvements,
        'lean_verification': False,
    }


def self_test(data):
    mutations = []
    def add(name, edit):
        changed = deepcopy(data)
        edit(changed)
        mutations.append((name, changed))
    add('illegal core phase', lambda d: d['core_phases'].__setitem__(0, 3))
    add('incomplete singleton dictionary', lambda d: d['singleton_old_phases'][0].pop())
    add('different scales', lambda d: d['scales'].__setitem__(0, 11))
    add('invalid dual slot', lambda d: d['dual_entries'][0].__setitem__(0, 300))
    add('negative dual multiplier', lambda d: d['dual_entries'][0].__setitem__(2, -1))
    add('duplicated dual query', lambda d: d['dual_entries'].append(d['dual_entries'][0]))
    add('excess dual budget', lambda d: d['dual_entries'][0].__setitem__(2, 10 ** 20))
    add('missing dual certificate', lambda d: d.__setitem__('dual_entries', []))
    add('negative primal weight', lambda d: d['joint_row_weights'][0].__setitem__(1, -1))
    add('duplicate primal row', lambda d: d['joint_row_weights'].append(d['joint_row_weights'][0]))
    rejected = []
    for name, changed in mutations:
        try:
            verify(changed)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('Malformed input incorrectly accepted: ' + name)
    need(len(rejected) == 10, 'All adversarial certificate mutations rejected')
    return rejected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name(
        Path(__file__).stem + '_input.json'))
    parser.add_argument('--write-result', type=Path)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    raw = args.input.read_bytes()
    data = json.loads(raw)
    result = verify(data)
    need(sha256(raw).hexdigest() == INPUT_SHA256, 'Pinned literal input')
    result['input_sha256'] = sha256(raw).hexdigest()
    if args.self_test:
        print(json.dumps({'malformed_inputs_rejected': self_test(data),
                          'optimization_safe_guards': True}, indent=2))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    else:
        expected = json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result == expected, 'Retained result matches exact recomputation')
    print(json.dumps({k: v for k, v in result.items() if k not in
                      ('core_rows', 'dual_slot_budgets', 'dual_row_loads',
                       'joint_primal_caps', 'actual_numerical_classes')}, indent=2))


if __name__ == '__main__':
    main()
