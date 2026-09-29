#!/usr/bin/env python3
"""Actual channel atoms pay every outside-box numerical label under one source.

The core is Report564's fixed formula with H=A=K=n. The computation uses
240000 channel atoms, not a full CRT period or a truncation of outside labels.
The outside charge is the complete Euler sum minus the complete finite box.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import argparse
import hashlib
import json

P = (3, 5, 7, 11, 13, 17, 19)
Q = P[1:]
HEIGHTS = (2, 3, 4)
NAMES = ('zero', 'base', 'extra5', 'missing5', 'missing5_extra7', 'missing7')
SIGNATURES = {
    (0, 0, 0): 'zero', (1, 1, 1): 'base', (1, 2, 1): 'extra5',
    (1, 0, 1): 'missing5', (1, 0, 2): 'missing5_extra7', (1, 1, 0): 'missing7',
}
B5 = F(19132074022251234990036997833948759259,
       18473247078046657922374787501704265625)
TARGET = 51 * B5 / 310
CHECKS = {}


def check(name, condition):
    if name in CHECKS or not condition:
        raise RuntimeError(name)
    CHECKS[name] = True


def comb(p, digit, depth):
    return digit * p ** (depth - 1) + (p ** (depth - 1) - 1) // (p - 1)


def root_profile_counts(n):
    counts = Counter()
    for root in range(3 ** n):
        if any(root % 3 ** a == comb(3, 0, a) for a in range(1, n + 1)):
            continue
        ordinary = sum(root % 3 ** a == comb(3, 2, a) for a in range(1, n + 1))
        singleton5 = sum(root % 3 ** a == (2 if a == 2 else comb(3, 2, a))
                         for a in range(1, n + 1))
        singleton7 = sum(root % 3 ** a == (7 + 9 * comb(3, 2, a - 2)
                                          if a >= 3 else comb(3, 2, a))
                         for a in range(1, n + 1))
        counts[SIGNATURES[ordinary, singleton5, singleton7]] += 1
    size = (3 ** n + 1) // 2
    moved = (3 ** (n - 2) - 1) // 2
    expected = dict(zip(NAMES, (1, 2 * 3 ** (n - 2), 3 ** (n - 2),
                                (3 ** (n - 2) + 1) // 2, moved, moved)))
    check(f'n{n}_literal_root_partition', dict((r, counts[r]) for r in NAMES) == expected)
    check(f'n{n}_root_mass', sum(counts.values()) == size)
    return expected


digits = {q: tuple(range(2, min(q - 1, 10) + 1)) for q in Q}
rows = {}
for n in HEIGHTS:
    weights = {}
    for q in Q:
        denominator = (q - 2) * q ** n + 1
        channel = q ** n - 1
        remainder = denominator - len(digits[q]) * channel
        check(f'n{n}_q{q}_nonnegative_remainder', remainder >= 0)
        weights[q] = {'denominator': denominator, 'channel': channel, 'remainder': remainder}
    rows[n] = {'coordinates': weights, 'root_counts': root_profile_counts(n),
               'denominator': prod(weights[q]['denominator'] for q in Q),
               'profile_numerators': dict.fromkeys(NAMES, 0), 'total_weight': 0}

atom_count = 0
for code in product(*((0,) + digits[q] for q in Q)):
    atom_count += 1
    late = code[2:]
    old_bad = late.count(8) >= 2 or late.count(9) >= 3 or late == (10, 10, 10, 10)
    allowed = []
    if not old_bad:
        allowed.append('zero')
        mixed_bad = any(sum(d == min(size + 1, q - 1) for q, d in zip(Q, code)) >= size
                        for size in range(2, 7))
        if not mixed_bad and all(d != 2 for d in late):
            if code[1] != 2:
                allowed.append('missing5')
                if code[1] != 3:
                    allowed.append('missing5_extra7')
            if code[0] != 2:
                allowed.append('missing7')
            if code[0] != 2 and code[1] != 2:
                allowed.append('base')
                if code[0] != 3:
                    allowed.append('extra5')
    for n, row in rows.items():
        weights = row['coordinates']
        mass = prod(weights[q]['channel'] if digit else weights[q]['remainder']
                    for q, digit in zip(Q, code))
        row['total_weight'] += mass
        for name in allowed:
            row['profile_numerators'][name] += mass

check('channel_atom_count', atom_count == 240000)
consumers = {}
for n, row in rows.items():
    check(f'n{n}_channel_normalization', row['total_weight'] == row['denominator'])
    profile = {name: F(value, row['denominator'])
               for name, value in row['profile_numerators'].items()}
    for name, value in profile.items():
        check(f'n{n}_{name}_conditional_probability', 0 <= value <= 1)
    root_size = (3 ** n + 1) // 2
    actual = sum((F(row['root_counts'][name], root_size) * profile[name]
                  for name in NAMES), F())
    den = {p: p - 2 + F(1, p ** n) for p in P}
    cap_full = prod((1 + 1 / den[p] for p in P), start=F(1))
    cap_box = prod(((p - 1) / den[p] for p in P), start=F(1))
    box_direct = prod((1 + sum((F(p - 1, p ** e) / den[p]
                               for e in range(1, n + 1)), F()) for p in P), start=F(1))
    check(f'n{n}_finite_box_geometric_identity', cap_box == box_direct)
    outside = cap_full - cap_box
    check(f'n{n}_outside_charge_positive', outside > 0)
    lower = actual - outside
    check(f'n{n}_remaining_source_positive', lower > 0)
    query = 5 + B5 / lower
    check(f'n{n}_threshold_query_equivalence', (lower > TARGET) == (query < F(565, 51)))
    pure_mass = 1 / cap_box
    reserve = 1 - (1 + query) * F(51, 616)
    originals = 7 * n + n * ((n + 1) ** 6 - 1) + (n + 1) ** 4 - 1 - 4 * n
    consumers[n] = {
        'core_original_count': originals,
        'root_profile_counts': row['root_counts'],
        'coordinate_atoms': row['coordinates'],
        'conditional_actual_survivals': profile,
        'actual_core_survival': actual,
        'full_cap_sum_including_unit': cap_full,
        'box_cap_sum_including_unit': cap_box,
        'complete_outside_charge': outside,
        'full_source_survival_lower': lower,
        'target_margin': lower - TARGET,
        'certificate_succeeds': lower > TARGET,
        'uniform_survivor_query_bound': query,
        'pure_source_Haar_mass': pure_mass,
        'Haar_survival_lower': pure_mass * lower,
        'fresh23_29_relative_reserve': reserve,
        'fresh23_29_Haar_lower': pure_mass * lower * reserve,
    }

check('height3_original_count', consumers[3]['core_original_count'] == 12549)
check('height3_exact_core', consumers[3]['actual_core_survival'] ==
      F(1157864475594883207, 3870838428711782528))
check('height3_exact_remaining', consumers[3]['full_source_survival_lower'] ==
      F(23298254753076498710959, 110984679428024228642816))
check('height3_certificate_succeeds', consumers[3]['certificate_succeeds'])
check('height3_fresh_reserve_positive', consumers[3]['fresh23_29_relative_reserve'] > 0)
check('height2_certificate_fails', not consumers[2]['certificate_succeeds'])
check('height4_certificate_succeeds', consumers[4]['certificate_succeeds'])

result = {'scope': __doc__, 'heights': consumers, 'target': TARGET,
          'channel_atom_count': atom_count, 'passed_checks': len(CHECKS), 'checks': CHECKS}


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
args.output.write_text(json.dumps(result, default=encode, indent=2) + '\n')
print(json.dumps({'passed_checks': len(CHECKS), 'channel_atoms': atom_count,
                  'heights': {n: {'originals': row['core_original_count'],
                                  'actual_core': float(row['actual_core_survival']),
                                  'outside_charge': float(row['complete_outside_charge']),
                                  'survival_lower': float(row['full_source_survival_lower']),
                                  'query_bound': float(row['uniform_survivor_query_bound']),
                                  'certificate_succeeds': row['certificate_succeeds']}
                              for n, row in consumers.items()}}, indent=2))
print('json_sha256=' + hashlib.sha256(args.output.read_bytes()).hexdigest())
