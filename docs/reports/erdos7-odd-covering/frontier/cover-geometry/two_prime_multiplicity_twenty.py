"""A projected two-prime covering with multiplicity20 and distinct-label lift.

Refutes upgrading the single-fibre Q<=19 criterion to Q<=20 from only a
modulus-multiplicity bound. It is not an original distinct odd covering.
"""
from fractions import Fraction as F
from collections import Counter
from pathlib import Path
from math import gcd
import argparse
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def crt(a, m, b, n):
    need(gcd(m, n) == 1, 'coprime CRT factors')
    return (a + m * ((b - a) * pow(m, -1, n) % n)) % (m * n)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    p, q = 23, 29
    period = p * p * q * q
    first_cells = [(a, b) for a in (20, 21) for b in range(20, 29)]
    first_cells += [(22, 20), (22, 21)]
    second_cells = [(22 + p * a, b) for a in (20, 21) for b in range(22, 29)]
    second_cells += [(528, b) for b in range(22, 28)]
    stages = [
        ('pure23', [(a, p) for a in range(20)]),
        ('pure29', [(b, q) for b in range(20)]),
        ('mixed23_29', [(crt(a, p, b, q), p * q) for a, b in first_cells]),
        ('pure23square', [(22 + p * a, p * p) for a in range(20)]),
        ('mixed23square_29', [(crt(a, p * p, b, q), p * p * q) for a, b in second_cells]),
        ('pure29square', [(28 + q * b, q * q) for b in range(20)]),
        ('mixed23square_29square', [(crt(528, p * p, 28 + q * b, q * q), period)
                                  for b in range(20, 29)]),
    ]
    need([len(cs) for _, cs in stages] == [20] * 6 + [9], 'seven declared rows')
    classes = [c for _, cs in stages for c in cs]
    need(len(classes) == len(set(classes)) == 129, '129 distinct projected classes')
    multiplicities = Counter(m for _, m in classes)
    need(max(multiplicities.values()) == 20
         and all(period % m == 0 and m > 1 and m % 2 for m in multiplicities),
         'only declared odd two-prime moduli, at most20 of each')
    covered = bytearray(period)
    rows = []
    expected = [58029, 18009, 4669, 609, 29, 9, 0]
    for stage, ((name, cs), remaining) in enumerate(zip(stages, expected), 1):
        newly_covered = 0
        for a, m in cs:
            need(0 <= a < m, 'canonical projected residue')
            for x in range(a, period, m):
                newly_covered += not covered[x]
                covered[x] = 1
        survivors = period - sum(covered)
        need(survivors == remaining, 'exact survivor count after ' + name)
        rows.append({'stage': stage, 'name': name, 'class_count': len(cs),
                     'newly_covered': newly_covered, 'survivors': survivors, 'classes': cs})
    need(all(covered), 'complete projected period is covered')
    coordinate_survivors = 0
    for x in range(p * p):
        for y in range(q * q):
            deleted = (x % p < 20 or y % q < 20 or (x % p, y % q) in first_cells
                       or (x % p == 22 and x // p < 20)
                       or (x, y % q) in second_cells
                       or (y % q == 28 and y // q < 20)
                       or (x == 528 and y % q == 28 and y // q >= 20))
            coordinate_survivors += not deleted
    need(coordinate_survivors == 0, 'independent Cartesian coverage')
    lifted = []
    for _, cs in stages:
        for index, (a, m) in enumerate(cs):
            d = 3 ** index
            residue = crt(0, d, a, m)
            need(residue % d == 0 and residue % m == a, 'same old-point restriction')
            lifted.append({'old_label': d, 'later_modulus': m, 'later_residue': a,
                           'original_modulus': d * m, 'original_residue': residue})
    need(len({row['original_modulus'] for row in lifted}) == 129
         and all(row['original_modulus'] > 1 and row['original_modulus'] % 2
                 for row in lifted), 'distinct original odd moduli')
    need({row['old_label'] for row in lifted} == {3 ** j for j in range(20)},
         'exactly20 original old labels')
    need(all((1 - row['original_residue']) % row['original_modulus'] != 0 for row in lifted),
         'integer1 survives the full original family')
    lower19 = (1 - F(19, 22)) * (1 - F(19, 28)) - F(19, 616)
    need(lower19 == F(1, 77), 'retained single-fibre lower bound at Q19')
    out = {'p': p, 'q': q, 'period': period, 'class_count': len(classes),
           'maximum_later_modulus_multiplicity': 20,
           'multiplicities': {str(m): c for m, c in sorted(multiplicities.items())},
           'stages': rows, 'complete_period_survivor_count': period - sum(covered),
           'independent_coordinate_pairs_checked': period,
           'independent_coordinate_survivor_count': coordinate_survivors,
           'fixed_old_point': 0, 'old_period': 3 ** 19, 'original_uncovered_integer': 1,
           'lifted_original_family': lifted, 'Q19_survivor_lower': str(lower19),
           'scope': 'Finite projected later-fibre cover, with later-modulus multiplicity20. All129 lifted original numerical moduli are distinct odd numbers; they cover the old residue0 fibre, while integer1 avoids them. Refutes a single-fibre multiplicity20 noncoverage claim, not Erdős7; no Lean verification.'}
    out = json.loads(json.dumps(out))
    if args.output:
        args.output.write_text(json.dumps(out, indent=2) + '\n')
    else:
        need(out == json.loads(Path(__file__).with_suffix('.json').read_text()), 'retained result differs')
    print(json.dumps({k: out[k] for k in ('period', 'class_count', 'multiplicities',
                                        'complete_period_survivor_count', 'original_uncovered_integer')}, indent=2))


if __name__ == '__main__':
    main()
