#!/usr/bin/env python3
"""Exact common-law prefix countermodel; no original AP realization claimed.

Requires Python 3.9+ and only the standard library. The compact JSON result
defaults beside this script; use --output to select another path.
"""
import argparse
from fractions import Fraction as F
from pathlib import Path
import json
from math import lcm

R = F(1301, 1185)
BETA = F(85, 99)
FEE = F(23, 48)
ATOM_COUNTS = (9358, 24217, 5530)
CHILD_SIZE = sum(ATOM_COUNTS)
FULL = 7
U = 1
A_MINUS_U = 2
A = 3
A_COMPLEMENT = 4


def mass(mask):
    return F(sum(n for i, n in enumerate(ATOM_COUNTS) if mask >> i & 1), CHILD_SIZE)


def digits(n, height):
    return tuple(n // 3**a % 3 for a in range(height))


def pure_prefix(a):
    return (1,) * (a - 1) + (0,)


def bad_prefix(a):
    return (1,) * (a - 1) + (2,)


def residue(word):
    return sum(d * 3**i for i, d in enumerate(word))


def check(height, beta=BETA):
    assert height >= 2
    atom_probabilities = (R-beta, 2*beta-R, 1-beta)
    assert all(0 < p <= beta for p in atom_probabilities)
    child_size = lcm(*(p.denominator for p in atom_probabilities))
    child_atom_counts = tuple(int(p*child_size) for p in atom_probabilities)
    assert sum(child_atom_counts) == child_size
    def event_mass(mask):
        return sum((p for i,p in enumerate(atom_probabilities) if mask >> i & 1), F())
    assert event_mass(A) == beta
    levels = {1: {(2,): A, (1,): U}}
    for a in range(2, height + 1):
        level = {bad_prefix(a): A_MINUS_U}
        for digit in range(3):
            key = bad_prefix(a - 1) + (digit,)
            assert key not in level
            level[key] = A_COMPLEMENT
        levels[a] = level
    budgets = []
    for a, level in levels.items():
        assert all(len(word) == a and event_mass(mask) <= beta for word, mask in level.items())
        total = sum((event_mass(mask) for mask in level.values()), F())
        assert total <= R
        assert total == (R if a == 1 else 3 - beta - R)
        budgets.append(dict(depth=a, total_mass=total, slack=R-total,
                            events=[dict(prefix=word, child_atom_mask=mask, mass=event_mass(mask))
                                    for word, mask in level.items()]))
    parent_size = 3**height
    blocked = set()
    pure = set()
    literal_blocked = set()
    literal_pure = set()
    union_histogram = {}
    for n in range(parent_size):
        word = digits(n, height)
        mask = 0
        for a in range(1, height + 1):
            mask |= levels[a].get(word[:a], 0)
            if word[:a] == pure_prefix(a):
                pure.add(n)
            if n % (3**a) == residue(pure_prefix(a)):
                literal_pure.add(n)
            if a < height and n % (3**a) == residue(bad_prefix(a)):
                literal_blocked.add(n)
        union_histogram[mask] = union_histogram.get(mask, 0) + 1
        if mask == FULL:
            blocked.add(n)
    assert blocked == literal_blocked
    assert pure == literal_pure
    assert not blocked & pure
    blocked_mass = F(len(blocked), parent_size)
    pure_mass = F(len(pure), parent_size)
    assert blocked_mass == (1-F(1, 3**(height-1)))/2
    assert pure_mass == (1-F(1, 3**height))/2
    if height == 4:
        assert len(blocked) == 39 and len(pure) == 40
        assert blocked_mass == F(13, 27) == FEE+F(1, 432)
        assert set(range(parent_size)) - blocked - pure == {40, 67}
    return dict(height=height, parent_size=parent_size, beta=beta, child_size=child_size,
                child_atom_counts=child_atom_counts,
                blocked_count=len(blocked), blocked_mass=blocked_mass,
                pure_count=len(pure), pure_mass=pure_mass,
                blocked_is_disjoint_from_pure=True, parent_words_exhausted=parent_size,
                child_union_atom_mask_histogram=union_histogram,
                fee=FEE, blocked_minus_fee=blocked_mass-FEE, levels=budgets,
                pure_residue_classes=[dict(modulus=3**a, residue=residue(pure_prefix(a)))
                                      for a in range(1, height+1)],
                blocked_residue_classes=[dict(modulus=3**a, residue=residue(bad_prefix(a)))
                                         for a in range(1, height)])


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [encode(v) for v in x]
    return x


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'),
                        help='Compact JSON destination (default: beside this script).')
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError('Assertions must be enabled.')
    assert CHILD_SIZE == 39105
    assert mass(A) == BETA and mass(U) == R-BETA
    assert mass(A_MINUS_U) == 2*BETA-R and mass(A_COMPLEMENT) == 1-BETA
    assert 3-2*R == F(953, 1185) < BETA
    cases = [check(h) for h in (2, 3, 4, 8)]
    coupled_beta = F(65,79)
    coupled_s = F(79,99)
    coupled_cases = [check(h, coupled_beta) for h in (2,3,4,8)]
    assert coupled_s*(1-coupled_beta) == F(14,99)
    assert F(1148,1485)/coupled_s > coupled_beta
    assert 2*R+coupled_beta-3 == F(22,1185)
    result = dict(scope='Relaxed common-law prefix model; no original child-divisor AP realization.',
                  R=R, beta=BETA, child_size=CHILD_SIZE, child_atom_counts=ATOM_COUNTS,
                  threshold_beta=3-2*R, higher_level_cost=3-BETA-R,
                  higher_level_budget_slack=2*R+BETA-3, cases=cases,
                  stronger_coupled_scalar_case=dict(s=coupled_s, beta=coupled_beta,
                      old_product_survival_lower=F(14,99), raw_union_upper=F(1148,1485),
                      budget_slack=F(22,1185), cases=coupled_cases))
    args.output.write_text(json.dumps(encode(result), separators=(',', ':'))+'\n')
    print(json.dumps(encode(dict(R=R, beta=BETA, threshold_beta=3-2*R,
                                summaries=[{k:c[k] for k in ('beta','height','parent_size','blocked_count',
                                            'blocked_mass','pure_count','blocked_minus_fee')}
                                           for c in cases+coupled_cases])), separators=(',', ':')))


if __name__ == '__main__':
    main()
