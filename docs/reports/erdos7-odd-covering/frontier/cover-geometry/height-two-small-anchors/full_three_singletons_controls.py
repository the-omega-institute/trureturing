#!/usr/bin/env python3
"""Exact controls for the ordinary three-singleton supplier, not a Lean proof."""
import argparse
import itertools
import json
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def subsets(values):
    values = tuple(values)
    return [frozenset(v for j, v in enumerate(values) if mask >> j & 1)
            for mask in range(1, 1 << len(values))]


def charge(caps):
    return sum(c * v for c, v in zip((1, 3, 3, 5, 9, 5, 15, 15, 25), caps))


def check_eta(fibres, weights, mode):
    require(sum(weights.values()) == 1, 'eta is not a probability')
    child, fine = Counter(), Counter()
    for (owner, label), mass in weights.items():
        require(mass > 0 and label in fibres[owner], 'nonactual eta incidence')
        child[owner] += mass
        fine[label] += mass
    if mode == 'H4':
        require(all(label < 4 for label in fine), 'H4 leaves its column')
        require(max(child.values()) <= Q(1, 4), 'H4 child cap')
        require(max(fine.values()) <= Q(3, 8), 'H4 fine cap')
        require(max(weights.values()) <= Q(1, 4), 'H4 atom cap')
    elif mode == 'H3+2':
        require(len(weights) == len(child) == len(fine) == 5, 'five distinct owners/labels')
        require(sum(label < 4 for label in fine) == 3, 'wrong H multiplicity')
        require(set(weights.values()) == {Q(1, 5)}, 'nonuniform H3+2')
    else:
        raise RuntimeError('unknown eta type')


def mono_route(E, F):
    A = frozenset((0, 1, 2))
    fibres = [frozenset((j,)) for j in range(3)] + [E, F]
    if len(E) == 1 or len(F) == 1:
        require(sum(len(f) == 1 for f in fibres) >= 4, 'IA2 missing four singletons')
        return 'IA2-four-singletons'
    for owner in (3, 4):
        new_H = sorted(fibres[owner] & frozenset((3,)))
        if new_H:
            weights = {(j, j): Q(1, 4) for j in range(3)}
            weights[owner, new_H[0]] = Q(1, 4)
            check_eta(fibres, weights, 'H4')
            return 'H4-new-H-label'
    for owner in (3, 4):
        inside = sorted(label for label in fibres[owner] if label < 4)
        if len(inside) >= 2:
            weights = {(j, j): Q(1, 4) for j in range(3)}
            weights.update({(owner, label): Q(1, 8) for label in inside[:2]})
            check_eta(fibres, weights, 'H4')
            return 'H4-two-H-labels'
    outside_E = sorted(label for label in E if label >= 4)
    outside_F = sorted(label for label in F if label >= 4)
    require(outside_E and outside_F, 'unhandled empty outside part')
    if len(set(outside_E + outside_F)) >= 2:
        x, y = next((x, y) for x in outside_E for y in outside_F if x != y)
        weights = {(j, j): Q(1, 5) for j in range(3)}
        weights.update({(3, x): Q(1, 5), (4, y): Q(1, 5)})
        check_eta(fibres, weights, 'H3+2')
        return 'H3+2-distinct-outside'
    require(len(E) == len(F) == 2, 'last branch is not two complete doubles')
    s = next(iter(E & A))
    t = next(iter(F & A))
    if s == t:
        require(len(E | F | fibres[s]) <= 2, 'IA1 anchor has over two labels')
        return 'IA1-repeated-double'
    z = next(iter(A - {s, t}))
    weights = {(z, z): Q(1, 4), (s, s): Q(3, 16),
               (3, s): Q(3, 16), (t, t): Q(3, 16), (4, t): Q(3, 16)}
    check_eta(fibres, weights, 'H4')
    return 'H4-shared-outside'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True, help='Write JSON results to this path.')
    args = parser.parse_args()
    psi = [Q(1), Q(1, 3), Q(2, 5), Q(1, 5), Q(2, 15), Q(1, 5), Q(2, 25), Q(1, 15), Q(1, 25)]
    eta = [Q(1), Q(1), Q(2, 3), Q(2, 3), Q(2, 3), Q(1, 3), Q(2, 3), Q(1, 3), Q(1, 3)]
    t = Q(25, 28)
    caps = [Q(1)] + [(t * psi[i] + (1 - t) * eta[i]) if i == 2 else
                    max(t * psi[i], (1 - t) * eta[i]) for i in range(1, 9)]
    expected = [Q(1), Q(25, 84), Q(3, 7), Q(5, 28), Q(5, 42), Q(5, 28), Q(1, 14), Q(5, 84), Q(1, 28)]
    require(caps == expected and charge(caps) == Q(249, 28), 'balanced cap replay')
    deletion_patterns = [p for p in itertools.product(range(3), repeat=3) if sum(p) <= 3]
    for p in deletion_patterns:
        require(min(3 - d for d in p) >= 1, 'empty punctured branch')
        require(sum(min(2, 3 - d) for d in p) >= 5, 'five-leaf puncture failed')
    owner_cases = 0
    label_subsets = subsets(range(3))
    for owner_count in (2, 3):
        for fibres in itertools.product(label_subsets, repeat=owner_count):
            if frozenset.union(*fibres) != frozenset(range(3)):
                continue
            choices = [tuple(i for i, f in enumerate(fibres) if label in f) for label in range(3)]
            require(any(max(Counter(a).values()) <= 2 for a in itertools.product(*choices)),
                    'three-label owner capacity-two matching failed')
            owner_cases += 1
    routes = Counter(mono_route(E, F) for E in subsets(range(6)) for F in subsets(range(6)))
    require(sum(routes.values()) == 3969, 'wrong incidence count')
    require(len(routes) == 6, 'missing mono branch control')
    result = {
        'status': 'PASS', 'scope': 'exact cap arithmetic, finite puncture and ownership controls; ordinary proof only',
        'balanced_caps': list(map(str, caps)), 'balanced_charge': str(charge(caps)),
        'deletion_patterns': len(deletion_patterns), 'owner_incidence_cases': owner_cases,
        'mono_actual_support_cases': sum(routes.values()), 'mono_routes': dict(sorted(routes.items())),
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
