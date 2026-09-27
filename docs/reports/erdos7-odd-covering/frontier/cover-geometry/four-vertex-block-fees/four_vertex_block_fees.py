#!/usr/bin/env python3
"""Independent exact finite edge/cycle/K4 fee certificate; standard library only.

The 1793 K4 rows certify one common cutoff at all shared-budget simplex
vertices. Boundary rows intentionally charge/subtract no large-prime fees.
The general convexity, block induction and infinite tail require proof.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import prod
from pathlib import Path
import json

SMALL = tuple(p for p in range(5, 97) if all(p % d for d in range(2, p)))
FEES = {5: Q(7, 24), 7: Q(1, 8), 11: Q(1, 24), 13: Q(1, 48)}
TOTAL = sum(FEES.values(), Q()) + Q(1, 128)


def fee(p):
    return FEES.get(p, Q(1, 2 ** ((p - 1) // 2)))


def moment(weights, minimum_size):
    return sum((prod(weights[i] for i in range(3) if mask & (1 << i))
                for mask in range(1, 8) if mask.bit_count() >= minimum_size), Q())


def k4_row(kind, children, charged_primes):
    charge = sum((fee(p) for p in charged_primes), Q())
    expense = TOTAL - charge
    vertices = []
    for occupied in range(3):
        allocations = tuple(expense if i == occupied else Q() for i in range(3))
        weights = tuple(1 / (Q(3) - Q(6, 5) * e) if p == 5
                        else 1 / (Q(p - 2) - 2 * e)
                        for p, e in zip(children, allocations))
        lam, inner = moment(weights, 1), moment(weights, 2)
        vertices.append(dict(expenses=allocations, weights=weights,
                             lambda_=lam, K=inner))
    cutoff = 1 if children[0] == 5 else 2
    while True:
        gaps = [1 - v['K'] - (cutoff - 1) * v['lambda_'] for v in vertices]
        assert min(gaps) > 0, (kind, children, cutoff, 'no valid common cutoff')
        A = 2 * charge * 3 ** (cutoff - 1)
        Hs = [(1 + A * (cutoff - 1)) * sum(v['weights'], Q())
              + (1 + A * cutoff) * v['K'] for v in vertices]
        if all(h <= A for h in Hs):
            break
        cutoff += 1
    for vertex, gap, H in zip(vertices, gaps, Hs):
        cost = vertex['lambda_'] / (2 * 3 ** (cutoff - 1) * gap)
        assert cost <= charge
        # Check using integer cross multiplication as well as Fraction order.
        assert H.numerator * A.denominator <= A.numerator * H.denominator
        vertex.update(gap=gap, cost=cost, A=A, H=H, H_slack=A-H)
    return dict(class_=kind, children=children, charged_primes=charged_primes,
                expense_upper=expense, charge=charge, common_cutoff=cutoff,
                vertices=vertices, worst_cost=max(v['cost'] for v in vertices))


def cactus_row(kind, s, t=None):
    x = Q(3, 2 * (s - 1))
    charge = fee(s) + (fee(t) if t is not None and t < 97 else Q())
    if t is None:
        lam, inner = x, Q()
    else:
        y = Q(3, 2 * (t - 1))
        if kind == 'triangle':
            lam, inner = x + y + x * y, x * y
        else:
            remaining = Q(13, 100) - sum((Q(1, (p - 1)**2) for p in SMALL
                                         if p < t and p != s), Q())
            lam, inner = x + y, Q(9, 4) * remaining - (x + y)**2 / 4
    cutoff = 1 if s == 5 else 2
    while True:
        gap = 1 - inner - (cutoff - 1) * lam
        assert gap > 0, (kind, s, t, 'no valid cutoff')
        cost = lam / (2 * 3 ** (cutoff - 1) * gap)
        if cost <= charge:
            break
        cutoff += 1
    return dict(kind=kind, children=(s,) if t is None else (s, t),
                lambda_=lam, K=inner, cutoff=cutoff, gap=gap,
                cost=cost, charge=charge, slack=charge-cost)


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are required.')
    assert len(SMALL) == 22 and TOTAL == Q(187, 384)
    rows = [k4_row('A_finite_three_small', triple, triple)
            for triple in combinations(SMALL, 3)]
    rows += [k4_row('B_two_small_one_large', (s, t, 97), (s, t))
             for s, t in combinations(SMALL, 2)]
    rows += [k4_row('C_one_small_two_large', (s, 97, 99), (s,)) for s in SMALL]
    classes = {name: sum(row['class_'] == name for row in rows)
               for name in sorted({row['class_'] for row in rows})}
    assert list(classes.values()) == [1540, 231, 22] and len(rows) == 1793
    cactus = [cactus_row('bridge', s) for s in SMALL]
    for s, t in combinations(SMALL + (97,), 2):
        cactus += [cactus_row('triangle', s, t), cactus_row('long_cycle', s, t)]
    assert len(cactus) == 528
    uniform = dict(root3=Q(1, 2)-TOTAL,
                   nonroot5=Q(3, 4)-Q(3, 10)*(TOTAL-fee(5)),
                   nonroot7=Q(5, 6)-Q(1, 3)*(TOTAL-fee(7)),
                   nonroot_at_least11=1-(1+2*TOTAL)/10)
    assert uniform == dict(root3=Q(5, 384), nonroot5=Q(177, 256),
                           nonroot7=Q(821, 1152), nonroot_at_least11=Q(1541, 1920))
    assert min(v for k, v in uniform.items() if k != 'root3') > Q(2, 3)
    worst = max(rows, key=lambda r: r['worst_cost']/r['charge'])
    summary = dict(total_fee=TOTAL, k4_class_counts=classes, k4_row_count=len(rows),
                   cactus_row_count=len(cactus), uniform_density_lower_bounds=uniform,
                   k4_worst_children=worst['children'],
                   k4_worst_common_cutoff=worst['common_cutoff'],
                   k4_worst_cost=worst['worst_cost'], k4_worst_charge=worst['charge'],
                   k4_worst_slack=worst['charge']-worst['worst_cost'],
                   cactus_worst=max(cactus,key=lambda r:r['cost']/r['charge']))
    data = dict(scope='Exact finite fee inequalities; general induction, convexity and infinite tail are separate proof obligations.',
                arithmetic='fractions.Fraction and integer cross multiplication; no floating point',
                common_cutoff='Each K4 row uses one cutoff for all three simplex vertices.',
                boundary='B charges/subtracts only s,t; C only s. 97 and 99 are odd bounds, not both original prime labels.',
                summary=summary, k4_rows=rows, cactus_rows=cactus)
    Path(__file__).with_suffix('.json').write_text(json.dumps(encode(data), separators=(',', ':'))+'\n')
    print(json.dumps(encode(summary), indent=2))


if __name__ == '__main__':
    main()
