#!/usr/bin/env python3
"""Exact controls for fixed-cofactor weighted original antichains.

The universal height bound and Gram direction are proved in the companion
note. This checks finite Bellman values and actual-AP sharpness witnesses.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, isqrt, lcm
from pathlib import Path
import argparse
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


head = tuple((i, j) for i in range(3) for j in range(3))
order = lambda i, j: all(a <= b for a, b in zip(head[i], head[j]))
all_mask = (1 << len(head))-1
up = [sum(1 << j for j in range(9) if order(i, j)) for i in range(9)]
antichains = [mask for mask in range(1 << 9)
              if all(not order(i, j) and not order(j, i)
                     for i, j in combinations([v for v in range(9) if mask >> v & 1], 2))]
require(len(antichains) == 20, 'all head-grid antichains')
cache = {}


def solve(mask, height):
    key = mask, height
    if key in cache:
        return cache[key]
    if not mask or not height:
        cache[key] = F(), ()
        return cache[key]
    best = F(-1), ()
    for selected in antichains:
        if selected & mask != selected:
            continue
        forbidden = 0
        for i in range(9):
            if selected >> i & 1:
                forbidden |= up[i]
        tail, layers = solve(mask & ~forbidden, height-1)
        value = F(selected.bit_count()) + tail/3
        if value > best[0]:
            best = value, (selected,)+layers
    cache[key] = best
    return best


def original_witness(layers, cofactor):
    rows = []
    for e, selected in enumerate(layers, 1):
        for i, (a5, a7) in enumerate(head):
            if selected >> i & 1:
                a = 5**a5 * 7**a7
                rows.append({'e': e, 'a': a, 'b': cofactor,
                             'modulus': 3**e*a*cofactor, 'residue': 1,
                             'weight': F(1, 3**(e-1))})
    return rows


def sharp_control(rows, expected):
    require(rows and all(row['a']*row['b'] > 1 for row in rows), 'original mixed labels')
    require(all(gcd(row['b'], 3*1225) == 1 and 1225 % row['a'] == 0 for row in rows),
            'complete original factorization')
    moduli = [row['modulus'] for row in rows]
    require(len(moduli) == len(set(moduli)), 'distinct numerical original moduli')
    require(all(d % e and e % d for d, e in combinations(moduli, 2)),
            'all sharp original labels are pairwise incomparable')
    require(all(1 % row['modulus'] == row['residue']
                and 2 % row['modulus'] != row['residue'] for row in rows),
            'one actual common AP point and one outside point')
    weights = [row['weight'] for row in rows]
    require(sum(weights, F()) == expected, 'pointwise weighted-count sharpness')
    period = lcm(*moduli)
    divisors = sorted({v for d in range(1, isqrt(period)+1) if period % d == 0
                       for v in (d, period//d)})
    load = {x: sum(x % d == 1 % d for d in divisors) for x in (1, 2)}
    require(load[1] == len(divisors) and load[2] == 1, 'one complete numerical test layout')
    # rho gives one-half to each actual full residue 1 and 2.
    p = F(1, 2)
    c = F(load[1], 2)
    credit = sum((w*c*c/p for w in weights), F())/expected
    loss = F(load[1]**2, 2)
    require(credit == loss, 'sharp same-law Gram deletion credit')
    v = weights
    gram_quadratic = sum((vi*vj*p for vi, vj in product(v, repeat=2)), F())
    diagonal_quadratic = expected*sum((p*vi*vi/w for vi, w in zip(v, weights)), F())
    require(gram_quadratic == diagonal_quadratic, 'sharp weighted Gram diagonal factor')
    survivor_upper = (F(load[1]**2+load[2]**2, 2)-credit)/F(1, 2)
    require(survivor_upper == 1, 'conditional upper-bound direction')
    return {'period': period, 'originals': [{**row, 'weight': str(row['weight'])} for row in rows],
            'weighted_point_count': str(expected), 'layout_divisor_count': len(divisors),
            'rho_atoms': [{'residue': 1, 'mass': '1/2'}, {'residue': 2, 'mass': '1/2'}],
            'deletion_loss': str(loss), 'Gram_credit': str(credit),
            'Gram_quadratic': str(gram_quadratic),
            'weighted_diagonal_quadratic': str(diagonal_quadratic),
            'conditioned_layout_second_moment': '1'}


def controls():
    cache.clear()
    tables, sharp = {}, {}
    for name, mask, b in [('b_gt_one', all_mask, 11), ('b_equal_one_mixed', all_mask & ~1, 1)]:
        tables[name] = []
        for height in range(1, 7):
            value, layers = solve(mask, height)
            expected = F(3) if height == 1 else F(11, 3) if height == 2 or b == 1 else F(34, 9)
            require(value == expected, 'finite-height weighted antichain value')
            witness = original_witness(layers, b)
            require(sum((row['weight'] for row in witness), F()) == value, 'DP witness value')
            tables[name].append({'height': height, 'maximum': str(value)})
            if height <= 3:
                sharp[name + '_H' + str(height)] = sharp_control(witness, value)

    # Different outside numerical cofactors may charge the same rho-supported set.
    _, layers = solve(all_mask, 3)
    rows_11 = original_witness(layers, 11)
    rows_13 = original_witness(layers, 13)
    require(all(d['modulus'] % e['modulus'] and e['modulus'] % d['modulus']
                for d, e in combinations(rows_11+rows_13, 2)), 'cross-block original incomparability')
    # L=1 under rho(1)=rho(2)=1/2 is enough: each block credit is 1/2.
    block_credit = sum((row['weight']*F(1, 2) for row in rows_11), F())/F(34, 9)
    require(block_credit == F(1, 2) and 2*block_credit > F(1, 2),
            'unbudgeted addition across b double counts deletion')

    return {
        'head_antichains': len(antichains), 'finite_height_tables': tables,
        'Bellman_states_checked': len(cache), 'sharp_actual_AP_controls': sharp,
        'cross_b_overlap_control': {'outside_cofactors': [11, 13],
            'same_deleted_mass': '1/2', 'each_block_credit': '1/2',
            'invalid_summed_credit': '1', 'load': 'constant 1'},
        'scope': 'Exact finite controls for ordinary weighted-antichain and same-law Gram arguments. '
                 'No whole-cover extremality, formal certification, or unrestricted contradiction is asserted.'
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = json.dumps(controls(), indent=2)+'\n'
    if args.output:
        args.output.write_text(payload, encoding='utf-8')
    else:
        print(payload, end='')


if __name__ == '__main__':
    main()
