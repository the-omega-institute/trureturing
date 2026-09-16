"""Rebuild the SH18 supported-law certificate from actual congruence classes.

Requires NumPy; no LP solver, cached layouts or external experiment files.
All maxima use bounded integer arithmetic; final comparisons use Fractions.
SH10-SH17 in marked_head_profile.md supply the arbitrary-height argument.
"""

import argparse
from fractions import Fraction as F
from itertools import product
from math import lcm, prod
from pathlib import Path
import json

import numpy as np


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def low_layouts(points, moduli):
    residues = [sorted({x % d for x in points}) for d in moduli]
    choices = list(product(*residues))
    features = np.array([
        [[int(x % d == a) for x in points] for d, a in zip(moduli, row)]
        for row in choices
    ], dtype=np.int64)
    return choices, features


def verify(path):
    data = json.loads(Path(path).read_text())
    family = data['family']
    exps = list(product(range(3), range(2), range(2)))
    divisors = [3**a * 5**b * 7**c for a, b, c in exps]
    require(sorted(d for d, _ in family) == sorted(divisors[1:]),
            'exact distinct nonunit315 divisor labels')
    require(all(0 <= a < d for d, a in family), 'actual original residues')
    old = [(d, a) for d, a in family if 45 % d == 0]
    points = [x for x in range(45) if all(x % d != a for d, a in old)]
    survivors = [z for z in range(315) if all(z % d != a for d, a in family)]
    fibres = [[z % 7 for z in survivors if z % 45 == x] for x in points]
    sizes = [len(fibre) for fibre in fibres]
    require(points == data['points'] and sizes == data['r'], 'actual low fibres')
    require(len(survivors) == data['N'] == 77, 'actual77-point support')
    require([6 - r for r in sizes] == data['b'], 'actual deletion vector')
    require(all(6 in fibre for fibre in fibres), 'globally surviving seven digit')
    nums, normalizer = data['weight_numerators'], data['weight_denominator']
    require(len(nums) == len(points) and all(isinstance(u, int) and u >= 0 for u in nums),
            'nonnegative per-digit integer weights')
    require(sum(r * u for r, u in zip(sizes, nums)) == normalizer > 0,
            'same-law normalization')
    require(normalizer < 2**63, 'normalizer fits integer arrays')
    weights = np.array(nums, dtype=np.int64)
    rweights = np.array([r * u for r, u in zip(sizes, nums)], dtype=np.int64)
    caps_num = []
    for d in divisors:
        c = d // 7 if d % 7 == 0 else d
        values = [sum(u * (1 if d % 7 == 0 else r)
                      for x, r, u in zip(points, sizes, nums) if x % c == a)
                  for a in range(c)]
        caps_num.append(max(values))
    caps = [F(v, normalizer) for v in caps_num]
    require(list(map(str, caps)) == data['caps'], 'exact actual cylinder caps')
    cap_gram = np.array([[caps_num[divisors.index(lcm(d, e))]
                         for e in divisors] for d in divisors], dtype=np.int64)
    gamma, pair_coeff = [], {}
    for a, d in zip(exps, divisors):
        gamma.append(prod(F(p, p - 1) if j == h else F(1)
                          for p, j, h in zip((3, 5, 7), a, (2, 1, 1))) - 1)
        for b, e in zip(exps, divisors):
            terms = [F(p * (p + 1), (p - 1)**2) if j == h and k == h
                     else F(p, p - 1) if j == h or k == h else F(1)
                     for p, j, k, h in zip((3, 5, 7), a, b, (2, 1, 1))]
            pair_coeff[d, e] = prod(terms) - 1
    require(list(map(str, gamma)) == data['gamma_full'], 'saturated mean coefficients')

    # The complete low maxima need only nonempty cylinders. Replacing an
    # empty cylinder by a nonempty one increases each nonnegative test load.
    _, raw_features = low_layouts(points, (3, 5, 9, 15, 45))
    count = len(raw_features)
    require(count == 4480, 'all active old45 layout choices')
    features = np.concatenate((np.ones((count, 1, len(points)), dtype=np.int64),
                               raw_features), axis=1)
    cutoffs = data['depth_box']
    require(cutoffs == [8, 5, 4], 'specified finite auxiliary box')
    recorded = {tuple(row['depth']): row for row in data['records']}
    require(len(recorded) == len(data['records']) == 270, 'unique complete depth observations')
    p0 = int(cap_gram.sum())
    beta, box_p, box_f = F(0), F(0), F(0)
    g0, max_range = None, 0
    for z3, z5 in product(range(cutoffs[0] + 1), range(cutoffs[1] + 1)):
        u3, u5 = z3 + 1, z5 + 1
        cofactor_weights = [1, 1, u5, u3, u5, u3 * u5]
        load_limit = sum(cofactor_weights)
        largest_seven = cutoffs[2] + 1
        range_bound = load_limit**2 * (normalizer +
                      (2 * largest_seven + largest_seven**2) * sum(nums))
        require(range_bound < 2**63, 'all square dot products fit signed64 integers')
        max_range = max(max_range, range_bound)
        loads = np.einsum('ajn,j->an', features,
                          np.array(cofactor_weights, dtype=np.int64), dtype=np.int64)
        gram = (loads * weights) @ loads.T
        qa, qb = (loads * loads) @ rweights, (loads * loads) @ weights
        for z7 in range(cutoffs[2] + 1):
            u7 = z7 + 1
            scores = 2 * u7 * gram + qa[:, None] + u7 * u7 * qb[None, :]
            location = np.unravel_index(scores.argmax(), scores.shape)
            value = int(scores[location])
            aa, bb = loads[location[0]].tolist(), loads[location[1]].tolist()
            require(value == sum(u * (r * a*a + 2*u7*a*b + u7*u7*b*b)
                                 for u, r, a, b in zip(nums, sizes, aa, bb)),
                    'independent Python-integer maximizing-layout evaluation')
            z = (z3, z5, z7)
            row = recorded[z]
            probability = F(2, 3**(z3+1)) * F(4, 5**(z5+1)) * F(6, 7**(z7+1))
            require(value == row['square_numerator'] and probability == F(row['probability']),
                    'complete weighted-square observation')
            ww = [(u3 if a == 2 else 1) * (u5 if b == 1 else 1) * (u7 if c == 1 else 1)
                  for a, b, c in exps]
            require(sum(ww)**2 * max(caps_num) < 2**63, 'pair-cap polynomial range')
            warray = np.array(ww, dtype=np.int64)
            pv = int(warray @ cap_gram @ warray)
            if z == (0, 0, 0):
                g0 = value
            require(g0 is not None and pv-value >= p0-g0, 'shared unweighted deficit')
            beta += probability
            box_p += probability * F(pv, normalizer)
            box_f += probability * F(value, normalizer)
    delta = sum((coefficient * caps[divisors.index(lcm(d, e))]
                 for (d, e), coefficient in pair_coeff.items()), F(0))
    upper = F(g0, normalizer) + delta - box_p + box_f + beta * F(p0-g0, normalizer)
    require(beta == F(data['beta']) and upper == F(data['U_B']), 'SH12 complete geometric remainder')

    # Independent SH13 evaluation using products of geometric moments.
    moments = [[sum((F(p-1, p**(z+1)) * (1+z)**k for z in range(n+1)), F(0))
                for k in range(3)] for p, n in zip((3, 5, 7), cutoffs)]
    eta = {d: F(0) for d in divisors}
    for a, d in zip(exps, divisors):
        for b, e in zip(exps, divisors):
            inside = prod(moments[i][int(a[i] == h) + int(b[i] == h)]
                          for i, h in enumerate((2, 1, 1))) - beta
            outside = pair_coeff[d, e] - inside
            require(outside >= 0, 'positive omitted ordered-pair contribution')
            eta[lcm(d, e)] += outside
    require([str(eta[d]) for d in divisors] == data['eta_out'], 'outside coefficients')
    require(upper == (1-beta) * F(g0, normalizer) + box_f +
            sum((eta[d] * m for d, m in zip(divisors, caps)), F(0)),
            'independent SH13 positive-coefficient evaluation')

    e3, e5, e7 = data['e3'], data['e5'], data['e7']
    require(e3 == [9, 45] and e5 == [5, 15, 45] and
            e7 == [7, 21, 35, 63, 105, 315], 'specified coordinate groups')
    remainder = [g - (F(1, 2) if d in e3 else 0) - (F(1, 4) if d in e5 else 0)
                 - (F(1, 6) if d in e7 else 0) for d, g in zip(divisors, gamma)]
    require(min(remainder) >= 0 and list(map(str, remainder)) == data['gamma_remaining'],
            'all original singleton blocks removed exactly once')
    _, fa = low_layouts(points, e3)
    _, fb = low_layouts(points, e5)
    a_loads, b_loads = fa.sum(axis=1), fb.sum(axis=1)
    require(a_loads.shape == (80, 16) and b_loads.shape == (448, 16), 'complete block layouts')
    require(48*normalizer + 48*sum(nums) < 2**63, 'all block arithmetic fits signed64')
    masks = [np.array([[int(x % c == t) for x in points] for t in range(c)], dtype=np.int64)
             for c in (1, 3, 5, 9, 15, 45)]
    best = -1
    for a in a_loads:
        base = (6 * (4*a + 2*b_loads - a*b_loads)) @ rweights
        residual = (2-a) * (4-b_loads) * weights
        require(residual.min() >= 0, 'nonnegative block residual weights')
        scores = base.copy()
        for mask in masks:
            scores += (residual @ mask.T).max(axis=1)
        index = int(scores.argmax())
        value = int(scores[index])
        if value > best:
            best = value
            witness = a.tolist(), b_loads[index].tolist()
    a, b = witness
    check = 6 * sum(r*u*(4*aa+2*bb-aa*bb) for r,u,aa,bb in zip(sizes,nums,a,b))
    for c in (1, 3, 5, 9, 15, 45):
        check += max(sum(u*(2-aa)*(4-bb) for x,u,aa,bb in zip(points,nums,a,b) if x%c == t)
                     for t in range(c))
    require(check == best, 'independent integer block witness evaluation')
    block = F(best, 48*normalizer)
    remaining = sum((g*m for g,m in zip(remainder,caps)), F(0))
    survival = 1-block-remaining
    require(block == F(data['block_union']) and remaining == F(data['remaining_union']),
            'same-law joint block union and remaining mass')
    require(survival == F(data['survival_lower']) > 0, 'positive same-law survival')
    result = 1 + (upper-1)/survival
    require(result == F(data['Gamma']) < F(3849,106), 'strict all-height comparison')
    require(F(data['saving']) == F(3849,106)-result, 'exact improvement')
    return {'verified': True, 'scope': 'specified77-point low geometry, arbitrary357 heights',
            'layout_pairs': count**2, 'depth_costs': len(recorded),
            'square_pairs_checked': count**2 * len(recorded),
            'block_pairs_checked': len(a_loads) * len(b_loads),
            'integer_range_bound': max_range, 'unconditional_square': str(upper),
            'survival_lower': str(survival), 'Gamma': str(result),
            'saving_over_3849_over_106': str(F(3849,106)-result)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=Path(__file__).with_name('saturated_joint_head_certificate.json'))
    print(json.dumps(verify(parser.parse_args().certificate), indent=2))
