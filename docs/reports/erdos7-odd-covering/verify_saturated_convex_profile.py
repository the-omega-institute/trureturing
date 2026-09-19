"""Rebuild SH19--SH29 on the single probability certified by SH18.

Requires NumPy. The adjacent SH18 certificate is an explicit, hash-bound
prerequisite; verify_saturated_joint_head.py verifies that prerequisite.
This replay checks new convex maxima and compares its reduced square
maxima with all 270 independently enumerated SH18 square observations.
All finite calculations use bounded integers and exact rational numbers.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

import numpy as np


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def prepare(head):
    family = head['family']
    require(len({d for d, _ in family}) == len(family), 'distinct original labels')
    points = [x for x in range(45)
              if all(x % d != a for d, a in family if 45 % d == 0)]
    survivors = [x for x in range(315) if all(x % d != a for d, a in family)]
    fibres = [[y % 7 for y in survivors if y % 45 == x] for x in points]
    sizes = [len(row) for row in fibres]
    require(points == head['points'] and sizes == head['r'], 'actual low geometry')
    require(len(survivors) == 77 and all(6 in row for row in fibres),
            'actual carrier and common surviving digit')
    nums, denominator = head['weight_numerators'], head['weight_denominator']
    require(all(isinstance(w, int) and w >= 0 for w in nums), 'nonnegative weights')
    require(sum(r*w for r, w in zip(sizes, nums)) == denominator > 0,
            'same-law normalization')
    moduli = (3, 5, 9, 15)
    choices = list(product(*[sorted({x % d for x in points}) for d in moduli]))
    require(len(choices) == 280, 'all base layouts omitting the singleton45 label')
    features = np.array([[[int(x % d == a) for x in points]
                          for d, a in zip(moduli, row)] for row in choices], dtype=np.int64)
    return points, sizes, nums, denominator, features


def exact_cost(features, sizes, nums, denominator, depth, threshold=None):
    """Maximize the two singleton choices by the SH21 convex increment identity."""
    u3, u5, u7 = [z+1 for z in depth]
    loads = 1 + np.einsum('ajn,j->an', features,
                         np.array([1, u5, u3, u5], dtype=np.int64), dtype=np.int64)
    singleton = u3*u5
    limit = (1+u7)*(2+2*u5+u3+singleton)
    # This bounds the sum of baseline and every nonnegative increment used
    # below, including the two independent maxima before their comparison.
    range_bound = 4*denominator*limit**2
    require(range_bound < 2**63, 'all vector arithmetic fits signed64')
    n = len(loads)
    base = np.zeros((n, n), dtype=np.int64)
    first, second, together = base.copy(), base.copy(), base.copy()

    def cost(x):
        return x*x if threshold is None else np.maximum(x-threshold, 0)

    for k, (r, weight) in enumerate(zip(sizes, nums)):
        aa, bb = loads[:, k, None], loads[None, :, k]
        xx = aa+u7*bb
        hx, ha = cost(xx), cost(aa)
        extra = (r-1)*(cost(aa+singleton)-ha)
        base += weight*((r-1)*ha+hx)
        a = weight*(extra+cost(xx+singleton)-hx)
        b = weight*(cost(xx+u7*singleton)-hx)
        j = weight*(extra+cost(xx+(1+u7)*singleton)-hx)
        require(np.all(j >= a+b), 'convex same-point increment dominates sum')
        np.maximum(first, a, out=first)
        np.maximum(second, b, out=second)
        np.maximum(together, j, out=together)
    return int((base+np.maximum(first+second, together)).max()), range_bound


def refine_hinge_two(points, sizes, nums, denominator, mean, q, records):
    moduli = (3, 5, 9, 15, 45)
    choices = product(*[sorted({x % d for x in points}) for d in moduli])
    masks = np.array([[[int(x % d == a) for x in points]
                       for d, a in zip(moduli, row)] for row in choices], dtype=np.int64)
    weights = np.array(nums, dtype=np.int64)
    rw = np.array([r*w for r, w in zip(sizes, nums)], dtype=np.int64)
    a_masses, b_masses = masks @ rw, masks @ weights
    a_caps, b_caps = a_masses.max(axis=0), b_masses.max(axis=0)
    deficits = a_caps-a_masses
    require(np.all(deficits >= 0) and np.any(np.all(deficits == 0, axis=1)),
            'nonnegative independent mean deficits with simultaneous zero')
    bonus = (masks.sum(axis=1) == 0) @ (rw-weights)
    n3, n5 = 12, 8
    require(2*denominator*(2+2*(n5+2)+(n3+2)+(n3+2)*(n5+2)) < 2**63,
            'all direct hinge2 arithmetic fits signed64')
    observations, table = [], {}
    for z3, z5 in product(range(n3+2), range(n5+2)):
        vv = np.array([1, z5+1, z3+1, z5+1, (z3+1)*(z5+1)], dtype=np.int64)
        g = int((bonus-deficits @ vv).max())
        require(g >= 0, 'nonnegative correction from a maximum-mean layout')
        qa = denominator+int(a_caps @ vv)
        qb = sum(nums)+int(b_caps @ vv)
        table[z3, z5] = (g, qa, qb)
        observations.append({'depth': [z3, z5], 'correction_numerator': g})
    for row in records:
        z3, z5, z7 = row['depth']
        g, qa, qb = table[z3, z5]
        require(qa+(z7+1)*qb-2*denominator+g == row['hinge_numerators'][0],
                'direct hinge2 identity agrees with every reduced convex maximum')
    inside = sum((F(2, 3**(z3+1))*F(4, 5**(z5+1))*F(table[z3, z5][0], denominator)
                  for z3, z5 in product(range(n3+1), range(n5+1))), F(0))
    tail3, tail5 = F(1, 3**(n3+1)), F(1, 5**(n5+1))
    remainder = tail3*sum((F(4, 5**(z5+1))*F(table[n3+1, z5][0], denominator)
                          for z5 in range(n5+1)), F(0))
    remainder += tail5*sum((F(2, 3**(z3+1))*F(table[z3, n5+1][0], denominator)
                           for z3 in range(n3+1)), F(0))
    remainder += tail3*tail5*F(table[n3+1, n5+1][0], denominator)
    require(remainder >= 0, 'nonnegative monotone orthant remainder')
    upper = mean-2+inside+remainder
    return {'depth_box': [n3, n5], 'observations': observations,
            'finite_correction': str(inside), 'geometric_remainder': str(remainder),
            'lambda_upper': str(upper), 'nu_upper': str(upper/q)}


def combined_prime_cost(square, mean, hinges, standard):
    """Exact natural-cap/charge consumer; no change of actual prime kernels."""
    def features(p, threshold, n, target, future):
        d = p-1-threshold
        aa, cap = F(3*p-1, (p-1)**2), F(p-1, d)

        def cost(z):
            return target*max(F(0), F(z-threshold))/d + future*aa*(
                F(p-1, p-1-min(z, threshold))-cap)

        top = (threshold+n-1)//n
        values = {k: cost(n*k) for k in range(1, top+2)}
        linear = values[2]-values[1]
        coeff = {k: values[k+1]-2*values[k]+values[k-1] for k in range(2, top+1)}
        bound = values[1]+linear*(mean-1)+sum(v*hinges[k] for k, v in coeff.items())
        for k in range(1, threshold+3):
            require(cost(n*k) == values[1]+linear*(k-1)+
                    sum(v*max(k-j, 0) for j, v in coeff.items()), 'integer cost expansion')
        return bound, linear, coeff

    probabilities = {1: F(28, 33), **{n: F(50, 3*11**n) for n in range(2, 5)}}
    tail_mass = 1-sum(probabilities.values())
    tail_mean = F(7, 6)-sum(n*pr for n, pr in probabilities.items())
    require(tail_mass > 0 and tail_mean >= 5*tail_mass, 'complete N>=5 multiplier tail')

    def costs(target):
        first = features(11, 4, 1, target, F(61, 42))[0]
        second = sum(pr*features(13, 5, n, target, F(1))[0] for n, pr in probabilities.items())
        second += target*(mean*tail_mean-5*tail_mass)/7
        return first+second

    # Evaluations at zero and one only extract an affine expression. They
    # are not claimed as probability bounds before final convexity checks.
    intercept = costs(F(0))
    slope = costs(F(1))-intercept
    require(slope == F(standard['total_charge_upper']) < 1, 'same fixed-schedule scalar coefficient')
    unconditioned = F(1403, 630)*square
    target = (unconditioned-1+intercept)/(1-slope)
    require(target > 1, 'positive final target compatible with the universal square floor')
    observations = []
    for p, threshold, future, ns in [(11, 4, F(61, 42), [1]), (13, 5, F(1), range(1, 5))]:
        require(target >= future*F(3*p-1, (p-1)**2)*F(p-1, p-1-threshold),
                'increasing continuous convex cost at final target')
        for n in ns:
            value, linear, coeff = features(p, threshold, n, target, future)
            require(linear >= 0 and all(v >= 0 for v in coeff.values()), 'nonnegative active features')
            observations.append({'p': p, 'n': n, 'upper': str(value), 'linear': str(linear),
                                 'hinge_coefficients': {str(k): str(v) for k, v in coeff.items()}})
    require(unconditioned-1+costs(target) == target, 'combined criterion closes at its exact target')
    require(target+1 < F(standard['supported_square_upper']), 'strict improvement on identical kernels')
    return {'target_excess': str(target), 'supported_square_upper': str(target+1),
            'affine_slope': str(slope), 'affine_intercept': str(intercept),
            'self_certified_survival_lower': str(1/target),
            'saving': str(F(standard['supported_square_upper'])-target-1),
            'observations': observations}


def compute(head_path):
    raw = read_artifact_bytes(head_path)
    head = json.loads(raw)
    points, sizes, nums, denominator, features = prepare(head)
    thresholds = (2, 3, 4, 5, 6, 8, 10, 12)
    rows = head['records']
    require(head['depth_box'] == [8, 5, 4], 'specified complete depth box')
    require({tuple(row['depth']) for row in rows} == set(product(range(9), range(6), range(5)))
            and len(rows) == 270, 'all and only the 270 depth triples')
    beta, box_square = F(0), F(0)
    totals = {t: F(0) for t in thresholds}
    records, largest_range = [], 0
    for row in rows:
        depth = row['depth']
        probability = F(2, 3**(depth[0]+1))*F(4, 5**(depth[1]+1))*F(6, 7**(depth[2]+1))
        require(probability == F(row['probability']), 'exact geometric atom')
        square, range_bound = exact_cost(features, sizes, nums, denominator, depth)
        require(square == row['square_numerator'], 'agreement with independent full square enumeration')
        largest_range = max(largest_range, range_bound)
        values = []
        for t in thresholds:
            value, _ = exact_cost(features, sizes, nums, denominator, depth, t)
            values.append(value)
            totals[t] += probability*F(value, denominator)
        records.append({'depth': depth, 'hinge_numerators': values})
        beta += probability
        box_square += probability*F(square, denominator)
    require(beta == F(head['beta']), 'same depth-box mass')
    outside_excess = F(head['U_B'])-box_square-(1-beta)
    require(outside_excess >= 0, 'nonnegative complete outside square-minus-one budget')
    q = F(head['survival_lower'])
    require(0 < q <= 1, 'positive prerequisite survival lower bound')
    hinges = {}
    for t in thresholds:
        # For integer k>=1, the positive-branch majorant difference is
        # (k-2t)*(t*(k-2t)+1)>=0. Equality at k=2t proves optimality.
        coefficient = F(t, 4*t*t-1)
        remainder = coefficient*outside_excess
        upper = totals[t]+remainder
        hinges[str(t)] = {'integer_square_coefficient': str(coefficient),
                          'finite_box': str(totals[t]), 'geometric_remainder': str(remainder),
                          'lambda_upper': str(upper), 'nu_upper': str(upper/q)}
    divisors = [3**a*5**b*7**c for a, b, c in product(range(3), range(2), range(2))]
    weights_by_residue = {x: F(nums[points.index(x % 45)], denominator) for x in survivors_from(head)}
    caps = [max(sum((w for x, w in weights_by_residue.items() if x % d == a), F(0))
                for a in range(d)) for d in divisors]
    require(list(map(str, caps)) == head['caps'], 'actual full315 cylinder masses')
    mean = sum(((1+F(g))*c for g, c in zip(head['gamma_full'], caps)), F(0))
    refined = refine_hinge_two(points, sizes, nums, denominator, mean, q, records)
    require(F(refined['nu_upper']) < F(hinges['2']['nu_upper']), 'strict direct hinge2 improvement')
    first = min([1+(mean-1)/q, 2+F(refined['nu_upper'])]+
                [t+F(hinges[str(t)]['nu_upper']) for t in thresholds])
    h2, h3 = F(refined['nu_upper']), F(hinges['3']['nu_upper'])
    h4, h5 = F(hinges['4']['nu_upper']), F(hinges['5']['nu_upper'])
    charge11 = h4/6
    charge13 = (F(131, 726)*h2+F(50, 363)*h3+F(28, 33)*h5+F(2, 121))/7
    p1, p2, multiplier_mean = F(28, 33), F(50, 363), F(7, 6)
    direct13 = (p1*h5+p2*(h2+h3)+(2+h2)*(multiplier_mean-p1-2*p2)
                -5*(1-p1-p2))/7
    require(charge13 == direct13, 'independent complete multiplier-tail evaluation')
    joint_square = F(1403, 630)*F(head['Gamma'])
    joint_survival = 1-charge11-charge13
    require(joint_survival > 0, 'positive exact two-prime continuation mass')
    continuation = {'threshold11': 4, 'threshold13': 5,
                    'charge11_upper': str(charge11), 'charge13_upper': str(charge13),
                    'total_charge_upper': str(charge11+charge13),
                    'survival_lower': str(joint_survival), 'square_before_conditioning': str(joint_square),
                    'supported_square_upper': str(1+(joint_square-1)/joint_survival)}
    selected_hinges = {int(t): F(row['nu_upper']) for t, row in hinges.items()}
    selected_hinges[2] = F(refined['nu_upper'])
    combined = combined_prime_cost(F(head['Gamma']), first, selected_hinges, continuation)
    result = {'schema': 1, 'scope': 'SH18 carrier and law; arbitrary finite original357 heights',
              'head_certificate_sha256': sha256(raw).hexdigest(),
              'thresholds': list(thresholds), 'base_layouts': len(features),
              'depth_count': len(rows), 'records': records,
              'outside_square_excess': str(outside_excess), 'survival_lower': str(q),
              'mean_lambda_upper': str(mean), 'mean_nu_upper': str(first),
              'square_nu_upper': head['Gamma'], 'hinges': hinges, 'refined_hinge2': refined,
              'continuation11_13': continuation, 'combined_prime_cost': combined}
    stats = {'verified': True, 'depth_count': len(rows), 'base_pairs_per_query': len(features)**2,
             'hinge_queries': len(rows)*len(thresholds),
             'independent_square_comparisons': len(rows), 'integer_range_bound': largest_range,
             'mean_nu_upper': str(first), 'hinge6_nu_upper': hinges['6']['nu_upper']}
    return result, stats


def survivors_from(head):
    return [x for x in range(315) if all(x % d != a for d, a in head['family'])]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--head', type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/saturated_joint_head_certificate.json'))
    parser.add_argument('--certificate', type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/saturated_convex_profile_certificate.json'))
    parser.add_argument('--write', action='store_true', help='write the exact research data')
    args = parser.parse_args()
    result, stats = compute(args.head)
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(read_artifact_text(args.certificate)), 'complete convex certificate equality')
    print(json.dumps(stats, indent=2))
