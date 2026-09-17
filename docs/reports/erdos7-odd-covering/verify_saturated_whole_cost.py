"""Exact whole-cost consumer on the single SH18 probability.

Requires NumPy. The SH18 and SH24 certificates are hash-bound prerequisites;
their existing verifiers own those prior square/profile observations.
This replay computes810 new whole-cost maxima with exact integer tables,
complete geometric remainders and the original zero exponent label.
It uses no solver, quantization, cache, scratch imports or Lean wrappers.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import lcm
from pathlib import Path
import json

import numpy as np


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def prepare(head):
    family = head['family']
    require(len(family) == len({d for d, _ in family}) == 11, 'distinct original low labels')
    points = [x for x in range(45)
              if all(x % d != a for d, a in family if 45 % d == 0)]
    survivors = [x for x in range(315) if all(x % d != a for d, a in family)]
    fibres = [[x % 7 for x in survivors if x % 45 == a] for a in points]
    sizes = [len(xs) for xs in fibres]
    require(points == head['points'] and sizes == head['r'] and len(survivors) == 77,
            'same actual77-point carrier')
    require(all(6 in xs for xs in fibres), 'one globally surviving seven digit')
    nums, denominator = head['weight_numerators'], head['weight_denominator']
    require(all(isinstance(w, int) and w >= 0 for w in nums), 'nonnegative exact weights')
    require(sum(r*w for r, w in zip(sizes, nums)) == denominator > 0,
            'unchanged probability normalization')
    choices = list(product(*[sorted({x % d for x in points}) for d in (3, 5, 9, 15)]))
    require(len(choices) == 280, 'all old base layouts without45')
    features = np.array([[[int(x % d == a) for x in points]
                          for d, a in zip((3, 5, 9, 15), row)] for row in choices], dtype=np.int64)
    rows = head['records']
    require(len(rows) == 270 and {tuple(r['depth']) for r in rows}
            == set(product(range(9), range(6), range(5))), 'complete prescribed depth box')
    beta, box_square = F(0), F(0)
    for row in rows:
        a, b, c = row['depth']
        probability = F(2, 3**(a+1))*F(4, 5**(b+1))*F(6, 7**(c+1))
        require(probability == F(row['probability']), 'exact independent geometric atom')
        beta += probability
        box_square += probability*F(row['square_numerator'], denominator)
    require(beta == F(head['beta']), 'complete box probability')
    outside = F(head['U_B'])-box_square-(1-beta)
    require(outside >= 0, 'complete outside square-minus-one budget')
    return features, sizes, nums, denominator, outside


def maximum_cost(features, sizes, nums, denominator, depth, table):
    u3, u5, u7 = [z+1 for z in depth]
    loads = 1+np.einsum('ajn,j->an', features,
                        np.array([1, u5, u3, u5], dtype=np.int64), dtype=np.int64)
    v = u3*u5
    limit = (1+u7)*(2+2*u5+u3+v)
    # Convexity makes first+second bounded by an attainable complete increment,
    # including when the two singleton maximizers coincide. Each intermediate
    # nonnegative sum is therefore bounded by a full cost <=D*table[limit].
    range_bound = denominator*int(table[limit])
    require(denominator >= max(sizes) and range_bound < 2**63, 'signed64 range for every intermediate')
    n = len(loads)
    base = np.zeros((n, n), dtype=np.int64)
    first, second, joint = base.copy(), base.copy(), base.copy()
    for i, (r, weight) in enumerate(zip(sizes, nums)):
        aa, bb = loads[:, i, None], loads[None, :, i]
        xx = aa+u7*bb
        hx, ha = table[xx], table[aa]
        extra = (r-1)*(table[aa+v]-ha)
        base += weight*((r-1)*ha+hx)
        da = weight*(extra+table[xx+v]-hx)
        db = weight*(table[xx+u7*v]-hx)
        both = weight*(extra+table[xx+(1+u7)*v]-hx)
        require(np.all(both >= da+db), 'exact convex singleton interaction')
        np.maximum(first, da, out=first)
        np.maximum(second, db, out=second)
        np.maximum(joint, both, out=joint)
    value = int((base+np.maximum(first+second, joint)).max())
    require(0 <= value <= range_bound, 'complete maximum within certified range')
    return value, range_bound


def scalar_cost(p, threshold, n, target, future):
    d = p-1-threshold
    a, c = F(3*p-1, (p-1)**2), F(p-1, d)
    require(1 < threshold < p-1 and c <= p, 'unchanged AP kernel admissibility')
    require(target >= future*a*F(p-1, d), 'continuous convexity at the clipping join')

    def cost(k):
        z = n*k
        return target*max(F(0), z-threshold)/d + future*a*(F(p-1, p-1-min(z, threshold))-c)

    return cost


def whole_observation(name, cost, linear_from, head, prepared, q):
    features, sizes, nums, denominator, outside = prepared
    center = cost(2)

    def cut(k):
        return max(F(0), cost(k)-center)

    values = [F(0)]+[cut(k) for k in range(1, 463)]
    require(values[1] == 0, 'cut cost vanishes atone')
    increments = [values[k]-values[k-1] for k in range(1, len(values))]
    require(all(0 <= x <= y for x, y in zip([F(0)]+increments, increments)),
            'exact increasing convex integer table')
    scale = lcm(*(v.denominator for v in values))
    scaled = [v*scale for v in values]
    require(all(v.denominator == 1 and 0 <= v < 2**63 for v in scaled), 'exact cost numerators')
    table = np.array([int(v) for v in scaled], dtype=np.int64)
    require(all(F(int(table[k]), scale) == values[k] for k in range(len(table))),
            'no quantization or rounding')

    # All supplied costs are affine from this integer onward. If cut(k)=A*k-B
    # there, convexity and the cut at2 give2A<=B<=A*linear_from.
    # For real x>=2*linear_from, derivative of(A*x-B)/(x²-1) is negative:
    # its numerator <=-A*x*(x-2*linear_from)-A<0. Thus the finite scan is complete.
    k0 = max(2, linear_from)
    slope = cut(k0+1)-cut(k0)
    intercept = slope*k0-cut(k0)
    require(slope > 0 and 2*slope <= intercept <= k0*slope, 'affine tail root interval')
    require(all(cut(k) == slope*k-intercept for k in range(k0, 463)), 'entire finite affine tail')
    ratios = [(cut(k)/F(k*k-1), k) for k in range(2, 2*k0+2)]
    coefficient, maximizing_integer = max(ratios)

    total, largest_range, records = F(0), 0, []
    for row in head['records']:
        value, range_bound = maximum_cost(features, sizes, nums, denominator, row['depth'], table)
        total += F(row['probability'])*F(value, denominator*scale)
        largest_range = max(largest_range, range_bound)
        records.append({'depth': row['depth'], 'cost_numerator': value})
    remainder = coefficient*outside
    bound = center+(total+remainder)/q
    return {'name': name, 'conditioning_cut': 2, 'conditioning_center': str(center),
            'exact_cost_denominator': scale, 'integer_range_bound': largest_range,
            'linear_from': linear_from, 'affine_slope': str(slope), 'affine_intercept': str(intercept),
            'square_majorant_coefficient': str(coefficient), 'majorant_maximizing_integer': maximizing_integer,
            'finite_box': str(total), 'geometric_remainder': str(remainder),
            'nu_cost_upper': str(bound), 'records': records}


def compute(head_path, profile_path):
    head_raw, profile_raw = read_artifact_bytes(head_path), read_artifact_bytes(profile_path)
    head, profile = json.loads(head_raw), json.loads(profile_raw)
    require(profile['head_certificate_sha256'] == sha256(head_raw).hexdigest(), 'same head prerequisite')
    prepared = prepare(head)
    q = F(head['survival_lower'])
    require(q == F(profile['survival_lower']) and 0 < q <= 1, 'same SH18 conditioned probability')
    h2 = F(profile['refined_hinge2']['nu_upper'])
    mean, square = F(profile['mean_nu_upper']), F(profile['square_nu_upper'])
    require(mean == 2+h2 and square == F(head['Gamma']), 'same simultaneous mean/square/hinge bounds')
    target = F(3049, 20)
    h11 = scalar_cost(11, 4, 1, target, F(61, 42))
    h13 = {n: scalar_cost(13, 5, n, target, F(1)) for n in range(1, 5)}
    probabilities = {1: F(28, 33), **{n: F(50, 3*11**n) for n in range(2, 5)}}
    tail_mass = 1-sum(probabilities.values())
    tail_mean = F(7, 6)-sum(n*p for n, p in probabilities.items())
    require(tail_mass == F(5, 43923) and tail_mean == F(17, 29282), 'complete multiplier tail')

    def zero_cost(k):
        return sum(probabilities[n]*h13[n](k)/n for n in probabilities)+target*tail_mass*k/7

    query11 = whole_observation('prime11_complete_cost', h11, 4, head, prepared, q)
    query13n2 = whole_observation('prime13_multiplier2_complete_cost', h13[2], 3, head, prepared, q)
    query13zero = whole_observation('prime13_original_zero_label', zero_cost, 5, head, prepared, q)
    b2 = F(query13n2['nu_cost_upper'])
    # For n=3,4 the integer cost is affine for L>=2. Mean=2+H2 supplies
    # this bound by the exact positive first/second-difference expansion.
    other_bounds = {}
    for n in (3, 4):
        v1, v2, v3 = [h13[n](k) for k in (1, 2, 3)]
        require(v2-v1 >= 0 and v3-2*v2+v1 >= 0, 'positive retained scalar coefficients')
        value = v1+(v2-v1)*(mean-1)+(v3-2*v2+v1)*h2
        require(value == target*(n*mean-5)/7, 'exact affine bound from the threshold-two mean')
        other_bounds[n] = value
    residual = probabilities[2]*F(1, 2)*b2
    residual += sum(probabilities[n]*(1-F(1, n))*other_bounds[n] for n in (3, 4))
    residual += target*(mean*(tail_mean-tail_mass)-5*tail_mass)/7
    charge_cost13 = F(query13zero['nu_cost_upper'])+residual
    square_before_conditioning = F(1403, 630)*square
    certificate_value = square_before_conditioning-1+F(query11['nu_cost_upper'])+charge_cost13
    margin = target-certificate_value
    require(margin > 0, 'strict combined same-law criterion')
    result = {'schema': 1, 'scope': 'same SH18 law; arbitrary finite original357/11/13 heights',
              'head_certificate_sha256': sha256(head_raw).hexdigest(),
              'profile_certificate_sha256': sha256(profile_raw).hexdigest(),
              'W': str(target), 'Gamma_upper': str(1+target),
              'Gamma_sharpened_upper': str(1+certificate_value),
              'survival_lower_SH18': str(q), 'mean_upper_SH24': str(mean), 'square_upper_SH24': str(square),
              'queries': [query11, query13n2, query13zero],
              'multiplier_probabilities': {str(n): str(p) for n, p in probabilities.items()},
              'multiplier_tail_mass': str(tail_mass), 'multiplier_tail_mean': str(tail_mean),
              'prime13_residual_cost': str(residual), 'prime13_total_cost': str(charge_cost13),
              'square_before_conditioning': str(square_before_conditioning),
              'criterion_value': str(certificate_value), 'criterion_margin': str(margin)}
    stats = {'verified': True, 'whole_cost_queries': 810, 'base_pairs_per_query': 280**2,
             'rounding': 'none', 'integer_range_bound': max(r['integer_range_bound'] for r in result['queries']),
             'Gamma_upper': result['Gamma_upper'], 'criterion_margin': str(margin)}
    return result, stats


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    directory = Path(__file__).parent
    parser.add_argument('--head', type=Path, default=directory/'certificates/saturated_joint_head_certificate.json')
    parser.add_argument('--profile', type=Path, default=directory/'certificates/saturated_convex_profile_certificate.json')
    parser.add_argument('--certificate', type=Path, default=directory/'certificates/saturated_whole_cost_certificate.json')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result, stats = compute(args.head, args.profile)
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(read_artifact_text(args.certificate)), 'complete exact whole-cost certificate equality')
    print(json.dumps(stats, indent=2))
