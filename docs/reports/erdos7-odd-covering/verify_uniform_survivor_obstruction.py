#!/usr/bin/env python3
"""Verify a complete uniform-survivor obstruction by exact finite arithmetic.

Python 3.9+ standard library only; no solver, oracle, or external imports.
The companion mathematical proof establishes the general residue geometry.
This program recomputes every finite H=5 cylinder sum, verifies disjointness
by the CRT criterion, and independently enumerates the 3^5 and 5^5 fibers.
It computes the score of one coherent layout, hence a lower bound on Gamma;
it does not assert that this layout maximizes Gamma.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import combinations
from math import isqrt, prod
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def primes_through(bound):
    return tuple(p for p in range(3, bound + 1)
                 if all(p % d for d in range(2, isqrt(p) + 1)))


def check_cylinder_geometry(p, height, beta):
    # A cylinder is represented by its modulus and its residue.
    forbidden = [(p**e, p**(e - 1) - 1) for e in range(1, height + 1)]
    removed = [(p**e, 2 * p**(e - 1) - 1) for e in range(1, height + 1)]
    require(forbidden[0] == (p, 0), 'other mixed zero classes must be redundant')
    for (m, a), (n, b) in combinations(forbidden + removed, 2):
        require(a % min(m, n) != b % min(m, n),
                'two pure/removed cylinders intersect')
    for e in range(1, height + 1):
        m = p**e
        for n, a in forbidden:
            require(beta % min(m, n) != a % min(m, n),
                    'a test cylinder meets a forbidden pure cylinder')
        if p == 3:
            require(beta % 3 == removed[0][1], '3-adic test cylinder is outside C3,1')
        if p == 5:
            for n, a in removed:
                require(beta % min(m, n) != a % min(m, n),
                        'a 5-adic test cylinder meets C5')


def enumerate_small_fiber(p, height, beta):
    # Independent direct counts: no use of s_p or W_p formulas here.
    counts = {'survivors': 0, 'removed': 0,
              'survivor_load_square_sum': 0, 'removed_load_square_sum': 0}
    for x in range(p**height):
        survives = all(x % p**e != p**(e - 1) - 1
                       for e in range(1, height + 1))
        removed = any(x % p**e == 2 * p**(e - 1) - 1
                      for e in range(1, height + 1))
        load = 1 + sum(x % p**e == beta % p**e
                       for e in range(1, height + 1))
        require(not removed or survives, 'removed cylinder is not a pure survivor')
        if survives:
            counts['survivors'] += 1
            counts['survivor_load_square_sum'] += load**2
        if removed:
            counts['removed'] += 1
            counts['removed_load_square_sum'] += load**2
    return counts


def compute_certificate():
    height = 5
    primes = primes_through(73)
    require(primes == (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
                      37, 41, 43, 47, 53, 59, 61, 67, 71, 73),
            'prime support mismatch')
    s, lam, weight = {}, {}, {}
    finite_rows = []
    for p in primes:
        beta = 2 if p == 5 else 1
        check_cylinder_geometry(p, height, beta)
        s[p] = sum((F(1, p**e) for e in range(1, height + 1)), F(0))
        lam[p] = 1 - s[p]
        weight[p] = sum((F(2 * e + 1, p**e) for e in range(1, height + 1)), F(0))
        require(s[p] == (1 - F(1, p**height)) / (p - 1), 'finite geometric sum mismatch')
        tail = F((2 * height + 3) * (p - 1) + 2,
                 p**height * (p - 1)**2)
        require(weight[p] == F(3 * p - 1, (p - 1)**2) - tail,
                'weighted finite geometric sum mismatch')
        require(lam[p] > F(p - 2, p - 1) > 0, 'pure density lower bound failed')
        score = 1 + weight[p] / lam[p]
        count = p**height - sum(p**(height - e) for e in range(1, height + 1))
        load_sum = p**height + sum(2 * e * p**(height - e) for e in range(1, height + 1))
        require(score == F(load_sum, count), 'integer count/score formula mismatch')
        require(score == F(p**5 + 2*p**4 + 4*p**3 + 6*p**2 + 8*p + 10,
                           p**5 - p**4 - p**3 - p**2 - p - 1),
                'height-five polynomial ratio mismatch')
        finite_rows.append({'prime': p, 'test_residue': beta, 's': str(s[p]),
                            'lambda': str(lam[p]), 'W': str(weight[p]),
                            'pure_survivor_count': count,
                            'pure_load_square_sum': load_sum,
                            'pure_normalized_score': str(score)})

    small = {p: enumerate_small_fiber(p, height, 2 if p == 5 else 1) for p in (3, 5)}
    for p in (3, 5):
        count = small[p]
        modulus = p**height
        require(F(count['survivors'], modulus) == lam[p], 'enumerated survivor density mismatch')
        require(F(count['removed'], modulus) == s[p], 'enumerated removed density mismatch')
        require(F(count['survivor_load_square_sum'], modulus) == lam[p] + weight[p],
                'enumerated survivor load-square sum mismatch')
        expected_removed = s[p] + weight[p] if p == 3 else s[p]
        require(F(count['removed_load_square_sum'], modulus) == expected_removed,
                'enumerated removed load-square sum mismatch')
    require(small == {3: {'survivors': 122, 'removed': 121,
                         'survivor_load_square_sum': 601, 'removed_load_square_sum': 600},
                      5: {'survivors': 2344, 'removed': 781,
                         'survivor_load_square_sum': 5075, 'removed_load_square_sum': 781}},
            'height-five small-fiber counts mismatch')

    block_density = lam[3] * lam[5] - s[3] * s[5]
    require(block_density == 1 - s[3] - s[5]
            == (1 + 2 * F(1, 3**height) + F(1, 5**height)) / 4 > F(1, 4),
            'actual rectangle survivor density mismatch')
    block_numerator = ((lam[3] + weight[3]) * (lam[5] + weight[5])
                       - (s[3] + weight[3]) * s[5])
    block_score = block_numerator / block_density
    joint_count = small[3]['survivors'] * small[5]['survivors'] - small[3]['removed'] * small[5]['removed']
    joint_load = (small[3]['survivor_load_square_sum'] * small[5]['survivor_load_square_sum']
                  - small[3]['removed_load_square_sum'] * small[5]['removed_load_square_sum'])
    require(joint_count == 191467 and joint_load == 2581475, 'actual 35 block count mismatch')
    require(block_score == F(joint_load, joint_count) == F(2581475, 191467),
            'finite-sum score differs from independent enumeration')

    score = block_score * prod(1 + weight[p] / lam[p] for p in primes if p >= 7)
    lower, upper, threshold = F(1423789923, 10**7), F(1423789924, 10**7), F(138877, 1000)
    require(lower < score < upper and score > 142 > threshold,
            'coherent layout does not exceed the claimed thresholds')
    density = block_density * prod(lam[p] for p in primes if p >= 7)
    density_lower = F(1, 4) * prod(F(p - 2, p - 1) for p in primes if p >= 7)
    require(density > density_lower == F(36779876601, 330712481792) > F(11, 100),
            'positive-density lower bound failed')

    # These are the rational limits furnished by finite geometric series.
    limit_s = {p: F(1, p - 1) for p in primes}
    limit_lam = {p: 1 - limit_s[p] for p in primes}
    limit_weight = {p: F(3 * p - 1, (p - 1)**2) for p in primes}
    limit_block_density = limit_lam[3] * limit_lam[5] - limit_s[3] * limit_s[5]
    limit_block = ((limit_lam[3] + limit_weight[3]) * (limit_lam[5] + limit_weight[5])
                   - (limit_s[3] + limit_weight[3]) * limit_s[5]) / limit_block_density
    require(limit_block_density == F(1, 4) and limit_block == F(55, 4),
            'coupled block limit mismatch')
    limit_score = limit_block * prod(1 + limit_weight[p] / limit_lam[p]
                                     for p in primes if p >= 7)
    require(F(1452186988, 10**7) < limit_score < F(1452186990, 10**7),
            'limiting coherent-layout score interval mismatch')
    before_mixed = prod(1 + limit_weight[p] / limit_lam[p] for p in (3, 5))
    require(before_mixed == F(65, 6) and limit_block / before_mixed == F(33, 26),
            'mixed-removal amplification mismatch')

    return {
        'schema': 'erdos7-uniform-survivor-obstruction-v1', 'height': height,
        'prime_support': list(primes),
        'law': 'uniform on the complete actual survivor set',
        'layout': 'coherent: beta_5=2; beta_p=1 for p!=5; b_d=beta mod d',
        'forbidden_assignment': {
            'pure': 'a_(p^e)=p^(e-1)-1',
            'support_3_5': 'CRT(2*3^(i-1)-1 mod 3^i, 2*5^(j-1)-1 mod 5^j)',
            'other_mixed': '0 mod d; redundant with a_(p)=0 for each p dividing d'},
        'claim_scope': 'one layout score lower-bounds Gamma; uniform-law obstruction only',
        'finite_geometric_data': finite_rows,
        'independent_small_fiber_enumeration': {str(p): small[p] for p in (3, 5)},
        'coupled_35_block': {'survivor_count': joint_count, 'load_square_sum': joint_load,
                            'ambient_density': str(block_density),
                            'ambient_load_square_integral': str(block_numerator),
                            'normalized_score': str(block_score)},
        'full_coherent_layout_score': str(score),
        'score_strict_interval': [str(lower), str(upper)],
        'uniform_target': str(threshold), 'score_minus_target': str(score - threshold),
        'finite_survivor_density': str(density),
        'all_height_density_strict_lower_bound': str(density_lower),
        'density_lower_bound_minus_11_percent': str(density_lower - F(11, 100)),
        'geometric_limits': {'coupled_35_density': str(limit_block_density),
                             'coupled_35_score': str(limit_block),
                             'full_coherent_layout_score': str(limit_score),
                             'pre_mixed_35_score': str(before_mixed),
                             'mixed_removal_amplification': str(limit_block / before_mixed)},
    }


def main():
    data = json.loads(read_artifact_text(Path(__file__).resolve().parent / 'certificates/uniform_survivor_obstruction_certificate.json'))
    expected = compute_certificate()
    require(data == expected, 'fixed certificate differs from exact independent reconstruction')
    print('Verified H=5 finite geometry and direct 3^5/5^5 counts: g35 = 2581475/191467.')
    print('One coherent layout has 142.3789923 < score < 142.3789924, hence score > 138.877.')
    print('Survivor density > 36779876601/330712481792 > 0.11; limiting g35 = 55/4.')


if __name__ == '__main__':
    main()
