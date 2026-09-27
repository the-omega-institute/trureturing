#!/usr/bin/env python3
"""Verify exact constants for general head laws and block tail obstructions.

Only the standard library is used. All comparisons use integers or
fractions. The arbitrary-height block theorem and cylinder estimates
remain ordinary mathematical proofs; this is not Lean certification.
The default run reads and checks the fixed adjacent JSON certificate.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product as cartesian_product
from math import gcd, isqrt, prod
from pathlib import Path
import argparse
import json

HEAD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
               37, 41, 43, 47, 53, 59, 61, 67, 71, 73)


from star_block.base import *

def stoploss_ceiling(a, b):
    require(a >= 0 and b > 0, 'nonnegative upward division')
    return (a + b - 1) // b

def stoploss_atom_bounds(p, c, cap, scale):
    # Multiplier f=1+K. Infinite-law probabilities:
    # f=1: 1-c/p; f>=2: c*(p-1)/p^f.
    cn, cd = c.numerator, c.denominator
    require(c > 0 and c <= p, 'height law exists')
    atoms = [0] * (cap + 1)
    atoms[1] = stoploss_ceiling(scale * (cd*p-cn), cd*p)
    numerator = scale * cn * (p-1)
    denominator = cd*p*p
    for f in range(2, cap+1):
        if denominator >= numerator:
            atoms[f:] = [1] * (cap+1-f)
            break
        atoms[f] = stoploss_ceiling(numerator, denominator)
        denominator *= p
    return atoms


def stoploss_product_update(weights, atoms, scale):
    cap = len(weights)-1
    raw = [0]*(cap+1)
    for f in range(1, min(cap+1, len(atoms))):
        if atoms[f]:
            for d in range(1, cap//f+1):
                raw[d*f] += weights[d]*atoms[f]
    return [stoploss_ceiling(w, scale) for w in raw]


def pure_head_unrestricted_stoploss(cases=None):
    """Keep mixed head exclusions until the single final conditioning."""
    import hashlib
    from runpy import run_path
    continuation = run_path(str((Path(__file__).resolve().parents[1] / "verify_finite_continuation.py")))
    scale = 10**18
    if cases is None:
        cases = [(head, 17 if head['period_bound'] == 315 else 19, 2048)
                 for head in finite_head_supported_laws()]
        cases.append(({'period_bound': None, 'mixed_budget': '2/3',
                       'product_moment_bound': '325/18',
                       'coordinates': [{'prime': p, 'height': None,
                                        'pure_survivor_density_lower': str(F(p-2, p-1))}
                                       for p in (3, 5, 7)]}, 23, 8192))
    results = []
    for head, q0, bound in cases:
        period = head['period_bound']
        name = f'head_divides_{period}' if period else 'arbitrary_357_head'
        cap = (2*bound+1)//5
        primes = primes_to(bound)
        k = len(primes)
        require(k >= 256 and F(448, 81) > 4, 'pure-head logarithm premise')
        stopping = (k*F(317, 81)**2 if bound == 2048
                    else continuation['stopping_threshold'](k))
        weights = [0]*(cap+1)
        weights[1] = scale
        mean = second = scale
        exact_mean = exact_second = F(1)
        head_law = {1: F(1)}
        ratios = []
        for coordinate in head['coordinates']:
            p, h = coordinate['prime'], coordinate['height']
            c = 1/F(coordinate['pure_survivor_density_lower'])
            ratios.append(c-1)
            if h is None:
                head_law = None
                upper_atoms = stoploss_atom_bounds(p, c, cap, scale)
                factor1 = 1+c/F(p-1)
                factor2 = 1+c*F(3*p-1, (p-1)**2)
            else:
                atoms = [F(0)]*(h+2)
                atoms[1] = 1-c/p
                for f in range(2, h+1):
                    atoms[f] = c*F(p-1, p**f)
                atoms[h+1] = c/F(p**h)
                require(sum(atoms) == 1 and all(a >= 0 for a in atoms),
                        'finite capped height law')
                next_law = {}
                for d, mass in head_law.items():
                    for f, a in enumerate(atoms):
                        if a:
                            next_law[d*f] = next_law.get(d*f, F(0))+mass*a
                head_law = next_law
                upper_atoms = [stoploss_ceiling(scale*a.numerator, a.denominator)
                               for a in atoms]
                factor1 = sum(f*a for f, a in enumerate(atoms))
                factor2 = sum(f*f*a for f, a in enumerate(atoms))
            weights = stoploss_product_update(weights, upper_atoms, scale)
            exact_mean *= factor1
            exact_second *= factor2
            mean = stoploss_ceiling(mean*factor1.numerator, factor1.denominator)
            second = stoploss_ceiling(second*factor2.numerator, factor2.denominator)
        require(exact_second == F(head['product_moment_bound']),
                'finite head law recovers existing full-layout moment')
        mixed = prod(1+r for r in ratios)-1-sum(ratios, F(0))
        require(mixed == F(head['mixed_budget']), 'mixed head charge from cylinder caps')
        charge = stoploss_ceiling(scale*mixed.numerator, mixed.denominator)
        steps = []
        for q in primes:
            if q < q0:
                continue
            cutoff = (2*q+1)//5
            numerator = (5*mean-(2*q+1)*scale
                         + sum((2*q+1-5*d)*weights[d]
                               for d in range(1, cutoff+1)))
            require(numerator >= 0, 'finite-head positive-part upper numerator')
            step = stoploss_ceiling(numerator, 3*(q-2))
            charge += step
            steps.append({'prime': q, 'charge_scaled_upper': step,
                          'cumulative_scaled_upper': charge})
            c = F(5*(q-1), 3*(q-2))
            weights = stoploss_product_update(
                weights, stoploss_atom_bounds(q, c, cap, scale), scale)
            factor1 = 1+c/F(q-1)
            factor2 = 1+c*F(3*q-1, (q-1)**2)
            mean = stoploss_ceiling(mean*factor1.numerator, factor1.denominator)
            second = stoploss_ceiling(second*factor2.numerator, factor2.denominator)
        require(charge < scale, 'positive mass after head and tail deletions')
        gamma = 1+F(second-scale, scale-charge)
        require(gamma < stopping, 'finite-head unrestricted-tail stopping')
        results.append({'head': name, 'head_period_bound': period,
                        'head_primes': [r['prime'] for r in head['coordinates']],
                        'tail_prime_lower_bound': q0,
                        'prime_cutoff': bound, 'last_prime': primes[-1],
                        'global_prime_index': k, 'delta': '2/5', 'scale': scale,
                        'retained_product_states': cap,
                        'mixed_head_charge': str(mixed),
                        'head_product_mean': str(exact_mean),
                        'head_product_second_moment': str(exact_second),
                        'head_product_distribution': {str(d): str(mass)
                            for d, mass in sorted(head_law.items())} if head_law is not None else None,
                        'total_charge_upper': str(F(charge, scale)),
                        'mean_upper': str(F(mean, scale)),
                        'second_moment_upper': str(F(second, scale)),
                        'supported_Gamma_upper': str(gamma),
                        'stopping_lower': str(stopping),
                        'stopping_margin': str(stopping-gamma), 'steps': steps,
                        'final_low_state_digest': hashlib.sha256(
                            json.dumps(weights, separators=(',', ':')).encode()).hexdigest(),
                        'scope': 'Arbitrary head residues with full head period dividing the stated bound, or arbitrary exponents on the listed head primes when that bound is null; all tail primes at least the stated lower bound; no restrictions on original tail support, heights or graph. Ordinary comparison and BBMST continuation are separate inputs.'})
    return results


def adaptive_head_stoploss(head_mass=None, *, finite_head=None,
                           threshold_runs=None, first=19):
    """Certify a fixed varying-delta schedule; greedy selection is not trusted."""
    import hashlib
    from runpy import run_path
    continuation = run_path(str((Path(__file__).resolve().parents[1] / "verify_finite_continuation.py")))
    # Each pair ends an inclusive prime interval on which the threshold is fixed.
    # The schedule is data: validity and the final strict inequality are rechecked.
    if threshold_runs is None:
        threshold_runs = (
            (19, 6), (29, 8), (31, 9), (41, 12), (43, 14),
            (53, 16), (59, 18), (61, 20), (79, 24), (83, 30),
            (103, 32), (113, 36), (157, 48), (163, 60), (199, 64),
            (227, 72), (233, 80), (239, 84), (311, 96), (313, 108),
            (317, 120), (401, 128), (449, 144), (467, 160), (619, 192),
            (631, 216), (641, 224), (653, 240), (811, 256), (919, 288),
            (971, 320), (977, 336), (983, 360), (1291, 384), (1319, 432),
            (1327, 448), (1373, 480), (1697, 512), (1951, 576), (2069, 640),
            (2083, 672), (2089, 720), (2797, 768), (2801, 800), (2861, 864),
            (2903, 896), (3001, 960), (3011, 1008), (3739, 1024), (4363, 1152),
            (4649, 1280), (4657, 1296), (4691, 1344), (4729, 1440), (6427, 1536),
            (6451, 1600), (6661, 1728), (6737, 1792), (7001, 1920), (7013, 2016),
            (8831, 2048), (8837, 2112), (8839, 2160), (8849, 2240), (10477, 2304),
            (10487, 2400), (11239, 2560), (11261, 2592), (11369, 2688), (11471, 2880),
            (11593, 3072),
        )
    last, scale = threshold_runs[-1][0], 10**18
    primes = primes_to(last)
    tail_primes = [q for q in primes if q >= first]
    cap = max(t for _, t in threshold_runs)
    require(all(end in tail_primes for end, _ in threshold_runs),
            'schedule endpoints are actual processed primes')
    choices, previous = [], first-1
    for end, threshold in threshold_runs:
        require(previous < end, 'strictly increasing schedule endpoints')
        choices.extend((q, threshold) for q in tail_primes if previous < q <= end)
        previous = end
    require([q for q, _ in choices] == tail_primes,
            'every prime from the first tail prime through stopping is processed')
    require(all(type(t) is int and 1 <= t <= q-2 for q, t in choices),
            'integer thresholds give nonnegative delta and positive denominator')
    if finite_head is None:
        mixed = F(head_mass['mixed_head_mass_upper'])
        require(mixed == F(82, 135) and 1-mixed == F(head_mass['pure_product_survival_lower']),
                'same-law mixed-head charge from the coupled density certificate')
        coordinates = [(3, None, F(2)), (5, None, F(4, 3)), (7, None, F(6, 5))]
    else:
        coordinates = [(r['prime'], r['height'], 1/F(r['pure_survivor_density_lower']))
                       for r in finite_head['coordinates']]
        ratios = [c-1 for _, _, c in coordinates]
        mixed = prod(1+r for r in ratios)-1-sum(ratios, F(0))
        require(mixed == F(finite_head['mixed_budget']),
                'finite mixed-head charge from the full-family cylinder caps')
    weights = [0]*(cap+1)
    weights[1] = scale
    mean = second = scale

    def append_prime(p, c, height=None):
        nonlocal weights, mean, second
        require(0 < c <= p, 'valid auxiliary height tails')
        if height is None:
            atoms = stoploss_atom_bounds(p, c, cap, scale)
            factor1, factor2 = 1+c/F(p-1), 1+c*F(3*p-1, (p-1)**2)
        else:
            require(type(height) is int and height >= 1, 'positive finite head height')
            exact_atoms = [F(0)]*(height+2)
            exact_atoms[1] = 1-c/p
            for f in range(2, height+1):
                exact_atoms[f] = c*F(p-1, p**f)
            # The terminal atom is the entire tail at the final allowed height.
            exact_atoms[height+1] = c/F(p**height)
            require(sum(exact_atoms) == 1 and min(exact_atoms) >= 0,
                    'finite auxiliary head law including its terminal atom')
            atoms = [stoploss_ceiling(scale*a.numerator, a.denominator)
                     for a in exact_atoms]
            factor1 = sum(f*a for f, a in enumerate(exact_atoms))
            factor2 = sum(f*f*a for f, a in enumerate(exact_atoms))
        weights = stoploss_product_update(
            weights, atoms, scale)
        mean = stoploss_ceiling(mean*factor1.numerator, factor1.denominator)
        second = stoploss_ceiling(second*factor2.numerator, factor2.denominator)
        return factor1, factor2

    head_mean = head_second = F(1)
    for p, height, c in coordinates:
        factor1, factor2 = append_prime(p, c, height)
        head_mean *= factor1
        head_second *= factor2
    require(head_second == F(finite_head['product_moment_bound'] if finite_head else '325/18'),
            'adaptive head law recovers the full-layout moment')
    charge = stoploss_ceiling(scale*mixed.numerator, mixed.denominator)
    steps = []
    for q, threshold in choices:
        denominator = q-1-threshold
        delta = F(threshold-1, q-2)
        c = F(q-1, denominator)
        require(0 <= delta < 1 and c == F(q-1, q-2)/(1-delta),
                'threshold and normalized-kernel parameters agree')
        # Exact identity V(t)=E D-t+sum_{d<t}(t-d)Pr(D=d). All stored
        # probabilities and the first moment have nonnegative coefficients.
        numerator = (mean-threshold*scale
                     + sum((threshold-d)*weights[d] for d in range(1, threshold)))
        require(numerator >= 0, 'adaptive positive-part upper numerator')
        step = stoploss_ceiling(numerator, denominator)
        charge += step
        require(charge < scale, 'positive actual survival throughout the fixed schedule')
        append_prime(q, c)
        steps.append({'prime': q, 'threshold': threshold, 's': denominator,
                      'delta': str(delta), 'charge_scaled_upper': step,
                      'cumulative_scaled_upper': charge})
    gamma = 1+F(second-scale, scale-charge)
    # primes_to includes 2 and every omitted small prime: this is the global
    # prime index required in BBMST Section 6, not the number of tail steps.
    k = len(primes)
    require(k >= 10, 'BBMST stopping index domain')
    stopping = continuation['stopping_threshold'](k)
    require(gamma < stopping, 'adaptive unrestricted-tail BBMST stopping')
    period = finite_head['period_bound'] if finite_head else None
    result = {'head': f'head_divides_{period}' if period else 'arbitrary_357_head',
            'head_period_bound': period,
            'head_primes': [3, 5, 7], 'tail_prime_lower_bound': first,
            'omitted_prime_factors': [p for p in primes if p < first and p not in (3, 5, 7)],
            'last_prime': last, 'global_prime_index': k, 'scale': scale,
            'retained_product_states': cap, 'mixed_head_charge': str(mixed),
            'head_product_mean': str(head_mean), 'head_product_second_moment': str(head_second),
            'threshold_runs': [{'last_prime': q, 'threshold': t} for q, t in threshold_runs],
            'total_charge_upper': str(F(charge, scale)),
            'survival_lower': str(F(scale-charge, scale)),
            'mean_upper': str(F(mean, scale)),
            'second_moment_upper': str(F(second, scale)),
            'supported_Gamma_upper': str(gamma), 'stopping_lower': str(stopping),
            'stopping_margin': str(stopping-gamma),
            'stopping_bound_method': 'Global prime index and verify_finite_continuation.stopping_threshold: exact binary range reduction, 24 positive atanh terms, downward rounding on a 10^-18 grid, positive logarithmic bracket before squaring.',
            'steps': steps,
            'final_low_state_digest': hashlib.sha256(
                json.dumps(weights, separators=(',', ':')).encode()).hexdigest(),
            'scope': 'Distinct odd original moduli with arbitrary {3,5,7} exponents and every other prime at least 19; no tail support, exponent, graph or prime-count restriction. The full-family head heights, comparison, coupled head density and BBMST restart are separate ordinary mathematical inputs. No greedy optimality claim is needed.'}
    if finite_head is not None:
        result['head_heights'] = [[p, height] for p, height, _ in coordinates]
        result['scope'] = ('Distinct odd original moduli with the full-family {3,5,7} head period '
                           f'dividing {period} and every other prime at least {first}; '
                           'the head-height bound includes moduli ending at future primes. '
                           'No tail support, exponent, graph or prime-count restriction. '
                           'The comparison and BBMST restart are separate ordinary mathematical '
                           'inputs. No greedy optimality claim is needed.')
    return result


def unrestricted_star_stoploss():
    import hashlib
    bound = 2048
    scale = 10**18
    delta = F(2, 5)
    cap = (2*bound+1)//5
    primes = primes_to(bound)
    weights = [0]*(cap+1)
    weights[1] = scale
    mean = second = scale
    charge = 0
    rows = []
    for p in primes[1:]:
        if p <= 73:
            c = F(2) if p == 3 else F(p-1, p-3)
        else:
            # D precedes the q=p step. T=1+(p-2)delta=(2p+1)/5.
            # E(D-T)+ = E D - T + E(T-D)+.
            # Stored probabilities and E D are upper bounds, and the
            # coefficients in the final expectation are nonnegative.
            cutoff = (2*p+1)//5
            numerator = (5*mean-(2*p+1)*scale
                         + sum((2*p+1-5*d)*weights[d]
                               for d in range(1, cutoff+1)))
            require(numerator >= 0, 'nonnegative upper stop-loss numerator')
            step = stoploss_ceiling(numerator, 3*(p-2))
            charge += step
            rows.append({'prime': p, 'charge_scaled_upper': step,
                         'cumulative_scaled_upper': charge})
            c = F(p-1, p-2)/(1-delta)
        atoms = stoploss_atom_bounds(p, c, cap, scale)
        weights = stoploss_product_update(weights, atoms, scale)
        factor1 = 1+c/F(p-1)
        factor2 = 1+c*F(3*p-1, (p-1)**2)
        mean = stoploss_ceiling(mean*factor1.numerator, factor1.denominator)
        second = stoploss_ceiling(second*factor2.numerator, factor2.denominator)
    require(charge < scale, 'positive actual survivor mass')
    gamma = 1+F(second-scale, scale-charge)
    k = len(primes)
    # log2 >= 2(1/3+(1/3)^3/3)=56/81. Since k>=256,
    # log k>=448/81>4, log log k>=log4>=112/81.
    # Hence log k+log log k-3 >=317/81>0.
    require(k >= 256 and F(448,81)>4, 'rational logarithm premise')
    stopping = k*F(317,81)**2
    require(gamma < stopping, 'strict BBMST stopping certificate')
    result = {'prime_cutoff': bound, 'last_prime': primes[-1], 'global_prime_index': k,
              'delta': str(delta), 'scale': scale, 'retained_product_states': cap,
              'charge_upper': str(F(charge, scale)),
              'mean_upper': str(F(mean, scale)), 'second_moment_upper': str(F(second, scale)),
              'supported_Gamma_upper': str(gamma), 'stopping_lower': str(stopping),
              'stopping_margin': str(stopping-gamma), 'steps': rows, 'scope': 'Finite directed certificate for the unrestricted-tail complete-star theorem; ordinary convex comparison and BBMST continuation are separate mathematical inputs.',
              'final_low_state_digest': hashlib.sha256(
                  json.dumps(weights,separators=(',',':')).encode()).hexdigest()}
    return result
