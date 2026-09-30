#!/usr/bin/env python3
"""Exact diagnostics for source-scale Robin estimates on n=5040*F_j.

Published Axler bounds and classical Fibonacci rank/valuation theorems are
inputs. Rational diagnostics do not prove those inputs or the universal
rank-bucket argument. No huge F_j is constructed by the adaptive certificate.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import factorial, prod
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from index_stopping import D, fib_mod_doubling, fib_mod_matrix, valuation
from kernel_tail import floor_to_scale, is_prime, log_interval

A0 = Q(94243, 10**7)
E_LO, E_HI = Q(65, 24), Q(49, 18)
P9 = (2, 3, 5, 7, 11, 13, 17, 19, 23)
METHOD_INDEX = D * prod(P9)**10


def rat(x):
    x = Q(x)
    return [x.numerator, x.denominator]


def log_upper(x):
    return -floor_to_scale(-log_interval(Q(x))[1])


def certificate(j, prime_limit=29, cap=40):
    """Sufficient condition only; a spent observation budget stays unresolved."""
    if j <= 0 or j % D:
        raise ValueError('this source-scale certificate requires a positive multiple of D')
    if prime_limit < 2 or cap < 0:
        raise ValueError('prime limit >= 2 and valuation cap >= 0 required')
    h = floor_to_scale(log_interval(Q(j, 4))[0])
    assert h > 54 and Q(j, 4) > 32 * 10**12
    eta, absent_factor, absent_product = Q(1), Q(1), 1
    observations = []
    bound = 1 + A0 / h**3
    for p in range(2, prime_limit + 1):
        if not is_prime(p):
            continue
        modulus = p**(cap + 1)
        f = fib_mod_doubling(j, modulus)
        assert f == fib_mod_matrix(j, modulus)
        residue = 5040 * f % modulus
        exponent = valuation(residue, p) if residue else None
        if exponent == 0:
            absent_product *= p
            absent_factor *= Q(p - 1, p)
        elif exponent is not None:
            eta *= 1 - Q(1, p**(exponent + 1))
        observations.append({'p': p, 'modulus': modulus, 'residue': residue,
                             'exact_valuation': exponent,
                             'valuation_lower_if_capped': cap + 1 if residue == 0 else None})
        # Padding uses the totient identity, not a fictitious sigma factor.
        distortion = 1 + 4 * log_upper(absent_product) / (j * h)
        bound = eta * absent_factor * distortion * (1 + A0 / h**3)
        if bound <= 1:
            break
    return {'index': j, 'loglog_n_lower': rat(h), 'prime_limit': prime_limit,
            'valuation_cap': cap, 'observations': observations,
            'eta_upper': rat(eta), 'absent_product': absent_product,
            'relative_bound_upper': rat(bound),
            'outcome': 'CERTIFIED_USING_PUBLISHED_INPUTS' if bound <= 1 else 'UNRESOLVED'}


def constants():
    # e=sum 1/k!: the tail from k=5 is at most (1/120)/(1-1/6).
    assert sum((Q(1, factorial(k)) for k in range(5)), Q(0)) == E_LO
    assert E_LO + Q(1, 100) < E_HI
    comparisons = {
        'D_gt_exp55': D > E_HI**55,
        'tauD_gt_exp10': 57024 > E_HI**10,
        'log4_lt_7_over_5': E_LO**7 > 4**5,
        'log513_lt_7': E_LO**7 > 513,
        'log10_lt_5_over_2': E_LO**5 > 100,
        'log_primorial_lt_32e12': 999999476056 * 32 < 32 * 10**12,
        'log_pK_lt_32': E_LO**32 > 29996208012611,
        'loglog_primorial_lt_31_5': E_LO**63 > (32 * 10**12)**2,
        'loglog_primorial_gt_1': 999999476056 * Q(1, 2) > E_HI,
        'divisor_constant_cube_lt_64': Q(1536, 35) < 64,
        'rank_tail_lt_one_over_40': Q(63, 2560) < Q(1, 40),
        'source_above_primorial': Q(D, 4) > 32 * 10**12,
    }
    assert all(comparisons.values())
    local_maxima = {2: (3, Q(8)), 3: (2, Q(3)),
                    5: (1, Q(8, 5)), 7: (1, Q(8, 7))}
    for p, (argmax, cube) in local_maxima.items():
        assert Q((argmax + 1)**3, p**argmax) == cube
        # Finite diagnostic; monotone adjacent ratios give the paper proof.
        assert all(Q((a + 1)**3, p**a) <= cube for a in range(81))
    final_slack = Q(55) - Q(7, 5) - Q(40, 39) * (Q(3, 4)*55 + Q(254, 25))
    assert final_slack == Q(34, 39)
    return {'comparisons': comparisons, 'e_bracket': [rat(E_LO), rat(E_HI)],
            'local_divisor_ratio_cubes': {p: rat(c) for p, (_, c) in local_maxima.items()},
            'rank_tail_upper': rat(Q(63, 2560)),
            'final_affine_slack_at_v55': rat(final_slack)}


def bootstrap():
    rows = []
    for multiplier, h, expected, next_multiplier in (
            (1, 54, (23, 15, 10, 8, 6), 1260),
            (1260, 61, (24, 15, 10, 8, 7), 27720),
            (27720, 64, (24, 15, 10, 8, 7), 27720)):
        assert E_HI**h < Q(multiplier * D, 4)
        threshold = 1 + Q(h**3, 1) / A0
        first_fail = []
        for p in P9[:5]:
            a = 0
            while p**(a + 1) <= threshold:
                a += 1
            first_fail.append(a)
        assert tuple(first_fail) == expected
        calculated = prod(p**(a-b) for p, a, b in zip(P9, expected, (21, 13, 9, 7, 6)))
        assert calculated == next_multiplier
        rows.append({'known_index_multiplier': multiplier, 'L_lower': h,
                     'necessary_n_valuations': first_fail,
                     'next_index_multiplier': next_multiplier})
    return rows


def method_obstruction():
    expected = (31, 23, 19, 17, 16, 11, 11, 11, 11)
    eta = prod(1 - Q(1, p**(a + 1)) for p, a in zip(P9, expected))
    assert 1 - eta < Q(1, 4 * 10**9)
    assert A0 / (258**3 + A0) > Q(1, 2 * 10**9)
    assert D < E_LO**57 and prod(P9) < E_LO**20
    for p, a in zip(P9 + (29,), expected + (1,)):
        modulus = p**(a + 1)
        f = fib_mod_doubling(METHOD_INDEX, modulus)
        assert f == fib_mod_matrix(METHOD_INDEX, modulus)
        residue = 5040 * f % modulus
        assert residue and valuation(residue, p) == a
    narrow = certificate(METHOD_INDEX, 23)
    adaptive = certificate(METHOD_INDEX, 29)
    exhausted = certificate(METHOD_INDEX, 29, 0)
    absent = certificate(METHOD_INDEX, 61, 0)
    assert narrow['outcome'] == exhausted['outcome'] == 'UNRESOLVED'
    assert adaptive['outcome'] == 'CERTIFIED_USING_PUBLISHED_INPUTS'
    assert adaptive['observations'][-1]['p'] == 29
    assert absent['outcome'] == 'CERTIFIED_USING_PUBLISHED_INPUTS'
    assert absent['absent_product'] == 59
    return {'index': METHOD_INDEX, 'n_valuations_first_nine': expected,
            'nine_factor_deficit': rat(1-eta), 'true_L_upper': 258,
            'prime29_exact_valuation': 1, 'fixed_nine': narrow,
            'adaptive_tenth': adaptive, 'exhausted_cap': exhausted,
            'absent_prime_padding': absent}


def finite_rank_buckets():
    """Factor actual small F_j; independent of the large-index certificate."""
    a, b, count = 0, 1, 0
    for j in range(1, 49):
        a, b = b, a+b
        rest, p, factors = a, 2, []
        while p*p <= rest:
            if rest % p == 0:
                factors.append(p)
                while rest % p == 0:
                    rest //= p
            p = 3 if p == 2 else p+2
        if rest > 1:
            factors.append(rest)
        groups = {}
        for p in factors:
            x, y = 0, 1
            for d in range(1, j+1):
                x, y = y, (x+y) % p
                if x % p == 0:
                    break
            assert j % d == 0
            if p != 5:
                assert (p-1) % d == 0 or (p+1) % d == 0
            groups.setdefault(d, []).append(p)
        for d, ps in groups.items():
            if d <= 5:
                continue
            assert len(ps) < d
            euler = prod(Q(p, p-1) for p in ps)
            harmonic = sum((Q(1, k) for k in range(1, d+1)), Q(0))
            assert log_interval(euler)[1] <= 6 * harmonic / d
            count += 1
    return {'indices': [1, 48], 'high_rank_buckets_checked': count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--index', action='append', type=int, default=[])
    parser.add_argument('--prime-limit', type=int, default=29)
    parser.add_argument('--valuation-cap', type=int, default=40)
    args = parser.parse_args()
    if not __debug__:
        parser.error('optimized Python disables verification; omit -O/-OO')
    if args.prime_limit < 2 or args.valuation_cap < 0 or any(j <= 0 or j % D for j in args.index):
        parser.error('require prime limit >= 2, cap >= 0, and indices positive multiples of D')
    report = {'schema': 'fib-robin-source-scale-v1', 'D': D,
              'constants': constants(), 'bootstrap': bootstrap(),
              'method_obstruction': method_obstruction(),
              'finite_rank_buckets': finite_rank_buckets(),
              'source_examples': [certificate(j) for j in (D, 1260*D, 27720*D)],
              'requested': [certificate(j, args.prime_limit, args.valuation_cap) for j in args.index],
              'sources_sha256': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                 for name in ('source_scale.py', 'index_stopping.py', 'kernel_tail.py')},
              'scope': 'Finite exact diagnostics and conditional certificates; published analytic inputs are not reverified. The universal rank-bucket argument is paper mathematics, not Lean; no RH or originality claim.'}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': 'EXACT_DIAGNOSTICS_PASSED',
                      'rank_buckets': report['finite_rank_buckets'],
                      'examples': [x['outcome'] for x in report['source_examples']]}))


if __name__ == '__main__':
    main()
