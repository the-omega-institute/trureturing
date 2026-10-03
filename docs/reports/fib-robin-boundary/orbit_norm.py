#!/usr/bin/env python3
"""Exact diagnostics for golden-norm exclusions and two-term rank carriers.

Finite checks do not prove the paper's universal statements or the published
Axler estimates. No Robin truth value is inferred from an exhausted test.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import gcd
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from kernel_tail import is_prime, log_interval

A0 = Q(94243, 10**7)
E_LO, E_HI = Q(65, 24), Q(49, 18)


def norm(a, b):
    return a*a + a*b - b*b


def factors(n):
    n = abs(n)
    if not n:
        raise ValueError('zero has no finite prime factorization')
    answer, p = {}, 2
    while p*p <= n:
        while n % p == 0:
            answer[p] = answer.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        answer[n] = 1
    return answer


def divisors(n):
    ds = {1}
    for p, a in factors(n).items():
        ds = {d*p**k for d in ds for k in range(a+1)}
    return ds


def fibs(limit):
    values = [0, 1]
    for _ in range(1, limit):
        values.append(values[-1]+values[-2])
    return values


def prime_rank(p):
    x, y = 0, 1
    for d in range(1, p+2):
        x, y = y, (x+y) % p
        if x % p == 0:
            return d
    raise ValueError('prime rank not found within the classical bound')


def norm_orbits():
    fs = fibs(82)
    invariant_checks = exclusion_checks = 0
    for a in range(33):
        for b in range(33):
            g = gcd(a, b)
            if not g:
                continue
            primitive = (a//g, b//g)
            delta = norm(*primitive)
            assert delta
            ps = factors(delta)
            core_valuations = factors(5040*g)
            u, v = b, a+b
            for j in range(81):
                assert u == a*fs[j] + b*fs[j+1]
                assert v*v-u*v-u*u == (-1)**j*norm(a, b)
                assert gcd(u, v) == g
                invariant_checks += 1
                for p in ps:
                    assert (u//g) % p != 0
                    # Independently divide the actual integer response.
                    value, exponent = 5040*u, 0
                    assert value > 0
                    while value % p == 0:
                        value //= p
                        exponent += 1
                    assert exponent == core_valuations.get(p, 0)
                    exclusion_checks += 1
                u, v = v, u+v
    a, b = 4, 5
    advanced = (a+2*b+1, 2*a+3*b)  # S x plus branch [2].
    assert norm(a, b) == 11 and norm(*advanced) == 41
    assert 2*a+3*b == fs[3]+fs[8] == 23
    assert 2*advanced[0]+3*advanced[1] == fs[3]+fs[6]+fs[11] == 99
    assert 99 % 11 == 0
    return {'coefficient_box': [0, 32], 'indices': [0, 80],
            'invariant_and_gcd_checks': invariant_checks,
            'primitive_norm_prime_exclusions': exclusion_checks,
            'legal_affine_branch_obstruction': {
                'seed': [a, b], 'seed_quantity': 23, 'seed_norm': 11,
                'branch': '[2]', 'new_composition': list(advanced),
                'new_quantity': 99, 'new_norm': 41, 'regained_prime': 11}}


def fibers():
    checks, roots = 0, 0
    primes = [p for p in range(2, 98) if is_prime(p)]
    for n in range(1, 129):
        b = n % 2
        a = (n-3*b)//2
        c = 4*a+7*b
        assert c*c+4*norm(a, b) == 5*n*n
        for p in primes:
            primitive_roots = all_roots = 0
            for t in range(p):
                at, bt = a+3*t, b-2*t
                value = norm(at, bt)
                assert 2*at+3*bt == n
                assert value == norm(a, b)+c*t-t*t
                is_root = value % p == 0
                primitive = at % p != 0 or bt % p != 0
                all_roots += is_root
                primitive_roots += is_root and primitive
                if p != 2:
                    assert is_root == (((2*t-c)**2-5*n*n) % p == 0)
                else:
                    assert is_root == (not primitive)
                checks += 1
            if p == 2:
                assert primitive_roots == 0
            elif n % p == 0:
                assert all_roots == 1 and primitive_roots == 0
            else:
                expected = 1 if p == 5 else (2 if pow(5, (p-1)//2, p) == 1 else 0)
                assert all_roots == primitive_roots == expected
            roots += primitive_roots
    return {'quantities': [1, 128], 'primes_through': 97,
            'fiber_residue_checks': checks, 'local_primitive_roots': roots,
            'same_quantity_example': {'n': 7, 'compositions': [[2, 1], [-1, 3]],
                                      'norms': [norm(2, 1), norm(-1, 3)]}}


def two_terms():
    fs = fibs(302)
    lucas = [2] + [fs[k-1]+fs[k+1] for k in range(1, 151)]
    identities = carrier_checks = shared_odd = 0
    rank_cache = {}
    for a in range(4, 151):
        for b in range(2, a-1):
            if (a-b) % 2:
                continue
            m, k = (a+b)//2, (a-b)//2
            r, s = (m, k) if k % 2 == 0 else (k, m)
            assert fs[a]+fs[b] == fs[r]*lucas[s]
            identities += 1
            if a > 48:
                continue
            odd, two_power = s, 2
            while odd % 2 == 0:
                odd //= 2
                two_power *= 2
            carrier = divisors(r) | {two_power*e for e in divisors(odd)} | {3}
            assert len(carrier) <= len(divisors(r))+len(divisors(odd))+1
            assert len(carrier)**3 < 8**3*a
            actual_factors = factors(fs[a]+fs[b])
            for p in actual_factors:
                if p not in rank_cache:
                    rank_cache[p] = prime_rank(p)
                assert rank_cache[p] in carrier
                carrier_checks += 1
            common = gcd(fs[r], lucas[s])
            shared_odd += any(p != 2 for p in factors(common))
    assert fs[12]+fs[4] == 147 == fs[8]*lucas[4]
    assert gcd(fs[8], lucas[4]) == 7
    assert fs[8]+fs[3] == 23 and prime_rank(23) == 24
    assert all(d % 24 != 0 for d in (8, 3, 11, 5, 16, 6, 22, 10))
    # The extra rank 3 is essential when 2 divides only the Lucas factor.
    raw_carrier = divisors(20) | {8*e for e in divisors(3)}
    assert fs[32]+fs[8] == fs[20]*lucas[12]
    assert all((fs[32]+fs[8]) % p == 0 for p in (2, 3, 5, 7))
    assert 3 not in raw_carrier and (fs[32]+fs[8]) % 2 == 0
    slack = Q(60)-Q(7, 5)-Q(40, 39)*(Q(3, 4)*60+Q(47, 4))
    assert slack == Q(77, 195)
    assert log_interval(Q(8))[1] < Q(21, 10)
    assert 7+Q(9, 4)*Q(21, 10)+A0 < Q(47, 4)
    assert 4 < Q(7, 4)**3 and E_HI**10 < 57024
    assert E_LO**60 > Q(57024, 8)**3
    return {'identity_high_index_range': [4, 150], 'identities': identities,
            'domain': '2 <= b <= a-2 and a == b modulo 2',
            'complete_factorization_high_index_range': [4, 48],
            'actual_prime_carrier_checks': carrier_checks,
            'pairs_with_shared_odd_prime': shared_odd,
            'shared_prime_example': {'indices': [12, 4], 'sum': 147, 'shared_prime': 7},
            'opposite_parity_obstruction': {'indices': [8, 3], 'sum': 23, 'rank': 24},
            'essential_rank_two_exception': {'indices': [32, 8],
                                             'factor_indices': [20, 12],
                                             'missing_rank_in_raw_carrier': 3},
            'analytic_log_high_index_threshold': 60,
            'relative_linear_slack_at_threshold': [slack.numerator, slack.denominator]}


def seed_certificates():
    rows = []
    for a, b in ((1, 4), (4, 5), (9, 13), (22, 34), (2, 1), (11**6, 4*11**6)):
        g = gcd(a, b)
        delta = norm(a//g, b//g)
        p = min(factors(delta))
        exponent = factors(5040*g).get(p, 0)
        h = 32
        if exponent:
            while h**3 < A0*(p**(exponent+1)-1):
                h += 1
            criterion = 'retained actual prime factor'
        else:
            logp_hi = log_interval(Q(p))[1]
            while h**3 < 2*A0*(p-1) or E_LO**h < 2*(p-1)*logp_hi:
                h += 1
            criterion = 'absent prime with totient padding'
        rows.append({'coefficients': [a, b], 'gcd': g, 'primitive_norm': delta,
                     'excluded_prime': p, 'constant_n_valuation': exponent,
                     'sufficient_L_lower': h, 'sufficient_index': f'j > 4*exp({h})',
                     'criterion': criterion})
    assert E_LO**32 > 32*10**12
    assert E_LO**55 > Q(57024, 4)**3
    return rows


def quarter_tail_bridge():
    peaks = ((2, 5), (3, 3), (5, 2), (7, 1), (11, 1), (13, 1))
    constant_fourth = Q(1)
    for p, exponent in peaks:
        assert Q(exponent+1, exponent)**4 > p
        assert Q(exponent+2, exponent+1)**4 < p
        constant_fourth *= Q((exponent+1)**4, p**exponent)
    assert constant_fourth == Q(576**4, 21621600) < 9**4
    assert 57024**4 < 19**4*E_LO**38
    assert 19 < E_LO**3
    assert Q(344, 25) < 14
    slack = 38-Q(7, 5)-Q(40, 39)*(Q(9, 16)*38+14)
    assert slack == Q(62, 195)
    core = 2**14*5**8*11**5*min(3**10, 7**5)
    assert core == 17323418604800000000
    assert core > 3**38 > E_HI**38
    multiplier_count = 0
    for c in divisors(5040):
        exponents = factors(c)
        assert all(exponents.get(p, 0) <= cap
                   for p, cap in ((2, 4), (3, 2), (5, 1), (7, 1), (11, 0)))
        multiplier_count += 1
    assert multiplier_count == 60
    assert E_HI**2 < 8  # e^2 < 8 gives log(2) > 2/3.

    fs = fibs(302)
    def valuation(value, p):
        assert value > 0
        exponent = 0
        while value % p == 0:
            value //= p
            exponent += 1
        return exponent

    for s in range(1, 151):
        ls = fs[s-1]+fs[s+1]
        assert fs[2*s] == fs[s]*ls
        expected_two = 0 if s % 3 else (2 if s % 2 else 1)
        assert valuation(ls, 2) == expected_two
        assert ls % 5 != 0
        assert (ls % 11 == 0) == (s % 2 == 1 and s % 5 == 0)
        assert (ls % 3 == 0) == (s % 4 == 2)
        assert (ls % 7 == 0) == (s % 8 == 4)
        assert not (ls % 3 == 0 and ls % 7 == 0)
    return {'prime_peak_exponents': [list(pair) for pair in peaks],
            'divisor_constant_fourth_power': [constant_fourth.numerator,
                                              constant_fourth.denominator],
            'carrier_coefficient': 19, 'analytic_log_high_index_threshold': 38,
            'relative_linear_slack_at_threshold': [slack.numerator, slack.denominator],
            'same_source_core_index_lower_bound': core,
            'multiplier_divisors_of': 5040, 'multiplier_count': multiplier_count,
            'robin_domain_lower_exclusive': 5040,
            'lucas_local_formula_indices': [1, 150],
            'lucas_local_formula_checks': 150,
            'scope': 'Rational constants and finite local identities; the all-index transfer is the paper proof in section 169.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error('optimized Python disables verification; omit -O/-OO')
    report = {'schema': 'fib-orbit-norm-v1', 'norm_orbits': norm_orbits(),
              'quantity_fibers': fibers(), 'two_term_carriers': two_terms(),
              'effective_seed_examples': seed_certificates(),
              'quarter_tail_bridge': quarter_tail_bridge(),
              'sources_sha256': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                                 for name in ('orbit_norm.py', 'kernel_tail.py')},
              'scope': 'Exact finite diagnostics only. Universal orbit, carrier and Robin arguments are paper mathematics using published inputs; no new Lean or RH proof and no originality claim.'}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ('norm_orbits', 'quantity_fibers',
                                           'two_term_carriers', 'quarter_tail_bridge')}))


if __name__ == '__main__':
    main()
