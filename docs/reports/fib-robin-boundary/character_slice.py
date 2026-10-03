#!/usr/bin/env python3
"""Finite exact diagnostics for quadratic characters of opposite-parity FIB sums.

Python 3.9+, standard library only, runnable from any working directory.
The sampled identities and finite Euler products do not prove an infinite
Euler-product bound, a uniform Robin estimate, RH, or a Lean theorem.
"""

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from math import gcd, isqrt, prod
from pathlib import Path


EXTRA_CHARACTER_D = (-75, -45, -20, -12, -4, 8, 12, 20, 45, 75)
MULTIPLIERS = tuple(range(-8, 9))


def fibonacci_table(limit):
    values = [0, 1]
    for _ in range(2, limit+1):
        values.append(values[-1]+values[-2])
    return values


def lucas(values, n):
    return 2 if n == 0 else values[n-1]+values[n+1]


def primes_through(limit):
    sieve = bytearray(b'\x01')*(limit+1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b'\x00'*((limit-p*p)//p+1)
    return tuple(n for n in range(2, limit+1) if sieve[n])


@lru_cache(maxsize=None)
def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


@lru_cache(maxsize=None)
def factorization(n):
    """Complete trial division, used only in the explicitly bounded small window."""
    assert n >= 1
    original, result, p = n, [], 2
    while p*p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            result.append((p, exponent))
        p = 3 if p == 2 else p+2
    if n > 1:
        result.append((n, 1))
    assert prod(p**e for p, e in result) == original
    assert all(trial_prime(p) for p, _ in result)
    return tuple(result)


def legendre(a, p):
    """Euler criterion; the caller supplies an odd prime."""
    assert p >= 3 and p % 2
    residue = pow(a % p, (p-1)//2, p)
    assert residue in (0, 1, p-1)
    return -1 if residue == p-1 else residue


def jacobi(a, n):
    """Binary reciprocity algorithm, independent of modular Euler powering."""
    assert n > 0 and n % 2
    a, result = a % n, 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def positive_square(n):
    return n >= 0 and isqrt(n)**2 == n


@lru_cache(maxsize=None)
def character_parameters(d_value):
    if d_value == 0 or positive_square(d_value):
        raise ValueError('a nonzero nonsquare D is required for this character check')
    squarefree, root = (-1 if d_value < 0 else 1), 1
    for p, exponent in factorization(abs(d_value)):
        squarefree *= p**(exponent % 2)
        root *= p**(exponent//2)
    assert d_value == squarefree*root*root and squarefree != 1
    assert all(e == 1 for _, e in factorization(abs(squarefree)))
    delta = squarefree if squarefree % 4 == 1 else 4*squarefree
    modulus = 4*abs(d_value)
    assert delta != 1 and modulus % abs(delta) == 0
    return squarefree, root, delta, modulus


def character(n, parameters):
    """Induced real character modulo Q=4|D|, including its extra zero primes.

    Every unit modulo Q is odd. Thus the fundamental Kronecker symbol is
    obtained from the ordinary Jacobi symbol and the sign of its denominator.
    """
    _, _, delta, modulus = parameters
    if gcd(n, modulus) != 1:
        return 0
    sign = -1 if n < 0 and delta < 0 else 1
    return sign*jacobi(delta, abs(n))


def source_checks(args, values, odd_primes):
    pairs = bounded_checks = common = at_five = induced_checks = 0
    ramified_screen = square_pairs = full_pairs = full_checks = 0
    companion_ramified_screen = 0
    full_ramified = beyond_screen = 0
    gcd_counts, companion_gcd_counts, square_gaps = Counter(), Counter(), set()
    distinct_factored = set()
    maximum_prime = {'p': 0}
    witnesses = {}
    for a in range(5, args.max_a+1):
        for b in range(2, a-2):
            k = a-b
            if k % 2 == 0:
                continue
            fa, fb = values[a], values[b]
            v = fa+fb
            d_value = (-1)**b*lucas(values, k)
            companion = -lucas(values, a+b)
            l_sum = lucas(values, a)+lucas(values, b)
            l_difference = lucas(values, a)-lucas(values, b)
            assert l_sum*l_sum-5*v*v == 4*d_value
            assert l_difference*l_difference-5*v*v == 4*companion
            assert companion < 0
            assert lucas(values, a+b)*lucas(values, k) == (
                5*v*(fa-fb)+4*(-1)**a)
            common_gcd = gcd(v, abs(d_value))
            assert 4 % common_gcd == 0
            gcd_counts[str(common_gcd)] += 1
            companion_gcd = gcd(v, abs(companion))
            assert 4 % companion_gcd == 0
            companion_gcd_counts[str(companion_gcd)] += 1
            square = positive_square(d_value)
            if square:
                square_pairs += 1
                square_gaps.add(k)
            if k == 3 and b % 2 == 0:
                assert d_value == 4 and v == 2*values[b+2]
                witnesses.setdefault('positive_square_exception',
                                     {'a': a, 'b': b, 'D': d_value, 'V': v})
            parameters = None
            if k <= args.character_gap_max and not square:
                parameters = character_parameters(d_value)

            def check_actual_prime(p):
                assert p % 2 and v % p == 0 and d_value % p != 0
                square_root = l_sum*pow(2, -1, p) % p
                assert square_root != 0 and square_root**2 % p == d_value % p
                assert legendre(d_value, p) == 1
                assert companion % p != 0
                companion_root = l_difference*pow(2, -1, p) % p
                assert companion_root != 0 and companion_root**2 % p == companion % p
                assert legendre(companion, p) == 1
                if parameters is not None:
                    assert character(p, parameters) == 1

            for p in odd_primes:
                if d_value % p == 0:
                    assert v % p != 0
                    ramified_screen += 1
                if companion % p == 0:
                    assert v % p != 0
                    companion_ramified_screen += 1
                if v % p != 0:
                    continue
                check_actual_prime(p)
                bounded_checks += 1
                induced_checks += parameters is not None
                if fa % p == 0 and fb % p == 0:
                    common += 1
                    witnesses.setdefault('common_fibonacci_support',
                                         {'a': a, 'b': b, 'p': p, 'D': d_value})
                if p == 5:
                    at_five += 1
                    witnesses.setdefault('prime_five',
                                         {'a': a, 'b': b, 'D': d_value, 'V': v})
            if a <= args.factor_max_a:
                v_factors = factorization(v)
                distinct_factored.add(v)
                assert prod(p**e for p, e in v_factors) == v
                for p, _ in v_factors:
                    if p == 2:
                        continue
                    check_actual_prime(p)
                    full_checks += 1
                    beyond_screen += p > args.prime_limit
                    if p > maximum_prime['p']:
                        maximum_prime = {'a': a, 'b': b, 'V': v,
                                         'D': d_value, 'p': p,
                                         'complete_V_factorization': v_factors}
                for p, _ in factorization(abs(d_value)):
                    if p != 2:
                        assert v % p != 0
                        full_ramified += 1
                full_pairs += 1
            pairs += 1
    return {
        'a_range': [5, args.max_a], 'b_minimum': 2, 'odd_gap_minimum': 3,
        'joint_integer_identities': pairs, 'gcd_V_D_counts': dict(gcd_counts),
        'bounded_prime_screen': {
            'odd_prime_upper_bound': args.prime_limit,
            'actual_prime_divisor_checks': bounded_checks,
            'common_fibonacci_support_checks': common, 'prime_five_checks': at_five,
            'ramified_prime_nondivisibility_checks': ramified_screen,
            'induced_character_checks_for_gap_at_most': args.character_gap_max,
            'induced_character_actual_prime_checks': induced_checks},
        'complete_factorization_window': {
            'a_range': [5, args.factor_max_a], 'pairs': full_pairs,
            'distinct_V_values': len(distinct_factored),
            'all_actual_odd_prime_divisor_checks': full_checks,
            'actual_prime_checks_beyond_bounded_screen': beyond_screen,
            'all_odd_ramified_prime_exclusion_checks': full_ramified,
            'largest_actual_prime_witness': maximum_prime},
        'positive_square_D_pairs': square_pairs,
        'positive_square_D_gaps_observed': sorted(square_gaps),
        'witnesses': witnesses,
        'companion_sum_discriminant': {
            'definition': 'E = -L_(a+b)',
            'square_identities': pairs,
            'gcd_V_E_counts': dict(companion_gcd_counts),
            'bounded_actual_odd_prime_checks': bounded_checks,
            'bounded_actual_prime_five_checks': at_five,
            'bounded_ramified_prime_exclusion_checks': companion_ramified_screen,
            'complete_window_actual_odd_prime_checks': full_checks,
            'scope': 'The same source pairs and actual-prime windows as above; '
                     'no complete factorization of E or new analytic bound.'},
        'scope': 'Finite source pairs only. Complete factorization is asserted only '
                 'in its separate window; the larger prime screen has a cutoff.'}


def finite_euler_check(parameters, primes):
    """Check all three kinds of local factors at s=2 in a finite prime set."""
    zeta = l_value = split = correction = Fraction(1)
    kinds = Counter()
    for p in primes:
        chi = character(p, parameters)
        kinds[str(chi)] += 1
        reciprocal = Fraction(1, p*p)
        zeta /= 1-reciprocal
        l_value /= 1-chi*reciprocal
        if chi == 1:
            split /= 1-reciprocal
        elif chi == -1:
            correction *= 1-reciprocal*reciprocal
        else:
            correction *= 1-reciprocal
    assert l_value > 0 and 0 < correction <= 1
    assert split*split == zeta*l_value*correction <= zeta*l_value
    return dict(kinds)


def character_checks(args, values, odd_primes, euler_primes):
    examples = {}
    for k in range(3, args.character_gap_max+1, 2):
        for sign in (-1, 1):
            d_value = sign*lucas(values, k)
            if not positive_square(d_value):
                examples.setdefault(d_value, []).append({'odd_gap': k, 'sign': sign})
    for d_value in EXTRA_CHARACTER_D:
        examples.setdefault(d_value, []).append({'generic_induction_example': True})
    rows = []
    for d_value in sorted(examples):
        parameters = character_parameters(d_value)
        squarefree, root, delta, modulus = parameters
        conductor = abs(delta)
        period = [character(n, parameters) for n in range(modulus)]
        assert all(value in (-1, 0, 1) for value in period)
        assert sum(period) == 0 and -1 in period
        unit_reductions = set()
        for n, value in enumerate(period):
            assert (value == 0) == (gcd(n, modulus) != 1)
            assert character(n+modulus, parameters) == value
            assert character(n-modulus, parameters) == value
            if value:
                unit_reductions.add(n % conductor)
            for multiplier in MULTIPLIERS:
                assert period[n*multiplier % modulus] == (
                    value*character(multiplier, parameters))
        assert unit_reductions == {
            n for n in range(conductor) if gcd(n, conductor) == 1}
        for p in odd_primes:
            # Includes primes ramified in D but not in the primitive conductor.
            assert character(p, parameters) == legendre(d_value, p)
            assert jacobi(d_value, p) == legendre(d_value, p)
        extra_zero_primes = [p for p, _ in factorization(modulus)
                             if conductor % p != 0]
        for p in extra_zero_primes:
            assert character(p, parameters) == 0
            if p % 2:
                assert jacobi(delta, p) != 0
        rows.append({
            'D': d_value, 'source_labels': examples[d_value],
            'signed_squarefree_part': squarefree, 'square_multiplier': root,
            'fundamental_discriminant': delta, 'primitive_modulus': conductor,
            'induced_modulus': modulus, 'period_sum': sum(period),
            'period_value_counts': {str(k): v for k, v in Counter(period).items()},
            'negative_unit_witness': period.index(-1),
            'extra_zero_primes_from_induction': extra_zero_primes,
            'unit_reduction_is_surjective': True,
            'period_comparisons': 2*modulus,
            'multiplicativity_comparisons': len(MULTIPLIERS)*modulus,
            'finite_euler_prime_classes': finite_euler_check(parameters, euler_primes)})
    assert any(any(p % 2 for p in row['extra_zero_primes_from_induction'])
               for row in rows)
    rejected = []
    for d_value in (0, 1, 4, 9, 36):
        try:
            character_parameters(d_value)
        except ValueError:
            rejected.append(d_value)
        else:
            raise AssertionError('a square D was admitted to the nonprincipal check')
    return {
        'source_odd_gap_range': [3, args.character_gap_max],
        'additional_generic_D_values': EXTRA_CHARACTER_D,
        'multiplicativity_multipliers': MULTIPLIERS,
        'jacobi_euler_odd_prime_limit': args.prime_limit,
        'finite_euler_prime_limit': args.algebra_prime_limit,
        'finite_euler_exponent': 2, 'rejected_zero_or_square_D': rejected,
        'rows': rows,
        'scope': 'Full periods at the displayed finite moduli, sampled '
                 'multiplicativity, and finite Euler-factor identities only.'}


def ring_mul(x, y, p):
    a, b = x
    c, d = y
    return (a*c+b*d) % p, (a*d+b*c+b*d) % p


def ring_conj(x, p):
    return (x[0]+x[1]) % p, -x[1] % p


def ring_norm(x, p):
    a, b = x
    value = (a*a+a*b-b*b) % p
    assert ring_mul(x, ring_conj(x, p), p) == (value, 0)
    return value


def ring_power(x, exponent, p):
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = ring_mul(result, x, p)
        x = ring_mul(x, x, p)
        exponent //= 2
    return result


def mobius(x, p):
    denominator = ((x[0]+1) % p, x[1])
    norm_denominator = ring_norm(denominator, p)
    if norm_denominator == 0:
        raise ValueError('x+1 is not a unit in the quadratic algebra')
    inverse = tuple(pow(norm_denominator, -1, p)*n % p
                    for n in ring_conj(denominator, p))
    assert ring_mul(denominator, inverse, p) == (1, 0)
    return ring_mul(((x[0]-1) % p, x[1]), inverse, p)


def algebra_checks(primes):
    rows = []
    for p in primes:
        if p in (2, 5):
            continue
        split = legendre(5, p) == 1
        roots = [r for r in range(p) if (r*r-r-1) % p == 0]
        assert len(roots) == (2 if split else 0)
        points = allowed = rejected = 0
        for a in range(p):
            for b in range(p):
                x = (a, b)
                if ring_norm(x, p) != p-1:
                    continue
                conjugate = ring_conj(x, p)
                assert ring_power(x, p, p) == (x if split else conjugate)
                if split:
                    first, second = roots
                    assert (conjugate[0]+conjugate[1]*first) % p == (a+b*second) % p
                    assert (conjugate[0]+conjugate[1]*second) % p == (a+b*first) % p
                points += 1
                try:
                    image = mobius(x, p)
                except ValueError:
                    assert split and ring_norm(((a+1) % p, b), p) == 0
                    rejected += 1
                    continue
                assert ring_norm(image, p) == p-1
                assert mobius(image, p) == conjugate
                assert ring_mul(x, conjugate, p) == (p-1, 0)
                allowed += 1
        assert points == (p-1 if split else p+1)
        assert rejected == (2 if split else 0)
        assert allowed+rejected == points
        rows.append({'p': p, 'kind': 'split' if split else 'nonsplit',
                     'all_norm_minus_one_points': points,
                     'mobius_iterate_checks': allowed,
                     'rejected_nonunit_denominators': rejected})
    return {'excluded_primes': [2, 5], 'rows': rows,
            'scope': 'All norm-minus-one points in the displayed finite quadratic '
                     'algebras. No extra Fibonacci rank constraint is asserted.'}


def primitive_atom_values(first, second):
    assert first >= 0 and second >= 0 and first+second > 0
    content = gcd(first, second)
    a, b = first//content, second//content
    u, w = 2*a+3*b, 4*a+7*b
    d_value = -(a*a+a*b-b*b)
    assert gcd(a, b) == 1 and d_value != 0
    assert w*w-5*u*u == 4*d_value
    assert gcd(u, abs(d_value)) == 1
    assert 2*first+3*second == content*u
    for p, _ in factorization(u):
        if p == 2:
            continue
        assert d_value % p != 0 and legendre(d_value, p) == 1
        root = w*pow(2, -1, p) % p
        assert root != 0 and root*root % p == d_value % p
    return content, a, b, u, w, d_value


def primitive_atom_checks(seed_max):
    samples = prime_checks = prime_five = square_samples = 0
    primitive_pairs = set()
    for first in range(seed_max+1):
        for second in range(seed_max+1):
            if first == second == 0:
                continue
            content, a, b, u, _, d_value = primitive_atom_values(first, second)
            assert content >= 1
            primitive_pairs.add((a, b))
            samples += 1
            square_samples += positive_square(d_value)
            for p, _ in factorization(u):
                if p != 2:
                    prime_checks += 1
                    prime_five += p == 5
    # This fixed boundary example is retained even if the optional grid is smaller.
    content, a, b, u, w, d_value = primitive_atom_values(16, 29)
    assert (content, a, b, u, w, d_value) == (1, 16, 29, 119, 267, 121)
    assert positive_square(d_value) and factorization(u) == ((7, 1), (17, 1))
    return {
        'coefficient_range': [0, seed_max], 'nonzero_seed_samples': samples,
        'distinct_primitive_pairs': len(primitive_pairs),
        'all_primitive_u_odd_prime_checks': prime_checks,
        'primitive_u_prime_five_checks': prime_five,
        'positive_square_D_samples': square_samples,
        'principal_character_boundary': {
            'input_coefficients': [16, 29], 'content': content,
            'primitive_coefficients': [a, b], 'u': u, 'w': w, 'D': d_value,
            'complete_u_factorization': factorization(u)},
        'scope': 'The primes checked divide normalized u=(2A+3B)/g. '
                 'No character condition is asserted for extra primes from g, '
                 'and nonsquareness is not assumed.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True,
                        help='output JSON file (overwritten)')
    parser.add_argument('--max-a', type=int, default=160)
    parser.add_argument('--prime-limit', type=int, default=500)
    parser.add_argument('--factor-max-a', type=int, default=44,
                        help='complete-factorization subwindow, not a prime cutoff')
    parser.add_argument('--character-gap-max', type=int, default=15,
                        help='odd Lucas gaps whose induced characters get full-period checks')
    parser.add_argument('--algebra-prime-limit', type=int, default=97)
    parser.add_argument('--seed-max', type=int, default=40,
                        help='upper bound for both nonnegative ATOM seed coefficients')
    args = parser.parse_args()
    if not __debug__:
        parser.error('optimized Python disables verification; run without -O/-OO')
    if not 5 <= args.factor_max_a <= args.max_a:
        parser.error('require 5 <= --factor-max-a <= --max-a')
    if args.prime_limit < 5 or args.algebra_prime_limit < 7:
        parser.error('require --prime-limit >= 5 and --algebra-prime-limit >= 7')
    if args.character_gap_max < 3:
        parser.error('require --character-gap-max >= 3')
    if args.seed_max < 1:
        parser.error('require --seed-max >= 1')
    if args.out.resolve() == Path(__file__).resolve():
        parser.error('--out must not overwrite the program source')
    values = fibonacci_table(max(2*args.max_a+2, args.character_gap_max+2))
    odd_primes = tuple(p for p in primes_through(args.prime_limit) if p != 2)
    algebra_primes = primes_through(args.algebra_prime_limit)
    result = {
        'schema': 'fib-character-slice-v1',
        'scope': 'Finite exact diagnostics only. No infinite Euler-product bound, '
                 'uniform Robin theorem, RH result, Lean verification, or novelty claim.',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'parameters': {key: value for key, value in vars(args).items() if key != 'out'},
        'source_slices': source_checks(args, values, odd_primes),
        'induced_characters': character_checks(args, values, odd_primes, algebra_primes),
        'quadratic_algebras': algebra_checks(algebra_primes),
        'primitive_atom': primitive_atom_checks(args.seed_max)}
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print(json.dumps({
        'joint_integer_identities': result['source_slices']['joint_integer_identities'],
        'bounded_prime_screen': result['source_slices']['bounded_prime_screen'],
        'complete_factorization_window': result['source_slices']['complete_factorization_window'],
        'induced_character_count': len(result['induced_characters']['rows']),
        'quadratic_algebra_prime_count': len(result['quadratic_algebras']['rows']),
        'primitive_atom': result['primitive_atom']},
        sort_keys=True))


if __name__ == '__main__':
    main()
