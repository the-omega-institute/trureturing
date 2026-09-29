#!/usr/bin/env python3
"""Exact diagnostics for context completion and its finite action boundaries.

Run: python3 context_completion.py --out /absolute/path/results.json
Only stdlib integer/Fraction arithmetic is used. Finite tests are diagnostics,
not a proof of the universal statements in theory section 99. No imports
from a repository, scratch directory, or external package are required.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from math import gcd, prod
from pathlib import Path
import sys

sys.dont_write_bytecode = True
if not __debug__:
    raise RuntimeError('run without -O or PYTHONOPTIMIZE; checks require assertions')

H = 5040


@lru_cache(maxsize=None)
def factor(n: int) -> tuple[tuple[int, int], ...]:
    if n < 1:
        raise ValueError('positive integers only')
    result = []
    p = 2
    while p * p <= n:
        a = 0
        while n % p == 0:
            n //= p
            a += 1
        if a:
            result.append((p, a))
        p = 3 if p == 2 else p + 2
    if n > 1:
        result.append((n, 1))
    return tuple(result)


def divisors(n: int) -> list[int]:
    values = [1]
    for p, a in factor(n):
        values = [d * p**k for d in values for k in range(a + 1)]
    return sorted(values)


def sigma(n: int) -> int:
    return prod((p**(a + 1) - 1) // (p - 1) for p, a in factor(n))


def z(n: int) -> Fraction:
    return Fraction(sigma(n), n)


def score(n: int) -> Fraction:
    """exp(25 J(n)) = sigma(n)^25 / n^26, exactly."""
    return Fraction(sigma(n)**25, n**26)


def q(n: int, h: int = H) -> int:
    return gcd(n, h)


def action(n: int, h: int = H) -> int:
    return h // q(n, h)


def join(d: int, e: int, h: int = H) -> int:
    return gcd(d * e, h)


def phi(n: int) -> int:
    return prod((p - 1) * p**(a - 1) for p, a in factor(n))


def rational(x: Fraction) -> str:
    return str(x.numerator) if x.denominator == 1 else f'{x.numerator}/{x.denominator}'


def two_three_counts(n: int) -> tuple[int, int]:
    """A numerical witness n = 2a + 3b for every n >= 2."""
    if n < 2:
        raise ValueError('need n >= 2')
    b = n % 2
    a = (n - 3*b) // 2
    assert a >= 0 and 2*a + 3*b == n
    return a, b


def run() -> dict:
    counts = Counter()
    # Independently check the factor-product weight against raw divisor sums.
    for n in range(1, 513):
        direct = sum((Fraction(1, d) for d in range(1, n + 1) if n % d == 0), Fraction())
        assert z(n) == direct
        counts['direct_divisor_weight_checks'] += 1

    # Verify the eight strict threshold inequalities without logarithms.
    thresholds = []
    for p, a in ((2, 4), (3, 2), (5, 1), (7, 1)):
        for k, adopted in ((a, True), (a + 1, False)):
            gain = z(p**k) / z(p**(k-1))
            assert (gain**25 > p) if adopted else (gain**25 < p)
            thresholds.append({'p': p, 'layer': k, 'adopted': adopted, 'gain': rational(gain)})
            counts['strict_boundary_threshold_checks'] += 1
    assert Fraction(12, 11)**25 < 11
    counts['uniform_tail_base_checks'] += 1

    # Independently compare fixed-context candidates using the exact objective.
    contexts = list(range(1, 257)) + [H, 2*H, 13*H, 2**40, 3**20, 11**5, 2**8*3**5*11**2]
    for c in contexts:
        a_star = action(c)
        target = c * a_star
        assert target == c // gcd(c, H) * H
        optimum = score(target)
        for a in sorted(set(range(1, 129)) | {a_star, 2*a_star, 3*a_star}):
            candidate = score(c*a)
            assert candidate <= optimum
            assert (candidate == optimum) == (a == a_star)
            counts['context_objective_comparisons'] += 1

    states = divisors(H)
    assert len(states) == 60
    assert len({action(d) for d in states}) == 60
    for d, e in product(states, repeat=2):
        assert q(d*e) == join(d, e)
        assert join(d, e) == join(e, d)
        assert join(1, d) == d
        assert join(H, d) == H
        counts['boundary_binary_checks'] += 1
    for d, e, f in product(states, repeat=3):
        assert join(join(d, e), f) == join(d, join(e, f))
        counts['boundary_associativity_checks'] += 1

    # Every coarse state is a gcd fiber, with an explicit unit coordinate.
    fibers = Counter(q(r) for r in range(H))
    for r in range(H):
        d = q(r)
        if d == H:
            assert r == 0
        else:
            u = r // d
            assert 0 <= u < H//d and gcd(u, H//d) == 1
            assert d*u == r
        counts['unit_fiber_coordinate_checks'] += 1
    assert sum(fibers.values()) == H
    for d in states:
        assert fibers[d] == phi(H//d)
        counts['unit_fiber_cardinality_checks'] += 1
    assert fibers[1] == 1152

    # Test raw integers against the actual refined transitions, not only residues.
    inputs = (2, 3, 5, 7, 11, 13, H-1, H+1)
    for r, t in product(range(H), inputs):
        n = r + 3*H
        assert action(n+t) == action((r+t) % H)
        assert action(n*t) == action((r*t) % H)
        assert q(n*t) == join(q(n), q(t))
        counts['fine_additive_transition_checks'] += 1
        counts['fine_multiplicative_transition_checks'] += 1
        counts['coarse_actual_multiplication_checks'] += 1

    # Distinguishing suffixes for the general H theorem on a complete small domain.
    for h in range(2, 65):
        ds = divisors(h)
        assert len({action(d, h) for d in ds}) == len(ds)
        for r in range(h):
            t = (-r) % h + 2*h
            two_three_counts(t)
            for s in range(h):
                if s == r:
                    continue
                assert action(r+t, h) == 1
                assert action(s+t, h) > 1
                counts['general_template_distinguishing_pairs'] += 1
    # For the large template, verify each chosen suffix separates its target
    # from each nonzero residue difference, using translation invariance.
    for r in range(H):
        t = (-r) % H + 2*H
        two_three_counts(t)
        assert (r+t) % H == 0 and action(r+t) == 1
        counts['large_template_distinguishing_suffixes'] += 1
    for difference in range(1, H):
        assert action(difference) > 1
        counts['large_template_nonzero_difference_checks'] += 1

    # Relation coordinates belong to the canonical q(C), not the raw syntax of C.
    for d in states:
        fs = dict(factor(d))
        i, j, k, ell = (fs.get(p, 0) for p in (2, 3, 5, 7))
        u, v, w, kap = i+ell, j, k+ell, ell
        complement = 2**(4-i)*3**(2-j)*5**(1-k)*7**(1-ell)
        assert complement == action(d)
        assert (4-i+1-ell, 2-j, 1-k+1-ell, 1-ell) == (5-u, 2-v, 2-w, 1-kap)
        counts['relation_coordinate_complement_checks'] += 1

    # Specialize the existing all-prime future-floor theorem to gcd endpoints.
    # Do not duplicate the canonical seam, KL, cocycle, or restricted-S audit.
    future_inputs = (1, 2, 3, 6, 30, 210, H, 2**7*3**5)
    witness_exponents = Counter()
    safe_pairs = 0
    samples = []
    for a, b in product(range(1, 65), repeat=2):
        g = gcd(a, b)
        lower, upper = z(g)/z(b), z(a)/z(g)
        safe = lower**25 >= Fraction(a, b)
        safe_pairs += int(safe)
        for c in future_inputs:
            ratio = z(a*c)/z(b*c)
            assert lower <= ratio <= upper
            if safe:
                assert ratio**25 >= Fraction(a, b)
            counts['gcd_future_endpoint_checks'] += 1
        if not safe:
            fa, fb = dict(factor(a)), dict(factor(b))
            advantage = prod(p for p, exponent in fa.items() if exponent > fb.get(p, 0))
            for n in range(65):
                c = advantage**n
                ratio = z(a*c)/z(b*c)
                if ratio**25 < Fraction(a, b):
                    witness_exponents[n] += 1
                    counts['finite_unsafe_pruning_witnesses'] += 1
                    if n >= 2 and len(samples) < 8:
                        samples.append({'A': a, 'B': b, 'C': c, 'exponent': n, 'ratio': rational(ratio)})
                    break
            else:
                raise AssertionError(('no witness within diagnostic cap', a, b))
    counts['universally_safe_price_pairs'] = safe_pairs

    assert score(H) > score(H//2)
    assert score(2*H) < score(H)
    assert q(11) == q(13) == 1
    assert action(11+2) == H and action(13+2) == 336
    assert action(7) == 720 and action(10) == 504
    assert action(11) == action(121) and score(11) != score(121)
    return {
        'scope': 'Exact finite diagnostics; universal results are paper proofs, no Lean build or RH claim.',
        'template': H,
        'counts': dict(sorted(counts.items())),
        'domains': {'context_count': len(contexts), 'bounded_candidate_A': [1, 128],
                    'gcd_future_pair_A_B': [1, 64], 'future_C': list(future_inputs),
                    'general_H': [2, 64]},
        'strict_thresholds': thresholds,
        'state_count': {'multiplicative': len(states), 'additive': H},
        'fibers': [{'gcd': d, 'size': fibers[d], 'action': action(d)} for d in states],
        'completion_examples': [{'C': c, 'gcd': q(c), 'action': action(c), 'final': c*action(c)}
                                for c in (1, 2, 7, 10, 12, 13*H)],
        'unsafe_witness_exponent_histogram': {str(k): v for k, v in sorted(witness_exponents.items())},
        'unsafe_witness_samples': samples,
        'counterexamples': {
            'context_reversal': {'initial': [H, H//2], 'multiply_by': 2, 'strict_order_reverses': True},
            'coarse_addition': {'initial': [11, 13], 'gcd': 1, 'add': 2, 'new_actions': [H, 336]},
            'relation_loss': {'canonical_blocks': [7, 10], 'leaf_counts': [1, 0, 1], 'actions': [720, 504]},
            'same_action_different_value': {'initial': [11, 121], 'action': H}
        }
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path, help='JSON output; parent directory is created')
    args = parser.parse_args()
    result = run()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps(result['counts'], sort_keys=True))


if __name__ == '__main__':
    main()
