#!/usr/bin/env python3
"""Exact finite FIB temporal diagnostics; Python 3.9+, standard library only.

Outputs mathematical data, not a proof of an unbounded claim. A full residue
ensemble is indexed by t=0,...,H-1 at actual quantity 6H. No random sampling.
"""
import argparse
import json
from math import gcd, isqrt
from pathlib import Path


def divisors(n):
    small = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return sorted(set(small + [n // d for d in small]))


def factor(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = 1
    return result


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def rank(m):
    """First zero, with a finite-state recurrence guard (including m=1)."""
    a, b = 0, 1 % m
    initial = (a, b)
    for r in range(1, m * m + 1):
        a, b = b, (a + b) % m
        if a == 0:
            return r
        if (a, b) == initial:
            raise AssertionError('orbit returned without zero')
    raise AssertionError('finite invertible orbit failed to return')


def temporal_catalogue(h):
    r = rank(h)
    by_loss = {}
    for d in range(1, r + 1):
        g = gcd(h, fib(d))
        by_loss.setdefault(g, d)
    ds = divisors(h)
    closure = {g: gcd(h, fib(rank(g))) for g in ds}
    assert set(by_loss) == {g for g in ds if closure[g] == g}
    for g in ds:
        assert closure[g] % g == 0
        assert closure[closure[g]] == closure[g]
        assert rank(closure[g]) == rank(g)
        for k in ds:
            if k % g == 0:
                assert closure[k] % closure[g] == 0
    # All these phases are actual nonnegative compositions at n=6H.
    for t in range(h):
        a, b = 3 * h - 3 * t, 2 * t
        assert a >= 0 and b >= 0 and 2 * a + 3 * b == 6 * h
        assert 3 * a + 5 * b == 9 * h + t
    # Check a complete period of temporal partitions, by two-way fiber labels.
    for d in range(r + 1):
        c = fib(d)
        m = h // gcd(h, c)
        forward, backward = {}, {}
        for t in range(h):
            y, q = c * t % h, t % m
            assert y not in forward or forward[y] == q
            assert q not in backward or backward[q] == y
            forward[y], backward[q] = q, y
        assert len(forward) == m
    return {
        'H': h, 'quantity': 6 * h, 'phase_count': h,
        'omitted_endpoint': {'t': h, 'composition': [0, 2 * h]},
        'rank_H': r,
        'raw_losses_first_times': {str(g): by_loss[g] for g in sorted(by_loss)},
        'closure': {str(g): closure[g] for g in ds},
        'prime_power_ranks': {str(p ** k): rank(p ** k)
                              for p, a in factor(h).items() for k in range(1, a + 1)},
        'checked_time_indices': r + 1,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--H', type=int, default=5040)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    if args.H < 1:
        parser.error('H must be positive')
    result = {'scope': 'finite exact integer temporal fibers and closure',
              'catalogue': temporal_catalogue(args.H),
              'edge_moduli': [temporal_catalogue(h) for h in (1, 2, 3, 6, 8, 12)]}
    data = json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + '\n'
    if args.out:
        args.out.write_text(data, encoding='utf-8')
    else:
        print(data, end='')


if __name__ == '__main__':
    main()
