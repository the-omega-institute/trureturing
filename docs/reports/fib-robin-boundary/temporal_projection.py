#!/usr/bin/env python3
"""Exact finite FIB temporal diagnostics; Python 3.9+, standard library only.

Outputs mathematical data, not a proof of an unbounded claim. A full residue
ensemble is indexed by t=0,...,H-1 at actual quantity 6H. No random sampling.
"""
import argparse
import json
from math import gcd, isqrt, factorial, prod
from fractions import Fraction as Q
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



def zeta_body(h):
    return sum((Q(1, q) for q in divisors(h)), Q(0))


def visible(h, m):
    assert h % m == 0
    return sum((Q(gcd(q, m), q * q) for q in divisors(h)), Q(0))


def local_visible(p, a, b):
    return sum((Q(p ** min(j, b), p ** (2 * j))
                for j in range(a + 1)), Q(0))


def mobius(n):
    fs = factor(n)
    return 0 if any(a > 1 for a in fs.values()) else (-1) ** len(fs)


def projection_diagnostics(h):
    fs = factor(h)
    z = zeta_body(h)
    r_h = rank(h)
    shells = {}
    layers = []
    for p, a in fs.items():
        for k in range(1, a + 1):
            ratio = local_visible(p, a, a-k) / local_visible(p, a, a-k+1)
            assert 0 < ratio < 1
            r = rank(p ** k)
            shells[r] = shells.get(r, Q(1)) * ratio
            layers.append({'p': p, 'k': k, 'rank': r, 'exp_minus_ell': str(ratio)})
    inversion = {}
    for r in divisors(r_h):
        value = Q(1)
        for d in divisors(r):
            value *= (visible(h, h // gcd(h, fib(d))) / z) ** mobius(r // d)
        assert value == shells.get(r, Q(1))
        if value != 1:
            inversion[str(r)] = str(value)
    for d in range(r_h + 1):
        ratio = prod((v for r, v in shells.items() if d % r == 0), start=Q(1))
        assert ratio == visible(h, h // gcd(h, fib(d))) / z
    gains = {}
    for p in sorted(set(fs) | {2, 3, 5, 7, 11}):
        gain = zeta_body(p*h) - z
        future_loss = zeta_body(p*h) - visible(p*h, h)
        assert gain == Q(p, p-1) * future_loss
        old_loss = None
        if h % p == 0:
            old_loss = z - visible(h, h//p)
            assert gain == old_loss / (p-1)
        gains[str(p)] = {'gain': str(gain), 'future_body_loss': str(future_loss),
                         'old_body_loss': str(old_loss) if old_loss is not None else None}
    ratio_8_4 = visible(h, h // gcd(h, 21)) / visible(h, h // gcd(h, 3))
    if h % 7 == 0:
        assert zeta_body(7*h)/z == 1 + (1-ratio_8_4)/6
    return {'Z': str(z), 'layers': layers, 'exp_minus_rank_shell': inversion,
            'V_time8_over_V_time4': str(ratio_8_4), 'prime_gains': gains}


def direct_projection(h):
    """Build fiber averages independently from the gcd norm formula."""
    for m in divisors(h):
        total, residual = Q(0), Q(0)
        for q in divisors(h):
            f = [Q(int(t % q == 0)) for t in range(h)]
            averages = [sum(f[r::m], Q(0)) / (h//m) for r in range(m)]
            norm = sum((averages[t % m] ** 2 for t in range(h)), Q(0)) / h
            error = sum(((f[t]-averages[t % m]) ** 2 for t in range(h)), Q(0)) / h
            assert norm == Q(gcd(q, m), q*q)
            assert norm + error == Q(1, q)
            total, residual = total + norm, residual + error
        assert total == visible(h, m) and total + residual == zeta_body(h)
    return {'H': h, 'quotients': len(divisors(h)), 'all_probes_checked': True}


def shell_bound(h, p):
    """Compare the observable shell product with a direct divisor-sum gain."""
    fs, r = factor(h), rank(p)
    a = fs[p]
    layers = [(q, k) for q, e in fs.items() for k in range(1, e+1)
              if fib(r) % (q**k) == 0 and rank(q**k) == r]
    ratios = [local_visible(q, fs[q], fs[q]-k) /
              local_visible(q, fs[q], fs[q]-k+1) for q, k in layers]
    shell = prod(ratios, start=Q(1))
    observable = prod((visible(h, h//gcd(h, fib(d))) ** mobius(r//d)
                       for d in divisors(r)), start=Q(1))
    assert r > 1 and observable == shell
    ell_ratio = local_visible(p, a, a-1) / local_visible(p, a, a)
    gain = (zeta_body(p*h)-zeta_body(h)) / zeta_body(h)
    bound = (1-shell)/(p-1)
    assert gain == (1-ell_ratio)/(p-1) <= bound
    assert (gain == bound) == (layers == [(p, 1)])
    excess = ell_ratio * (1-shell/ell_ratio)/(p-1)
    assert bound-gain == excess
    return {'H': h, 'p': p, 'rank': r, 'layers': layers,
            'exp_minus_shell': str(shell), 'relative_gain': str(gain),
            'shell_upper': str(bound), 'excess': str(excess),
            'upper_over_gain': str(bound/gain)}


def collision_diagnostics():
    single = shell_bound(5040, 7)
    assert single['exp_minus_shell'] == '25/28'
    assert single['relative_gain'] == single['shell_upper'] == '1/56'
    rows = [shell_bound(37**a * 113, 37) for a in range(1, 5)]
    for a, row in enumerate(rows, 1):
        assert row['layers'] == [(37, 1), (113, 1)]
        assert Q(row['relative_gain']) == Q(36, 37*(37**(a+1)-1))
        assert Q(row['shell_upper']) > Q(14, 57969)
    for first, second in zip(rows, rows[1:]):
        assert Q(first['relative_gain']) > Q(second['relative_gain'])
        assert Q(first['shell_upper']) > Q(second['shell_upper'])
        assert Q(first['upper_over_gain']) < Q(second['upper_over_gain'])
    other = shell_bound(4181, 113)
    assert rows[0]['exp_minus_shell'] == '4373725/4528023'
    assert rows[0]['shell_upper'] == '77149/81504414'
    assert other['relative_gain'] == '1/12882'
    assert other['shell_upper'] == '77149/253569288'
    return {'single_layer': single, 'collision_family': rows,
            'other_colliding_prime': other,
            'scope': 'six exact finite shell/gain checks; no asymptotic certification'}


def finite_prime_sign_diagnostics():
    """Independent integer sieve, squarefree expansion and greedy FIB digits."""
    ps, checkpoints = (2, 3, 5, 7), (100, 1000, 10000, 100000)
    limit, q = checkpoints[-1], prod(ps)
    mu, prime = [1]*(limit+1), [True]*(limit+1)
    mu[0] = 0
    for p in range(2, limit+1):
        if prime[p]:
            for n in range(p, limit+1, p):
                mu[n] = -mu[n]
                prime[n] = False
            for n in range(p*p, limit+1, p*p):
                mu[n] = 0
    weights = [1, 2]
    while weights[-1] < limit:
        weights.append(weights[-1]+weights[-2])
    totals, rows = [0]*5, []
    for n in range(1, limit+1):
        remainder, digital = n, 1
        for w in reversed(weights):
            if w <= remainder:
                remainder -= w
                digital = -digital
        assert remainder == 0
        fp = mu[n]**2 * prod(-1 if n % p == 0 else 1 for p in ps)
        for j, value in enumerate((mu[n], mu[n]**2, fp, digital*fp, digital*mu[n])):
            totals[j] += value
        if n in checkpoints:
            expanded = 0
            for d in divisors(q):
                direct = sum(mu[m]**2 for m in range(d, n+1, d))
                squarefree = sum(mu[k]*(n//(d*k*k//gcd(d, k*k)))
                                 for k in range(1, isqrt(n)+1))
                assert direct == squarefree
                expanded += (-2)**len(factor(d)) * squarefree
            assert expanded == totals[2]
            rows.append(dict(zip(('X', 'M', 'squarefree', 'finite_prime_sign_sum',
                                  'digital_twisted_fP_sum', 'digital_twisted_mu_sum'),
                                 (n, *totals))))
    assert [list(row.values()) for row in rows] == [
        [100, 1, 61, -1, -5, 17], [1000, 2, 608, 52, -16, 30],
        [10000, -23, 6083, 509, 45, 113],
        [100000, -48, 60794, 5064, 326, -230]]
    coefficient = prod((Q(p-1, p+1) for p in ps), start=Q(1))
    assert coefficient == Q(1, 12)
    return {'finite_prime_set': ps, 'density_coefficient_times_zeta2': str(coefficient),
            'squarefree_expansion_checks': len(checkpoints)*len(divisors(q)),
            'rows': rows, 'scope': 'exact finite diagnostic; no asymptotic or RH proof'}


def log_interval(x, terms=32):
    """Rational atanh expansion with geometric upper bound on its tail."""
    assert x > 0
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    while x < 1:
        x *= 2
        k -= 1
    def reduced(y):
        t = (y-1)/(y+1)
        s = 2 * sum((t**(2*j+1)/(2*j+1) for j in range(terms)), Q(0))
        tail = 2*t**(2*terms+1)/((2*terms+1)*(1-t*t))
        return s, s+tail
    lo, hi = reduced(x)
    l2, u2 = reduced(Q(2))
    return lo + k*(l2 if k >= 0 else u2), hi + k*(u2 if k >= 0 else l2)


def outward_decimal_rat(bounds, denominator=10**9):
    lo, hi = bounds
    return [str(Q((lo*denominator).__floor__(), denominator)),
            str(Q((hi*denominator).__ceil__(), denominator))]


def seed_certificate():
    n = 1000
    harmonic = sum((Q(1, j) for j in range(1, n+1)), Q(0))
    ln, un = log_interval(Q(n))
    # RobinRationalBasis.eulerMascheroni_remainder_bounds, N=1000.
    gamma = (harmonic-un-Q(1, 2*n), harmonic-ln-Q(1, 2*(n+1)))
    assert gamma[0] > Q(577, 1000)
    exp_lower = sum((Q(577, 1000)**j / factorial(j) for j in range(6)), Q(0))
    assert exp_lower > Q(89, 50)
    l, u = log_interval(Q(10080))
    ll = (log_interval(l)[0], log_interval(u)[1])
    assert ll[0] > Q(11, 5)
    assert log_interval(Q(2))[0] > Q(2, 3)
    assert log_interval(Q(20160))[1] < 10
    z = zeta_body(10080)
    gain = zeta_body(20160)-z
    assert z == Q(39, 10) and gain == Q(13, 420)
    assert Q(89, 50)*Q(11, 5)-z == Q(2, 125)
    # log(1+x) >= x/(1+x) at x=log(2)/log(10080).
    budget_lower = Q(89, 50)*Q(2, 3)/10
    assert budget_lower == Q(89, 750) and budget_lower > gain
    return {'gamma_enclosure': outward_decimal_rat(gamma),
            'loglog10080_enclosure': outward_decimal_rat(ll),
            'exp_gamma_lower': '89/50', 'delta10080_lower': '2/125',
            'gain_10080_to_20160': str(gain), 'budget_lower': str(budget_lower),
            'scope': 'strict rational bounds using standard log/exp and gamma remainder inequalities'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--H', type=int, default=5040)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    if args.H < 1:
        parser.error('H must be positive')
    result = {'scope': 'finite exact temporal, projection, rank-shell and Robin diagnostics',
              'catalogue': temporal_catalogue(args.H),
              'edge_moduli': [temporal_catalogue(h) for h in (1, 2, 3, 6, 8, 12)],
              'projection': projection_diagnostics(args.H),
              'edge_projections': [projection_diagnostics(h) for h in (1, 2, 3, 6, 8, 12)],
              'direct_fiber_averages': [direct_projection(h) for h in (1, 2, 6, 12, 24, 60)],
              'rank_shell_bounds': collision_diagnostics(),
              'finite_prime_signs': finite_prime_sign_diagnostics(),
              'seed_10080': seed_certificate()}
    data = json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + '\n'
    if args.out:
        args.out.write_text(data, encoding='utf-8')
    else:
        print(data, end='')


if __name__ == '__main__':
    main()
