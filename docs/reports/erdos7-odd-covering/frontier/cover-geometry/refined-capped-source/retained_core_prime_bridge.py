#!/usr/bin/env python3
"""Exact finite-prime continuation of the Report801 23-label source.

Explicit inputs only; standard library; no dynamic imports or shell calls.
The analytic Rosser--Schoenfeld premise and the actual phase-null contract
remain ordinary mathematical premises, not consequences of this verifier.
"""
import argparse
import hashlib
import json
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial, isqrt, prod
from pathlib import Path

HEAD = (5, 7, 11, 13, 17, 19, 23)
SOURCE_CASE = 'three_sixteenths_short_leaf'
WEIGHTS = (F(3, 16), F(3, 16), F(5, 24), F(5, 24), F(5, 24))
LABELS = (15, 21, 45, 33, 35, 39, 63, 51, 57, 55, 105, 75,
          69, 65, 99, 77, 85, 117, 95, 165, 91, 147, 225)
CHECKS = 0


def need(ok, message):
    global CHECKS
    CHECKS += 1
    if not ok:
        raise ValueError(message)


def unique_pairs(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError('duplicate JSON key: ' + key)
        out[key] = value
    return out


def read_json(path):
    raw = path.read_bytes()
    return json.loads(raw, object_pairs_hook=unique_pairs), raw


def a4(p):
    t = F(1, p - 1)
    return 15*t + 50*t*t + 60*t**3 + 24*t**4


def source_replay(source):
    """Reconstruct precisely the source clauses consumed by this bridge.

    No claim to recheck the other two laws or Report801's minimality claim.
    """
    need(source['schema'] == 'retained-core-phase-union-result-v1', 'source schema')
    case = source['cases'][-1]
    need(case['name'] == SOURCE_CASE, 'last source case identity')
    need(tuple(map(F, case['weights'])) == WEIGHTS, 'one fixed source law')
    need(tuple(case['selected_labels']) == LABELS and case['count'] == 23,
         'original 23 numerical labels')
    a, b = WEIGHTS[0], WEIGHTS[2]
    caps = tuple(F(q - 1, q - 2) for q in HEAD)
    support_budget = tuple(prod(F(1, q - 2) for i, q in enumerate(HEAD)
                                if mask >> i & 1) for mask in range(128))
    remain = [[support_budget[s] if s and (h or s.bit_count() >= 2) else F(0)
               for s in range(128)] for h in range(3)]
    for label in LABELS:
        h, n = 0, label
        while n % 3 == 0:
            h, n = h + 1, n // 3
        support, unfactored = 0, n
        for i, q in enumerate(HEAD):
            if unfactored % q == 0:
                support |= 1 << i
                while unfactored % q == 0:
                    unfactored //= q
        need(unfactored == 1 and n > 1 and h <= 2,
             'selected original lies in the shallow inventory')
        cap = prod(caps[i] for i in range(7) if support >> i & 1) / n
        remain[h][support] -= cap
    need(all(v >= 0 for row in remain for v in row), 'nonnegative remaining inventory')
    vertices = []
    for mask in range(128):
        t = tuple(caps[i] / q if mask >> i & 1 else F(0)
                  for i, q in enumerate(HEAD))
        responses = []
        for removed in range(128):
            live = [i for i in range(1, 7) if not removed >> i & 1]
            zero = prod(1 - t[i] for i in live)
            one = sum((t[i] * prod(1 - t[j] for j in live if j != i)
                       for i in live), F(0))
            A = (1 if removed & 1 else 1 - t[0]) * (zero + one)
            B = zero
            responses.append((2*a*A + 3*b*B, max(2*a*A, 3*b*B), max(a*A, b*B)))
        core = responses[0][0]
        high = sum((support_budget[s] * responses[s][2] / 2 for s in range(128)), F(0))
        low = sum((remain[h][s] * responses[s][h] for h in range(3) for s in range(128)), F(0))
        vertices.append(dict(mask=mask, core=str(core), high_loss=str(high),
                             shallow_loss=str(low), lower_bound=str(core-high-low)))
    need(case['all_vertices'] == vertices, 'every same-source core vertex')
    worst = min(range(128), key=lambda i: F(vertices[i]['lower_bound']))
    alpha = F(vertices[worst]['lower_bound'])
    need(case['worst_vertex'] == worst == 127, 'source worst vertex')
    need(F(case['alpha']) == alpha > 0, 'same source mass')

    r, v = max(2*a, 3*b), max(a, b)
    axes = (3,) + HEAD

    def run_tail(axis, e):
        if e == 0:
            return F(1)
        if axis == 3:
            return r if e == 1 else v / 3**(e-2)
        return F(axis-1, axis-2) / axis**e

    @lru_cache(None)
    def product_atom(k, n):
        if k == 0:
            return F(n == 1)
        p = axes[k-1]
        return sum(((run_tail(p, d-1) - run_tail(p, d)) * product_atom(k-1, n//d)
                    for d in range(1, n+1) if n % d == 0), F(0))

    mean = (1+r+3*v/2) * prod(caps)
    hinges = {h: mean-h+sum(((h-j)*product_atom(8, j) for j in range(1, h)), F(0))
              for h in range(28)}
    need({str(k): str(x) for k, x in hinges.items()} == case['full_hinges'],
         'all-height query hinges for this fixed law')
    threshold = min(hinges, key=lambda h: h + hinges[h]/alpha)
    query = threshold + hinges[threshold]/alpha
    mass = (28-query)/27
    fourth0 = (1+15*r+216*v) * prod(1+c*a4(q) for c, q in zip(caps, HEAD))
    fourth29 = fourth0 * (1+F(28, 27)*a4(29))
    need(case['threshold'] == threshold == 16, 'same complete-query threshold')
    need(F(case['query_upper']) == query < 28, 'same complete-query upper bound')
    need(F(case['post29_mass']) == mass > 0, 'same post29 absolute source mass')
    need(F(case['fourth_product_before29']) == fourth0, 'same head quartic factor')
    need(F(case['fourth_product_with29']) == fourth29, 'same post29 quartic factor')
    return case, alpha, mass, fourth29/alpha


def complete_primes(lower, upper):
    """Sieve plus independent least-divisor check on every interval integer."""
    sieve = bytearray(b'\x01') * (upper+1)
    sieve[0:2] = b'\x00\x00'
    for p in range(2, isqrt(upper)+1):
        if sieve[p]:
            for n in range(p*p, upper+1, p):
                sieve[n] = 0
    out = []
    for n in range(lower+1, upper+1):
        witness = next((d for d in range(2, isqrt(n)+1) if n % d == 0), None)
        need(bool(sieve[n]) == (witness is None), 'prime completeness at ' + str(n))
        if witness is None:
            out.append(n)
    return out


def ceil_grid(value, scale):
    return F(-((-value.numerator*scale)//value.denominator), scale)


def continuation(primes, tail, delta, C, scale):
    upper, exact = tail, tail
    rows = []
    for p in reversed(primes):
        loss = C/F((p-1)**4)
        growth = 1+a4(p)/(1-delta)
        need(loss > 0 and growth >= 1 and upper >= 0, 'positive monotone transition')
        raw = loss+growth*upper
        new_upper = ceil_grid(raw, scale)
        slack = new_upper-raw
        need(0 <= slack < F(1, scale), 'upward rounding has sub-grid slack')
        need((new_upper*scale).denominator == 1, 'rounded value is on declared grid')
        exact = loss+growth*exact
        need(new_upper >= exact, 'upper envelope dominates exact continuation')
        rows.append(dict(prime=p, cost=str(loss), growth=str(growth),
                         next_upper=str(upper), previous_upper=str(new_upper),
                         rounding_slack=str(slack)))
        upper = new_upper
    need(F(0) <= upper-exact < F(1, 10**26), 'total rounding error below 1e-26')
    return upper, exact, rows


def calculate(cert, source, source_bytes):
    global CHECKS
    CHECKS = 0
    keys = {'schema', 'source_sha256', 'source_case', 'cutoff', 'analytic_cutoff',
            'delta', 'growth', 'ell', 'rounding_denominator', 'reserve_floor', 'primes'}
    need(set(cert) == keys, 'exact certificate fields')
    need(cert['schema'] == 'retained-core-finite-prime-bridge-v1', 'certificate schema')
    need(cert['source_case'] == SOURCE_CASE, 'certificate source identity')
    digest = hashlib.sha256(source_bytes).hexdigest()
    need(cert['source_sha256'] == digest, 'source SHA256 binding')
    for key in ('cutoff', 'analytic_cutoff', 'growth', 'ell', 'rounding_denominator'):
        need(type(cert[key]) is int, 'integer certificate parameter ' + key)
    lower, upper = cert['cutoff'], cert['analytic_cutoff']
    growth, ell, delta = cert['growth'], cert['ell'], F(cert['delta'])
    scale, floor = cert['rounding_denominator'], F(cert['reserve_floor'])
    need((lower, upper, growth, ell, delta, scale, floor) ==
         (1600, 3000, 21, 7, F(2,7), 10**30, F(9,1000)), 'stated fixed bridge parameters')
    need(isinstance(cert['primes'], list) and all(type(p) is int for p in cert['primes']),
         'integer prime list')
    primes = complete_primes(lower, upper)
    need(cert['primes'] == primes, 'complete ordered finite prime interval')
    case, alpha, mass, K = source_replay(source)

    C = F(27, 256)/(delta**3*(1-delta))
    coefficients = (F(1),) + tuple(F(n)/(1-delta) for n in (15, 50, 60, 24))
    need(upper >= 286 and ell >= 4 and 3**ell <= upper and 4*ell >= growth,
         'inherited analytic-tail range premises')
    need(all(x <= comb(growth, i) for i, x in enumerate(coefficients)),
         'quartic growth dominated by degree21 binomial')
    series = sum((F(factorial(growth), factorial(growth-j)*(3*ell)**j)
                  for j in range(growth+1)), F(0))
    tail = C/3 * F(2*ell*ell+1, 2*ell*ell-1)**growth * F(upper, (upper-1)**4) * series
    need(F(case['tau3000']) == tail, 'same complete analytic tail above3000')
    need(F(case['full_tail_reserve']) == mass-K*tail, 'original same-source tail identity')
    envelope, exact, rows = continuation(primes, tail, delta, C, scale)
    forward_loss, forward_growth = F(0), F(1)
    for p in primes:
        forward_loss += forward_growth*C/F((p-1)**4)
        forward_growth *= 1+a4(p)/(1-delta)
    need(forward_loss+forward_growth*tail == exact,
         'forward same-source absolute loss equals backward recursion')
    reserve = mass-K*envelope
    need(reserve > floor, 'strict positive absolute distorted mass floor')

    controls = []
    # Two specified neighboring controls, not an unbounded cutoff search.
    extension = complete_primes(1530, lower)
    for start in (1543, 1531):
        ps = [p for p in extension if p >= start] + primes
        bound, exact_bound, ignored = continuation(ps, tail, delta, C, scale)
        margin = mass-K*bound
        need(margin > F(1,2000) if start == 1543 else margin < 0,
             'specified neighboring cutoff control')
        controls.append(dict(first_prime=start, prime_count=len(ps), upper=str(bound),
                             exact=str(exact_bound), reserve=str(margin), reserve_decimal=float(margin)))
    return dict(schema='retained-core-finite-prime-bridge-result-v1', check_count=CHECKS,
                scope='Ordinary conditional same-source continuation. The original23 phase-null conditions and inherited Rosser--Schoenfeld analytic premise remain required. All original labels, all finite heights, all finite prime subsets above1600 are retained. No Lean or unrestricted Erdos7 conclusion.',
                source_sha256=digest, source_case=SOURCE_CASE,
                source_alpha=str(alpha), source_post29_mass=str(mass), source_K=str(K),
                delta=str(delta), loss_constant=str(C), cutoff=lower, analytic_cutoff=upper,
                prime_count=len(primes), first_prime=primes[0], last_prime=primes[-1],
                interval_composite_count=upper-lower-len(primes), primes=primes,
                rounding_denominator=scale, tau3000=str(tail), rows=rows,
                finite_loss_coefficient=str(forward_loss),
                finite_growth_product=str(forward_growth),
                finite_prime_upper=str(envelope), exact_finite_prime_value=str(exact),
                total_rounding_error=str(envelope-exact), reserve=str(reserve),
                reserve_decimal=float(reserve), reserve_floor=str(floor),
                floor_margin=str(reserve-floor), controls=controls)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--certificate', type=Path, required=True)
    output = parser.add_mutually_exclusive_group(required=True)
    output.add_argument('--result', type=Path)
    output.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    try:
        cert, ignored = read_json(args.certificate)
        source, raw = read_json(args.source)
        result = calculate(cert, source, raw)
        if args.write_result:
            args.write_result.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
        else:
            retained, ignored = read_json(args.result)
            need(result == retained, 'exact retained result replay')
        print(json.dumps({k: result[k] for k in ('schema', 'check_count', 'source_case',
                          'prime_count', 'first_prime', 'last_prime', 'finite_prime_upper',
                          'reserve_decimal', 'reserve_floor')}, indent=2))
    except (ValueError, KeyError, TypeError, OSError, IndexError, ZeroDivisionError) as exc:
        parser.exit(1, 'REJECTED: '+str(exc)+'\n')


if __name__ == '__main__':
    main()
