"""Exact finite bounds and an actual retained-pure repair control.

Use --input INPUT.json --output OUTPUT.json. Checks remain active under -O.
Requires Python 3.9+ and its standard library; no installation is needed.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import isqrt, lcm
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def divisors(n):
    low = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return sorted(set(low + [n // d for d in low]))


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def valuation(n, p):
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def class_map(rows):
    result = {}
    require(bool(rows), 'empty class input')
    for d, a in rows:
        require(type(d) is int and type(a) is int and d > 1 and d % 2 == 1,
                'invalid odd class')
        require(0 <= a < d and d not in result, 'noncanonical residue or repeated label')
        result[d] = a
    return result


def forest(p, R, t):
    require(p * t > (p - 1) * R, 'infeasible root forest')
    if t >= R:
        return 0, R, R
    delta = p * t - (p - 1) * R
    J = 0
    while p ** J * delta < t:
        J += 1
    s = Fraction(p * t - p ** J * delta, p - 1)
    require(s.denominator == 1 and 1 <= s <= t, 'invalid final layer')
    return J, int(s), t * J + int(s)


def finite_bounds(ranges):
    rows = []
    total = equal_last = 0
    require(len(set(tuple(pair) for pair in ranges)) == len(ranges), 'duplicate range')
    require(set(tuple(pair) for pair in ranges) == {(3, 2), (3, 3), (3, 4), (3, 5), (5, 2)},
            'the five analytic exception ranges must all be present')
    for p, k in ranges:
        require((p == 3 and 2 <= k <= 5) or (p == 5 and k == 2), 'unsupported exception range')
        r = p ** k
        C = Fraction(1) + Fraction(5 * k, 9 if p == 3 else 6)
        maximum = Fraction(0)
        witness = None
        count = 0
        for R in range(p, r + 1, p):
            if (p - 1) * R <= (p - 2) * r:
                continue
            for t in range(1, R):
                if p * t <= (p - 1) * R:
                    continue
                J, s, N = forest(p, R, t)
                require(1 <= J <= k - 1, 'stopping-depth bound fails')
                last = min(C, Fraction(s, 3)) if s < t else C
                U = r * (Fraction(p ** J - 1, p - 1) * C + p ** J * last)
                ratio = U / (N * N)
                require(ratio < 1, 'strict tie bound fails at ' + str((p, k, R, t)))
                count += 1
                equal_last += s == t
                if ratio > maximum:
                    maximum = ratio
                    witness = {'R': R, 't': t, 'J': J, 's': s, 'N': N, 'U': str(U)}
        total += count
        rows.append({'p': p, 'k': k, 'cases': count, 'C': str(C),
                     'max_upper_ratio': str(maximum), 'maximizer': witness})
    return {'cases': total, 'equal_final_layer_cases': equal_last, 'ranges': rows}


def actual_control(data):
    original = class_map(data['original_classes'])
    repairs = class_map(data['repairs'])
    labels = sorted(original)
    Q = lcm(*labels)
    require(all(e in original for d in labels for e in divisors(d) if e > 1),
            'original palette not divisor-closed')
    pairs = [(d, e) for d, e in combinations(labels, 2) if e % d == 0]
    require(all(original[e] % d != original[d] for d, e in pairs), 'comparable intersection')
    private = dict.fromkeys(labels, 0)
    holes = 0
    for x in range(Q):
        owners = [d for d in labels if x % d == original[d]]
        holes += not owners
        if len(owners) == 1:
            private[owners[0]] += 1
    require(all(private.values()), 'some original has no private point')
    h, c, p = (data['target'][key] for key in ('h', 'phase', 'prime'))
    require(h in original and original[h] == c and prime(p) and p % 2 == 1,
            'invalid actual target')
    H, a = valuation(Q, p), valuation(h, p)
    n = h // p ** a
    require(n > 1, 'target must have a nontrivial p-free cofactor')
    t, r = len(divisors(n)), p ** (H - a + 1)
    eligible = [(p ** i, original[p ** i]) for i in range(a + 1, H + 1)
                if p ** i in original and original[p ** i] % (p ** a) == c % (p ** a)]
    R = r - sum(p ** (H + 1 - valuation(d, p)) for d, b in eligible)
    require(R % p == 0 and (p - 1) * R > (p - 2) * r, 'residual-root lower bound')
    J, s, N = forest(p, R, t)
    divs = divisors(n)
    S = p ** (H + 1) * (sum(divs[:R]) if J == 0 else
         sum(divs) * ((p ** J - 1) // (p - 1)) + p ** J * sum(divs[:s]))
    require(set(repairs).isdisjoint(original), 'repair label is not fresh')
    require(len(repairs) == N and sum(repairs) == S, 'minimum count/sum formula mismatch')
    require(S < h * N * N, 'strict repair sum comparison fails')
    require(all(valuation(d, p) > H and n % (d // p ** valuation(d, p)) == 0
                for d in repairs), 'repair outside specified fresh palette')
    old_feasible = p * t > (p - 1) * r
    require(not old_feasible, 'control does not separate old and retained-pure qualification')
    comparison = lcm(Q, *repairs)
    pure_points = fresh_points = 0
    for x in range(c, comparison, h):
        pure = sum(x % d == b for d, b in eligible)
        fresh = sum(x % d == b for d, b in repairs.items())
        require(pure + fresh == 1, 'target has missing or repeated ownership')
        pure_points += pure
        fresh_points += fresh
    return {'original_period': Q, 'comparable_pairs': len(pairs),
            'private_counts': private, 'original_holes': holes,
            'h': h, 'c': c, 'p': p, 'H': H, 'a': a, 't': t, 'r': r, 'R': R,
            'eligible_retained_pure_classes': eligible, 'J': J, 's': s,
            'N': N, 'S': S, 'h_N_squared': h * N * N,
            'old_qualification': old_feasible, 'comparison_period': comparison,
            'target_points': comparison // h, 'pure_target_points': pure_points,
            'fresh_target_points': fresh_points, 'repairs': sorted(repairs.items())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text(encoding='utf-8'))
    result = {'scope': 'ordinary exact arithmetic and finite noncover control; no Lean verification',
              'finite_bounds': finite_bounds(data['exception_ranges']),
              'actual_control': actual_control(data)}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
