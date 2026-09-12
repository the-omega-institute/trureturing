"""One-off exact-rational measurement for LANE #6160; not Lean evidence."""

from fractions import Fraction as Q
from math import factorial, prod
import json


def log_bounds(x, terms=20):
    assert x >= 1
    k = 0
    while x >= 2:
        x /= 2
        k += 1

    def series(t):
        lo = 2 * sum((t ** (2 * j + 1) / (2 * j + 1)
                      for j in range(terms)), Q(0))
        return lo, lo + 2 * t ** (2 * terms + 1) / (
            (2 * terms + 1) * (1 - t * t))

    a, b = series(Q(1, 3))
    c, d = series((x - 1) / (x + 1))
    return k * a + c, k * b + d


def exp_bounds(x, terms=16):
    assert 0 <= x < 1
    lo = sum((x ** j / factorial(j) for j in range(terms)), Q(0))
    return lo, lo + x ** terms / factorial(terms) / (1 - x / (terms + 1))


eg_lo = exp_bounds(Q(5772155, 10000000))[0]
eg_hi = exp_bounds(Q(5772161, 10000000))[1]


def rhs_bounds(n):
    log_lo, log_hi = log_bounds(Q(n))
    return eg_lo * log_bounds(log_lo)[0], eg_hi * log_bounds(log_hi)[1]


# Find integer bounds for the exact crossing using only rational comparisons.
left, right = 5040, 131072
while right - left > 1:
    mid = (left + right) // 2
    if rhs_bounds(mid)[1] < Q(35, 8):
        left = mid
    else:
        right = mid
threshold_lower = left
left, right = threshold_lower, 131072
while right - left > 1:
    mid = (left + right) // 2
    if rhs_bounds(mid)[0] > Q(35, 8):
        right = mid
    else:
        left = mid
threshold_upper = right

rows = []
for a in range(17):
    for b in range(11):
        for c in range(8):
            for d in range(7):
                exponents = (a, b, c, d)
                n = prod(p ** e for p, e in zip((2, 3, 5, 7), exponents))
                if 5040 < n < 131072:
                    sigma = prod((p ** (e + 1) - 1) // (p - 1)
                                 for p, e in zip((2, 3, 5, 7), exponents))
                    rows.append((n, sigma, exponents))
rows.sort()
assert len({n for n, _, _ in rows}) == len(rows)
uncertified = []
counterexamples = []
minimum = None
for n, sigma, exponents in rows:
    lower, upper = rhs_bounds(n)
    margin = lower - Q(sigma, n)
    if margin <= 0:
        uncertified.append(n)
    if upper <= Q(sigma, n):
        counterexamples.append(n)
    if minimum is None or margin < minimum[0]:
        minimum = (margin, n, sigma, exponents)

windows = []
for lo, hi in zip((5040, 10000, 20000, 40000, 80000),
                  (10000, 20000, 40000, 80000, 131072)):
    members = [row for row in rows if lo <= row[0] < hi]
    maximal = max(members, key=lambda row: Q(row[1], row[0]))
    windows.append({"lower": lo, "upper": hi, "count": len(members),
                    "max_ratio": str(Q(maximal[1], maximal[0])),
                    "maximizer": maximal[0],
                    "rhs_lower_approx": float(rhs_bounds(lo)[0])})

nonvacuity = []
for exponents in ((5, 2, 1, 1), (4, 2, 1, 1)):
    n = prod(p ** e for p, e in zip((2, 3, 5, 7), exponents))
    sigma = prod((p ** (e + 1) - 1) // (p - 1)
                 for p, e in zip((2, 3, 5, 7), exponents))
    lower, upper = rhs_bounds(n)
    scale = 10 ** 8
    outer_lower = Q((lower * scale).__floor__(), scale)
    outer_upper = Q((upper * scale).__ceil__(), scale)
    nonvacuity.append({
        "n": n, "exponents": exponents, "sigma": sigma,
        "ratio": str(Q(sigma, n)),
        "rhs_rational_enclosure": [str(outer_lower), str(outer_upper)],
        "hypothesis_holds": n > 5040,
        "conclusion_certified_true": Q(sigma, n) < outer_lower,
        "conclusion_certified_false": outer_upper < Q(sigma, n)
    })

print(json.dumps({
    "method": "Fraction arithmetic; atanh log remainder, geometric exp tail",
    "threshold_strict_integer_enclosure": [threshold_lower, threshold_upper],
    "chosen_tail_start": 131072,
    "tail_rhs_lower_approx": float(rhs_bounds(131072)[0]),
    "exact_tail_check": rhs_bounds(131072)[0] > Q(35, 8),
    "finite_exponent_box_inclusive": [[0, 16], [0, 10], [0, 7], [0, 6]],
    "box_count": 17 * 11 * 8 * 7,
    "finite_count": len(rows),
    "first": rows[0], "last": rows[-1],
    "uncertified": uncertified, "counterexamples": counterexamples,
    "minimum_certified_margin": {"lower_approx": float(minimum[0]),
                                  "n": minimum[1], "sigma": minimum[2],
                                  "exponents": minimum[3]},
    "windows": windows,
    "nonvacuity": nonvacuity,
    "nonclaim": "Not a kernel proof; decimal fields are display only."
}, indent=2))
