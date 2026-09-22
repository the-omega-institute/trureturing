#!/usr/bin/env python3
"""Exact controls for free-coordinate Gamma completion and the H1 scalar barrier.

No repository imports, solver, floating point, or claimed Lean certification.
The all-parameter proofs are in the accompanying report; these controls check
independent divisor/center formulas and the explicit rational H1 boundary.
"""

from fractions import Fraction as F
from math import gcd, isqrt, lcm
import argparse
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def factors(n):
    result = []
    p = 2
    while p * p <= n:
        h = 0
        while n % p == 0:
            n //= p
            h += 1
        if h:
            result.append((p, h))
        p += 1
    if n > 1:
        result.append((n, 1))
    return result


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def prime_factor(p, h):
    return 1 + sum((F(2 * j + 1, p**j) for j in range(1, h + 1)), F())


def factor_product(n):
    result = F(1)
    for p, h in factors(n):
        result *= prime_factor(p, h)
    return result


def divisor_factor(n):
    ds = divisors(n)
    return sum((F(1, lcm(a, b)) for a in ds for b in ds), F())


def center_controls(n):
    ds = divisors(n)
    target = divisor_factor(n)
    require(target == factor_product(n), "divisor/product factor disagreement")
    numerators = []
    for y in range(n):
        total = 0
        for center in range(n):
            load = sum((y - center) % d == 0 for d in ds)
            total += load * load
        require(F(total, n) == target, "center average not pointwise constant")
        numerators.append(total)
    require(len(set(numerators)) == 1, "center numerator varies with point")
    return {"M": n, "divisors": ds, "F": str(target),
            "center_pairs_checked": n * n,
            "common_sum_of_center_squares": numerators[0]}


def sqrt_bounds(q, scale=10**12):
    a = isqrt(q.numerator * scale * scale // q.denominator)
    lo, hi = F(a, scale), F(a + 1, scale)
    require(lo * lo <= q < hi * hi, "invalid exact square-root enclosure")
    return lo, hi


def h1_lambdas(c, root):
    return (c - 1) / 32 + root / 12 + (c - 1) / 840


def h1_controls():
    lower_c, upper_c = F(68, 15), F(46, 9)
    # On 1<=C<=D^2, (C-1)/(D^2-1)<=C/D^2<=sqrt(C)/D.
    # On C>=D^2, sqrt(C)/D is minimal: putting t=sqrt(C),
    # D(t^2-1)-(D^2-1)t=(t-D)(Dt+1)>=0.
    require(1 <= lower_c <= upper_c <= 3**2 <= 6**2,
            "third H2 entry is not valid over the whole D=3,6 interval")
    require(2**2 <= lower_c, "sqrt H2 entry is not valid over the D=2 interval")
    require(F(1, 32) + F(1, 840) == F(109, 3360), "lambda simplification")
    b5 = 1 + F(2, 3) * F(1, 4) + F(1, 9) * F(6, 16)
    b7 = 1 + F(1, 6) + F(1, 4) * F(8, 36)
    b = b5 * b7
    require((b5, b7, b) == (F(29, 24), F(11, 9), F(319, 216)), "B constants")
    root_lower = F(17, 8)
    root_upper = F(7, 3)
    require(lower_c - root_lower**2 == F(17, 960), "strict sqrt lower margin")
    require(upper_c < root_upper**2, "global sqrt upper")
    lambda_upper = h1_lambdas(upper_c, root_upper)
    require(lambda_upper == F(9913, 30240) < 1, "positive H1 denominator over interval")
    lambda_lower = h1_lambdas(lower_c, root_lower)
    margin_lower = lower_c * b + 8 * lambda_lower - 9
    require(margin_lower == F(407, 14175) > 0, "infinite-height strict barrier")

    # Explicit finite-height obstruction: four extra levels in each coordinate.
    n = 4
    u5 = sum((F(1, 5**j) for j in range(1, n + 1)), F())
    u7 = sum((F(1, 7**j) for j in range(1, n + 1)), F())
    v5 = sum((F(2 * j - 1, 5**j) for j in range(1, n + 1)), F())
    v7 = sum((F(2 * j - 1, 7**j) for j in range(1, n + 1)), F())
    finite_b = (1 + F(2, 3) * u5 + F(1, 9) * v5) * (1 + u7 + v7 / 4)
    finite_lambda_lower = (u5 * (lower_c - 1) / 8 + u7 * root_lower / 2
                           + u5 * u7 * (lower_c - 1) / 35)
    finite_margin = lower_c * finite_b + 8 * finite_lambda_lower - 9
    require(finite_b == F(2214518, 1500625), "finite B")
    require(finite_lambda_lower == F(30614733, 105043750), "finite lambda lower")
    require(finite_margin == F(3396739, 157565625) > 0, "finite-height strict barrier")

    enclosures = []
    for c in (lower_c, F(149, 30), upper_c):
        lo, hi = sqrt_bounds(c)
        lam_lo, lam_hi = h1_lambdas(c, lo), h1_lambdas(c, hi)
        require(lam_hi < 1, "H1 denominator")
        value_lo = (c * b - lam_lo) / (1 - lam_lo)
        value_hi = (c * b - lam_hi) / (1 - lam_hi)
        require(value_hi > value_lo > 9, "exact J enclosure")
        enclosures.append({"C": str(c), "sqrt_interval": [str(lo), str(hi)],
                           "lambda_interval": [str(lam_lo), str(lam_hi)],
                           "H1_interval": [str(value_lo), str(value_hi)]})

    c = F(149, 30)
    one_lambda = (c - 1) / 32
    one_value = (c * b5 - one_lambda) / (1 - one_lambda)
    require(one_value == F(16927, 2523) < 9, "one-axis comparison")
    return {"coarse_exponents": {"5": 2, "7": 1},
            "C_domain": [str(lower_c), str(upper_c)],
            "H2_minimizers": {"D3": "(C-1)/8", "D2": "sqrt(C)/2", "D6": "(C-1)/35"},
            "B5": str(b5), "B7": str(b7), "B": str(b),
            "global_lambda_strict_upper": str(lambda_upper),
            "sqrt68over15_lower": str(root_lower), "squared_margin": str(F(17, 960)),
            "infinite_threshold_excess_strict_lower": str(margin_lower),
            "finite_witness": {"final_exponents": {"5": 6, "7": 5},
                "u5": str(u5), "u7": str(u7), "v5": str(v5), "v7": str(v7),
                "B": str(finite_b), "lambda_strict_lower": str(finite_lambda_lower),
                "threshold_excess_strict_lower": str(finite_margin)},
            "exact_H1_enclosures": enclosures,
            "only_five_height_extension_at_149over30": str(one_value)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional exact JSON result path")
    args = parser.parse_args()
    centers = [center_controls(m) for m in (1, 3, 5, 9, 15, 25, 35, 175)]
    coprime_products = []
    for q, m in ((2, 15), (3, 25), (5, 49), (9, 35), (25, 7)):
        require(gcd(q, m) == 1, "CRT coprimality")
        actual = divisor_factor(q * m)
        require(actual == divisor_factor(q) * divisor_factor(m), "coprime F multiplicativity")
        coprime_products.append({"Q": q, "M": m, "F_QM": str(actual)})
    outside_primes = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)
    full_floor = F(1)
    squarefree_b = 1
    for p in outside_primes:
        require(p >= 2 and all(p % d for d in range(2, isqrt(p) + 1)), "prime list")
        squarefree_b *= p
        full_floor *= 1 + F(3, p)
    require(full_floor == F(25836912640000, 2775498881101), "full inventory floor")
    require(full_floor - 9 == F(857422710091, 2775498881101) > 0,
            "nine cannot bound every full prime inventory")
    result = {
        "scope": "Exact controls accompanying ordinary general proofs; no Lean, arbitrary-source theorem, or actual minimum-cover realization claimed.",
        "center_controls": centers, "coprime_factor_controls": coprime_products,
        "all_probability_full_inventory_floor": {"primes": outside_primes,
            "squarefree_B": squarefree_b, "F_B": str(full_floor),
            "F_B_minus_nine": str(full_floor - 9),
            "scope": "Unavoidable complete-layout cost for every law, not a covering counterexample."},
        "H1_scalar_barrier": h1_controls(),
    }
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as stream:
            stream.write(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
