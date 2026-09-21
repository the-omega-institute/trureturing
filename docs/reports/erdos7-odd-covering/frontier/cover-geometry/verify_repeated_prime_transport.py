#!/usr/bin/env python3
"""Check exact original-label transport, all-height potentials, and SRCT data.

Standard-library direct residue counting; no external SRCT code is imported.
The universal statements and limitations are in problem-details/75. These
finite checks are regressions, not a proof of the unrestricted odd-covering
conjecture. Run with python3 -I -O; require remains active under optimization.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json
from math import gcd, isqrt, prod
from random import Random


CHECKS = 0


def require(condition, message):
    global CHECKS
    if not condition:
        raise ValueError(message)
    CHECKS += 1


def divisors(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)


def valuation(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def capacities(points, labels):
    return {d: max(Counter(x % d for x in points).values(), default=0)
            for d in labels}


def deficit(points, caps, excluded):
    return len(points) - sum(c for d, c in caps.items() if d not in excluded)


def top(caps, period, primes):
    return sum(c for d, c in caps.items()
               if all(valuation(d, p) == valuation(period, p) for p in primes))


def penalty(caps, period, primes, heights=None):
    value = Fraction(0)
    for count in range(1, len(primes) + 1):
        for subset in combinations(primes, count):
            weight = prod(Fraction(1, p - 1) if heights is None else
                          Fraction(1 - Fraction(1, p ** heights[p]), p - 1)
                          for p in subset)
            value += weight * top(caps, period, subset)
    return value


def direct_transport_checks():
    rng = Random(729413)
    cases = 0
    for base, p, support in ((15, 3, 7), (45, 3, 7), (15, 5, 7),
                             (75, 5, 7), (9, 3, 35)):
        labels = divisors(base)
        support_primes = tuple(r for r in divisors(support) if r > 1
                               and all(r % z for z in range(2, r)))
        support_points = {x for x in range(support) if gcd(x, support) == 1}
        h = len(support_points)
        sigma = sum(h // (r - 1) for r in support_primes)
        for _ in range(8):
            parent = {x for x in range(base) if rng.randrange(3) > 0}
            excluded = {1} | {d for d in labels if rng.randrange(4) == 0}
            choices = [d for d in labels if d not in excluded]
            if not choices:
                continue
            q = rng.choice(choices)
            residue = rng.randrange(q)
            child = {x for x in parent if x % q != residue}
            before = capacities(parent, labels)
            after = capacities(child, labels)
            dp = deficit(parent, before, excluded)
            dc = deficit(child, after, excluded | {q})
            tp, tc = top(before, base, (p,)), top(after, base, (p,))
            dqp = h * dp - (support - h) * sum(before.values()) + sigma * len(parent)
            dqc = h * dc - (support - h) * sum(after.values()) + sigma * len(child)
            for height in range(3):
                scale = p ** height
                beta = (scale - 1) // (p - 1)
                period = base * scale
                up = {x for x in range(period) if x % base in parent}
                uc = {x for x in range(period) if x % base in child}
                cp = capacities(up, divisors(period))
                cc = capacities(uc, divisors(period))
                require(sum(cp.values()) == scale * sum(before.values()) + beta * tp,
                        "exact one-prime raw sum")
                require(deficit(up, cp, excluded) == scale * dp - beta * tp,
                        "exact one-prime deficit")
                require(deficit(uc, cc, excluded | {q}) - deficit(up, cp, excluded)
                        == scale * (dc - dp) + beta * (tp - tc), "exact TAKE gain")
                sp = {x for x in range(period * support)
                      if x % period in up and x % support in support_points}
                sc = {x for x in range(period * support)
                      if x % period in uc and x % support in support_points}
                csp = capacities(sp, divisors(period * support))
                csc = capacities(sc, divisors(period * support))
                ep = excluded | set(support_primes)
                require(deficit(sp, csp, ep) == scale * dqp - support * beta * tp,
                        "exact CRT support deficit")
                require(deficit(sc, csc, ep | {q}) - deficit(sp, csp, ep)
                        == scale * (dqc - dqp) + support * beta * (tp - tc),
                        "exact CRT support TAKE gain")
                cases += 1
    return cases


def simultaneous_transport_checks():
    rng = Random(104729)
    cases = 0
    for base, primes in ((15, (3, 5)), (45, (3, 5))):
        labels = divisors(base)
        for _ in range(8):
            parent = {x for x in range(base) if rng.randrange(3) > 0}
            excluded = {1}
            q = rng.choice(labels[1:])
            residue = rng.randrange(q)
            child = {x for x in parent if x % q != residue}
            before = capacities(parent, labels)
            after = capacities(child, labels)
            dp = deficit(parent, before, excluded)
            dc = deficit(child, after, excluded | {q})
            jp = dp - penalty(before, base, primes)
            jc = dc - penalty(after, base, primes)
            require(jc >= jp, "limiting potential is nondecreasing under actual TAKE")
            for depths in product(range(3), repeat=len(primes)):
                heights = dict(zip(primes, depths))
                scale = prod(p ** heights[p] for p in primes)
                period = base * scale
                lifted = {x for x in range(period) if x % base in parent}
                actual = capacities(lifted, divisors(period))
                d = deficit(lifted, actual, excluded)
                require(Fraction(d, scale) == dp - penalty(before, base, primes, heights),
                        "simultaneous finite-depth identity")
                require((d - penalty(actual, period, primes)) / scale == jp,
                        "normalized limiting potential is refinement invariant")
                cases += 1
    return cases


def srct_initial_state():
    base = 51975
    primes = (3, 5, 7, 11)
    excluded = {1, 3, 5, 7, 9, 11}
    parent = {x for x in range(base)
              if all(x % p for p in primes) and x % 9 not in (1, 2)}
    labels = divisors(base)
    before = capacities(parent, labels)
    d = deficit(parent, before, excluded)
    t = top(before, base, (3,))
    require((len(parent), sum(before.values()), d, t) == (14400, 44044, 2996, 2002),
            "actual SRCT initial state")
    j3 = d - Fraction(t, 2)
    j4 = d - penalty(before, base, primes)
    require(j3 == 1995 and j4 == Fraction(1785, 32), "positive four-prime potentials")
    support = 221
    h = 192
    sigma = 28
    dq = h * d - (support - h) * sum(before.values()) + sigma * len(parent)
    j_support3 = dq - support * Fraction(t, 2)
    j_support4 = dq - support * penalty(before, base, primes)
    require(dq == -298844 and j_support3 == -520065
            and j_support4 == Fraction(-30356235, 32), "negative fixed-support potentials")
    # CRT with actual nonzero residues at 13 and 17, then extend all six primes.
    support_caps = {1: 192, 13: 16, 17: 12, 221: 1}
    full_caps = {d0 * e: c * support_caps[e] for d0, c in before.items()
                 for e in support_caps}
    require(len(full_caps) == len(before) * len(support_caps), "original labels unique")
    j6 = dq - penalty(full_caps, base * support, primes + (13, 17))
    require(j6 == Fraction(-2157798825, 2048), "all six prime heights retain negative limit")
    old_s = (sum(before.values()) + penalty(before, base, primes)) / base
    old_phi = j4 / base
    support_factor = prod(1 + Fraction(q, (q - 1) ** 2) for q in (13, 17))
    fresh_formula = Fraction(h, support) * (
        old_phi - (support_factor - 1) * old_s
        + Fraction(len(parent), base) * sum(Fraction(1, q - 1) for q in (13, 17)))
    require(fresh_formula == j6 / (base * support), "fresh-prime all-height formula")
    children = []
    for q, residue, expected_j3, expected_supported in (
            (15, 1, 2025, -497715), (27, 4, 2177, -460663)):
        child = {x for x in parent if x % q != residue}
        after = capacities(child, labels)
        dc = deficit(child, after, excluded | {q})
        tc = top(after, base, (3,))
        dcq = h * dc - (support - h) * sum(after.values()) + sigma * len(child)
        require(t - tc == 0, "positive mass removal can have zero top-label capacity drop")
        require(dc - Fraction(tc, 2) == expected_j3
                and dcq - support * Fraction(tc, 2) == expected_supported,
                "actual child limiting potentials")
        children.append({"modulus": q, "residue": residue,
                         "top3_drop": t - tc, "J3": str(expected_j3),
                         "supported_J3": str(expected_supported)})
    return {"base_period": base, "J3": str(j3), "J_four_old_primes": str(j4),
            "supported_D0": str(dq), "supported_J3": str(j_support3),
            "supported_J_four_old_primes": str(j_support4),
            "supported_J_all_six_primes": str(j6), "children": children}


def fresh_prime_barrier_check():
    # The fixed seed has only the allowed prime 1229, no used nonunit label,
    # and full residual mass. The genuinely fresh primes below 1229 suffice.
    primes = tuple(q for q in range(3, 1229, 2)
                   if all(q % d for d in range(3, isqrt(q) + 1, 2)))
    require(len(primes) == 199 and primes[-1] == 1223, "fresh-prime witness set")
    require(all(1229 % d for d in range(2, 36)), "seed prime is prime")
    y = sum(Fraction(1, q - 1) for q in primes)
    f = prod(1 + Fraction(q, (q - 1) ** 2) for q in primes)
    h = prod(Fraction(q - 1, q) for q in primes)
    pair_bound = (y * y - y / 2) / 2
    require(y >= 2, "fresh-prime reciprocal budget reaches two")
    require(f >= 1 + y + pair_bound and pair_bound >= Fraction(3, 2),
            "quadratic elementary-product lower bound")
    a = Fraction(1)
    raw_s = Fraction(1229, 1228)
    phi = 2 - raw_s
    transformed = h * (phi - (f - 1) * raw_s + a * y)
    require(phi > 0 and transformed <= -h * a / 2 < 0,
            "fresh zero-root classes destroy a positive potential")
    require(h > 0, "actual residual product retains strictly positive Haar mass")
    return {"seed_prime": 1229, "fresh_prime_count": len(primes),
            "last_fresh_prime": primes[-1], "Y_at_least_two": True,
            "initial_potential_positive": True, "final_potential_negative": True,
            "actual_residual_measure_positive": True}


def main():
    one_prime = direct_transport_checks()
    simultaneous = simultaneous_transport_checks()
    actual = srct_initial_state()
    barrier = fresh_prime_barrier_check()
    print(json.dumps({"schema": "exact-repeated-prime-transport-v1", "status": "PASS",
                      "checks": CHECKS, "one_prime_cases": one_prime,
                      "simultaneous_height_cases": simultaneous, "srct": actual,
                      "fresh_prime_barrier": barrier,
                      "scope": "Exact finite regressions and actual SRCT readings; "
                               "no Lean certification or unrestricted E7 conclusion."},
                     indent=2))


if __name__ == "__main__":
    main()
