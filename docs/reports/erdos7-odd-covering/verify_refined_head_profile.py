#!/usr/bin/env python3
"""Exact survivor profiles with the first-ternary-fibre improvement.

The mathematical proof is in Problems/erdos-7-odd-covering-systems.md.
This program checks its rational arithmetic and exact infinite sums, then
independently brackets the final sums by a finite box and geometric tails.
It does not enumerate residue families or claim Lean certification.
Python 3.9+ standard library only; no optimization solver is used.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def subsets(s):
    for n in range(len(s) + 1):
        yield from combinations(s, n)


def envelope_sums(s, c, b):
    """c[T]/prod(p^e), b[T]/(3 prod(q^e)); b requires 3 in T."""
    cutoffs = {}
    for p in s:
        others = tuple(q for q in s if q != p)
        ratios = [c[tuple(sorted(t + (p,)))] / c[t]
                  for t in subsets(others)]
        if p == 3:
            ratios += [3 * c[t] / b[t] for t in b]
        else:
            ratios += [b[tuple(sorted(t + (p,)))] / b[t]
                       for t in subsets(others) if 3 in t]
        cutoff = 1 if p == 3 else 0
        while p ** (cutoff + 1) < max(ratios):
            cutoff += 1
        cutoffs[p] = cutoff

    mass = moment = F(0)
    # State cutoff+1 denotes the entire infinite tail.
    for states in product(*(range(cutoffs[p] + 2) for p in s)):
        high = tuple(p for p, e in zip(s, states) if e == cutoffs[p] + 1)
        low = tuple(p for p, e in zip(s, states) if 0 < e <= cutoffs[p])
        exponents = dict(zip(s, states))
        values = []
        for t in subsets(low):
            support = tuple(sorted(high + t))
            values.append(c[support] / prod(p ** exponents[p] for p in t))
            if 3 in t and 3 not in high:
                values.append(b[support] /
                              (3 * prod(p ** exponents[p] for p in t if p != 3)))
        value = min(values)
        r = k = value
        for p in high:
            cutoff = cutoffs[p]
            r *= F(1, p ** cutoff * (p - 1))
            k *= F((2 * cutoff + 3) * (p - 1) + 2,
                   p ** cutoff * (p - 1) ** 2)
        for p in low:
            k *= 2 * exponents[p] + 1
        mass += r
        moment += k
    return mass - 1, moment, cutoffs


def recurrence(primes):
    profiles = {(): ({(): F(1)}, {})}
    metrics = {(): (F(0), F(1), {})}
    deletion_bounds = {}
    for size in range(1, len(primes) + 1):
        for s in combinations(primes, size):
            candidates = []
            deletion_bounds[s] = {}
            for p in s:
                old = tuple(q for q in s if q != p)
                if old not in profiles:
                    continue
                deletion = metrics[old][0] / (p - 2)
                deletion_bounds[s][p] = deletion
                if deletion >= 1:
                    continue
                old_c, old_b = profiles[old]
                c, b = {(): F(1)}, {}
                for t in subsets(s):
                    if not t:
                        continue
                    previous = tuple(q for q in t if q != p)
                    factor = ((F(p - 1, p - 2) if p in t else F(1)) /
                              (1 - deletion))
                    c[t] = old_c[previous] * factor
                    if 3 in t:
                        b[t] = ((old_c[previous] if p == 3 else old_b[previous]) *
                                factor)
                candidates.append((c, b))
            if not candidates:
                continue
            c = {t: min(cc[t] for cc, _ in candidates) for t in subsets(s)}
            b = {t: min(bb[t] for _, bb in candidates)
                 for t in subsets(s) if 3 in t}
            if size == 2 and 3 in s:
                q = next(p for p in s if p != 3)
                # The same uniform survivor law has mod-3 mass at most
                # 2(q-2)/(3q-8); b stores three times that mass.
                b[(3,)] = min(b[(3,)], F(6 * (q - 2), 3 * q - 8))
            profiles[s] = c, b
            metrics[s] = envelope_sums(s, c, b)
    return profiles, metrics, deletion_bounds


def finite_box_bracket(primes, c, b, heights):
    """Independent finite enumeration plus ordinary-c upper tails.

    This does not use the cell cutoffs or tail factorization in envelope_sums.
    Every cylinder is evaluated directly over every applicable projection.
    Outside the finite box we discard all projection improvements and use
    only c[exact support]/prod(p^e). Exact support classes partition the tail.
    """
    r_lower = k_lower = F(0)
    for exponents in product(*(range(h + 1) for h in heights)):
        support = tuple(p for p, e in zip(primes, exponents) if e)
        exp = dict(zip(primes, exponents))
        value = F(1)
        for t in subsets(support):
            value = min(value, c[t] / prod(p ** exp[p] for p in t))
        if 3 in support:
            for t in subsets(support):
                if 3 in t:
                    value = min(value, b[t] /
                                (3 * prod(p ** exp[p] for p in t if p != 3)))
        r_lower += value
        k_lower += value * prod(2 * e + 1 for e in exponents)
    r_lower -= 1

    height = dict(zip(primes, heights))
    r_tail = k_tail = F(0)
    for support in subsets(primes):
        if not support:
            continue
        r_whole = prod(F(1, p - 1) for p in support)
        k_whole = prod(F(3 * p - 1, (p - 1) ** 2) for p in support)
        r_box = prod(sum((F(1, p ** e) for e in range(1, height[p] + 1)), F(0))
                     for p in support)
        k_box = prod(sum((F(2 * e + 1, p ** e)
                          for e in range(1, height[p] + 1)), F(0))
                     for p in support)
        r_tail += c[support] * (r_whole - r_box)
        k_tail += c[support] * (k_whole - k_box)
    return (r_lower, r_lower + r_tail), (k_lower, k_lower + k_tail)


def main():
    primes = (3, 5, 7, 11)
    profiles, metrics, deletions = recurrence(primes)
    require(len(profiles) == 16, "all four-prime subsets must have a profile")
    expected = {
        (3, 5): (F(33, 14), F(429, 28)),
        (3, 5, 7): (F(36903, 7585), F(336438, 7585)),
        primes: (F(7621078040639947, 773234757691590),
                 F(47039764798810808, 386617378845795)),
    }
    for s, bound in expected.items():
        require(metrics[s][:2] == bound, "displayed profile bound mismatch")
    for s, (c, b) in profiles.items():
        require(c[()] == 1, "unit cylinder cap must equal one")
        require(set(c) == set(subsets(s)), "ordinary profile support mismatch")
        require(set(b) == {t for t in subsets(s) if 3 in t},
                "first-ternary-fibre profile support mismatch")
        require(all(v > 0 for v in list(c.values()) + list(b.values())),
                "all cylinder coefficients must be positive")
        if s:
            require(any(v < 1 for v in deletions[s].values()),
                    "survivor normalization is not certified")

    c, b = profiles[primes]
    heights = (12, 8, 6, 5)
    r_bracket, k_bracket = finite_box_bracket(primes, c, b, heights)
    r, k, cutoffs = metrics[primes]
    require(r_bracket[0] <= r <= r_bracket[1], "R is outside independent bracket")
    require(k_bracket[0] <= k <= k_bracket[1], "K is outside independent bracket")
    require(k_bracket[1] < 122, "independent Gamma upper bound exceeds 122")
    require(r / 11 < F(89601, 100000), "prime-13 deletion bound mismatch")
    require(k < F(127225, 1000), "head exceeds the prime-73 continuation bridge")
    p, delta = 73, F(27, 100)
    a = F(3 * p - 1, (p - 1) ** 2)
    survivor_mass = 1 - k / (4 * delta * (1 - delta) * (p - 1) ** 2)
    continued_ratio = k * (1 + a / (1 - delta)) / survivor_mass
    require(survivor_mass == F(23954544135062588143, 24689540460044007018),
            "prime-73 survivor-mass lower bound mismatch")
    require(survivor_mass > 0, "prime-73 survivor mass is not positive")
    require(continued_ratio == F(15885128653558014915666, 119772720675312940715),
            "prime-73 continued ratio mismatch")
    require(continued_ratio < F(138877, 1000),
            "prime-73 continued ratio exceeds the tail seed")
    print(json.dumps({
        "prime_support": primes,
        "cylinder_sum_bound": str(r),
        "Gamma_bound": str(k),
        "Gamma_bound_decimal": float(k),
        "first_ternary_fibre_cap_for_3_5": "6/7",
        "cutoffs": cutoffs,
        "profile": {"*".join(map(str, t)) or "1": str(v) for t, v in c.items()},
        "first_ternary_fibre_profile": {
            "*".join(map(str, t)): str(v) for t, v in b.items()},
        "last_prime_deletion_bounds": {str(p): str(v)
                                       for p, v in deletions[primes].items()},
        "prime_13_deletion_bound": str(r / 11),
        "prime_73_bridge": {
            "delta": str(delta),
            "survivor_mass_lower_bound": str(survivor_mass),
            "continued_ratio_upper_bound": str(continued_ratio),
            "continued_ratio_decimal": float(continued_ratio),
            "tail_seed": "138877/1000",
        },
        "independent_finite_box": {
            "heights": heights,
            "R_interval": list(map(str, r_bracket)),
            "K_interval": list(map(str, k_bracket)),
            "K_interval_decimal": list(map(float, k_bracket)),
        },
        "scope": "Exact profile arithmetic and infinite geometric sums, "
                 "independently bracketed by a finite box. The accompanying "
                 "proof establishes uniformity over residue choices and "
                 "finite heights. No Lean formalization is claimed.",
    }, indent=2))


if __name__ == "__main__":
    main()
