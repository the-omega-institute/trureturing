#!/usr/bin/env python3
"""Exact survivor profiles with coupled two-root budgets.

The mathematical proof is in Problems/erdos-7-odd-covering-systems.md.
This program checks its rational arithmetic and exact infinite sums, then
independently brackets the final sums by a finite box and geometric tails.
It does not enumerate residue families or claim Lean certification.
Python 3.9+ standard library only; no optimization solver is used.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
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


def joint_pair_bounds(q):
    """The two-root rational bound, including an absent-modulus-3 branch.

    With modulus 3 present, w and v are the surviving fractions inside the
    two remaining roots after pure higher ternary exclusions. Their triangle
    has vertices (1/2,1), (1,1/2), (1,1). First-ternary mixed deletions alpha,
    beta occupy a triangle with vertices (0,0), (y,0), (0,y). The pure-q
    survivor density z lies in [1-y,1]. Higher mixed deletions are bounded by
    y/6 and, for this upper bound, assigned entirely to the other root.

    Both objectives are linear-fractional in each of the three blocks, with
    a positive denominator throughout. Their maxima occur among 18 vertices.
    The proof of this reduction and its probability interpretation is in
    the dossier. These combined bounds need not equal the envelope sums.
    """
    y = F(1, q - 1)
    a = F(3 * q - 1, (q - 1) ** 2)
    r_values, k_values, denominators = [], [], []
    for (w, v), (alpha, beta), z in product(
            ((F(1, 2), F(1)), (F(1), F(1, 2)), (F(1), F(1))),
            ((F(0), F(0)), (y, F(0)), (F(0), y)),
            (1 - y, F(1))):
        x = (w + v) / 3
        n = w * (z - alpha) / 3
        denominator = n + v * (z - beta) / 3 - y / 6
        require(denominator > 0, "joint two-root denominator is not positive")
        denominators.append(denominator)
        r_values.append((n + z / 6 + x * y + y / 2) / denominator)
        k_values.append(1 + (3 * n + z + a * x + 2 * a) / denominator)

    # Without a pure modulus-3 class, the pure ternary density is >=5/6.
    # The raw two-prime bounds decrease in x and z, so use their minima.
    x, z = F(5, 6), 1 - y
    absent_denominator = x * z - y / 2
    require(absent_denominator > 0, "absent-modulus-3 denominator is not positive")
    absent_r = (z / 2 + x * y + y / 2) / absent_denominator
    absent_k = 1 + (2 * z + a * x + 2 * a) / absent_denominator
    r_bound, k_bound = max(r_values + [absent_r]), max(k_values + [absent_k])
    return r_bound, k_bound, {
        "vertex_count": len(r_values),
        "minimum_vertex_denominator": str(min(denominators)),
        "present_modulus_3_R_bound": str(max(r_values)),
        "present_modulus_3_K_bound": str(max(k_values)),
        "absent_modulus_3_R_bound": str(absent_r),
        "absent_modulus_3_K_bound": str(absent_k),
    }


def recurrence(primes, use_joint_budget=True):
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
            r, k, cutoffs = envelope_sums(s, c, b)
            if use_joint_budget and size == 2 and 3 in s:
                q = next(p for p in s if p != 3)
                joint_r, joint_k, _ = joint_pair_bounds(q)
                r, k = min(r, joint_r), min(k, joint_k)
            metrics[s] = r, k, cutoffs
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
        (3, 5): (F(13, 6), F(59, 4)),
        (3, 5, 7): (F(9937, 2142), F(179315, 4284)),
        primes: (F(1200449891, 129232735), F(28643873521, 258465470)),
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

    _, baseline_metrics, _ = recurrence(primes, use_joint_budget=False)
    for s, bounds in {
            (3, 5): (F(33, 14), F(429, 28)),
            (3, 5, 7): (F(36903, 7585), F(336438, 7585)),
            primes: (F(7621078040639947, 773234757691590),
                     F(47039764798810808, 386617378845795)),
    }.items():
        require(baseline_metrics[s][:2] == bounds, "first-ternary-fibre baseline changed")
    joint_results = {}
    for q, expected_pair in {
            5: (F(13, 6), F(59, 4)),
            7: (F(21, 13), F(29, 3)),
            11: (F(33, 25), F(29, 4)),
    }.items():
        joint_r, joint_k, detail = joint_pair_bounds(q)
        require((joint_r, joint_k) == expected_pair, "joint vertex bound mismatch")
        pair_c, pair_b = profiles[(3, q)]
        raw_r, raw_k, _ = envelope_sums((3, q), pair_c, pair_b)
        joint_results[str(q)] = {
            "combined_R_bound": str(metrics[(3, q)][0]),
            "combined_K_bound": str(metrics[(3, q)][1]),
            "raw_envelope_R": str(raw_r),
            "raw_envelope_K": str(raw_k),
            **detail,
        }

    c, b = profiles[primes]
    heights = (12, 8, 6, 5)
    r_bracket, k_bracket = finite_box_bracket(primes, c, b, heights)
    r, k, cutoffs = metrics[primes]
    raw_r, raw_k, _ = envelope_sums(primes, c, b)
    require(r == raw_r and k == raw_k,
            "the four-prime metric should equal its raw profile envelope")
    require(r_bracket[0] <= raw_r <= r_bracket[1],
            "raw R is outside independent bracket")
    require(k_bracket[0] <= raw_k <= k_bracket[1],
            "raw K is outside independent bracket")
    require(k_bracket[1] < 111, "independent Gamma upper bound exceeds 111")
    require(r / 11 < F(845, 1000), "prime-13 deletion bound mismatch")
    continued_ratio = k
    bridge = []
    for p, delta in ((71, F(53, 200)), (73, F(27, 100))):
        a = F(3 * p - 1, (p - 1) ** 2)
        survivor_fraction = 1 - continued_ratio / (
            4 * delta * (1 - delta) * (p - 1) ** 2)
        require(survivor_fraction > 0, "continuation survivor fraction is not positive")
        continued_ratio *= (1 + a / (1 - delta)) / survivor_fraction
        bridge.append({
            "prime": p,
            "delta": str(delta),
            "survivor_fraction_lower_bound": str(survivor_fraction),
            "continued_ratio_upper_bound": str(continued_ratio),
            "continued_ratio_decimal": float(continued_ratio),
        })
    require(continued_ratio < F(138877, 1000),
            "two-prime continued ratio exceeds the tail seed")
    print(json.dumps({
        "prime_support": primes,
        "cylinder_sum_bound": str(r),
        "Gamma_bound": str(k),
        "Gamma_bound_decimal": float(k),
        "baseline_Gamma_without_joint_budget": str(baseline_metrics[primes][1]),
        "two_root_joint_bounds": joint_results,
        "first_ternary_fibre_cap_for_3_5": "6/7",
        "cutoffs": cutoffs,
        "profile": {"*".join(map(str, t)) or "1": str(v) for t, v in c.items()},
        "first_ternary_fibre_profile": {
            "*".join(map(str, t)): str(v) for t, v in b.items()},
        "last_prime_deletion_bounds": {str(p): str(v)
                                       for p, v in deletions[primes].items()},
        "prime_13_deletion_bound": str(r / 11),
        "prime_71_73_bridge": {
            "steps": bridge,
            "tail_seed": "138877/1000",
        },
        "independent_finite_box": {
            "checks": "raw profile envelope; combined two-root metrics are separate",
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
