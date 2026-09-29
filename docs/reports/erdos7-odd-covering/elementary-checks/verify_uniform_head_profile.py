#!/usr/bin/env python3
"""Exact support-profile recurrence for uniform congruence survivors.

No residue search or optimization solver is used. All bounds are rational;
the infinite projection-envelope sums are evaluated by exact geometric tails.
The proof is in Problems/erdos-7-odd-covering-systems.md. This program
verifies profile arithmetic, not the universal congruence argument or Lean
formalization. Python 3.9+ standard library only.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parents[1]
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
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


def envelope_sums(s, coefficients):
    """Return R=sum(nonunit envelopes), K=sum(pair weights * envelopes)."""
    cutoffs = {}
    for p in s:
        others = tuple(q for q in s if q != p)
        ratio = max(
            coefficients[tuple(sorted(t + (p,)))] / coefficients[t]
            for t in subsets(others)
        )
        cutoff = 0
        while p ** (cutoff + 1) < ratio:
            cutoff += 1
        cutoffs[p] = cutoff

    mass = moment = F(0)
    # State cutoff+1 denotes the entire infinite tail, not one exponent.
    for states in product(*(range(cutoffs[p] + 2) for p in s)):
        high = tuple(p for p, a in zip(s, states) if a == cutoffs[p] + 1)
        low = tuple(p for p, a in zip(s, states) if 0 < a <= cutoffs[p])
        exponents = dict(zip(s, states))
        value = min(
            coefficients[tuple(sorted(high + t))]
            / prod(p ** exponents[p] for p in t)
            for t in subsets(low)
        )
        r = k = value
        for p in high:
            cutoff = cutoffs[p]
            r *= F(1, p**cutoff * (p - 1))
            k *= F((2 * cutoff + 3) * (p - 1) + 2,
                   p**cutoff * (p - 1) ** 2)
        for p in low:
            k *= 2 * exponents[p] + 1
        mass += r
        moment += k
    return mass - 1, moment


def recurrence(primes):
    profiles = {(): {(): F(1)}}
    metrics = {(): (F(0), F(1))}
    deletion_bounds = {}
    for size in range(1, len(primes) + 1):
        for s in combinations(primes, size):
            candidates = []
            bounds = {}
            for p in s:
                old = tuple(q for q in s if q != p)
                if old not in profiles:
                    continue
                deletion = metrics[old][0] / F(p - 2)
                bounds[p] = deletion
                if deletion >= 1:
                    continue
                candidate = {(): F(1)}
                for t in subsets(s):
                    if t:
                        previous = tuple(q for q in t if q != p)
                        pure_factor = F(p - 1, p - 2) if p in t else F(1)
                        candidate[t] = profiles[old][previous] * pure_factor / (1 - deletion)
                candidates.append(candidate)
            deletion_bounds[s] = bounds
            if candidates:
                profiles[s] = {
                    t: min(candidate[t] for candidate in candidates)
                    for t in subsets(s)
                }
                metrics[s] = envelope_sums(s, profiles[s])
    return profiles, metrics, deletion_bounds


def pure_source_reserves(primes, profiles, metrics):
    """Lower masses under the actual product of pure-coordinate survivors."""
    reserve = {(): F(1)}
    for size in range(1, len(primes) + 1):
        for s in combinations(primes, size):
            candidates = []
            for p in s:
                old = tuple(q for q in s if q != p)
                if old not in reserve:
                    continue
                deletion = metrics[old][0] / (p - 2)
                if deletion < 1:
                    candidates.append(reserve[old] * (1 - deletion))
            if candidates:
                reserve[s] = max(candidates)
                require(reserve[s] * profiles[s][s]
                        == prod(F(p - 1, p - 2) for p in s),
                        "pure-source reserve/full-profile identity")
    return reserve


def complete_product_hinge(primes, threshold):
    """Use exact atoms below the threshold and the full infinite mean."""
    atoms = {1: F(1)}
    for p in primes:
        cap = F(p - 1, p - 2)
        new = {}
        for m, probability in atoms.items():
            for factor in range(1, (threshold - 1) // m + 1):
                mass = (1 - cap / p if factor == 1
                        else cap * F(p - 1, p**factor))
                new[m * factor] = new.get(m * factor, F(0)) + probability * mass
        atoms = new
    mean = prod(1 + F(1, p - 2) for p in primes)
    return mean - threshold + sum((threshold - m) * a for m, a in atoms.items())


def missing_seven_marginal_certificate():
    """MF10--MF14: one common query law excludes omission of seven."""
    primes = (3, 5, 11, 13, 17, 19, 23, 29)
    profiles, metrics, _ = recurrence(primes)
    reserve = pure_source_reserves(primes, profiles, metrics)
    require(len(profiles) == len(reserve) == 256,
            "every eight-prime subset needs both profile and reserve")
    hinge = complete_product_hinge(primes, 16)
    require(hinge == complete_product_hinge(tuple(reversed(primes)), 16),
            "independent-coordinate hinge convolution disagrees")
    require(reserve[primes] > F(2, 125), "MF11 reserve lower bound")
    require(hinge < F(21, 125), "MF13 complete hinge bound")
    require(15 + hinge / reserve[primes] < F(51, 2), "MF10 query bound")
    require(F(53, 2) / 30 == F(53, 60) < 1, "MF14 deficient marginal")
    return {
        "cofactor_primes": primes,
        "all_subsets_admissible": True,
        "subset_count": len(profiles),
        "pure_source_reserve_decimal": float(reserve[primes]),
        "pure_source_reserve_strict_lower": "2/125",
        "complete_hinge_threshold": 16,
        "complete_hinge_exact": str(hinge),
        "complete_hinge_strict_upper": "21/125",
        "query_strict_upper": "51/2",
        "complete_marginal_strict_upper": "53/60",
    }


def main():
    primes = (3, 5, 7, 11)
    profiles, metrics, deletions = recurrence(primes)
    require(len(profiles) == 16, "all four-prime subsets must have a profile")
    expected = {
        (3, 5): (F(5, 2), F(63, 4)),
        (3, 5, 7): (F(77, 15), F(237, 5)),
        primes: (F(1514, 145), F(3885, 29)),
    }
    for s, bound in expected.items():
        require(metrics[s] == bound, "displayed profile bound mismatch")
    for s, coefficients in profiles.items():
        require(coefficients[()] == 1, "unit cylinder cap must equal one")
        require(all(v > 0 for v in coefficients.values()),
                "all cylinder coefficients must be positive")
        if s:
            require(any(v < 1 for v in deletions[s].values()),
                    "survivor normalization is not certified")
    require(metrics[primes][1] < F(138877, 1000),
            "head bound exceeds the continuation seed")

    # MF3 in Library/Arith/lettlsun2008cosets.md.  Each row excludes every
    # ordered six-prime support dominating its listed support.  These are
    # five-prime complete-survivor profiles, not residue enumerations.
    marginal_cases = (
        ((3, 5, 11, 13, 17, 19), 3, F(58495, 63454)),
        ((3, 5, 7, 11, 19, 23), 23, F(11159716533087, 534598681841)),
        ((3, 5, 7, 11, 17, 29), 29, F(1652775682537, 66859985411)),
        ((3, 5, 7, 13, 17, 23), 23, F(507203988220491, 29060939613244)),
        ((3, 5, 7, 11, 13, 73), 73, F(814972792, 11609325)),
    )
    marginal_bounds = []
    for support, target, expected_r in marginal_cases:
        cofactor = tuple(p for p in support if p != target)
        five_profiles, five_metrics, five_deletions = recurrence(cofactor)
        require(len(five_profiles) == 32,
                "every five-prime cofactor subset needs a profile")
        for subset, coefficients in five_profiles.items():
            require(coefficients[()] == 1 and all(v > 0 for v in coefficients.values()),
                    "invalid cofactor cylinder profile")
            if subset:
                require(any(v < 1 for v in five_deletions[subset].values()),
                        "cofactor survivor normalization is not certified")
        actual_r = five_metrics[cofactor][0]
        require(actual_r == expected_r, "six-prime exclusion parameter mismatch")
        ceiling = (1 + actual_r) / (target - 1)
        require(ceiling < 1, "complete marginal exclusion must be strict")
        marginal_bounds.append({
            "ordered_support": support,
            "target_prime": target,
            "cofactor_cylinder_sum_bound": str(actual_r),
            "complete_marginal_ceiling": str(ceiling),
            "all_cofactor_subsets_admissible": True,
        })
    print(json.dumps({
        "prime_support": primes,
        "cylinder_sum_bound": str(metrics[primes][0]),
        "Gamma_bound": str(metrics[primes][1]),
        "continuation_seed": "138877/1000",
        "all_subsets_admissible": True,
        "profile": {"*".join(map(str, t)) or "1": str(v)
                    for t, v in profiles[primes].items()},
        "last_prime_deletion_bounds": {str(p): str(b)
                                       for p, b in deletions[primes].items()},
        "six_prime_marginal_exclusions": marginal_bounds,
        "missing_seven_marginal_exclusion": missing_seven_marginal_certificate(),
        "scope": "Exact profile recurrence and infinite geometric sums. "
                 "Uniformity in residues and finite heights is established "
                 "by the accompanying mathematical proof, not by enumeration. "
                 "No Lean formalization is claimed."
    }, indent=2))


if __name__ == "__main__":
    main()
