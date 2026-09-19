#!/usr/bin/env python3
"""Verify the actual-layout lcm-block certificate with exact rationals.

Python 3.9+ standard library only; no solver, network, or external imports.
The accompanying proof supplies the complete-survivor inputs R35, R357,
Gamma35 and the profile recurrence. This verifier checks that recurrence,
the outside-coordinate factorization, every infinite support-mode sum,
the improved four-prime head, and the fixed prime-67/71/73 continuation.
It verifies the rational certificate, not a Lean formalization of the proof.
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
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)

def subsets(s):
    for n in range(len(s) + 1):
        yield from combinations(s, n)

def envelope_sums(primes, c, b):
    """Exact R and K from ordinary and first-ternary-projection coefficients."""
    cutoffs = {}
    for p in primes:
        others = tuple(q for q in primes if q != p)
        ratios = [c[tuple(sorted(t + (p,)))] / c[t] for t in subsets(others)]
        if p == 3:
            ratios += [3 * c[t] / b[t] for t in b]
        else:
            ratios += [b[tuple(sorted(t + (p,)))] / b[t]
                       for t in subsets(others) if 3 in t]
        cutoff = 1 if p == 3 else 0
        while p ** (cutoff + 1) < max(ratios):
            cutoff += 1
        cutoffs[p] = cutoff

    total = moment = F(0)
    for states in product(*(range(cutoffs[p] + 2) for p in primes)):
        exponents = dict(zip(primes, states))
        high = tuple(p for p in primes if exponents[p] == cutoffs[p] + 1)
        low = tuple(p for p in primes if 0 < exponents[p] <= cutoffs[p])
        terms = []
        for t in subsets(low):
            support = tuple(sorted(high + t))
            terms.append(c[support] / prod(p ** exponents[p] for p in t))
            if 3 in t and 3 not in high:
                terms.append(b[support] /
                             (3 * prod(p ** exponents[p] for p in t if p != 3)))
        cell = weighted_cell = min(terms)
        for p in high:
            cell *= F(1, p ** cutoffs[p] * (p - 1))
            weighted_cell *= F((2 * cutoffs[p] + 3) * (p - 1) + 2,
                               p ** cutoffs[p] * (p - 1) ** 2)
        for p in low:
            weighted_cell *= 2 * exponents[p] + 1
        total += cell
        moment += weighted_cell
    return total - 1, moment, cutoffs

def head_recurrence(primes, pair_bounds, density_bound):
    """Keep cylinder envelopes separate from bounds on their actual sums."""
    profiles = {(): ({(): F(1)}, {})}
    metrics = {(): (F(0), F(1))}
    for size in range(1, len(primes) + 1):
        for support in combinations(primes, size):
            candidates = []
            for p in support:
                old = tuple(q for q in support if q != p)
                if old not in profiles:
                    continue
                survival = 1 - metrics[old][0] / (p - 2)
                if survival <= 0:
                    continue
                old_c, old_b = profiles[old]
                c, b = {(): F(1)}, {}
                for t in subsets(support):
                    if not t:
                        continue
                    previous = tuple(q for q in t if q != p)
                    factor = (F(p - 1, p - 2) if p in t else F(1)) / survival
                    c[t] = old_c[previous] * factor
                    if 3 in t:
                        b[t] = (old_c[previous] if p == 3 else old_b[previous]) * factor
                candidates.append((c, b))
            require(candidates, "no certified survivor normalization for a subset")
            c = {t: min(cc[t] for cc, _ in candidates) for t in subsets(support)}
            b = {t: min(bb[t] for _, bb in candidates)
                 for t in subsets(support) if 3 in t}
            if size == 2 and 3 in support:
                q = next(p for p in support if p != 3)
                b[(3,)] = min(b[(3,)], F(6 * (q - 2), 3 * q - 8))
            profiles[support] = c, b
            r, k, _ = envelope_sums(support, c, b)
            if size == 2 and 3 in support:
                joint_r, joint_k = pair_bounds[next(p for p in support if p != 3)]
                r, k = min(r, joint_r), min(k, joint_k)
            if support == (3, 5, 7):
                r = min(r, density_bound)
            metrics[support] = r, k
    return profiles, metrics


def serialize_profile(profile):
    return {"*".join(map(str, t)) if t else "1": str(value)
            for t, value in profile.items()}


def compute_certificate():
    primes, old, outside = (3, 5, 7, 11), (3, 5), (7, 11)
    pair_bounds = {
        5: (F(15, 7), F(173, 12)),
        7: (F(21, 13), F(19, 2)),
        11: (F(33, 25), F(181, 25)),
    }
    density, gamma_old = F(1649, 360), F(57, 4)
    survival_7 = 1 - pair_bounds[5][0] / (7 - 2)
    survival_11 = 1 - density / (11 - 2)
    require(survival_7 > 0 and survival_11 > 0,
            "same-law survival lower bound is not positive")
    domination = 1 / (survival_7 * survival_11)
    require(domination == F(5670, 1591), "domination factor mismatch")

    profiles, metrics = head_recurrence(primes, pair_bounds, density)
    c, b = profiles[primes]
    require(all(value > 0 for value in list(c.values()) + list(b.values())),
            "nonpositive projection coefficient")
    raw_r, raw_k, cutoffs = envelope_sums(primes, c, b)
    require(raw_k == F(187719326, 1723053), "full profile moment mismatch")
    require(tuple(cutoffs[p] for p in primes) == (2, 1, 0, 0),
            "unexpected exact-tail cutoffs")

    # For every positive outside exponent, adding that prime to a projection
    # support weakly decreases the envelope term. This checks factorization
    # for all exponents, not just one sampled finite range.
    for p in outside:
        other = tuple(q for q in primes if q != p)
        for t in subsets(other):
            extended = tuple(sorted(t + (p,)))
            require(c[extended] <= p * c[t],
                    "ordinary outside-support factorization failed")
            if 3 in t:
                require(b[extended] <= p * b[t],
                        "ternary outside-support factorization failed")

    mode_rows = []
    profile_total = selected_total = F(0)
    for support in subsets(outside):
        ordinary = {t: c[tuple(sorted(t + support))] for t in subsets(old)}
        ternary = {t: b[tuple(sorted(t + support))]
                   for t in subsets(old) if 3 in t}
        # The effective empty coefficient need not be 1. Only the weighted
        # moment is used; the helper's unit-normalized R return is irrelevant.
        _, profile_coefficient, mode_cutoffs = envelope_sums(old, ordinary, ternary)
        transport_coefficient = domination * gamma_old * prod(
            F(p - 1, p - 2) for p in support)
        # Sum_{e>=1} (2e+1)/p^e = (3p-1)/(p-1)^2.
        weight = prod(F(3*p - 1, (p - 1)**2) for p in support)
        selected = min(profile_coefficient, transport_coefficient)
        profile_total += weight * profile_coefficient
        selected_total += weight * selected
        mode_rows.append({
            "outside_support": list(support),
            "profile_coefficient": str(profile_coefficient),
            "transport_coefficient": str(transport_coefficient),
            "infinite_weight": str(weight),
            "selected": "profile" if profile_coefficient <= transport_coefficient
                        else "transport",
            "selected_contribution": str(weight * selected),
            "old_coordinate_cutoffs": {str(p): mode_cutoffs[p] for p in old},
        })
    require(profile_total == raw_k, "four modes do not recover the full infinite profile")
    require(selected_total == F(168332, 1591), "improved head constant mismatch")
    require(selected_total < raw_k, "no strict head improvement")

    value = selected_total
    bridge = []
    for p, delta in ((67, F(1, 4)), (71, F(53, 200)), (73, F(27, 100))):
        require(0 < delta < 1, "threshold is outside (0,1)")
        a = F(3*p - 1, (p - 1)**2)
        denominator = 1 - value / (4 * delta * (1 - delta) * (p - 1)**2)
        require(denominator > 0, "bridge denominator is not positive")
        next_value = value * (1 + a / (1 - delta)) / denominator
        bridge.append({"prime": p, "delta": str(delta), "input": str(value),
                       "a": str(a), "denominator": str(denominator),
                       "output": str(next_value)})
        value = next_value
    continuation_bound = F(138877, 1000)
    require(value < continuation_bound, "prime-73 continuation threshold failed")
    return {
        "schema": "erdos7-lcm-block-v1",
        "prime_support": list(primes),
        "old_support": list(old),
        "outside_support": list(outside),
        "analytical_inputs": {
            "R_3_5": str(pair_bounds[5][0]),
            "R_3_5_7": str(density), "Gamma_3_5": str(gamma_old)},
        "survival_factors": {"7": str(survival_7), "11": str(survival_11)},
        "pointwise_domination_factor": str(domination),
        "ordinary_profile": serialize_profile(c),
        "first_ternary_profile": serialize_profile(b),
        "full_profile_cutoffs": {str(p): cutoffs[p] for p in primes},
        "full_profile_R": str(raw_r),
        "full_profile_K": str(raw_k),
        "support_modes": mode_rows,
        "head_bound": str(selected_total),
        "head_improvement": str(raw_k - selected_total),
        "bridge": bridge,
        "prime_73_upper_threshold": str(continuation_bound),
        "prime_73_threshold_margin": str(continuation_bound - value),
    }


def main():
    certificate_path = (Path(__file__).resolve().parents[1] / 'certificates/lcm_block_certificate.json')
    certificate = json.loads(read_artifact_text(certificate_path))
    expected = compute_certificate()
    require(certificate == expected, "fixed certificate differs from exact recomputation")
    print("Verified four infinite outside-support modes; "
          "Gamma <= " + expected["head_bound"] + ".")
    final = F(expected["bridge"][-1]["output"])
    print("Positive prime-67/71/73 denominators; F73 = " + str(final) +
          " < " + expected["prime_73_upper_threshold"] + ".")


if __name__ == "__main__":
    main()
