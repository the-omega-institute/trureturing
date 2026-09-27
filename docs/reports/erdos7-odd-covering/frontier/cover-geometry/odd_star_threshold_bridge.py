"""Exact odd-star threshold reduction and finite controls.

Mathematical source: Michael Schroeder, Erdős Problem 278: Formulas and
Complexity of Maximum Covered Density, V1 (2026), DOI 10.5281/zenodo.22874487,
lem:generalwindows, prop:star, lem:starseparation, thm:stardecision.
The construction uses c=6 to enforce odd cofactors. This is an original
implementation of the cited formulas, not a copy of the upstream Python.

Run without arguments for exact controls, or --weights 1 2 3 4 to construct
an instance. Subset enumeration is exponential and is only a research
verifier; the reduction itself uses polynomial-bit arithmetic. No Lean
certification or unrestricted odd-covering decision is claimed.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement
from math import gcd, prod


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def coprime_windows(weights: tuple[F, ...], eta: F, s: int, c: int = 6):
    """Return (cofactors, t) in [t/w_i, (1+eta)t/w_i]."""
    require(bool(weights), "at least one weight is required")
    require(c >= 2 and 0 < eta <= 1, "invalid window parameters")
    require(all(0 < w <= 1 for w in weights), "weights must lie in (0,1]")
    require(s * eta >= 2 * len(weights), "window allocation is too short")
    starts: list[int] = []
    for w in weights:
        ratio = s / w
        a = -(-ratio.numerator // ratio.denominator)
        while a in starts:
            a += 1
        starts.append(a)
    scale = c * prod(abs(a - b) for a, b in combinations(starts, 2))
    return tuple(scale * a + 1 for a in starts), s * scale


def reduce_partition(weights: tuple[int, ...]):
    """Map binary PARTITION to U({3} union {3*m_i}) < theta."""
    require(all(type(w) is int and w > 0 for w in weights),
            "PARTITION weights must be positive integers")
    total = sum(weights)
    if not weights:
        return (5,), F(2, 3), None
    if total % 2 or 2 * max(weights) > total:
        return (5,), F(1, 3), None
    half = total // 2
    scaled = tuple(F(w, half) for w in weights)
    eta = F(1, 64 * half**2)
    s = 128 * len(weights) * half**2
    cofactors, t = coprime_windows(scaled, eta, s)
    X = sum((F(1, m) for m in cofactors), F(0))
    theta = (4 * t*t - 2 * t*t * X - sum(w*w for w in scaled)
             + 2 + F(1, half*half)) / (6 * t*t)
    return cofactors, theta, (half, scaled, eta, s, t)


def star_minimum(cofactors: tuple[int, ...]):
    """Exact minimum over all placements in the two uncovered 3-fibres."""
    require(all(m > 1 and gcd(m, 3) == 1 for m in cofactors),
            "invalid cofactor")
    require(all(gcd(a, b) == 1 for a, b in combinations(cofactors, 2)),
            "cofactors must be pairwise coprime")
    best: F | None = None
    selected = 0
    for mask in range(1 << len(cofactors)):
        left = right = F(1)
        for i, m in enumerate(cofactors):
            if mask >> i & 1:
                left *= F(m - 1, m)
            else:
                right *= F(m - 1, m)
        value = (left + right) / 3
        if best is None or value < best:
            best, selected = value, mask
    require(best is not None, "no partition examined")
    return best, selected


def source_has_partition(weights: tuple[int, ...]) -> bool:
    return any(2 * sum(w for i, w in enumerate(weights) if mask >> i & 1)
               == sum(weights) for mask in range(1 << len(weights)))


def check_instance(weights: tuple[int, ...]):
    cofactors, theta, construction = reduce_partition(weights)
    moduli = (3,) + tuple(3*m for m in cofactors)
    require(len(set(moduli)) == len(moduli), "modulus labels repeated")
    require(all(m > 1 and m % 2 for m in moduli), "oddness lost")
    value, mask = star_minimum(cofactors)
    yes = source_has_partition(weights)
    require((value < theta) == yes, "threshold/source mismatch")
    require(value > 0, "the star unexpectedly covers")
    if construction is not None:
        half, scaled, eta, s, t = construction
        require(t >= 6*s and t >= 64*half*half, "scale lower bound lost")
        require(all(gcd(m, 6) == 1 for m in cofactors), "parity guard lost")
        require(all(t / w <= m <= (1 + eta) * t / w
                    for m, w in zip(cofactors, scaled)), "window violated")
        margin = F(1, 8*t*t*half*half)
        require(theta - value >= margin if yes else value - theta >= margin,
                "uniform rational separation violated")
    return {"weights": weights, "moduli": moduli, "theta": str(theta),
            "minimum_uncovered_density": str(value),
            "optimal_partition_mask": mask, "partition_exists": yes,
            "max_modulus_bits": max(m.bit_length() for m in moduli)}


def run_controls():
    cases = [()] + [(i,) for i in range(1, 6)]
    for n in range(2, 7):
        cases.extend(combinations_with_replacement(range(1, 6), n))
    yes = no = largest = 0
    for weights in cases:
        result = check_instance(weights)
        yes += result["partition_exists"]
        no += not result["partition_exists"]
        largest = max(largest, result["max_modulus_bits"])
    # An independent period calculation checks the arithmetic star objective.
    # All 15*21 original independent phases are examined, with a_3=0 fixed
    # by a common translation. This checks the normalized full search, not
    # merely the two-fibre formula against another copy of itself.
    cofactors = (5, 7)
    formula, _ = star_minimum(cofactors)
    best_holes = min(sum(x % 3 != 0 and x % 15 != a and x % 21 != b
                         for x in range(105))
                     for a in range(15) for b in range(21))
    require(formula == F(best_holes, 105), "literal CRT control mismatch")
    require(formula == F(58, 105), "unexpected star control value")
    # This refutes an inference of zero uncovered density from a YES answer
    # to the positive-threshold problem.
    witness = check_instance((1, 1))
    require(witness["partition_exists"] and
            0 < F(witness["minimum_uncovered_density"]) < F(witness["theta"]),
            "positive-threshold/zero distinction was lost")
    return {"cases": len(cases), "yes": yes, "no": no,
            "max_modulus_bits": largest, "literal_phase_vectors": 315,
            "literal_minimum_holes": best_holes,
            "positive_threshold_with_no_cover": witness}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--weights", nargs="*", type=int)
    options = parser.parse_args()
    result = (run_controls() if options.weights is None
              else check_instance(tuple(options.weights)))
    print(json.dumps(result, sort_keys=True))
