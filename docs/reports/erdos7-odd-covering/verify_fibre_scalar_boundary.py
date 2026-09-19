#!/usr/bin/env python3
"""Exact scalar fibre boundary checks for the Erdős #7 problem dossier.

This checks the actual congruence construction, its invariant equalities,
and algebraic boundary data. The universal scalar-optimality statement is
proved by the continuous argument in the accompanying note.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

import argparse
from fractions import Fraction as F
from itertools import product
import json
from math import isqrt
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def laws_and_fibres(p):
    t = p * p + p + 1
    epsilon = F(1, 120 * p * t)
    direction = (1, -t, p * t, -p**3)
    plus = [F(16, 75)] + [F(59, 300) + epsilon * v for v in direction]
    minus = [F(16, 75)] + [F(59, 300) - epsilon * v for v in direction]
    alpha = [F(1, p)] + [F(1, p) + F(1, p**j) for j in range(1, 5)]
    return epsilon, direction, plus, minus, alpha


def exact_old_gamma(nu):
    """Enumerate all 3*5*15 actual divisor layouts on old period 15."""
    weights = {
        (r, c): (nu[c] / 2 if r != 0 else F(0))
        for r, c in product(range(3), range(5))
    }
    maximum = F(0)
    for root, column, pair_root, pair_column in product(range(3), range(5), range(3), range(5)):
        value = F(0)
        for (r, c), mass in weights.items():
            load = 1 + (r == root) + (c == column) + ((r, c) == (pair_root, pair_column))
            value += mass * load * load
        maximum = max(maximum, value)
    return maximum


def verify(certificate):
    require(certificate["schema"] == "fibre-scalar-boundary-v1", "Wrong schema")
    primes = certificate["primes"]
    require(primes == [13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61],
            "Wrong prime window")
    desired_gamma = F(certificate["old_gamma"])
    desired_r = F(certificate["old_r"])
    density_cap = F(certificate["reference_density_cap"])
    old_cap = F(certificate["old_marginal_cap"])
    require((desired_gamma, desired_r, density_cap, old_cap) ==
            (F(41, 10), F(41, 50), F(16, 15), F(300, 241)), "Wrong targets")
    for p in primes:
        require(is_prime(p), f"Not prime: {p}")
        epsilon, direction, plus, minus, alpha = laws_and_fibres(p)
        for k in range(3):
            require(sum(F(direction[j - 1], p**(k * j)) for j in range(1, 5)) == 0,
                    f"Direction fails moment {k} at p={p}")
        for nu in (plus, minus):
            require(sum(nu) == 1 and min(nu) > 0, "Invalid old law")
            require(max(nu) == F(16, 75) and all(x < nu[0] for x in nu[1:]),
                    "Wrong maximum old weight")
            require(F(5, 2) * (1 + 3 * max(nu)) == desired_gamma, "Wrong Gamma formula")
            require(F(1, 2) + F(3, 2) * max(nu) == desired_r, "Wrong R formula")
            require(5 * max(nu) == density_cap, "Wrong RN cap")
        for k in (1, 2):
            require(sum(x * a**k for x, a in zip(plus, alpha)) ==
                    sum(x * a**k for x, a in zip(minus, alpha)), "Moment mismatch")
        geometric = sum(F(1, p**j) for j in range(1, 5))
        second_geometric = sum(F(1, p**(2 * j)) for j in range(1, 5))
        expected_first = F(1, p) + F(59, 300) * geometric
        expected_second = F(1, p*p) + F(59, 150*p) * geometric + F(59, 300) * second_geometric
        require(sum(x * a for x, a in zip(plus, alpha)) == expected_first, "First moment formula")
        require(sum(x * a*a for x, a in zip(plus, alpha)) == expected_second, "Second moment formula")
        conditional_cap = F(2*p, 2*p-3)
        good = [j for j in range(5) if 1-alpha[j] >= 1/conditional_cap]
        require(good == [0, 2, 3, 4], "Wrong actual good fibres")
        good_plus = sum(plus[j] for j in good)
        good_minus = sum(minus[j] for j in good)
        require(good_plus == F(241, 300)-epsilon and good_minus == F(241, 300)+epsilon,
                "Good mass formula")
        require(old_cap * good_plus < 1 < old_cap * good_minus, "Capacity distinction failed")
        require(F(5, 2)*(good_plus+3*max(plus)) == F(433, 120)-F(5, 2)*epsilon,
                "Wrong plus weighted-layout profile")
        require(F(5, 2)*(good_minus+3*max(minus)) == F(433, 120)+F(5, 2)*epsilon,
                "Wrong minus weighted-layout profile")
        # Construct the feasible old marginal, and check its cap exactly.
        lifted_old = [minus[j]/good_minus if j in good else F(0) for j in range(5)]
        require(sum(lifted_old) == 1, "Constructed old marginal not normalized")
        require(all(lifted_old[j] <= old_cap*minus[j] for j in range(5)),
                "Constructed old marginal exceeds cap")
        require(all(1/(1-alpha[j]) <= conditional_cap for j in good),
                "Conditional survivor density exceeds cap")

    p = 13
    epsilon, _, plus, minus, alpha = laws_and_fibres(p)
    saved = certificate["p13"]
    require(epsilon == F(saved["epsilon"]), "Wrong p13 epsilon")
    require(1-plus[1] == F(saved["good_mass_plus"]), "Wrong p13 good-plus mass")
    require(1-minus[1] == F(saved["good_mass_minus"]), "Wrong p13 good-minus mass")
    # Independent layout enumeration, using the actual old congruence classes.
    require(exact_old_gamma(plus) == desired_gamma, "Enumerated plus Gamma differs")
    require(exact_old_gamma(minus) == desired_gamma, "Enumerated minus Gamma differs")
    plus_good = [mass if j != 1 else F(0) for j, mass in enumerate(plus)]
    minus_good = [mass if j != 1 else F(0) for j, mass in enumerate(minus)]
    require(exact_old_gamma(plus_good) == F(433, 120)-F(5, 2)*epsilon,
            "Enumerated plus weighted Gamma differs")
    require(exact_old_gamma(minus_good) == F(433, 120)+F(5, 2)*epsilon,
            "Enumerated minus weighted Gamma differs")
    powers = [p**j for j in range(5)]
    row_forbidden = []
    for x in range(5):
        count = 0
        for y in range(p**4):
            forbidden = y % p == 0 or (x != 0 and y % powers[x] == 1)
            count += forbidden
        row_forbidden.append(count)
    require(row_forbidden == saved["five_row_new_forbidden_counts"], "Actual row counts differ")
    require([F(n, p**4) for n in row_forbidden] == alpha, "Actual alpha differs")
    survivors = 2*(5*p**4-sum(row_forbidden))
    require(survivors == saved["complete_survivors_in_full_period"], "Wrong full survivor count")
    require(15*p**4 == saved["full_period"], "Wrong full period")

    for example in certificate["moment_extremizers"]:
        delta, variance = F(example["delta"]), F(example["V"])
        atoms = [(F(t), F(weight)) for t, weight in example["atoms"]]
        require(sum(weight for _, weight in atoms) == 1, "Extremizer not normalized")
        require(all(0 <= t <= 1 and weight >= 0 for t, weight in atoms), "Invalid extremizer")
        require(sum(weight*t*t for t, weight in atoms) == variance, "Wrong extremizer moment")
        loss = sum(weight*max(F(0), t-delta)/(1-delta) for t, weight in atoms)
        require(loss == F(example["loss"]), "Wrong extremizer loss")

    seed = F(certificate["current_four_prime_seed"])
    require(seed == F(4939031, 47730), "Wrong current seed")
    variance, a = seed/144, F(19, 72)
    threshold = F(certificate["next_prime_square"])
    require(0 < variance < 1 and threshold == 16**2, "Wrong transition regime")
    quadratic = 4*(threshold-seed)
    linear = 4*((seed-threshold)+a*seed)
    constant = threshold*variance
    require(quadratic > 0, "Comparison quadratic is not convex")
    minimum = constant-linear*linear/(4*quadratic)
    require(minimum == F(certificate["quadratic_global_minimum"]) and minimum > 0,
            "Scalar transition obstruction failed")
    print(json.dumps({
        "result": "PASS", "prime_instances": len(primes),
        "exact_old_layouts_per_law": 225,
        "p13_actual_five_rows_checked": 5*p**4,
        "p13_complete_survivors": survivors,
        "old_gamma": str(desired_gamma), "old_r": str(desired_r),
        "reference_density_cap": str(density_cap),
        "moment_extremizers": len(certificate["moment_extremizers"]),
        "p13_scalar_comparison_quadratic_minimum": str(minimum),
    }, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/fibre_scalar_boundary_certificate.json'))
    args = parser.parse_args()
    verify(json.loads(read_artifact_text(args.certificate, encoding="utf-8")))


if __name__ == "__main__":
    main()
