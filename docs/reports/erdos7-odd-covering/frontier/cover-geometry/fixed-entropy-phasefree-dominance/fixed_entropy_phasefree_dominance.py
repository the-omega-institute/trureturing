#!/usr/bin/env python3
"""Exact constants for the fixed-head joint entropy dominance theorem.

Standard library only. No original-family enumeration, numerical logarithms,
external producers, or floating-point proof decisions. The accompanying note
supplies the all-depth, entropy, and association arguments.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import factorial, prod
from pathlib import Path
import argparse
import hashlib
import json


PRIMES = (3, 5, 7, 11, 13, 17, 19)
ROOT_LOWER = {
    3: Q(8, 9), 5: Q(5, 8), 7: Q(2, 5), 11: Q(1, 4),
    13: Q(1, 5), 17: Q(3, 20), 19: Q(2, 15),
}
DELTA = Q(51863873, 25500000)
checks = {}


def check(name, condition):
    if name in checks or not condition:
        raise RuntimeError(name)
    checks[name] = True


def moment_tail(p, n, exponential, depth):
    if depth > n:
        return exponential ** n / p ** depth
    return sum((Q(p - 1, p ** (k + 1)) * exponential ** k
                for k in range(depth, n)), Q()) + exponential ** n / p ** n


coordinate_certificates = {}
for p in PRIMES:
    n = 8 if p == 3 else 7
    base_atom = Q(p - 1, p) - sum((Q(1, p ** j) for j in range(1, n + 1)), Q())
    exponential_lower = Q(19, 7) if p == 5 else Q(8, 3)
    numerator = moment_tail(p, n, exponential_lower, 1)
    root_lower = ROOT_LOWER[p]
    residual = (1 - root_lower) * numerator - root_lower * base_atom
    check(f"base_atom_positive_{p}", base_atom > 0)
    check(f"root_tail_lower_{p}", residual > 0)

    root_cap = Q(p - 1, p * (p - 2))
    other_cap = Q(4, 15) if p == 3 else Q(2, 3)
    allocation_gap = Q(2, 7) * root_lower - other_cap * root_cap
    check(f"allocation_dominance_{p}", allocation_gap >= 0)
    ratio_lower = Q(4, 3) if p == 3 else Q(7, 3)
    check(f"phasefree_coordinate_ratio_{p}", root_lower >= ratio_lower * root_cap)

    upper_margin = None
    if p >= 5:
        upper_numerator = moment_tail(p, n, Q(11, 4), 1)
        upper_margin = Q(2, 3) - upper_numerator / (base_atom + upper_numerator)
        check(f"root_tail_below_two_thirds_{p}", upper_margin > 0)

    for j in range(1, n):
        check(f"strict_head_depth_{p}_{j}",
              moment_tail(p, n, exponential_lower, j)
              < p * moment_tail(p, n, exponential_lower, j + 1))
    for j in (n, n + 1, n + 4):
        check(f"tail_depth_equality_{p}_{j}",
              moment_tail(p, n, exponential_lower, j)
              == p * moment_tail(p, n, exponential_lower, j + 1))

    coordinate_certificates[p] = {
        "head_depth": n,
        "exponential_lower": exponential_lower,
        "root_tail_lower": root_lower,
        "base_atom": base_atom,
        "positive_residual": residual,
        "allocation_gap": allocation_gap,
        "two_thirds_upper_margin": upper_margin,
    }

singleton_capacity = Q(2, 7) * DELTA + Q(1, 10000)
phasefree_capacity = Q(15, 49) * DELTA + Q(1, 10000)
check("singleton_inside_old_region", singleton_capacity < Q(2, 3))
check("phasefree_inside_old_region", phasefree_capacity < Q(2, 3))
check("logarithm_rational_certificate", Q(11, 4) ** 7 < Q(19, 9) ** 10)
check("exponential_lower_nineteen_sevenths",
      sum((Q(1, factorial(k)) for k in range(6)), Q())
      == Q(163, 60) > Q(19, 7))

label_choices = []
for support in combinations(PRIMES[1:], 3):
    modulus = 3 * prod(support)
    allocated = ROOT_LOWER[max(support)]
    density = Q(800, modulus)
    label_choices.append({
        "support": support,
        "modulus": modulus,
        "allocation_lower": allocated,
        "density_lower": density,
        "minimum_lower": min(allocated, density),
        "cheaper_lower_bound": "density" if density < allocated else "allocation",
    })
minimum = sum((row["minimum_lower"] for row in label_choices), Q())
reconstructed = Q(12, 5) + 800 * sum(
    (Q(1, modulus) for modulus in (6783, 7293, 8151, 10659, 12597)), Q())
check("twenty_label_partition_minimum", minimum == reconstructed)
check("twenty_label_exceeds_residual_budget", minimum > DELTA)

result = {
    "scope": {
        "primes": PRIMES,
        "heads": (8, 7, 7, 7, 7, 7, 7),
        "exponential_parameter": 1,
        "shallow_cutoff": 10 ** 9,
        "base_budget": Q(4522277, 500000),
        "residual_budget": DELTA,
        "verification_scope": "ordinary proof plus exact finite constants; no Lean claim",
    },
    "coordinate_certificates": coordinate_certificates,
    "singleton_capacity_upper": singleton_capacity,
    "singleton_gap_to_two_thirds": Q(2, 3) - singleton_capacity,
    "phasefree_capacity_upper": phasefree_capacity,
    "phasefree_gap_to_two_thirds": Q(2, 3) - phasefree_capacity,
    "twenty_label_choices": label_choices,
    "twenty_label_minimum_lower": minimum,
    "twenty_label_gap": minimum - DELTA,
    "passed_checks": len(checks),
    "checks": checks,
}


def encode(value):
    if isinstance(value, Q):
        return str(value)
    raise TypeError(type(value).__name__)


payload = json.dumps(result, default=encode, indent=2) + "\n"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
args.output.write_text(payload)
print(json.dumps({k: result[k] for k in ('passed_checks', 'singleton_capacity_upper',
      'phasefree_capacity_upper', 'twenty_label_minimum_lower', 'twenty_label_gap')},
      default=encode, indent=2))
print('json_sha256=' + hashlib.sha256(args.output.read_bytes()).hexdigest())
