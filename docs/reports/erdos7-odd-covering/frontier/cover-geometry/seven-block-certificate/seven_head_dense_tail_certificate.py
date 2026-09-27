#!/usr/bin/env python3
"""Exact arithmetic for the seven-small-prime, unrestricted-tail theorem.

The inherited head mass is read from Chapter 31's existing certificate.
This program does not rerun its geometry, prove the measure construction,
or certify the external analytic prime-product estimate.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import factorial, prod
from pathlib import Path
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    require(not sys.flags.optimize, "Run with assertions enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--head-certificate", type=Path,
                        default=Path(__file__).with_name("seven_block_certificate.json"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    raw = args.head_certificate.read_bytes()
    head_sha = sha256(raw).hexdigest()
    require(head_sha == "b6c47c2e710cdb27e599b92ccfe7d1b5c4e55b4b4082ad8058d196c1e964b9b2",
            "Head certificate differs from the inspected Chapter 31 snapshot")
    head = json.loads(raw)
    require(head["schema"] == "seven-block-certificate-v1", "Unexpected head schema")
    source_primes = (3, 5, 7, 11, 13, 17, 19)
    selected = [r for r in head["core_results"]
                if r["children_lower_bounds"] == list(source_primes[1:])]
    require(len(selected) == 1, "Expected exactly one densest seven-prime row")
    row = selected[0]
    thresholds = (2, 4, 4, 8, 8)
    require(row["thresholds"] == list(thresholds), "Unexpected source thresholds")
    caps = (F(1), F(1)) + tuple(F(p - 1, p - 1 - t)
                               for p, t in zip(source_primes[2:], thresholds))
    require(tuple(map(F, row["coordinate_marginal_caps"])) == caps,
            "Source cap mismatch")
    density_cap = prod(caps)
    require(density_cap == F(27, 2) == F(row["global_density_cap"]),
            "Joint density cap mismatch")
    mass = F(row["mass_lower_bound"])
    require(mass == F(7235955529, 450000000000), "Unexpected inherited head mass")
    require(F(2, 125) < mass < 1, "Head reserve comparison failed")

    local_moments = tuple(1 + F(3*p - 1, (p - 1)**2) for p in source_primes)
    haar_moment = prod(local_moments)
    joint_load = density_cap * haar_moment
    require(haar_moment == F(2263261, 110592), "Haar second moment mismatch")
    require(joint_load == F(2263261, 8192), "Joint-load seed mismatch")

    B, ell = 100000, 10
    require(B >= 286 and ell >= 4 and 3**ell <= B, "Analytic premise parameters")
    c = F(2*ell**2 + 1, 2*ell**2 - 1)
    polynomial = sum((F(factorial(7), factorial(7-h) * ell**h)
                      for h in range(8)), F(0))
    tau = c**7 / B * F(B, B-3)**2 * polynomial
    tail_charge = joint_load * tau
    require(tail_charge == F(482499472365859733223806367,
                             66602699562724767891160975360),
            "Tail charge mismatch")
    require(tail_charge < F(29, 4000), "Tail allowance failed")
    remaining_mass = mass - tail_charge
    require(remaining_mass > F(7, 800), "Positive survivor reserve failed")

    # A second application takes the published eight-prime density theorem
    # as an attributed ordinary-mathematics premise, not as a program output.
    eight_primes = source_primes + (23,)
    eight_mass = F(1, 1002375)
    eight_moment = prod(1 + F(3*p - 1, (p - 1)**2) for p in eight_primes)
    require(eight_moment == F(4732273, 202752), "Eight-prime moment mismatch")
    B8, ell8 = 100000000, 16
    require(B8 >= 286 and ell8 >= 4 and 3**ell8 <= B8,
            "Eight-prime analytic premise parameters")
    c8 = F(2*ell8**2 + 1, 2*ell8**2 - 1)
    polynomial8 = sum((F(factorial(7), factorial(7-h) * ell8**h)
                       for h in range(8)), F(0))
    tau8 = c8**7 / B8 * F(B8, B8-3)**2 * polynomial8
    charge8 = eight_moment * tau8
    require(charge8 == F(1097047779531311514783771237357421875,
                         2741275994402057415260186461015293546201088),
            "Eight-prime tail charge mismatch")
    remaining8 = eight_mass - charge8
    require(remaining8 > F(1, 2000000), "Eight-prime survivor reserve failed")

    def encode(value):
        if isinstance(value, F):
            return str(value)
        if isinstance(value, (list, tuple)):
            return [encode(v) for v in value]
        if isinstance(value, dict):
            return {k: encode(v) for k, v in value.items()}
        return value

    result = encode({
        "schema": "seven-head-dense-tail-certificate-v1",
        "scope": "Exact arithmetic for at most seven odd prime divisors <=100000, "
                 "and for an attributed eight-prime head at cutoff 100000000; "
                 "with any finite number of larger prime divisors, arbitrary original "
                 "finite heights, residues, and support arities. Ordinary proof, not Lean.",
        "head_certificate_sha256": head_sha,
        "head_row_children": source_primes[1:],
        "head_mass_lower_bound": mass,
        "head_thresholds": thresholds,
        "source_kernel_caps": caps,
        "joint_density_cap": density_cap,
        "haar_local_second_moments": local_moments,
        "haar_joint_second_moment_upper_bound": haar_moment,
        "homogeneous_joint_load_seed_upper_bound": joint_load,
        "tail_cutoff": B,
        "logarithm_lower_bound": ell,
        "prime_product_constant": c,
        "tau7": tau,
        "tail_loss_upper_bound": tail_charge,
        "tail_loss_strict_simple_upper_bound": F(29, 4000),
        "weighted_survivor_mass_lower_bound": remaining_mass,
        "weighted_survivor_mass_strict_simple_lower_bound": F(7, 800),
        "head_geometry_reexecuted": False,
        "analytic_premise_checked_by_this_program": False,
        "original_haar_density_claim": "Only positivity; weighted mass is not Haar density.",
        "eight_prime_application": {
            "source": "schroeder2026nine, cor:uncovered-density",
            "source_archive_sha256": "9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c",
            "head_density_is_attributed_source_premise": True,
            "head_mass_lower_bound": eight_mass,
            "joint_density_cap": F(1),
            "haar_joint_second_moment_upper_bound": eight_moment,
            "tail_cutoff": B8,
            "logarithm_lower_bound": ell8,
            "tau7": tau8,
            "tail_loss_upper_bound": charge8,
            "weighted_survivor_mass_lower_bound": remaining8,
            "weighted_survivor_mass_strict_simple_lower_bound": F(1, 2000000),
        },
    })
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
