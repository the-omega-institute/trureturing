#!/usr/bin/env python3
"""Exact finite diagnostics for Hough--Nielsen prefix conditioning.

Standard library only. This checks explicit arithmetic inputs and rational
supersolution inequalities; it does not re-prove Hough--Nielsen Theorem 4.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from fractions import Fraction as F
from math import gcd, isqrt, prod
from pathlib import Path

sys.dont_write_bytecode = True
CERTIFICATE = "certificates/source_norms/hn_current_prefix.json"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode_fraction(value):
    value = F(value)
    return f"{value.numerator}/{value.denominator}"


def primes_up_to(limit):
    return [n for n in range(2, limit + 1)
            if all(n % d for d in range(2, isqrt(n) + 1))]


def crt(congruences):
    value, period = 0, 1
    for residue, modulus in congruences:
        if modulus == 1:
            continue
        require(gcd(period, modulus) == 1, "CRT factors are not coprime")
        step = ((residue - value) * pow(period, -1, modulus)) % modulus
        value += period * step
        period *= modulus
    return value, period


def pullback(originals, fixed_residue, fixed_modulus):
    """Keep each original label, then group equal residual modulus/events."""
    rows = []
    grouped = {}
    for index, (residue, modulus) in enumerate(originals):
        common = gcd(modulus, fixed_modulus)
        if (residue - fixed_residue) % common:
            rows.append(None)
            continue
        residual_modulus = modulus // common
        require(residual_modulus > 1, "Future residual modulus must exceed one")
        residual_residue = (
            ((residue - fixed_residue) // common)
            * pow(fixed_modulus // common, -1, residual_modulus)
        ) % residual_modulus
        rows.append((residual_residue, residual_modulus))
        grouped.setdefault(residual_modulus, set()).add(residual_residue)
    return rows, grouped


def check_pullback():
    # All original moduli are distinct and odd. The first two labels merge
    # to the same residual event at old 0, prefix 0; another label gives a
    # different residue at that same residual modulus.
    originals = [(0, 21), (0, 63), (15, 105), (0, 525),
                 (0, 275), (1, 77), (13, 231), (0, 1925)]
    old_period, p, height = 9, 5, 2
    whole_period = old_period * p ** height * 7 * 11
    require(len(set(m for _, m in originals)) == len(originals),
            "Diagnostic original moduli must be distinct")
    evaluations, fibres = 0, 0
    sample = None
    for x in range(old_period):
        for depth in range(height + 1):
            for prefix in range(p ** depth):
                b, scale = crt([(x, old_period), (prefix, p ** depth)])
                rows, grouped = pullback(originals, b, scale)
                relative_period = whole_period // scale
                fibres += 1
                for n in range(relative_period):
                    integer = b + scale * n
                    for (a, d), row in zip(originals, rows):
                        direct = integer % d == a % d
                        reduced = row is not None and n % row[1] == row[0]
                        require(direct == reduced, "Original/residual membership differs")
                        evaluations += 1
                    direct_union = any(integer % d == a % d for a, d in originals)
                    grouped_union = any(n % m in residues for m, residues in grouped.items())
                    require(direct_union == grouped_union, "Grouping changed the union")
                if x == 0 and depth == 1 and prefix == 0:
                    require(grouped[7] == {0, 5}, "Expected duplicate/grouped residue fixture")
                    require(rows[0] == rows[1] == (0, 7), "Original duplicate witness lost")
                    sample = {
                        "original_pullbacks": rows,
                        "grouped_residues": {str(m): sorted(a) for m, a in sorted(grouped.items())},
                    }
    return {"original_classes": originals, "whole_period": whole_period,
            "old_period": old_period, "p": p, "height": height,
            "fibres_checked": fibres, "individual_membership_checks": evaluations,
            "old_0_depth_1_prefix_0_sample": sample}


def benchmark():
    qs = [q for q in primes_up_to(857) if q >= 11]
    require(len(qs) == 144 and qs[-1] == 857, "Prime block changed")
    reciprocal = sum((F(1, q) for q in qs), F(0))
    require(reciprocal > 1, "Raw future reciprocal sum must exceed one")
    require(reciprocal - F(1, qs[-1]) < 1, "Upper prime is not the first crossing")
    originals = [(25, 75), (0, 175)] + [(0, q) for q in qs]
    require(len(originals) == len({m for _, m in originals}), "Original modulus collision")
    require(all(m > 1 and m % 2 for _, m in originals), "Not distinct odd inputs")
    p, height, depth, old_x, prefix = 5, 2, 1, 0, 0
    b, scale = crt([(old_x, 3), (prefix, p ** depth)])
    require((b, scale) == (0, 15), "Wrong old/prefix arithmetic parameter")
    rows, grouped = pullback(originals[1:], b, scale)
    require(rows[0] == (0, 35), "Mixed future modulus did not reduce to 35")
    require(grouped == {m: {0} for m in [35] + qs}, "Unexpected residual family")
    # Empty modulus 5 is needed to invoke conclusion (6) for the current leaf.
    grouped_with_empty = dict(grouped)
    grouped_with_empty[5] = set()
    weights = {5: F(1, 32), 7: F(1, 32)}
    weights.update({q: F(1, q - 1) for q in qs})
    factors = {m: [q for q in weights if m % q == 0] for m in grouped_with_empty}
    loads = {
        m: F(len(residues), m) * prod(1 + weights[q] for q in factors[m])
        for m, residues in grouped_with_empty.items()
    }
    constraints = []
    for q, value in weights.items():
        rhs = sum((load for m, load in loads.items() if m % q == 0), F(0))
        require(value >= rhs, "HN nonnegative supersolution inequality fails")
        constraints.append({"prime": q, "weight": encode_fraction(value),
                            "rhs": encode_fraction(rhs), "slack": encode_fraction(value-rhs)})
    require(weights[5] - loads[35] == F(31, 35840), "Mixed slack mismatch")
    require(loads[5] == 0, "Empty test event must have zero cost")
    raw_future_load = reciprocal / 5 + F(1, 175)
    require(raw_future_load > F(1, 5), "Raw CP2 lower bound is not zero")
    a_j = F(0)
    require(old_x != 25 % 3, "Current class unexpectedly active on old fibre")
    atom_counts = [sum(n % 5 == r for n in range(35) if n != 0) for r in range(5)]
    require(atom_counts == [6, 7, 7, 7, 7], "Conditional current marginals differ")
    conditional_marginals = [F(count, 34) for count in atom_counts]
    independent_tail_hole = prod(F(q - 1, q) for q in qs)
    future_hole = F(34, 35) * independent_tail_hole
    require(future_hole > 0, "CRT product hole must be positive")
    # Every original class is irredundant on the union; this is still a noncover.
    private_points = []
    for target in range(len(originals)):
        if target == 0:
            conditions = [(1, 3), (0, 25), (1, 7)]
        elif target == 1:
            conditions = [(0, 3), (0, 25), (0, 7)]
        else:
            conditions = [(0, 3), (1, 25), (1, 7)]
        conditions += [(0 if target == k + 2 else 1, q) for k, q in enumerate(qs)]
        witness, period = crt(conditions)
        memberships = [witness % m == a % m for a, m in originals]
        require(memberships == [k == target for k in range(len(originals))],
                "Claimed private integer is not exclusive")
        private_points.append(str(witness))
    require(all(15 % m != a % m for a, m in originals), "Noncoverage witness fails")
    require(15 % 3 == old_x and 15 % 5 == prefix, "Witness is outside the target fibre")
    return {
        "original_classes": [{"residue": a, "modulus": m,
                              "private_integer": private_points[k]}
                             for k, (a, m) in enumerate(originals)],
        "original_count": len(originals), "period": str(period),
        "old_period": 3, "old_x": old_x, "current_prime": p,
        "current_height": height, "prefix_depth": depth, "prefix": prefix,
        "uncovered_integer_in_target_fibre": 15,
        "future_prime_block": qs, "prime_reciprocal_sum": encode_fraction(reciprocal),
        "current_prefix_haar_mass": encode_fraction(a_j),
        "raw_future_prefix_load": encode_fraction(raw_future_load),
        "prefix_haar_mass": "1/5", "cp2_deficit_positive_part": "0/1",
        "residual_moduli": [35] + qs, "added_empty_test_modulus": 5,
        "hn_supersolution_constraints": constraints,
        "hn_total_cost_B": encode_fraction(sum(loads.values(), F(0))),
        "hn_current_weight": "1/32",
        "hn_conditional_occupancy_bound": "exp(-1/32)/5 > 31/160",
        "hn_noncover_prefix_bound": "exp(-B)/5",
        "exact_conditional_current_marginals": [encode_fraction(x) for x in conditional_marginals],
        "exact_relative_future_hole": encode_fraction(future_hole),
        "exact_uncovered_prefix_mass": encode_fraction(future_hole / 5),
        "private_integer_modular_checks": len(originals) ** 2,
        "scope": "Finite noncover illustrating the conditional HN interface; no uniform odd-cover result.",
    }


def compute():
    return {"schema": "hn-prefix-diagnostic-v1", "pullback": check_pullback(),
            "benchmark": benchmark(),
            "source": {"url": "https://arxiv.org/pdf/1703.02133v2",
                       "theorem": "Theorem 4, equations (5) and (6), page 4",
                       "proof": "Section 4, pages 7-9"}}


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    parser.add_argument("--base", type=Path,
                        default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location("hn_certificate_io", args.base / "certificate_io.py")
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    actual = compute()
    if args.write:
        io.write_certificate_text(args.base / CERTIFICATE, json.dumps(actual, indent=2) + "\n")
    else:
        # JSON normalization converts tuples to the certificate's lists.
        normalized = json.loads(json.dumps(actual))
        require(json.loads(io.read_artifact_bytes(args.base / CERTIFICATE),
                           object_pairs_hook=io._unique) == normalized,
                "Certificate does not match exact recomputation")
    print(json.dumps({"result": "PASS", "original_count": actual["benchmark"]["original_count"],
                      "pullback_membership_checks": actual["pullback"]["individual_membership_checks"],
                      "private_integer_modular_checks": actual["benchmark"]["private_integer_modular_checks"]}))


if __name__ == "__main__":
    main()
