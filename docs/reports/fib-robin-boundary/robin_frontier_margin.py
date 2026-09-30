#!/usr/bin/env python3
"""Attach conservative exact Robin-margin lower bounds to a frontier.

The frontier certificate contains the exact suffix weight.  This script uses
the existing rational logarithm and Euler-constant bounds from ``kernel_tail``
to certify positive lower bounds for a finite fixed-core scan.  It never
claims a bound outside the supplied certificate.
"""
import sys
sys.dont_write_bytecode = True

import argparse
from fractions import Fraction
import hashlib
import json
from math import gcd
from pathlib import Path

from kernel_tail import exp_gamma_lower, log_interval
from robin_frontier_check import check as check_frontier


def factor(n):
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            exponent = 0
            while n % p == 0:
                n //= p
                exponent += 1
            result.append((p, exponent))
        p += 1
    if n > 1:
        result.append((n, 1))
    return result


def normalized_sigma(n):
    value = Fraction(1)
    for p, exponent in factor(n):
        value *= sum((Fraction(1, p ** j) for j in range(exponent + 1)),
                     Fraction(0))
    return value


def lower_margin(core, suffix, weight, gamma_exp):
    number = core * suffix
    log_lower = log_interval(Fraction(number))[0]
    if log_lower <= 1:
        raise ValueError("the supplied core is too small for log-log bounds")
    loglog_lower = log_interval(log_lower)[0]
    return gamma_exp * loglog_lower - normalized_sigma(core) * weight


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--core", type=int, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    certificate_bytes = args.certificate.read_bytes()
    certificate = json.loads(certificate_bytes)
    if certificate.get("schema") != "robin-rough-frontier-v1":
        raise ValueError("wrong frontier schema")
    frontier_check = check_frontier(certificate)
    if args.core < 5040:
        raise ValueError("core must be at least 5040")
    y = certificate.get("y")
    if type(y) is not int or y < 1:
        raise ValueError("frontier certificate has invalid rough cutoff")
    if any(p > y for p, _ in factor(args.core)):
        raise ValueError("core has a prime factor outside the rough cutoff")
    if not certificate.get("frontier"):
        raise ValueError("frontier certificate is empty")
    gamma_exp = exp_gamma_lower()[2]
    rows = []
    for entry in certificate["frontier"]:
        suffix = entry["number"]
        weight = Fraction(*entry["weight"])
        if gcd(args.core, suffix) != 1:
            raise ValueError("frontier suffix is not coprime to the core")
        gap = lower_margin(args.core, suffix, weight, gamma_exp)
        rows.append({
            "suffix": suffix,
            "number": args.core * suffix,
            "weight": [weight.numerator, weight.denominator],
            "margin_lower": [gap.numerator, gap.denominator],
            "positive": gap > 0,
        })
    minimum = min(rows, key=lambda row: Fraction(*row["margin_lower"]))
    result = {
        "status": "PASS" if all(row["positive"] for row in rows) else "OPEN",
        "core": args.core,
        "frontier_certificate": str(args.certificate),
        "certificate_sha256": hashlib.sha256(certificate_bytes).hexdigest(),
        "frontier_check": frontier_check,
        "y": y,
        "suffix_bound": certificate["bound"],
        "frontier_size": len(rows),
        "all_lower_bounds_positive": all(row["positive"] for row in rows),
        "minimum": minimum,
        "rows": rows,
        "scope": (
            "Verified finite frontier for this core, rough cutoff and suffix "
            "bound, including suffix 1. Rational log and exp(gamma) lower "
            "bounds certify positive signs only; OPEN is not a counterexample."
        ),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "status": result["status"],
        "core": args.core,
        "frontier_size": len(rows),
        "all_lower_bounds_positive": result["all_lower_bounds_positive"],
        "minimum_suffix": minimum["suffix"],
    }))


if __name__ == "__main__":
    main()
