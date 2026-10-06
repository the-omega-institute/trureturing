#!/usr/bin/env python3
"""Enclose the golden dyadic prime-kernel coefficient and finite cuts."""

from __future__ import annotations

import argparse
import json
import math
import sys
from bisect import bisect_right
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "fib-source-local-multipliers"))
from certify_multipliers import SUPPLIER_SHA256, load_supplier


def pair(value: Fraction) -> list[str]:
    return [str(value.numerator), str(value.denominator)]


def interval_record(interval) -> dict:
    return {"lower": pair(interval.lower), "upper": pair(interval.upper)}


def run(supplier, cutoffs: list[int], bits: int) -> dict:
    scale = 2 ** (bits + 12)
    root = math.isqrt(5 * scale * scale)
    assert root * root <= 5 * scale * scale < (root + 1) ** 2
    q_lower = (3 - Fraction(root + 1, scale)) / 2
    q_upper = (3 - Fraction(root, scale)) / 2
    assert 0 < q_lower <= q_upper < Fraction(2, 5)
    terms = 7

    def enclose(lower: Fraction, upper: Fraction):
        return supplier.dyadic_enclosure(supplier.Interval(lower, upper), bits)

    def log_range(lower: Fraction, upper: Fraction):
        return enclose(
            supplier.log_interval(lower, bits + 12).lower,
            supplier.log_interval(upper, bits + 12).upper,
        )

    beta = [log_range(1 + q_lower, 1 + q_upper)]
    for a in range(1, terms):
        exponent = 2**a
        beta.append(log_range(1 - q_upper**exponent, 1 - q_lower**exponent))

    coefficient_lower = sum(-beta[a].upper / 2 ** (a + 1) for a in range(terms))
    coefficient_upper = sum(-beta[a].lower / 2 ** (a + 1) for a in range(terms))
    coefficient_tail = q_upper ** (2**terms) / (2**terms * (1 - q_upper**2))
    coefficient = enclose(coefficient_lower, coefficient_upper + coefficient_tail)
    assert Fraction(-12, 100) < coefficient.lower
    assert coefficient.upper < Fraction(-119, 1000)

    primes = [p for p in supplier.primes_up_to(max(cutoffs)) if p != 2]
    rows = []
    for cutoff in cutoffs:
        count = bisect_right(primes, cutoff)
        depth = (cutoff // 3).bit_length() - 1
        bands = [
            bisect_right(primes, cutoff // 2**a)
            - bisect_right(primes, cutoff // 2 ** (a + 1))
            for a in range(depth + 1)
        ]
        assert sum(bands) == count
        lower = sum(-bands[a] * beta[a].upper for a in range(min(terms, len(bands))))
        upper = sum(-bands[a] * beta[a].lower for a in range(min(terms, len(bands))))

        # Every terminal exceeds cutoff/2 >= 128.  For a >= 7, 2^a >= 128.
        # q < 1/2 gives the same coarse bound for the terminal error and
        # the omitted positive even-beta contribution, without huge powers.
        allowance = Fraction(count, 2**128) / (1 - q_upper)
        prime_cut = enclose(lower - allowance, upper + 2 * allowance)
        log_cutoff = supplier.log_interval(Fraction(cutoff), bits + 12)
        products = [
            endpoint * log_endpoint / cutoff
            for endpoint in (prime_cut.lower, prime_cut.upper)
            for log_endpoint in (log_cutoff.lower, log_cutoff.upper)
        ]
        normalized = enclose(min(products), max(products))
        rows.append(
            {
                "cutoff": cutoff,
                "odd_prime_count": count,
                "dyadic_band_counts": bands,
                "retained_beta_terms": terms,
                "terminal_error_upper": pair(allowance),
                "omitted_even_beta_upper": pair(allowance),
                "prime_kernel_cut": interval_record(prime_cut),
                "normalized_cut": interval_record(normalized),
                "normalized_midpoint_float": float((normalized.lower + normalized.upper) / 2),
                "negative": prime_cut.upper < 0,
            }
        )

    return {
        "quantity": "sum over odd primes p<=X of beta(2^A*p)-beta(2^A), A=floor(log2(X/p))",
        "q": {"definition": "(3-sqrt(5))/2", "lower": pair(q_lower), "upper": pair(q_upper)},
        "supplier_sha256": SUPPLIER_SHA256,
        "supplier_calls": ["primes_up_to", "log_interval", "Interval", "dyadic_enclosure"],
        "enclosure_bits": bits,
        "coefficient": interval_record(coefficient),
        "coefficient_midpoint_float": float((coefficient.lower + coefficient.upper) / 2),
        "coefficient_tail_upper": pair(coefficient_tail),
        "retained_beta_intervals": [interval_record(value) for value in beta],
        "rows": rows,
        "scope": "exact finite prime cuts and coefficient enclosure; no composite cut calculation, CA events, original root verification or Lean",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--cutoffs", type=int, nargs="+", default=[1000, 10000, 100000, 1000000])
    parser.add_argument("--bits", type=int, default=80)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.bits < 40 or any(cutoff < 256 for cutoff in args.cutoffs):
        parser.error("require at least 40 bits and cutoffs >= 256")
    supplier, _, _ = load_supplier(args.archive.resolve())
    result = run(supplier, args.cutoffs, args.bits)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"{len(result['rows'])} exact cuts; coefficient in (-0.12,-0.119)")


if __name__ == "__main__":
    main()
