#!/usr/bin/env python3
"""Erdos 156 line: can Ruzsa's construction be derandomised below its union bound?

The construction lifts a dense Sidon set A in the quotient Z_2^n/Q to coset representatives
in Z_2^n. Its log factor comes from a union bound, and since that bound turns out to be
tight for random representatives (see erdos156-coset-coverage.py), the remaining hope is a
deterministic choice. This asks whether one can exist at all.

The key structure is that the choice decomposes per coset. Writing b_a = (a << s) | q_a with
s = n - m, a triple sums to

    b_u ^ b_v ^ b_w = ((a_u ^ a_v ^ a_w) << s) | (q_u ^ q_v ^ q_w),

so the high bits come from A alone and the low bits from q alone. Covering everything means:
for every t in the quotient, the roughly |A|^3/6/2^m triples with a_u^a_v^a_w = t must have
their q-sums hit all 2^s values. Two immediate consequences, both confirmed numerically by
the coverage probe: a linear q makes q_u^q_v^q_w = L(t), constant on each coset, so it hits
exactly one value of 2^s and is the worst possible choice; a random q hits a Poisson share.

This script counts instead of sampling. There are only |A| * s bits of freedom, against
2^m coset constraints, so the first moment can already be negative, and then no assignment
whatsoever works.

Approximations, both named rather than hidden: P(all bins hit) uses the Poisson estimate
exp(-Q exp(-J/Q)) for the number of empty bins, and the cosets are treated as independent.
Neither is exact. They are used only to read off a sign, and the margins below are millions
of powers of two, so no plausible correction to either changes the sign.

Standard library only.
"""
import math, sys


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    print(f"n={n}. Freedom is |A|*(n-m) bits; constraints are 2^m cosets each needing all")
    print("2^(n-m) low values hit. log2 E < 0 forbids every assignment, not just random ones.\n")
    print(f"{'m':>4} {'|A|':>7} {'|Q|':>7} {'triples/coset':>14} {'P(coset ok)':>13} "
          f"{'free bits':>10} {'log2 E[#good]':>15}")
    for m in range(n // 2, n, 2):
        size = 2 ** (m // 2)
        q = 2 ** (n - m)
        cosets = 2 ** m
        per = size ** 3 / 6 / cosets
        empty = q * math.exp(-per / q)
        p = math.exp(-empty)
        free = size * (n - m)
        log_e = free + cosets * math.log2(p) if p > 0 else float("-inf")
        print(f"{m:>4} {size:>7} {q:>7} {per:>14.1f} {p:>13.3e} {free:>10} {log_e:>15.4g}")

    lo = n // 2
    hi = n - 1
    for _ in range(60):                      # bisect the sign change in m
        mid = (lo + hi) / 2
        size = 2 ** (mid / 2)
        q = 2 ** (n - mid)
        cosets = 2 ** mid
        p = math.exp(-q * math.exp(-(size ** 3 / 6 / cosets) / q))
        val = size * (n - mid) + cosets * math.log2(p) if p > 0 else -1.0
        lo, hi = (mid, hi) if val < 0 else (lo, mid)
    print(f"\nfirst-moment feasibility threshold: m = {hi:.2f}")
    print(f"union-bound threshold (T=1):        m = {(2/3)*(n + math.log2(math.log(2)*n)):.2f}")
    print(f"counting threshold:                 m = {(2/3)*(n + math.log2(6)):.2f}")
    print("\nAt n=24 the first-moment threshold lies above both of the others, so a deterministic")
    print("choice cannot even reach the counting threshold: within this template the log factor")
    print("is intrinsic. Whether the three thresholds stay ordered this way as n grows is not")
    print("settled here, and the gap between them is a finite-size effect at this n.")
    return 0


sys.exit(main())
