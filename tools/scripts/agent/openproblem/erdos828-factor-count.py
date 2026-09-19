#!/usr/bin/env python3
"""Erdos #828 (Graham): complete enumeration by NUMBER of prime factors.

Companion to erdos828-radical-reduction.py, which reduces phi(n) | n + a to the
squarefree problem phi(A) | A + a' and searches with a prime cap.  This script
removes the prime cap entirely, at the cost of fixing the number k of prime
factors: for each k the search space is provably finite.

    A = p_1 < ... < p_k odd squarefree,   A + a' = t * phi(A).

Writing S = p_1..p_{k-1} and F(S) = t*phi(S) - S, the last prime is solved for
rather than searched, because A = S*p_k and phi(A) = phi(S)*(p_k - 1) give

    S*p_k + a' = t*phi(S)*(p_k - 1)      =>   p_k * F(S) = t*phi(S) + a'.

A positive p_k forces F(S) >= 1, which is the lower bound q > t*phi/F on every
continuation.  The upper bound comes from p_k > p_{k-1}.  Writing S = S'*Q and
F(S) = Q*F(S') - t*phi(S'), the inequality p_k > Q reads

    Q^2 * F' < 2t*phi'*Q - t*phi' + a' < 2t*phi'*Q,     so   Q < 2t*phi'/F'.

Propagating that back one prime at a time: if the next prime must satisfy
x < c*phi/F, then the prime y before it must leave room for such an x above y,
c*phi_y*(y-1)/(y*F_y - t*phi_y) > y, which gives y*y*F_y < (c+t)*phi_y*y, i.e.
y < (c+t)*phi_y/F_y.  So the factor grows by t each level:

    c_1 = 2t,   c_{j+1} = c_j + t,   hence   c_j = (j+1)*t,

and the i-th prime of a k-chain is confined to

    t*phi/F  <  p_i  <  (k-i+1) * t*phi/F.

The empty prefix has phi = 1, S = 1, F = t-1, so for t = 2 the smallest prime
obeys p_1 < 2k.  Every level is a finite interval, so the enumeration is
complete for each k with no bound on the size of the primes.  Each step uses
only F >= 1 and drops a positive term, so the bound over-approximates and
completeness is preserved.

LADDER.  a = 1, t = 2 must reproduce A050474 exactly, one term per k and none
missing, with the budget guard never tripping:
    k=1: 3        k=4: 65535
    k=2: 15       k=5: 83623935, 4294967295
    k=3: 255      k=6: 6992962672132095
A run that misses any of these, or that trips the budget on the control, means
the bounds above are wrong and no emptiness result from this script stands.
"""

from __future__ import annotations

import sys

from sympy import isprime, primerange

# Primes examined per (ap, t, k) before the run is declared inconclusive.
BUDGET = 4_000_000


def chains(ap: int, t: int, k: int, budget: int = BUDGET) -> tuple[list[int], bool]:
    """Every odd squarefree A with exactly k prime factors and A + ap = t*phi(A).

    Returns (solutions, capped).  `capped` true means the budget stopped the
    walk, so an empty result is inconclusive rather than a proof.
    """
    out: list[int] = []
    examined = 0
    capped = False

    def rec(i: int, m: int, phi: int, last: int) -> None:
        nonlocal examined, capped
        f = t * phi - m
        if i == k - 1:
            if f >= 1:
                num = t * phi + ap
                if num > 0 and num % f == 0:
                    p = num // f
                    if p > last and isprime(p):
                        out.append(m * p)
            return
        if f < 1 or capped:
            return
        lo = max((t * phi) // f, last) + 1
        hi = ((k - i) * t * phi) // f
        if hi < lo:
            return
        for q in primerange(lo, hi + 1):
            examined += 1
            if examined > budget:
                capped = True
                return
            rec(i + 1, m * q, phi * (q - 1), q)

    rec(0, 1, 1, 2)
    return sorted(set(out)), capped


A050474 = {3, 15, 255, 65535, 83623935, 4294967295, 6992962672132095}


def main() -> int:
    failures: list[str] = []

    got: set[int] = set()
    for k in range(1, 7):
        found, capped = chains(1, 2, k)
        got |= set(found)
        if capped:
            failures.append(f"control a=1 t=2 k={k} tripped the budget")
        print(f"control a=1 t=2 k={k}: {found}")
    missing = A050474 - got
    if missing:
        failures.append(f"control lost A050474 terms {sorted(missing)}")
    print(f"control verdict: A050474 {'PASS' if not missing else 'FAIL'}")
    print()

    for ap in (-7, -11, -13, -37):
        for t in (2, 3):
            hits, capped_at = [], []
            for k in range(2, 8):
                found, capped = chains(ap, t, k)
                if found:
                    hits.append((k, found))
                if capped:
                    capped_at.append(k)
            verdict = hits if hits else "EMPTY"
            note = f"; inconclusive at k in {capped_at}" if capped_at else "; complete"
            print(f"a={ap:4d} t={t} k in [2,7]: {verdict}{note}")

    if failures:
        print()
        for msg in failures:
            print(f"LADDER FAILURE: {msg}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
