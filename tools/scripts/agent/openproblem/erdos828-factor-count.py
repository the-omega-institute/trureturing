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

THE LAST SEARCHED PRIME IS NOT SEARCHED EITHER.  For the prime q chosen just
before the solved-for p_k, put D = F(S u {q}) = q*F - t*phi.  Then q = (D+t*phi)/F
and q - 1 = (D+S)/F, so p_k = (t*phi*(q-1) + a')/D rearranges to

    D * (F*p_k - t*phi) = N,        N = t*phi(S)*S + a'*F(S),

a single fixed integer.  So D ranges over the DIVISORS of N, and both
q = (D + t*phi)/F and p_k = (t*phi + N/D)/F follow.  This is what makes the
search tractable: the widest interval in the whole walk is the F=1 Fermat-type
branch, where the prefix 3*5*17*257*65537 has phi = 2^31 and the next prime
would have to be scanned over (2^32, 2^33] -- some 2*10^8 primes.  As a divisor
condition that branch is just the factorisation of N = 2^64 - 2^32 - 7.

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

from fractions import Fraction

from sympy import divisors, isprime, primerange

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
        if f < 1 or capped:
            return
        if i == k - 2:
            # Last searched prime: solve D | N instead of scanning an interval.
            n_fixed = t * phi * m + ap * f
            if n_fixed <= 0:
                return
            tphi = t * phi
            for d in divisors(n_fixed):
                if (d + tphi) % f:
                    continue
                q = (d + tphi) // f
                if q <= last or not isprime(q):
                    continue
                co = tphi + n_fixed // d
                if co % f:
                    continue
                p = co // f
                if p > q and isprime(p):
                    out.append(m * q * p)
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

    if k >= 2:
        rec(0, 1, 1, 2)
    return sorted(set(out)), capped


# A050474 from k = 2 upward; k = 1 is the single prime 3, which has no
# searched prime and so no chain to enumerate.
A050474 = {15, 255, 65535, 83623935, 4294967295, 6992962672132095}


def max_ratio(k: int) -> Fraction:
    """Sup of A/phi(A) over odd squarefree A with k prime factors.

    Attained in the limit by the k smallest odd primes.  Since A + a' = t*phi(A)
    forces A/phi(A) > t, this caps t as a function of k: t <= 2 for k <= 7,
    t <= 3 for k <= 20.  Reporting an empty result for a (t, k) pair above this
    cap would be vacuous, not evidence, so main() skips those pairs instead of
    printing them.
    """
    r = Fraction(1)
    for i, q in enumerate(primerange(3, 10 ** 6)):
        if i >= k:
            break
        r *= Fraction(q, q - 1)
    return r


def main() -> int:
    failures: list[str] = []

    got: set[int] = set()
    for k in range(2, 7):
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

    targets = [int(x) for x in sys.argv[1:]] or [-7]
    for ap in targets:
        for t in (2, 3):
            hits, capped_at, live = [], [], []
            for k in range(2, 8):
                if max_ratio(k) <= t:
                    continue        # A/phi(A) cannot exceed t with k factors
                live.append(k)
                found, capped = chains(ap, t, k)
                if found:
                    hits.append((k, found))
                if capped:
                    capped_at.append(k)
            if not live:
                print(f"a={ap:4d} t={t}: no k in [2,7] admits this t "
                      f"(A/phi(A) tops out at {float(max_ratio(7)):.4f})")
                continue
            verdict = hits if hits else "EMPTY"
            note = f"; inconclusive at k in {capped_at}" if capped_at else "; complete"
            print(f"a={ap:4d} t={t} k in {live}: {verdict}{note}")

    if failures:
        print()
        for msg in failures:
            print(f"LADDER FAILURE: {msg}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
