#!/usr/bin/env python3
"""Erdos 828 (a conjecture of Graham): for every a in Z, are there infinitely many n with
phi(n) | n + a?

Two cases are settled and they bracket the question. For a = 0 the solutions are exactly
n = 2^alpha * 3^beta with alpha >= 1, so infinitely many. For a = -1 every prime works, since
phi(p) = p - 1, so infinitely many again (whether composites also work is Lehmer's conjecture,
which is a different question).

This probe looks at the remaining a, and a = 1 is where the conjecture is in danger. Three
constraints hold for any n > 2 with phi(n) | n + a where a is odd and n is odd, and for a = 1
they are:

  n is odd         an even n > 2 has phi(n) even while n + 1 is odd;
  n is squarefree  if p^2 | n then p | phi(n) | n + 1 and p | n, so p | 1;
  gcd(n, phi(n))=1 if p | n and p | phi(n) | n + 1 then p | 1.

So n is a squarefree odd cyclic number. Every solution found so far is moreover an initial
Fermat segment, n = F_0 F_1 ... F_{k-1} = 2^(2^k) - 1, for which phi(n) = 2^(2^k - 1) and
n + 1 = 2^(2^k), giving (n+1)/phi(n) = 2 exactly.

That shape cannot continue. F_5 = 4294967297 = 641 * 6700417 is composite, so no initial
segment beyond F_0..F_4 exists, and the largest solution of this shape is 2^32 - 1. Hence if
the characterisation is complete, a = 1 admits only finitely many n and Graham's conjecture is
false. Whether it is complete is exactly what is open here, and nothing below proves it.

The ladder pins the two settled cases, since getting either wrong invalidates every reading.

Standard library plus numpy.
"""
import sys
import numpy as np


def totients(n):
    phi = np.arange(n + 1, dtype=np.int64)
    for p in range(2, n + 1):
        if phi[p] == p:                       # p is prime
            phi[p::p] -= phi[p::p] // p
    return phi


def solutions(phi, a, limit):
    n = np.arange(1, limit + 1)
    keep = n + a >= 1
    out = np.zeros(limit, dtype=bool)
    out[keep] = ((n[keep] + a) % phi[1:limit + 1][keep]) == 0
    return n[out]


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 3_000_000
    phi = totients(limit)

    small = min(limit, 20000)
    zero = set(solutions(phi, 0, small).tolist())
    want = {2 ** i * 3 ** j for i in range(1, 20) for j in range(20) if 2 ** i * 3 ** j <= small}
    want.add(1)
    if zero != want:
        print(f"ladder FAILED for a=0: {sorted(zero ^ want)[:10]}", file=sys.stderr)
        return 1
    minus = set(solutions(phi, -1, small).tolist())
    primes = {p for p in range(2, small + 1) if phi[p] == p - 1}
    if not primes <= minus:
        print("ladder FAILED for a=-1: some prime is not a solution", file=sys.stderr)
        return 1
    print("ladder: ok (a=0 gives exactly 1 and 2^alpha 3^beta; a=-1 contains every prime)",
          file=sys.stderr)

    print(f"{'a':>4}  solutions n <= {limit}")
    for a in (1, 2, 3, 5, 7, -3, -7):
        s = solutions(phi, a, limit).tolist()
        shown = s if len(s) <= 12 else s[:12] + ["..."]
        print(f"{a:>4}  count={len(s):<8} {shown}")
    print("\nfor a = 1 the solutions listed are 1, 2 and the initial Fermat segments")
    print("2^(2^k) - 1 for k = 1..4; the next such value is 2^32 - 1 = 4294967295, and")
    print("F_5 is composite so the shape stops there.")
    return 0


sys.exit(main())
