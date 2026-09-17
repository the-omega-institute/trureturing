#!/usr/bin/env python3
"""Exhaustive check of the Rotondo sufficient condition for Lucas-Carmichael numbers.

Source: OEIS A006972, COMMENTS, Davide Rotondo, Dec 23 2020, verbatim:

    Conjecture: if k = p*q*r, p = a*d - 1, q = b*d - 1, r = c*d - 1 are distinct odd
    primes, with d = gcd(p + 1, q + 1, r + 1) and a*b*c*d divides k + 1, then k is a
    Lucas-Carmichael number.

A006972's own definition line, verbatim:

    Lucas-Carmichael numbers: squarefree composite numbers k such that p | k => p+1 | k+1.

The script enumerates every odd-prime triple with k = p*q*r <= LIMIT, evaluates the
hypothesis exactly, and reports three numbers a reader can recompute: how often the
hypothesis holds, how often the conclusion holds with it, and how many three-factor
Lucas-Carmichael numbers in range the hypothesis fails to capture. The condition is
stated as sufficient, not necessary, so a non-zero miss count is not a counterexample.

Exact integer arithmetic only; no floating point anywhere. Standard library only.

usage: rotondo-lucas-carmichael-check.py [LIMIT]   (default 200000)
exit 0 = no counterexample found; exit 1 = counterexample found (printed).
"""
import math
import sys


def sieve(n):
    """Every prime <= n, by a plain sieve of Eratosthenes."""
    flags = bytearray([1]) * (n + 1)
    flags[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(n) + 1):
        if flags[i]:
            flags[i * i :: i] = bytearray(len(flags[i * i :: i]))
    return [i for i in range(n + 1) if flags[i]]


def factor(n, primes):
    """Prime factorisation of n as {p: exponent}, by trial division."""
    f = {}
    for p in primes:
        if p * p > n:
            break
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def is_lucas_carmichael(k, primes):
    """The %N definition, applied literally: squarefree, composite, and p+1 | k+1."""
    f = factor(k, primes)
    if len(f) < 2 or any(e > 1 for e in f.values()):
        return False
    return all((k + 1) % (p + 1) == 0 for p in f)


def main(limit):
    primes = sieve(limit)
    odd = [p for p in primes if p > 2]
    hits, counterexamples = [], []
    n = len(odd)
    for i in range(n):
        p = odd[i]
        if p * 5 * 7 > limit:
            break
        for j in range(i + 1, n):
            q = odd[j]
            if p * q * (q + 2) > limit:
                break
            for m in range(j + 1, n):
                r = odd[m]
                k = p * q * r
                if k > limit:
                    break
                d = math.gcd(p + 1, math.gcd(q + 1, r + 1))
                a, b, c = (p + 1) // d, (q + 1) // d, (r + 1) // d
                if (k + 1) % (a * b * c * d) != 0:
                    continue
                hits.append((k, p, q, r, a, b, c, d))
                if not is_lucas_carmichael(k, primes):
                    counterexamples.append(k)

    print("LIMIT=%d" % limit)
    print("hypothesis satisfied by %d triples; conclusion holds for %d; COUNTEREXAMPLES: %d"
          % (len(hits), len(hits) - len(counterexamples), len(counterexamples)))
    for k, p, q, r, a, b, c, d in sorted(hits)[:12]:
        print("  k=%d = %d*%d*%d   a,b,c,d = %d,%d,%d,%d   abcd=%d | k+1=%d"
              % (k, p, q, r, a, b, c, d, a * b * c * d, k + 1))
    if counterexamples:
        print("  COUNTEREXAMPLES:", counterexamples[:20])
        return 1

    captured = {h[0] for h in hits}
    missed = [k for k in range(3, limit, 2)
              if k not in captured
              and len(factor(k, primes)) == 3
              and all(e == 1 for e in factor(k, primes).values())
              and is_lucas_carmichael(k, primes)]
    print("three-factor Lucas-Carmichael numbers below %d not captured by the hypothesis: %d"
          % (limit, len(missed)))
    if missed:
        print("  e.g.", missed[:12])
    return 0


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 200000))
