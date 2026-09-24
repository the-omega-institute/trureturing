#!/usr/bin/env python3
"""Erdos 985: for every prime p, is there a prime q < p that is a primitive root mod p?

A counterexample is a single prime, so the negative side is finitely certifiable and this
search can settle it outright. What the run actually reports is the margin: the least PRIME
primitive root g(p) against p itself, since a counterexample needs g(p) > p.

The ladder is the three smallest primes whose least prime primitive root is not 2, which
must come out as 7 -> 3, 17 -> 3 and 23 -> 5. A run that cannot reproduce them says nothing
about any range, so it exits non-zero before searching.

Standard library only; no third-party dependency.
"""
import sys


def sieve(n):
    """Primes below n."""
    flag = bytearray([1]) * n
    flag[0:2] = b"\0\0"
    for i in range(2, int(n ** 0.5) + 1):
        if flag[i]:
            flag[i * i::i] = bytearray(len(flag[i * i::i]))
    return [i for i in range(n) if flag[i]]


def prime_factors(m):
    """Distinct primes dividing m, by trial division."""
    out, d = [], 2
    while d * d <= m:
        if m % d == 0:
            out.append(d)
            while m % d == 0:
                m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        out.append(m)
    return out


def least_prime_proot(p, primes):
    """Smallest prime q < p that generates (Z/p)*, or None if no such q exists."""
    if p == 2:
        return None                        # no prime lies below 2
    fac = prime_factors(p - 1)
    for q in primes:
        if q >= p:
            return None                    # counterexample: every prime below p fails
        if all(pow(q, (p - 1) // f, p) != 1 for f in fac):
            return q


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    primes = sieve(limit)
    for p, want in ((7, 3), (17, 3), (23, 5)):
        got = least_prime_proot(p, primes)
        if got != want:
            print(f"ladder FAILED at p={p}: got {got} want {want}", file=sys.stderr)
            return 1
    print("ladder: ok (7->3, 17->3, 23->5)", file=sys.stderr)

    counterexamples, worst_g, worst_p = [], 0, 0
    for p in primes:
        g = least_prime_proot(p, primes)
        if g is None:
            counterexamples.append(p)      # p=2 is the vacuous literal case
            continue
        if g > worst_g:
            worst_g, worst_p = g, p
    print(f"primes below {limit}: {len(primes)}")
    print(f"counterexamples with p > 2: {[c for c in counterexamples if c > 2]}")
    print(f"largest least-prime-primitive-root: g={worst_g} at p={worst_p}")
    print(f"vacuous literal case p=2 present: {2 in counterexamples}")
    return 0


sys.exit(main())
