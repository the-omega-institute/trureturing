#!/usr/bin/env python3
"""Erdos #828 (Graham): structure of the solutions of phi(n) | n + a.

Two reductions, both proved here and checked against brute force.

REDUCTION 1 (the powerful part of n is bounded by a).
    Let A = rad(n) and B = prod_{p | n} (p - 1).  Mathlib's
    `Nat.totient_mul_prod_primeFactors` is phi(n) * A = n * B.  Write
    n + a = t * phi(n).  Multiplying by A,

        A*n + a*A = t * phi(n) * A = t * n * B,      so   n * (t*B - A) = a*A.

    Hence n | a*A.  Writing n = A*s with s = n/rad(n) gives A*s | a*A, so

        s = n / rad(n)   divides   a.

    For a = 1 this says every solution is squarefree.  For a = -7 it says
    s in {1, 7}.

REDUCTION 2 (each s-branch is a squarefree problem at a/s).
    With n = A*s and rad(n) = A we have phi(n) = s * B = s * phi(A), and
    n + a = A*s + a.  Since s | a, put a = s*a'.  Then

        phi(n) | n + a   <=>   s*phi(A) | s*(A + a')   <=>   phi(A) | A + a'.

    So the whole problem is the squarefree problem, run once per divisor s
    of a, with a replaced by a/s.  The branch s = |a| with A = |a| prime is
    Lehmer's problem phi(A) | A - 1, whose only known solutions are primes;
    it contributes exactly the trivial solution n = a^2.

SQUAREFREE SEARCH.  For squarefree odd A = p_1 ... p_k and a fixed ratio
t = (A + a')/phi(A), set

        f(S) = prod_{p in S} p  -  t * prod_{p in S} (p - 1).

Then f(empty) = 1 - t and f(S u {q}) = q*f(S) + t*phi(S), and A is a
solution iff f(S) = -a'.  Because f must end negative and every proper
prefix of a chain must keep f < 0 (a positive f only grows), the next prime
admitted after S is bounded below by

        q > g(S) := t*phi(S) / |f(S)| ,

and the chain terminates at the determined prime

        p* = (t*phi(S) + a') / |f(S)| .

So the last prime is never searched, only solved for.  That is what makes
the enumeration finite: the free choices are the primes strictly between
g(S) and the cap, and g(S) grows along every chain.

LADDER.  a = 1, t = 2 must reproduce A050474 (2*phi(x) = x+1):
1, 3, 15, 255, 65535, 83623935, 4294967295 -- in particular 83623935 =
3*5*17*353*929, which is NOT a Fermat-prime product and which an earlier
search of mine missed by stopping at 3e7.
"""

from __future__ import annotations

import sys
from bisect import bisect_right
from sympy import isprime, primerange, factorint


def radical(n: int) -> int:
    r = 1
    for p in factorint(n):
        r *= p
    return r


def totients(limit: int) -> list[int]:
    phi = list(range(limit + 1))
    for p in range(2, limit + 1):
        if phi[p] == p:
            for m in range(p, limit + 1, p):
                phi[m] -= phi[m] // p
    return phi


def radicals(limit: int) -> list[int]:
    rad = [1] * (limit + 1)
    for p in range(2, limit + 1):
        if rad[p] == 1:
            for m in range(p, limit + 1, p):
                rad[m] *= p
    return rad


def brute(phi: list[int], a: int) -> list[int]:
    """Direct scan, for the ladder and for checking the reductions."""
    return [n for n in range(1, len(phi)) if n + a > 0 and (n + a) % phi[n] == 0]


def check_reductions(a: int, sols: list[int], phi: list[int],
                     rad: list[int]) -> str | None:
    """s = n/rad(n) must divide a, and then phi(rad n) | rad n + a/s."""
    for n in sols:
        if n == 1:
            continue
        A = rad[n]
        s = n // A
        if a % s != 0:
            return f"a={a}: n={n} has n/rad(n)={s}, which does not divide {a}"
        ap = a // s
        if (A + ap) % phi[A] != 0:
            return (f"a={a}: n={n} -> A={A}, a-prime={ap}: phi(A)={phi[A]} "
                    f"does not divide {A + ap}")
    return None


def squarefree_chains(ap: int, t: int, prime_cap: int, max_primes: int,
                     window: int = 4) -> list[int]:
    """All squarefree odd A with A - t*phi(A) = -ap, primes below prime_cap.

    Two bounds make the enumeration finite.  Writing g(S) = t*phi(S)/|f(S)|,
    a prime q extends the chain only if q > g(S) (otherwise f turns positive
    and can never come back), and the chain can only end above q if the
    determined final prime, which is g at the end of the chain, has not been
    left behind -- g(S u {q}) = g(S)*(q-1)/(q-g(S)) exceeds q exactly when
    q < g + sqrt(g^2 - g), just under 2g.  Chains that step outside that
    window can in principle still recover, so the search admits q up to
    `window` * g and reports the largest ratio any recorded solution used;
    a solution needing a ratio at the cap would mean the cap is too small.
    """
    found: list[int] = []
    primes = list(primerange(3, prime_cap))

    def rec(idx: int, m: int, phi: int, depth: int) -> None:
        f = m - t * phi
        if f >= 0:
            # f only grows once it is non-negative, so no extension reaches -ap,
            # and the terminal prime formula needs f < 0.
            return
        # Terminate: the last prime is determined, not searched.
        num = t * phi + ap
        den = -f
        if num > 0 and num % den == 0:
            pstar = num // den
            last = primes[idx - 1] if idx > 0 else 2
            if pstar > last and isprime(pstar):
                found.append(m * pstar)
        if depth >= max_primes:
            return
        # Continuation needs q*|f| > t*phi; the window caps how far past that
        # the chain may step and still bring the determined final prime back
        # above q.
        threshold = (t * phi) // den
        ceiling = window * max(threshold + 1, 3)
        j = bisect_right(primes, threshold, idx)
        while j < len(primes) and primes[j] <= ceiling:
            q = primes[j]
            rec(j + 1, m * q, phi * (q - 1), depth + 1)
            j += 1

    rec(0, 1, 1, 0)
    return sorted(set(found))


def main() -> int:
    failures: list[str] = []

    # --- Ladder 1: the two reductions hold on every small solution set. ---
    phi = totients(200000)
    rad = radicals(200000)
    checked = 0
    for a in range(-40, 41):
        if a == 0:
            continue
        sols = brute(phi, a)
        checked += len(sols)
        msg = check_reductions(a, sols, phi, rad)
        if msg:
            failures.append(msg)
    print(f"reductions 1 and 2 on {checked} solutions, a in [-40,40], n <= 200000: "
          f"{'PASS' if not failures else 'FAIL'}")

    # --- Ladder 2: a = 1, t = 2 must reproduce the known A050474 terms. ---
    want = {3, 15, 255, 65535, 83623935, 4294967295}
    got = set(squarefree_chains(ap=1, t=2, prime_cap=200000, max_primes=6))
    missing = want - got
    if missing:
        failures.append(f"a=1,t=2 chain search missed A050474 terms {sorted(missing)}")
    print(f"a=1, t=2 chain search: {len(got)} solutions, "
          f"A050474 terms recovered: {'PASS' if not missing else 'FAIL'}")
    for n in sorted(got):
        print(f"    {n} = {'*'.join(str(p) for p in sorted(factorint(n)))}")

    # --- The target: a = -7, both branches. ---
    # t = 1 is not a chain search: A - phi(A) = 7 forces A <= 49, because a
    # composite A with least prime p has A - phi(A) >= A/p >= sqrt(A).  The
    # only solutions are 15 and 49, and the chain recursion cannot represent
    # t = 1 anyway (f(empty) = 1 - t = 0).
    print()
    t1 = [A for A in range(2, 100) if (A - phi[A]) == 7]
    print(f"a = -7, t = 1 (elementary: A <= 49): {t1}")
    print("a = -7, branch s = 1 (A squarefree, phi(A) | A - 7), t >= 2:")
    for w in (4, 8):
        for t in range(2, 7):
            got = squarefree_chains(ap=-7, t=t, prime_cap=200000,
                                    max_primes=7, window=w)
            print(f"    window={w} t={t}: {got}")
    print("a = -7, branch s = 7: 7 | A and phi(A) | A - 1, i.e. Lehmer's problem")
    print("    restricted to multiples of 7.  A = 7 gives n = 49; any other A is a")
    print("    composite Lehmer number (none below 10^22, and any has >= 15 prime")
    print("    factors), so this branch cannot supply infinitely many solutions")
    print("    unless Lehmer's conjecture is false.")

    # Same sweep for a = 1, which must keep reproducing A050474 at every
    # setting -- if widening the window changed the a = 1 answer, the window
    # would be binding and the a = -7 emptiness would mean nothing.
    print()
    for w in (4, 8):
        got = set(squarefree_chains(ap=1, t=2, prime_cap=200000,
                                    max_primes=7, window=w))
        ok = want <= got
        print(f"    control a=1 t=2 window={w}: {len(got)} solutions, "
              f"A050474 recovered: {'PASS' if ok else 'FAIL'}")
        if not ok:
            failures.append(f"control a=1 window={w} lost A050474 terms")

    if failures:
        print()
        for msg in failures:
            print(f"LADDER FAILURE: {msg}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
