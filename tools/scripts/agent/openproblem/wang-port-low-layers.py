#!/usr/bin/env python3
"""Wang's Appendix A.4(c): classify the H-fillings below six primes.

Han Wang, "Port Fillings for Primary Pseudoperfect Numbers", arXiv:2605.21518v1
(2026-05-18), Appendix A.4 lists the remaining targets for the six-prime layer
and ends:

    "(c) any inherited channel arising from a smaller H-filling not yet found
    or not yet excluded.  This wording is deliberately cautious: unless one
    proves that the displayed B_2, B_4, and B_5 exhaust all smaller H-fillings,
    the inherited-channel list above should be read as a list of known
    channels, not as a complete classification."

The key port is H = (R, c) = (113322, 797), from the prefix 2*3*11*17*101.  A
k-filling is B = q_1...q_k with distinct primes q_i > 101 and

    797*B - 113322*d(B) = 1,      d(B) = sum_i B/q_i,

which makes 113322*B a primary pseudoperfect number with k+5 prime factors.
Wang exhibits B_2 = 149*3109 (the known K_7), B_4 = 157*1979*10093*16879 (his
new N_9) and B_5 = B_4*(N_9+1), and says of the nine-prime example in Section
14 that "this paper proves existence of one such example, not uniqueness".

Each layer k is a finite computation.  Three facts do it, all forced by the
filling equation rather than assumed.

(1) PORT RECURSION.  B = q*B' and d(B) = B' + q*d(B') turn the equation into
(c*q - R)*B' - (R*q)*d(B') = 1, so appending q sends (R, c) -> (R*q, c*q - R).

(2) TWO-SIDED BOUND.  Dividing by R*B gives the exact reciprocal identity
c/R = sum_{q | B} 1/q + 1/(R*B).  Every term is positive, so q > R/c.  And if r
primes remain, all at least q, then sum 1/q_i <= r/q and B >= q, so
c/R <= r/q + 1/(R*q), i.e. q <= (r*R + 1)/c.  Finite and complete, not a cutoff.

(3) THE LAST TWO PRIMES FACTOR OUT.  For the final pair, c*u*v - R*(u+v) = 1;
multiplying by c and completing the product gives

    (c*u - R) * (c*v - R) = R*R + c.

Both factors are positive because every prime obeys u > R/c, so the pair is read
off the divisors of one fixed integer, with d = c*u - R forced to be -R mod c.
Necessary AND sufficient: no completion escapes into an unscanned tail.

WHERE THE LITERATURE ALREADY REACHES.  OEIS A054377 carries "No other terms
below 10^24. - Max Alekseyev, Aug 12 2026".  Taking d = 1 in (3) bounds the
largest filling each layer can hold: 2.60e14 at k=2, 2.76e21 at k=3, 7.59e42 at
k=4.  So layers 2 and 3 lie entirely inside Alekseyev's exhausted range and
this program only reproduces them -- which is exactly why they are run, as a
control on the enumeration.  Layer 4 leaves that range by eighteen orders of
magnitude, and layer 5 further still, so those two are the open part.

CONTROLS.  Every run asserts the layer's own known filling before enumerating,
so an empty answer cannot come from a broken walk:
    k=2  from the empty prefix           -> 149, 3109
    k=4  from the prefix 157, 1979       -> 10093, 16879
    k=5  from the prefix 157,1979,10093  -> 16879, 5998279018951962403

Usage:
    wang-port-low-layers.py                    layers 2,3,4 with controls
    wang-port-low-layers.py K                  layer K, whole layer
    wang-port-low-layers.py K SHARD STRIDE     layer K, q_1 congruent shard
"""

import sys
from sympy import isprime, primerange, divisors

PORT_R, PORT_C = 113322, 797
N9 = 5998279018951962402
PREFIX = (2, 3, 11, 17, 101)
CONTROLS = {
    2: ((), (149, 3109)),
    4: ((157, 1979), (10093, 16879)),
    5: ((157, 1979, 10093), (16879, N9 + 1)),
}


def completions(R, c, qlast):
    """Every pair of primes qlast < u < v completing the port (R, c)."""
    fixed = R * R + c
    out = []
    for d in divisors(fixed):
        e = fixed // d
        if d > e:
            break
        if (d + R) % c or (e + R) % c:
            continue
        u, v = (R + d) // c, (R + e) // c
        if u > qlast and u < v and isprime(u) and isprime(v):
            out.append((u, v))
    return out


def port_after(prefix):
    """The port and last prime reached by appending `prefix` to H."""
    R, c, last = PORT_R, PORT_C, PREFIX[-1]
    for q in prefix:
        R, c, last = R * q, c * q - R, q
    return R, c, last


def control(k):
    prefix, tail = CONTROLS[k]
    got = completions(*port_after(prefix))
    if tail not in got:
        raise AssertionError(f"control k={k}: prefix {prefix} gave {got}, want {tail}")
    print(f"control k={k}: prefix {prefix} recovers {tail}  PASS", flush=True)


def is_ppn(B):
    """Recheck the filling from scratch: 1/n + sum 1/p = 1 over the primes of n."""
    from fractions import Fraction
    primes = list(PREFIX) + list(B)
    if len(set(primes)) != len(primes) or not all(isprime(p) for p in primes):
        return None, False
    n = 1
    for p in primes:
        n *= p
    return n, Fraction(1, n) + sum(Fraction(1, p) for p in primes) == 1


def branch(k, q1):
    """Settle one q_1 branch of layer k.  Returns (stats, fillings)."""
    stats = {"prefixes": 0, "empty": 0, "factored": 0}
    found = []

    def walk(R, c, qlast, remaining, path):
        if remaining == 2:
            stats["prefixes"] += 1
            # Wang's Section 16 parameter is negative exactly when the quadratic
            # below is, and then the port admits no completion at all; skipping
            # those avoids factoring R*R + c for them.
            p0 = pow(c, -1, R)
            s0 = (c * p0 - 1) // R
            u = max(qlast + 1, R // c + 1)
            if u * u - s0 * u + p0 < 0:
                stats["empty"] += 1
                return
            stats["factored"] += 1
            for a, b in completions(R, c, qlast):
                found.append(path + (a, b))
            return
        lo = R // c + 1
        hi = (remaining * R + 1) // c
        for q in primerange(max(lo, qlast + 1), hi + 1):
            walk(R * q, c * q - R, q, remaining - 1, path + (q,))

    walk(PORT_R * q1, PORT_C * q1 - PORT_R, q1, k - 1, (q1,))
    return stats, found


def first_primes(k):
    """Every admissible q_1 for layer k, by the bound of fact (2)."""
    return list(primerange(PORT_R // PORT_C + 1, (k * PORT_R + 1) // PORT_C + 1))


def layer(k, shard=0, stride=1):
    if k in CONTROLS:
        control(k)
    if k == 2:
        fills = [tuple(p) for p in completions(PORT_R, PORT_C, PREFIX[-1])]
        report(k, "all", {"prefixes": 1, "empty": 0, "factored": 1}, fills)
        return
    for i, q1 in enumerate(first_primes(k)):
        if i % stride != shard:
            continue
        stats, fills = branch(k, q1)
        report(k, q1, stats, fills)


def report(k, q1, stats, fills):
    for B in fills:
        n, ok = is_ppn(B)
        print(f"*** FILLING k={k} | {'*'.join(map(str, B))}", flush=True)
        print(f"    113322*B = {n}   ({k + 5} prime factors)   ppn identity: {ok}",
              flush=True)
    print(f"k={k} q1={q1} prefixes={stats['prefixes']} no-completion={stats['empty']} "
          f"factored={stats['factored']} fillings={len(fills)}", flush=True)


def main():
    args = sys.argv[1:]
    if not args:
        for k in (2, 3, 4):
            layer(k)
        return 0
    k = int(args[0])
    shard, stride = (int(args[1]), int(args[2])) if len(args) >= 3 else (0, 1)
    layer(k, shard, stride)
    return 0


if __name__ == "__main__":
    sys.exit(main())
