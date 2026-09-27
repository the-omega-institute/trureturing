#!/usr/bin/env python3
"""Erdos 156 line: is the union bound in Ruzsa's construction lossy, or tight?

Ruzsa's construction, as reproduced for Z_2^n by Redman, Rose and Walker
(arXiv:2109.00292, section 3), takes a dense Sidon set A in the quotient Z_2^n/Q and lifts
each element to a uniformly random coset representative. Its log factor comes from wanting
each point's failure probability below 2^-n so a union bound over the 2^n points closes.

If that union bound were lossy, a sharper probabilistic tool would remove the log. This
builds the construction explicitly at n=24 and measures the uncovered fraction against the
Poisson prediction e^-lambda, where lambda is the ratio of available triples to points that
must be covered. Agreement means the triples behave like independent draws, the union bound
is tight, and no probabilistic tool can help; only a deterministic choice of representatives
could.

A is the BCH Sidon set {(x, x^3)} in F_{2^k} x F_{2^k} = Z_2^m with m = 2k, and Q is the
subgroup of low n-m bits, so the quotient map is a shift. The ladder checks A really is
Sidon in the quotient before anything is measured, since the whole reading is vacuous
otherwise.

Standard library plus numpy.
"""
import math, sys
import numpy as np

PRIMITIVE = {9: 0x211, 10: 0x409, 11: 0x805}      # x^9+x^4+1, x^10+x^3+1, x^11+x^2+1


def multiplier(k):
    poly, top = PRIMITIVE[k], 1 << k

    def mul(a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
            if a & top:
                a ^= poly
        return r
    return mul


def sidon_set(k):
    """{(x, x^3)} in F_{2^k} x F_{2^k}, packed as 2k-bit integers."""
    mul = multiplier(k)
    return np.array([(x << k) | mul(mul(x, x), x) for x in range(1 << k)], dtype=np.uint32)


def is_sidon(a):
    x = (a[:, None] ^ a[None, :]).ravel()
    return len(np.unique(x[x != 0])) == len(a) * (len(a) - 1) // 2


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    N = 1 << n
    rng = np.random.default_rng(11)

    for k in PRIMITIVE:
        if 2 * k <= n and not is_sidon(sidon_set(k)):
            print(f"ladder FAILED: {{(x,x^3)}} over F_2^{k} is not Sidon", file=sys.stderr)
            return 1
    print("ladder: ok (the BCH sets are Sidon in their quotients)", file=sys.stderr)

    print(f"n={n}, N=2^{n}={N}.  lambda = triples / targets; Poisson predicts e^-lambda uncovered")
    print(f"{'m':>3} {'|A|':>6} {'|Q|':>5} {'targets':>10} {'lambda':>7} {'e^-lambda':>10} {'measured':>10}")
    for k in sorted(PRIMITIVE):
        m = 2 * k
        if m >= n:
            continue
        shift = n - m
        a = sidon_set(k)
        size = len(a)
        in_a = np.zeros(1 << m, dtype=bool)
        in_a[a] = True
        target = ~in_a[np.arange(N, dtype=np.uint32) >> shift]
        targets = int(target.sum())

        q = rng.integers(0, 1 << shift, size).astype(np.uint64)
        b = ((a.astype(np.uint64) << shift) | q).astype(np.uint32)
        lam = (size * (size - 1) * (size - 2) / 6 + size * (size - 1) + size) / targets

        mark = np.zeros(N, dtype=bool)
        pairs = (b[:, None] ^ b[None, :]).ravel()
        for v in b:
            mark[pairs ^ v] = True
        uncovered = int((target & ~mark).sum())
        print(f"{m:>3} {size:>6} {1 << shift:>5} {targets:>10} {lam:>7.2f} "
              f"{math.exp(-lam):>10.3e} {uncovered / targets:>10.3e}")

    print(f"\nfull coverage by a random choice needs lambda >~ ln(targets) = {math.log(N):.1f},")
    print("that is |B|^3 >~ N log N, which is exactly Ruzsa's bound.")
    return 0


sys.exit(main())
