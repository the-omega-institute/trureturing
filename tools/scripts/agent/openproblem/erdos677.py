#!/usr/bin/env python3
"""Erdos 677: is M(n,k) != M(m,k) for every m >= n+k, where M(n,k)=lcm(n+1..n+k)?

A counterexample is a finite triple, so this is a search whose positive answer settles the
question. The ladder is Erdos's own two known near-misses, M(4,3)=M(13,2) and M(3,4)=M(19,2):
they must appear when unequal block lengths are allowed, and must NOT appear under the
same-k restriction the problem actually asks about. A run that cannot reproduce them is not
evidence about the same-k question.
"""
import sys
from math import gcd

def M(n, k):
    v = 1
    for i in range(1, k + 1):
        v = v * (n + i) // gcd(v, n + i)
    return v

def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    KMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    # ladder: unequal lengths must show Erdos's two known solutions
    lad = []
    for k in range(2, 6):
        for l in range(2, 6):
            for n in range(1, 40):
                for m in range(n + k, 60):
                    if M(n, k) == M(m, l):
                        lad.append((n, k, m, l))
    want = {(4, 3, 13, 2), (3, 4, 19, 2)}
    print("ladder unequal-length hits:", sorted(lad)[:8], file=sys.stderr)
    print("ladder contains Erdos's two:", want <= set(lad), file=sys.stderr)
    hits = []
    for k in range(2, KMAX + 1):
        seen = {}
        for n in range(1, N + 1):
            v = M(n, k)
            if v in seen:
                for prev in seen[v]:
                    if n >= prev + k:
                        hits.append((prev, n, k))
            seen.setdefault(v, []).append(n)
    for a, b, k in hits:
        print(f"n={a} m={b} k={k} M={M(a,k)}")
    print(f"N={N} kmax={KMAX} same_k_hits={len(hits)}", file=sys.stderr)

main()
