#!/usr/bin/env python3
"""Erdos 156 line: is the second moment of a+b-c a route to a better lower bound?

The frozen bound card_le_of_maximal counts a blocked x into |A+A-A| <= |A|^3, which
ignores what being Sidon does to the multiplicities of a+b-c. The obvious way to exploit
that is Cauchy-Schwarz: with r(x) = #{(a,b,c) in A^3 : a+b-c = x} one has

    |A+A-A| >= (sum r)^2 / sum r^2 = |A|^6 / sum r^2,

so an upper bound on the second moment would lower-bound |A+A-A| and hence force |A| up.
This measures whether that can work, on prefixes of the greedy set (A005282), which are
maximal in [1,a(k)] and so must satisfy A+A-A superset [1,N].

Reports |A+A-A| against both N and |A|^3, the second moment, the Cauchy-Schwarz bound it
yields, and the fraction of [1,N] actually covered (which must be 1 by maximality, and so
doubles as a check that the prefix really is maximal).

Cost is |A|^3 per row, so k stays small. Standard library only.
"""
import collections, sys

LADDER = [1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182, 204]


def main():
    if len(sys.argv) < 2:
        print("usage: erdos156-second-moment.py <b005282.txt> [kmax]", file=sys.stderr)
        return 2
    A = [int(line.split()[1]) for line in open(sys.argv[1]) if line.strip()]
    if A[:15] != LADDER:
        print(f"ladder FAILED: {A[:15]}", file=sys.stderr)
        return 1
    print("ladder: ok (A005282 under the strong Sidon convention)", file=sys.stderr)
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 200

    print(f"{'k':>5} {'N':>10} {'|A+A-A|':>10} {'/N':>6} {'/k^3':>7} "
          f"{'sum r^2':>14} {'CS/N':>6} {'cover':>6}")
    for k in (20, 40, 60, 80, 120, 160, 200, 260):
        if k > kmax or k > len(A):
            break
        S, N = A[:k], A[k - 1]
        r = collections.Counter()
        for a in S:
            for b in S:
                ab = a + b
                for c in S:
                    r[ab - c] += 1
        total = sum(r.values())
        m2 = sum(v * v for v in r.values())
        cs = total * total / m2
        cover = sum(1 for x in r if 1 <= x <= N) / N
        print(f"{k:>5} {N:>10} {len(r):>10} {len(r)/N:>6.2f} {len(r)/k**3:>7.3f} "
              f"{m2:>14} {cs/N:>6.2f} {cover:>6.4f}")
    return 0


sys.exit(main())
