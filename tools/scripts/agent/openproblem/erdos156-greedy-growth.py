#!/usr/bin/env python3
"""Erdos 156 research line: does the greedy maximal Sidon set reach O(N^(1/3))?

Erdos 156 asks whether some maximal Sidon set in [1,N] has size O(N^(1/3)). The greedy
set built from below is maximal in [1,N] -- an x rejected against a prefix stays rejected
against the whole set -- so if its counting function were O(N^(1/3)) it would answer the
question affirmatively on its own. This measures whether it does.

The greedy set under the strong Sidon convention (a+b=c+d implies {a,b}={c,d}, summands
allowed to coincide, equivalently all differences distinct) is Mian-Chowla, OEIS A005282.
That convention matters: A005282 is often quoted through the weaker "sums of two distinct
elements" reading, under which {1,2,3} is admissible and the sequence would start
1,2,3,5,8. It does not. The ladder pins the real terms so the confusion cannot survive a
run, and the repository's own `IsSidon` uses the strong convention.

Reads the OEIS b-file (n, a(n) per line) rather than recomputing, since the greedy search
costs about n^4 to reach n terms. Standard library only.
"""
import math, sys

LADDER = [1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, 123, 148, 182, 204]


def load(path):
    a = [0]
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        a.append(int(line.split()[1]))
    return a


def main():
    if len(sys.argv) < 2:
        print("usage: erdos156-greedy-growth.py <b005282.txt>", file=sys.stderr)
        return 2
    a = load(sys.argv[1])
    if a[1:16] != LADDER:
        print(f"ladder FAILED: {a[1:16]}", file=sys.stderr)
        return 1
    print("ladder: ok (A005282 under the strong Sidon convention)", file=sys.stderr)

    print(f"{'n':>7} {'a(n)':>14} {'|A|/N^(1/3)':>13} {'|A|/(N logN)^(1/3)':>20}")
    prev = None
    for n in (10, 30, 100, 300, 1000, 3000, 6000, 10000):
        if n >= len(a):
            break
        N = a[n]                       # counting function of the greedy set at N=a(n) is n
        flat = n / (N * math.log(N)) ** (1 / 3)
        print(f"{n:>7} {N:>14} {n / N ** (1 / 3):>13.4f} {flat:>20.4f}")
        prev = flat
    return 0


sys.exit(main())
