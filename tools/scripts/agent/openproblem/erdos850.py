#!/usr/bin/env python3
"""Search for Erdos problem 850: distinct x, y with rad(x+i) = rad(y+i) for every i < steps.

The pair condition is equality of prime support, not divisibility: 75 = 3*5^2 and
1215 = 3^5*5 share the support {3,5} while neither divides the other. An earlier form of
this search walked within-support multiples y = x*m and silently missed exactly that pair.
Grouping by the radical itself is the correct shape, and the ladder below is what caught the
difference.

Ladder: at steps=2 the pairs (2,8), (6,48), (14,224), (30,960) and (75,1215) must all appear
below 2000. A run that misses any of them says nothing about steps=3, however far it reaches.
"""
import argparse, sys
from collections import defaultdict

def radicals(n):
    """rad(v) for every v <= n, by sieving each prime across its multiples."""
    r = [1] * (n + 1)
    for p in range(2, n + 1):
        if r[p] == 1:
            for m in range(p, n + 1, p):
                r[m] *= p
    return r

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, required=True, help="upper bound on the larger member")
    ap.add_argument("--steps", type=int, default=3)
    a = ap.parse_args()
    N, k = a.limit, a.steps
    r = radicals(N + k)
    groups = defaultdict(list)
    for v in range(2, N + 1):
        groups[r[v]].append(v)
    found = []
    for members in groups.values():
        if len(members) < 2:
            continue
        for i, x in enumerate(members):
            for y in members[i + 1:]:
                if all(r[x + t] == r[y + t] for t in range(1, k)):
                    found.append((x, y))
    found.sort()
    for x, y in found:
        print(f"{x} {y}")
    print(f"limit={N} steps={k} pairs={len(found)}", file=sys.stderr)
    return 0

sys.exit(main())
