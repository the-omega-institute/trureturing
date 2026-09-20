#!/usr/bin/env python3
"""Erdos #699 (FALSIFIABLE): for every 1 <= i < j <= n/2 is there a prime p >= i with
p | gcd(C(n,i), C(n,j))?

Kummer: v_p(C(n,i)) is the number of carries when adding i and n-i in base p, so "p divides
C(n,i)" is decided without building a binomial coefficient.

The p >= i bound is a property of the PAIR, not of either index: masks are built unrestricted
and the bound is applied at pair time against the smaller index. Restricting each row by its own
index instead silently checks p >= j, a strictly stronger demand -- that mistake reports (6,1,3)
as a counterexample when in fact p=2 divides gcd(C(6,1),C(6,3)) = gcd(6,20) = 2. That stronger
predicate is kept below as the positive control, since it is known to fail at (6,1,3): a sweep
whose predicate can never fail would prove nothing.
"""
import sys
import numpy as np
from sympy import primerange

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 400

def carries(a, b, p):
    c = carry = 0
    while a or b or carry:
        s = a % p + b % p + carry
        carry = 1 if s >= p else 0
        c += carry
        a //= p; b //= p
    return c

def check(n):
    primes = list(primerange(2, n + 1))
    W = (len(primes) + 63) // 64
    half = n // 2
    masks = np.zeros((half + 1, W), dtype=np.uint64)
    for i in range(1, half + 1):
        for bi, p in enumerate(primes):
            if carries(i, n - i, p):
                masks[i, bi // 64] |= np.uint64(1) << np.uint64(bi % 64)
    # ge[i] = bitmask of primes p >= i
    ge = np.zeros((half + 2, W), dtype=np.uint64)
    for i in range(1, half + 2):
        for bi, p in enumerate(primes):
            if p >= i:
                ge[i, bi // 64] |= np.uint64(1) << np.uint64(bi % 64)
    for i in range(1, half + 1):
        rows = masks[i + 1:half + 1] & masks[i] & ge[i]
        if rows.size == 0:
            continue
        empty = ~rows.any(axis=1)
        if empty.any():
            return (n, i, int(np.flatnonzero(empty)[0]) + i + 1)
    return None

def check_stronger(n):
    """Control: demand p >= j instead of p >= i. Known to fail at n=6, i=1, j=3."""
    primes = list(primerange(2, n + 1))
    half = n // 2
    for i in range(1, half + 1):
        for j in range(i + 1, half + 1):
            if not any(p >= j and carries(i, n - i, p) and carries(j, n - j, p) for p in primes):
                return (n, i, j)
    return None

ctrl = next((r for n in range(4, 60) if (r := check_stronger(n))), None)
print("control (stronger demand p>=j) first failure:", ctrl)
assert ctrl == (6, 1, 3), f"control drifted: {ctrl}"

first_bad = None
for n in range(4, NMAX + 1):
    r = check(n)
    if r is not None:
        print("COUNTEREXAMPLE n=%d i=%d j=%d" % r, flush=True)
        first_bad = r
        break
    if n % 100 == 0:
        print(f"  n<={n} ok", flush=True)
print("result:", "counterexample found" if first_bad else f"no counterexample for n <= {NMAX}")
