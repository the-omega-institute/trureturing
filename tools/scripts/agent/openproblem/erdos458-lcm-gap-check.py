#!/usr/bin/env python3
"""Erdos #458 (FALSIFIABLE): is [1..p_{k+1}-1] < p_k * [1..p_k] for all k >= 1?

[1..m] is lcm(1..m). Writing L(m)=lcm(1..m): L(p_k)=p_k*L(p_k-1), and between p_k and
p_{k+1}-1 the lcm only gains a factor q for each prime power q^a with p_k < q^a < p_{k+1}.
So the claim is equivalent to  prod{ q : q^a prime power in (p_k, p_{k+1}) } < p_k,
which is what this checks -- exactly, in integers, with no lcm ever materialised.

A positive control is printed for k=1..6 so a zero hit count cannot be confused with a
predicate that is constantly true by construction.

Requires sympy. Usage: erdos458-lcm-gap-check.py [N]  (checks every p_k < N).
Not run by any check; it is a probe kept because its reduction is reusable.
"""
import sys
from sympy import primerange, integer_nthroot

N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7

primes = list(primerange(2, N))
print(f"primes below {N}: {len(primes)}")

# prime powers q^a (a>=2) up to N, as (value, base)
pp = []
a = 2
while 2**a < N:
    lim = integer_nthroot(N, a)[0] + 1
    for q in primerange(2, lim + 1):
        v = q**a
        if v < N:
            pp.append((v, q))
    a += 1
pp.sort()
print(f"prime powers q^a (a>=2) below {N}: {len(pp)}")

hits = []
idx = 0
shown = 0
for k in range(len(primes) - 1):
    pk, pk1 = primes[k], primes[k + 1]
    prod = 1
    while idx < len(pp) and pp[idx][0] <= pk:
        idx += 1
    j = idx
    while j < len(pp) and pp[j][0] < pk1:
        prod *= pp[j][1]
        j += 1
    ok = prod < pk
    if shown < 6:
        print(f"  control k={k+1} p_k={pk} p_(k+1)={pk1} prod={prod} < p_k -> {ok}")
        shown += 1
    if not ok:
        hits.append((k + 1, pk, pk1, prod))

print(f"counterexamples (prod >= p_k): {len(hits)}")
for h in hits[:20]:
    print("   HIT k=%d p_k=%d p_(k+1)=%d prod=%d" % h)
