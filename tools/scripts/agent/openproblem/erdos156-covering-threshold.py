#!/usr/bin/env python3
"""Erdos 156 line: separate the counting threshold from the union-bound threshold.

Ruzsa's construction, as reproduced for Z_2^n by Redman, Rose and Walker
(arXiv:2109.00292, section 3), picks a subgroup Q with quotient Z_2^m, takes a dense Sidon
set A of size 2^(m/2) in the quotient, and lifts each element of A to a uniformly random
coset representative. The resulting maximal set has size at most |A| + |Q| = 2^(m/2) +
2^(n-m), so everything turns on how small m may be.

Two separate requirements push m up, and they are not the same size:

  counting     the triples drawn from B must at least outnumber the points they cover,
               which needs 2^(3m/2)/6 >= 2^n, i.e. m >= (2/3)(n + log2 6);
  union bound  each point's failure probability must fall below 2^-n so the union bound
               over the 2^n points closes, which needs m > (2/3)(n + log2(T ln2 n)).

The first costs a constant and still yields |S| = O(2^(n/3)), which is the conjectured
answer. The second costs log2 n, which is exactly the factor separating O(N^(1/3)) from
Ruzsa's O((N log N)^(1/3)). This prints both, so the gap can be read off rather than
asserted.

Standard library only.
"""
import math, sys


def triples(b):
    """Unordered a+b+c from a b-element set, repeats allowed."""
    return b * (b - 1) * (b - 2) / 6 + b * (b - 1) + b


def main():
    T = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0

    print("at the exact balance point m = 2n/3:")
    print(f"{'n':>5} {'|B|':>10} {'#triples':>12} {'to cover':>12} {'ratio':>7}")
    for n in (24, 48, 72, 96, 120):
        m = 2 * n / 3
        b = 2 ** (m / 2)
        need = 2 ** n - 2 ** (m / 2) * 2 ** (n - m)
        print(f"{n:>5} {b:>10.3g} {triples(b):>12.4g} {need:>12.4g} {triples(b)/need:>7.3f}")
    print("\nthe ratio sits at 1/6, so the balance point is short by a constant factor,")
    print("and the counting threshold is m = (2/3)(n + log2 6), still giving |S| = O(2^(n/3)).\n")

    print("counting threshold against union-bound threshold:")
    print(f"{'n':>5} {'m_count':>9} {'m_union':>9} {'gap in m':>9} {'|B| ratio':>10}")
    for n in (24, 48, 96, 192, 384, 768):
        mc = (2 / 3) * (n + math.log2(6))
        mu = (2 / 3) * (n + math.log2(T * math.log(2) * n))
        print(f"{n:>5} {mc:>9.2f} {mu:>9.2f} {mu - mc:>9.2f} {2 ** ((mu - mc) / 2):>10.3f}")
    print("\nthe |B| ratio grows like n^(1/3) = (log N)^(1/3): that is the disputed factor.")
    return 0


sys.exit(main())
