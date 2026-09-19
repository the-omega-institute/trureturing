[Index](../marked_head_profile.md) · [Complete HSW family](349-real-odd-cover-private-cylinders-and-transport-obstruction.md) · [Multiple descendants](351-multiple-descendants-fresh-prime-budget-and-local-repair.md)

# The complete private region exceeds the reserved transport palette

The local repair in 351 cannot become a complete repair under the following
explicit interface. Keep the same HSW source and old-3 memory map, allow
one standard modulus-9 image of the original class 1 mod3, and allow
arbitrarily many additional descendants. Each AP must be sound on its
entire progression for one fixed original label. Additional descendants
of 1 mod3 may use only the original primes, including 11, at arbitrary heights,
but their numerical moduli must avoid the **entire standard candidate
pool**, including candidates not selected by the particular root map.
All emitted moduli must be pairwise distinct, odd, and greater than one.

Every such output leaves full-Haar mass greater than 1/120 uncovered.
The conclusion allows the three-of-four root selection and injection
to depend on all retained cofactor coordinates. It concerns the complete
original private region, rather than only the cylinders repaired in 351.

Reserving every standard candidate modulus is a substantive restriction.
This does not exclude a transformation that reallocates other candidate
moduli, changes the memory map, or adds other prime factors. No new
distinct odd cover, unrestricted noncoverage theorem, or Lean result is
claimed.

When the entire output uses at most eight primes, the attributed
[Schroeder result](../../../../Library/Arith/schroeder2026nine.md) already gives
noncoverage and uncovered density at least 1/1,002,375, with arbitrary
heights. The present contribution is the larger bound for this specified
source and reservation interface, not a newly excluded prime-support case.
The argument also permits other original labels to emit sound APs with
additional primes: their source soundness keeps them off A-private points.

## 1. The private region has a finite exact digit description

The original support is

    P0 = {3,5,7,11,13,17,19,23}.

The old 11 height is one, the nonpure roots are 0,1,2,3, and the six
power-prime heights run through every value 1,...,22. Restrict to the
literal original class A=1 mod3. Every other normal parameter family
containing 3 has first nonzero 3 digit 2, so none can cover a point of A.
The higher instances of the family containing A have first 3 digit zero
and also miss. All remaining normal competitors are 3-free originals.

For each prime p in {5,7,13,17,19}, record the position h_p and value d_p
of its first nonzero digit. A normal family covers exactly when its
specified nonzero digits match and its 11 root, if specified, matches.
Its full range of heights is retained in this criterion.

Write j for the old 23 residue. The common closing class excludes j=0.
For 1<=j<=22, the other closing classes are 0 mod p^j together with
j mod23. Avoiding every closing class is therefore equivalent to
h_p<=j for each of the five primes above; the 3 closing class already
misses A. A coordinate zero modulo p^22 is consequently never private.

There are exactly

    (5−1)(7−1)(13−1)(17−1)(19−1) = 82944

nonzero digit tuples. For each tuple, let M be the subset of old roots
on which A is the sole covering original label. Testing the 3-free
normal patterns gives this complete joint count; a mask encodes root r
by bit 2^r:

| root mask | 0 | 1 | 3 | 5 | 7 | 9 | 11 | 13 | 15 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| digit tuples | 48186 | 1159 | 876 | 5078 | 2180 | 1837 | 2886 | 8840 | 11902 |

The four root totals are 34758,17844,28000,25465. Counts come from
joint original memberships; separate root marginals would not suffice.

For one fixed nonzero digit at prime p, the total Haar mass over
heights 1,...,j is

    g_p(j) = sum_(h=1)^j p^(-h) = (1−p^(-j))/(p−1).

Thus every digit tuple in the table has the same exact cofactor mass

    K = (1/23) sum_(j=1)^22
              g_5(j) g_7(j) g_13(j) g_17(j) g_19(j).         (PC1)

This includes every original height and closing residue, without
enumerating the complete CRT period or the 19,329,428 source labels.

## 2. One standard modulus-9 image is already credited

At a cofactor with k=|M| private roots, selecting three of the four roots
retains at least max(k−1,0) private demands. Their distinct new roots
and old 3 digit 1 produce distinct residues among 3,4,5 mod9.
The standard modulus-9 AP can cover at most one of these demands.
Even allowing the injection to place any private demand on its chosen
new root leaves at least max(k−2,0) demands.

The table therefore gives

    sum_M count(M) max(|M|−2,0) = 37710,
    R = (37710/9) K.                                        (PC2)

This is a lower bound on the full output mass still requiring extra
descendants of A after one modulus-9 AP. It is uniform over
cofactor-dependent root choices. Each surviving demand is private for
the same original A, so APs sound for another fixed original label
cannot cover it.

## 3. The reserved numerical pool is counted once

A whole-AP-sound descendant of A lies inside {3,4,5} mod9. Its modulus
must be divisible by 9: an AP with 3-adic modulus exponent zero or one
has a larger image modulo 9 and is not contained in that band.

An original 11-free, 3-bearing modulus m has standard candidate modulus
3m; an original 11-bearing modulus 11m has candidate modulus 3m as well.
These are numerical candidates across all source choices. They must
be merged before computing the reserved reciprocal mass.

For the literal HSW family, the resulting 9-divisible normal candidates
have 3 exponent 2,...,23; the other present exponents range over 1,...,22.
The 24 possible prime supports are exactly

    3 * 5^a * 7^b * 19^c * t,
    a,b,c in {0,1},  t in {1,13,17}.

Here the expression specifies prime support, not the numerical exponent.
The only further 9-divisible closing candidates are 23*3^h,
2<=h<=23. Normal candidates contain no 23, so these boxes do not overlap.
There are 22*23^3*45+22=12,045,352 distinct reserved numerical moduli.

Put g_p=g_p(22). Their exact reciprocal sum is

    P = (g_3/3) [ (1+g_5)(1+g_7)(1+g_19)(1+g_13+g_17)
                  + 1/23 ].                               (PC3)

In particular 9 belongs to this pool. It has already been permitted and
credited once in PC2; it is not being excluded from the output.

Grant all arbitrary heights on P0 to the remaining descendants. The
sum of reciprocals over every P0-supported modulus divisible by 9 is

    E = (1/6) product_(p in P0, p!=3) p/(p−1)
      = 676039/1990656.                                    (PC4)

The additional descendants avoid the reserved pool, so any finite list
has reciprocal sum strictly below V=E−P. This grants even unused 11
powers and every other available height. By the union bound its mass
on the required residual private region is at most that sum.

## 4. Exact gap and the fresh-prime boundary

Direct rational evaluation of PC1--PC4 gives

    R > 47175/1000000,
    V < 38387/1000000.

Consequently the full output hole mass satisfies

    H(holes) > R−V
             > 8788/1000000
             > 1/120.                                     (PC5)

The exact difference is between 0.008789432366321339 and
0.008789432366321340. These are outward rational bounds; no floating
calculation decides the sign. In particular, old-cofactor subdivisions
of the three local repairs from 351 cannot close the complete private
region while retaining this reserved-pool interface.

If a finite fresh prime set F disjoint from P0 is also allowed, the
same calculation changes V to E product_(ell in F) ell/(ell−1)−P.
Complete repair would then require

    product_(ell in F) ell/(ell−1) > (R+P)/E.                (PC6)

The right side lies between 1.025881252822117913 and
1.025881252822117914. One fresh prime 29 passes this necessary capacity
test; a single fresh prime at least 41 does not. Passing is not a
covering construction. This condition belongs to the present reserved
pool and cannot be used as a necessary bound for arbitrary reallocation.

## 5. Reproducible scope

The [standard-library checker](../frontier/hsw11_private_region_capacity.py)
reads the literal sibling HSW constructor, verifies the relevant normal
and closing interfaces, and checks all 82,944 digit tuples. It compares
all four local root choices for each private mask, sums the full height
ranges exactly, merges the candidate modulus boxes, and verifies PC5
with rational arithmetic. It does not enumerate a truncated source
family or infer global coverage from sampled integers.

The obstruction is to completing the actual private region under the
specified modulus reservations. It neither requires a repair of the
entire larger band {3,4,5} mod9 nor excludes transformations that reuse
other standard candidate moduli or change source-label soundness.
