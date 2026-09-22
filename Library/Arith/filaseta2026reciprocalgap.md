---
bibkey: filaseta2026reciprocalgap
authors: "Michael Filaseta; Alexandros Kalogirou"
year: 2026
title: "Covering systems with the sum of the reciprocals of the moduli close to 1"
doi: 10.1090/tran/9670
url: https://arxiv.org/abs/2407.15280v1
claim: "A positive lower bound on the density left uncovered by the 3-smooth classes forces a uniform positive reciprocal-sum excess in every finite distinct covering system; this applies to an all-odd family even when modulus 3 is permitted."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: citation-only
triage: anchor
---

# Uniform reciprocal excess and bounded intersecting original classes

The inspected primary text is [arXiv:2407.15280v1](https://arxiv.org/pdf/2407.15280v1),
submitted 21 July 2024; its manuscript title page is dated 23 July 2024.
The journal DOI is [10.1090/tran/9670](https://doi.org/10.1090/tran/9670),
whose Crossref record gives online publication on 22 January 2026 in
*Transactions of the American Mathematical Society*. The quantitative
statements and proof locators below refer to that inspected 2024 author
version, not to an independently compared journal PDF. The primary
statements and main proof were read on 19 September 2026.

Let C be a finite covering system with pairwise distinct moduli, and let
C_3 contain exactly those original classes whose moduli have no prime
divisors other than 2 and 3. Write Delta for the natural density of the
integers not covered by C_3. It is the Haar measure of that complement on
a common finite period.

Theorem 1, page 2, states that if the minimum modulus exceeds 4, then

    sum_(m in C) 1/m >= 1 + exp(-3.363054 * 10^21).

Page 3 explicitly extends the same bound to every such covering with
Delta >= 1/12, even if its minimum modulus is 2. Minimum modulus >4 is a
sufficient way to ensure this density condition, not the actual limitation
of the argument. Theorem 2 on page 3 states, for 0 < Delta < 1/12, that

    sum_(m in C) 1/m >=
      1 + exp(-(5.846 * 10^20 - 1.242 * 10^19 * log(Delta))/Delta).

The systems are finite and their moduli distinct. These theorems do not
assume oddness, squarefreeness or a bound on prime-power heights.

## The all-odd specialization permits modulus 3

In a finite distinct family of odd moduli greater than one, the C_3 moduli
are powers 3^e with e >= 1. Their total reciprocal mass is strictly less
than sum_(e>=1) 3^(-e) = 1/2. The union bound gives Delta > 1/2.
Consequently, if this original family covers, the first uniform excess
bound applies, including when its smallest modulus is 3. This is a direct
application of the authors' stated Delta extension, not a new theorem.
Deleting a possible 3-class is unnecessary and would generally destroy
the covering premise.

## A stronger form in the proof: an actual bounded intersecting pair

Section 3, pages 7–12, uses

    K = exp(1.681527 * 10^21),
    epsilon = K^(-2) = exp(-3.363054 * 10^21)

when Delta >= 1/12. The contradiction on pages 8–12 proves that two
different original classes with moduli m_1 <= K and m_2 <= K must
intersect. The endpoint is **<= K**, not a strict <K cutoff. For their
nonempty intersection, the same original Haar law gives

    u(C_1 intersect C_2) = 1/lcm(m_1,m_2) > K^(-2),

since distinct moduli bounded by K satisfy m_1*m_2 < K^2. Under the
whole-cover premise, let L be the original covering multiplicity. Then

    u(L-1) = sum_m 1/m - 1 >= u(C_1 intersect C_2) > epsilon.

The displayed theorems state the non-strict lower bound; the proof gives
the bounded-pair consequence and its strict intersection estimate. For
0 < Delta < 1/12 the same mechanism uses

    K = exp((2.923 * 10^20 - 6.21 * 10^18 * log(Delta))/Delta).

## Proof mechanism and transfer boundary

Assume that all original classes with moduli <= K are pairwise disjoint.
For successive primes, let U_i be the set missed by the retained
p_i-smooth classes. The proof combines an argument attributed to E. Lewis
with a union-density comparison attributed to C. A. Rogers. For the next
prime, contract each division-minimal original modulus by one factor of
that prime. Disjointness implies that every contracted class lies in U_i.
Rogers' comparison bounds its shifted union below by the union with all
residues zero. Inclusion–exclusion then yields

    d(U_(i+1)) >= d(U_i) * (1-M_1(p_(i+1))),
    M_1(p_i) = (p_i-1)^(-1) * product_(j<i)(1+(p_j-1)^(-1)).

This supplies a positive smooth-prefix reserve. Fourth-moment distortion
bounds control the large-prime tail, while an explicit reciprocal tail
bound controls smooth moduli above K. The bounds contradict complete
coverage under the assumed pairwise disjointness. The numerical constants
are established in the paper's Lemmas 1–4; they have not been separately
recomputed here.

For exact source transport, the cutoff definition only ensures
d(U_2) >= Delta: U_2 omits classes with modulus >K, whereas Delta uses all
3-smooth original classes. Pages 9 and 11 write equality, but the lower
bound is sufficient everywhere it is used in the argument and in the
stated Delta extension.

The result forces overlap somewhere in a whole original cover, uniformly
over its height and number of classes. It does not identify a prescribed
partner label, ending-prime bucket, smooth head or conditionally retained
fibre. Conditioning can remove the intersecting region, and a different
probability law need not retain its Haar mass. The premise is complete
coverage; an arbitrary noncovering family need not have this overlap.
The uniform epsilon is extremely small and, without an upper bound on the
same-law reciprocal excess, does not contradict a hypothetical odd cover.

These are mature external results and their direct application boundaries.
No Lean implementation, new proof, or source-text vendoring is supplied
by this citation note.
