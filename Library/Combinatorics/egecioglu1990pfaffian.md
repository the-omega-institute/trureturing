---
bibkey: egecioglu1990pfaffian
authors: Ömer Eğecioğlu
year: 1990
title: "Skew-symmetric matrices and the Pfaffian"
doi: null
url: https://sites.cs.ucsb.edu/~omer/DOWNLOADABLE/Pfaffian90.pdf
claim: "Fixed-point elimination, single odd-cycle reversal, and the alternating-color bijection between ordered perfect matchings and even-cycle permutations."
strata_touched:
  - D5/S3/Combinatorics/Permutation/SkewDeterminantCycleCancellation
  - D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles
license: citation-only
triage: anchor
---

# Skew-symmetric matrices and the Pfaffian

Section 1.1, printed pages 108–109, eliminates permutation terms with fixed
points and pairs the remaining terms containing odd cycles by reversing one
odd cycle, chosen through its smallest label. Lemma 1.1 states the resulting
restriction to permutations with even cycles. The cancellation uses no division
and applies to zero-diagonal skew matrices over commutative rings, including
characteristic two. A finite set of odd supports permits the same invariant
selection without imposing an order on the underlying finite type.

The paper's convention separates the inversion sign from the signs of lower
triangular entries. In the row-image convention, the ordinary permutation sign
is unchanged by reversing one cycle, while the product of the matrix entries
changes by minus one for an odd support. The later matching-pair sign is a
different sign and is not used in this cancellation statement.

Sections 1.2–1.3, printed pages 109–111, identify fixed-point-free
involutions with perfect matchings and give the alternating-color bijection
between ordered pairs of matchings and permutations with only even cycles.
Common matching edges produce two-cycles. The paper labels the incoming edge
at each cycle minimum alpha. The rooted implementation in InvolutionEvenCycles
chooses its first input as the outgoing edge at that minimum; it states its
phase explicitly and does not assert equality of the two conventions.

## Verified locator

URL: https://sites.cs.ucsb.edu/~omer/DOWNLOADABLE/Pfaffian90.pdf

Ömer Eğecioğlu, *Ars Combinatoria* 29 (1990), 107–116; §1.1, printed
pages 108–111, including Lemma 1.1 and the section 1.3 bijection. The source is cited for its mathematics;
no external Lean code is incorporated.
