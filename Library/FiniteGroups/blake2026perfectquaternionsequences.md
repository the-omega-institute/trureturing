---
bibkey: blake2026perfectquaternionsequences
authors: Sam Blake
year: 2026
title: A Recursive Construction of Perfect and Odd Perfect Sequences of Unbounded Length over the Unit Quaternions
doi: 10.48550/arXiv.2611.19627
url: https://arxiv.org/abs/2611.19627v1
claim: "Conjecture 5.2 excludes all six noncentral twists for every sequence over Q8 of length at least two."
strata_touched:
  - D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52
license: "arXiv.org perpetual non-exclusive license (citation only)"
triage: anchor
---

# Noncentral twists of quaternion sequences

## Verified locator

Sam Blake, *A Recursive Construction of Perfect and Odd Perfect Sequences of
Unbounded Length over the Unit Quaternions*, arXiv:2611.19627v1, submitted
14 November 2026.

DOI [10.48550/arXiv.2611.19627](https://doi.org/10.48550/arXiv.2611.19627).
Versioned abstract <https://arxiv.org/abs/2611.19627v1>.

- Conjecture 5.2, https://arxiv.org/html/2611.19627v1#S5.Thmtheorem2
- Definition 2.1, https://arxiv.org/html/2611.19627v1#S2.Thmtheorem1

> No sequence of length M ≥ 2 over Q₈ has type ±i, ±j or ±k.

For an integer n, write n = qM + r with 0 ≤ r < M. Definition 2.1 extends s
by sᵣuᑫ, with multiplication on the right, and sums sᵣ times the quaternion
conjugate of the extended entry at r + τ. A positive shift below M inserts
the conjugate of u between sᵣ and the conjugate of the wrapped entry. Type u
requires the sum to vanish for every integer shift outside the multiples
of M.

## Integral Hamilton coordinates

The eight signed coordinate units are integral. The inclusion of the integral
Hamilton quaternions into the real Hamilton quaternions is injective on each
coordinate and preserves the Hamilton product, conjugation and finite sums.
Each twist has inverse its conjugate, so the inclusion also preserves its
integer powers in the extension. The Lean witness lies strictly between zero
and M and gives the required off-period correlation in either ring.

The proof uses the literal sequence and twist. The characteristic-two
augmentation forces even length from shift one. A second quaternion character
sends the selected twist to an involution in the polynomial quotient by
T to the power 2d, where d is the power-of-two part of the length. The cyclic
correlation identity forces a product to vanish, while its coefficient at
degree 2d − 2 is one.
