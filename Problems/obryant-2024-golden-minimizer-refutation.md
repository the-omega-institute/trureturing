---
slug: obryant-2024-golden-minimizer-refutation
bibkey: obryant2024sumproduct
doi: 10.48550/arXiv.2411.08139
url: https://arxiv.org/abs/2411.08139v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/SumProductGoldenMinimizerRefutation.result
---

# O'Bryant §5.7: the golden minimizer

## Problem

Kevin O'Bryant, *Visualizing the Sum-Product Conjecture*, arXiv:2411.08139v2,
§5.7 asks:

> What is the smallest possible value of |A + A|, where A is a set of n
> positive real numbers with |AA| ≤ 3n − 4? Is it achieved by
> {φ^i : 1 ≤ i ≤ n}, where φ = (1 + √5)/2?

The Lean `claim` retains the universal quantifiers over n and finite positive
real sets and compares the pointwise sumsets. The theorem `result : ¬ claim`
refutes this universal minimizer assertion.

## Motivation

The question proposes the consecutive golden powers as a universal minimizer
under a product-cardinality constraint. A single seven-element positive-real
set with no more than seventeen products and fewer sums disproves it.

## Gap

The counterexample uses the real root r in (1,2) of r³ − r − 1 = 0 and
A = {r^e : e ∈ {0,3,5,6,7,8,9}}. The product set is covered by the sixteen
exponent sums. The relation r³ = r + 1 gives a coefficient-vector cover of
A + A by twenty-two values. The geometric seven-term lower bound gives at
least twenty-four sums for the golden set at n = 7.

## Route

The intermediate value theorem supplies r with 1 < r < 2 and r³ = r + 1.
Strict monotonicity of powers gives seven distinct elements. Pointwise products
map into the image of E + E, whose computed cardinality is 16. For sums, the
seven powers are evaluated from seven integer coefficient vectors; the vector
sumset has cardinality 22 and evaluation preserves the required inclusions.
The existing geometric lower bound is applied with both scale and ratio equal
to the golden ratio.

## Falsifier

The refutation would fail if the root interval argument did not produce a
strictly larger-than-one root, if the exponent-sum cover were invalid, if the
coefficient-vector evaluation did not cover A + A, or if the golden lower
bound were applied to a different seven-term set. Each obligation is checked
by Lean's kernel in `result` and its live helper proofs.

## Evidence

`D5/S3/Arith/SumProductGoldenMinimizerRefutation.result` has closed type
`¬ claim`. The witness proves `(A * A).card ≤ 16 ≤ 17` and
`(A + A).card ≤ 22`, while the golden sumset has cardinality at least 24.
The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

Literature: the latest source for the question is arXiv:2411.08139v2. arXiv:2601.21828v3
concerns integer sets and does not settle this positive-real minimizer question;
arXiv:2605.28781 concerns asymptotic sum-product behavior and does not settle
the finite claim. `formal-conjectures/ErdosProblems/52.lean` states the main
conjecture only and does not settle this §5.7 minimizer assertion.

## Triage

- [proved: D5/S3/Arith/SumProductGoldenMinimizerRefutation.result] The claim is false.
- [computed] The witness has an upper bound of 22 for |A+A| and an upper bound of 16 for |AA|; the coefficient and exponent covers are kernel-checked.
- [proved: D5/S3/Arith/SumProductGoldenMinimizerRefutation.result] The golden seven-point set has |G₇ + G₇| ≥ 24, from the seven-point geometric sumset bound.
- [computed: exact integer-pair arithmetic, writing φ^i = F_{i−1} + F_i φ and enumerating all 28 unordered pair sums, which give 24 distinct coefficient pairs; φ is irrational] |G₇ + G₇| = 24 exactly. [computed: the exponent set {2,…,14} of pairwise products] |G₇G₇| = 13.
- [computed: exact coefficient vectors over ℤ[r]/(r³ − r − 1), enumerating all 28 unordered pair sums and all 49 products of exponents] The witness has |A + A| = 22 and |AA| = 16 exactly; equality of the sum count uses the irreducibility of X³ − X − 1 and is not part of the formal proof, which uses only the upper bounds.
- [open] The exact minimum of |A+A| for n = 7 under |AA| ≤ 17, and the exact minimum for general n.
- [open] Whether plastic-number subsets beat golden ones for every n ≥ 7.

## ASSUMED-UNVERIFIED

The literature status is limited to the cited versions and repository source
listed above; it is not an exhaustive priority determination.
