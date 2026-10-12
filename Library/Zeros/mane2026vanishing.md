---
bibkey: mane2026vanishing
authors: S. R. Mane
year: 2026
title: Identically vanishing k-generalized Fibonacci polynomials
doi: null
url: https://arxiv.org/abs/2507.11596v4
claim: Conjecture 6.6 asserts a negative-index root-amplitude upper bound and attainment at every negative multiple of k; the attainment clause fails at k = 3 and n = -15.
strata_touched:
  - D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2507.11596v4

The inspected source is version 4. Equations (1.2)–(1.3), p. 2, give the
forward and backward polynomial recurrences. Equations (1.4a)–(1.4b), p. 3,
define the quotient and remainder. Conjecture 6.4 and the paragraph defining
ζ occur on p. 19; Conjectures 6.5–6.6 occur on p. 20.

Crossref's title query returned no exact matching work among its first twenty
results; no Crossref DOI is assigned here.

## Source definitions

The recurrence (1.2) is

$$
\mathcal F_{n,k}(x)=x^{k-1}\mathcal F_{n-1,k}(x)
 +x^{k-2}\mathcal F_{n-2,k}(x)+\cdots+\mathcal F_{n-k,k}(x).
$$

“By convention, the initial values are 𝓕_{n,k}(x) = 1 for n = 1 and
𝓕_{n,k}(x) = 0 for n ∈ [−(k−2), 0].” (p. 2.)

“For k ≥ 2 and n ∈ ℤ, let ζ_{n,k} denote the maximum amplitude of |x_root|^k,
where P_{n,k}(x_root^k) = 0. Set ζ_{n,k} = 0 if 𝓕_{n,k}(x) has no nonzero
roots, including vanishing polynomials.” (p. 19.)

## Conjecture 6.6

“For fixed k ≥ 3 and n < 0, the upper bound is ζ_{n,k} ≤ ⌊|n|/k⌋. The bound
is attained whenever r_{n,k} = 1 (equivalently n = −sk, where s ≥ 1), i.e.
it is a tight bound.” (p. 20.)

The encoded proposition is only the attainment clause, with all natural
k ≥ 3 and s ≥ 1. The backward recurrence uses a k m = 𝓕_{1−m,k} and
F k n = a k (1−n).toNat. The statistic is Real sSup of the image of the
nonzero complex root set under z ↦ ‖z‖^k. The empty-set and unbounded-set
totalizations both give zero, including the zero-polynomial case for k ≥ 2.

## Refutation and scope

The recurrence gives

$$
\mathcal F_{-15,3}(x)=-x(x^{12}+8x^9+18x^6+15x^3+5).
$$

Every nonzero complex root has |x|³ < 5. The amplitude set is finite and
nonempty, so ζ_{−15,3} < 5. This refutes attainment at the nondegenerate
instance k = 3, s = 5. It preserves the upper-bound inequality at that
instance and does not settle the universal upper-bound clause or the branch
slope assertions in Conjecture 6.6. Conjectures 6.4 and 6.5 are separate
statements; their validity is not a premise of this refutation.
