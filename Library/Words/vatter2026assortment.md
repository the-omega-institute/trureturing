---
bibkey: vatter2026assortment
authors: Vincent Vatter
year: 2026
title: "An Assortment of Problems in Permutation Patterns: Unimodality, Equivalence, Derangements, and Sorting"
doi: null
url: https://arxiv.org/abs/2602.16355
claim: "Section 4 records Conjecture 4.1 (123-avoidance limit 9/16), Question 4.2 (231-avoidance limit 0), and Question 4.3 (universal convergence of derangement ratios)."
strata_touched:
  - D5/S1/Words/Patterns/DerangementRatioNonconvergence
license: citation-only
triage: anchor
---

# Vatter's derangement questions

Section 4 defines a permutation class as a downset in the pattern-containment
order, and its derangement slice as the fixed-point-free members of a given
length. It asks for the 123-avoidance limit in Conjecture 4.1, the
231-avoidance limit in Question 4.2, and universal convergence in Question 4.3.

The prior theorem recorded in `hoffmanrizzoloslivken2015pattern` already
settles the first two questions. Its Theorem 1.1(a) gives a positive almost
sure limiting total mass after `n^(-1/4)` scaling for 231-avoiding fixed
points; the closed-set Portmanteau bound then forces the probability of zero
fixed points to tend to zero. Its Theorem 1.1(b) gives the 123 limit as
`A + B` for independent Bernoulli(`1/4`) variables, so the continuity interval
`(-1/2, 1/2)` gives the zero-fixed-point probability `(3/4)^2 = 9/16`.
These are literature implications, not new formalized repository results.

The follow-up `doughertyblissgalvanpolleyshuster2026enumerating` partially
answers the separate separable-derangement Problem 4.4 and gives bounds for
Question 4.5, while its Conjecture 15 leaves the separable ratio limit open.

The Lean module gives the decreasing class Av(12) as a literal counterexample:
each length slice is a singleton, and its member is a derangement exactly at
even lengths. The author may have had nontrivial (e.g. infinite-growth) classes
in mind; the module claims only the refutation of the universally quantified
statement. This note attests the question, not a published answer.

## Verified locator

- URL: https://arxiv.org/abs/2602.16355
- Version and location: arXiv:2602.16355v2 (February 25, 2026), Section 4,
  Conjecture 4.1 and Questions 4.2-4.3.
- HTML: https://arxiv.org/html/2602.16355v2#S4
