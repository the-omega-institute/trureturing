---
bibkey: vatter2026assortment
authors: Vincent Vatter
year: 2026
title: "An Assortment of Problems in Permutation Patterns: Unimodality, Equivalence, Derangements, and Sorting"
doi: null
url: https://arxiv.org/abs/2602.16355
claim: "Question 4.3. Does the ratio |𝒞°_n|/|𝒞_n| converge for every permutation class 𝒞?"
strata_touched:
  - D5/S1/Words/Patterns/DerangementRatioNonconvergence
license: citation-only
triage: anchor
---

# Vatter's Question 4.3

Section 4 defines a permutation class as a downset in the pattern-containment
order, and its derangement slice as the fixed-point-free members of a given
length. Question 4.3 asks whether the ratio of derangements to all members
converges for every permutation class.

The Lean module gives the decreasing class Av(12) as a literal counterexample:
each length slice is a singleton, and its member is a derangement exactly at
even lengths. The author may have had nontrivial (e.g. infinite-growth) classes
in mind; the module claims only the refutation of the universally quantified
statement. This note attests the question, not a published answer.

## Verified locator

- URL: https://arxiv.org/abs/2602.16355
- Version and location: arXiv:2602.16355v2, Section 4, Question 4.3.
- The orchestrator supplied the verbatim question and definitions from HTML
  fetched on September 8, 2026. This implementation seat did not independently
  access the source, because Stage A has no network access.
