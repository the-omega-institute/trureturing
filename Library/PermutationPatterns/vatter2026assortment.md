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
  - D5/S1/Words/Patterns/DerangementLimitsCofinal
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

## Largest limit below one

The unnumbered paragraph immediately after Question 4.3 in Section 4 of
arXiv:2602.16355v2 asks:

> Is there a largest possible limit strictly less than 1?

The precise locator is https://arxiv.org/html/2602.16355v2#S4. The question
allows arbitrary hereditary permutation classes, including classes whose
slice sizes are eventually constant. It is distinct from Question 4.3 and
is not numbered 4.4. Its single-question dossier is
`Problems/vatter-largest-derangement-limit-below-one.md`.

The repository-derived theorem `exists_derangement_limit_between` in
`D5/S1/Words/Patterns/DerangementLimitsCofinal` gives, for every real `q < 1`,
a hereditary class with nonempty slices and an attained limit `l` satisfying
`q < l < 1`. The class consists of permutations `(a+1,...,n,a,...,1)` with
`a <= min(k,n)`; eventually it has `k+1` members and `k` derangements, giving
limit `k/(k+1)`. Setting `q` to a proposed largest limit refutes maximality.
This answers the literal question without classifying all attainable limits
or imposing a growth condition. Vatter is credited for the question.

The source capture and bounded source/citation, bounded-grid and `k/(k+1)`
searches reported by the research caller and probes located no direct prior
answer. The caller's 2026-09-14 UTC GitHub discussion search for
`derangement+largest` returned `total_count=0`, `incomplete_results=false`.
These results bound the searched scope; publication priority outside it is
ASSUMED-UNVERIFIED.

The implementation's repository and pinned-Mathlib searches found no theorem
already giving bounded-tail class closure, its derangement counts, or
cofinality of these limits. They reused the existing permutation-class
carriers and generic monotonicity, bijection, cardinality and limit APIs.
In the caller's authenticated public GitHub code searches on 2026-09-14 UTC,
`derangement limit language:Lean` returned one hit: `todbeibrot/lemma-set`,
`imports.lean` at commit `263a7257416e21c5e148fbeebfaa9b67dbb04d99`.
Inspection of all 2,158 split lines found ordinary old Mathlib imports,
including `combinatorics.derangements.*`, and only the unrelated definitions
`yyy_to`, `zzz_forall`, and `www_fun`; no permutation-class limit result was
supplied. `PermClass language:Lean` returned zero hits. Both responses had
`incomplete_results=false`. These are bounded third-party search results,
not exhaustive absence evidence. The supplied v2 capture was inspected for
the question and class definitions; no fresh external fetch was performed
for this record.

## Verified locator

- URL: https://arxiv.org/abs/2602.16355
- Version and location: arXiv:2602.16355v2 (February 25, 2026), Section 4,
  Conjecture 4.1 and Questions 4.2-4.3.
- HTML: https://arxiv.org/html/2602.16355v2#S4
