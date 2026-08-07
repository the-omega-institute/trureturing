---
bibkey: robertson1929uncertainty
authors: H. P. Robertson
year: 1929
title: The Uncertainty Principle
doi: 10.1103/PhysRev.34.163
claim: Robertson gives the variance-commutator uncertainty relation, and Schrodinger's 1930 refinement retains the symmetric covariance term.
strata_touched:
  - D5/S3/QuantumBounds/RobertsonSchrodinger
license: citation-only
triage: anchor
---

# The uncertainty principle

Robertson's 1929 relation bounds the product of two variances by the
commutator contribution. Schrodinger's 1930 refinement retains the additional
symmetric covariance contribution. Both arise by applying the complex
inner-product decomposition to the centered vectors associated with two
observables.

The Lean declaration keeps one more term than either lower-bound presentation:
the nonnegative Gram remainder
`G = ||u||^2 ||v||^2 - ||<u,v>||^2`. Thus its displayed equality is the
two-vector Gram identity specialized to the Robertson-Schrodinger setting.
This note does not claim that either historical paper uses the identifier `G`,
the exact Lean type-class generality, or the repository's normalization
conventions.

## Search log

- 2026-08-07: The task supplied Robertson's locator as *Physical Review* 34
  (1929), starting at 163, and identified Schrodinger's refinement as 1930.
- 2026-08-07: DOI resolution for `10.1103/PhysRev.34.163` was attempted from
  the worktree and failed because `doi.org` could not be resolved in the
  restricted environment. No page range, equation number, or other locator
  detail was inferred from that failed route.
- 2026-08-07: The attribution is limited to the standard hierarchy: Robertson
  retains the commutator lower bound, Schrodinger additionally retains the
  symmetric covariance term, and the repository retains the Gram remainder to
  recover the exact identity.

## Verified locator

- DOI supplied by the task: https://doi.org/10.1103/PhysRev.34.163
