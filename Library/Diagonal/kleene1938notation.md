---
bibkey: kleene1938notation
authors: Stephen Cole Kleene
year: 1938
title: On notation for ordinal numbers
doi: 10.2307/2267778
claim: Self-application of a code for a partial recursive substitution yields the recursion theorem's fixed point.
strata_touched:
  - D5/S0/Computability/CodeFixedPoint
license: citation-only
triage: anchor
---

# On Notation for Ordinal Numbers

Stephen Cole Kleene's paper introduces the recursion theorem: every partial
recursive operation on indices of partial recursive functions admits an index
whose described function coincides with the one described by its image. The
proof is the diagonal self-application of a substitution code, the same
construction the repository's module wraps.

The deposited statement is the code-transformation variant usually attributed
to Hartley Rogers Jr. (Theory of Recursive Functions and Effective
Computability, McGraw-Hill 1967, Theorem 11-I): for every computable total
transformation of codes there is a code whose evaluation equals the evaluation
of its image. The 1967 book carries no DOI, so this note anchors the family at
Kleene's original recursion theorem, from which the Rogers form is the
standard total-transformation specialization. The pinned Mathlib names record
the same attribution: `Nat.Partrec.Code.fixed_point` (Rogers) and
`Nat.Partrec.Code.fixed_point₂` (Kleene's second recursion theorem).

## Search log

- 2026-08-11: Pinned Mathlib checkout searched first (`fixed_point` in
  `Mathlib/Computability/PartrecCode.lean`); the statement exists upstream, so
  the deposit is a declared thin wrapper. Journal of Symbolic Logic 3(4),
  pages 150-155; the DOI recorded here is the JSTOR article locator. No
  online metadata query was run in the restricted implementation worker.

## Locator

- DOI: https://doi.org/10.2307/2267778
