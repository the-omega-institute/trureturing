---
slug: przytycki-silvero-2024-four-braid-extreme-khovanov
bibkey: przytyckisilvero2024khovanov
doi: 10.1007/s13398-024-01594-z
url: https://arxiv.org/abs/2305.18648v1
triage: theorem
motivation_gids:
  - D5/S3/Topology/FiniteMatchingClosure
---

# The actual extreme integral Khovanov row of a four-braid

## Problem

Section 9.1 of Przytycki and Silvero's *Khovanov homology, wedges of
spheres and complexity* conjectures that a link has braid index greater
than four if its actual extreme integral Khovanov row falls outside
the graded list in Corollary 1.6. With framed homological grading, this
list allows zero, a single copy of `ℤ`, or `ℤ[k] ⊕ ℤ^r[i]` with
`k ≥ i` and `1 ≤ r ≤ 3`.

## Motivation

The diagram's potential extreme row can vanish. In that case the
link-level conjecture concerns a different row, beyond the diagram
calculation in Corollary 1.6.

## Gap

The checked arXiv and citing literature yielded no explicit settlement
of the graded assertion. ArXiv:2601.02119 addresses the separate
computational-complexity question.

## Route

Take the closure of the four-strand braid with signed generators
`(1,2,1,1,-3,2,2,-3,2,1,2)`. The two highest possible normalized quantum
rows, 21 and 19, are acyclic. Row 17 has `ℤ²` in normalized homological
degree 5 and `ℤ` in degree 6. The signed cube computation checks all
retained differential terms and the integral homotopy identities.
Remark 2.1 sends these to framed homological degrees −3 and −5 at
quantum degree −13. The lower of those two homological degrees contains
the singleton, which violates the ordered list. The displayed
presentation gives braid index at most four.

## Falsifier

The ordered ranks `(-3, 2)` and `(-5, 1)` are forbidden in the
first nonzero framed row of a link satisfying the conjecture.

## Evidence

`FourBraidKhovanovCounterexample.gradedExtremeClaim_refuted` refutes the
restriction of the conjecture to the displayed four-braid closure.
An independent crossing-port computation reproduced the integral row.

## Triage

`theorem`. The explicit four-braid closure refutes the graded
link-level assertion.

## ASSUMED-UNVERIFIED

The LinkInfo entry `L11n294{0,0}` supplies the braid and earlier
tabulated group data. Historical priority is unverified.
