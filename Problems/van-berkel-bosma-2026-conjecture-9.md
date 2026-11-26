---
slug: van-berkel-bosma-2026-conjecture-9
bibkey: vanberkelbosma2026periodicity
doi: 10.48550/arXiv.2609.18522
url: https://arxiv.org/abs/2609.18522v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Sumfree/StrictTwoSumfreePreperiodRefutation.result
---

# Van Berkel–Bosma Conjecture 9 as printed

## Problem

Conjecture 9 asserts that for positive initial entry f and positive seed
difference d, the strict greedy 2-sumfree sequence with seeds f and f+d has
minimal difference preperiod Q(d,f), prescribed by Definition 8. The
Introduction on printed pages 1–2 defines the sequences, Definition 8(e)
and (k1) appear on pages 7–8, and Conjecture 9 is on page 10.
[arXiv:2609.18522v1](https://arxiv.org/abs/2609.18522v1)

## Motivation

The asserted preperiod counts the initial differences to discard. Write
`d = r + 2fh` with `1 ≤ r ≤ 2f`. In the case `f ≥ 5`, `r = f+1` and
`h = 1`, Definition 8(e) gives `(2f+3)h + (2f+7)` and (k1) subtracts
`3f+r`. The actual seeds `f = 5` and `g = 21` give `d = g−f = 16`,
`r = 6` and `h = 1`, hence `Q(16,5) = 30−21 = 9`. Instantiating the
universal conjecture would require every sequence satisfying the strict
greedy recurrence at these seeds to have minimal gap preperiod 9. In
particular, there would be a positive period after its first nine gaps.

## Gap

Example 10 lists 15 at this pair, while the displayed formula gives 9.
The anchored assertion is Conjecture 9 with Definition 8 as printed.

## Route

The candidate range has a finite head and fourteen-entry blocks translated
by multiples of 56. A finite kernel certificate and residue witnesses
prove the strict-sum recurrence for every integer greater than 21. The
explicit ordered enumeration obeys the least-next-entry rule and is unique.

## Falsifier

The gap from 51 to 61 at zero-based gap index 14 is 10. Every later gap is
at most 9. For any positive proposed period p from gap index 9, index 14+p
would have gap 10, contradicting the bound.

## Evidence

The Lean `claim` is the exact specialization of the printed assertion.
The public theorem `result` has type `Not claim`.
[Literature note](../Library/Automata/vanberkelbosma2026periodicity.md)
[Issue #34312](https://github.com/the-omega-institute/trureturing/issues/34312)
[Independent mathematical certificate](https://github.com/the-omega-institute/trureturing/issues/34312#issuecomment-7178554093)

## Triage

The counterexample refutes the printed universal preperiod formula. The
mathematical scope is the formula at the single pair (5,21).

## ASSUMED-UNVERIFIED

The source-to-formal correspondence uses a human reading of the versioned
paper. The Lean proof verifies the recurrence and the negation of the
specialized claim. The literature review is limited to the supplied v1
source and recorded certificate.
