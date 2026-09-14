---
slug: oeis-a060693-schroeder-peak-alternating-quadratic-moment
bibkey: schulte2017a060693
doi: null
url: https://oeis.org/A060693
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment
---

# Schulte's alternating quadratic peak moment for Schröder paths

## Problem

OEIS A060693, NAME:

> Triangle (0 <= k <= n) read by rows: T(n, k) is the number of Schröder paths from (0,0) to (2n,0) having k peaks.

COMMENT:

> T(n,k) is the number of Schroeder paths (i.e., consisting of steps U=(1,1), D=(1,-1), H=(2,0) and never going below the x-axis) from (0,0) to (2n,0), having k peaks. Example: T(2,1)=3 because we have UU*DD, U*DH and HU*D, the peaks being shown by *.

FORMULA:

> Conjecture: Sum_{k=0..n} (-1)^k*T(n,k)*(n+1-k)^2 = 1+n+n^2. - _Werner Schulte_, Jan 11 2017

## Motivation

The target is the full unbounded identity in the formula field. The Lean
module gives a concrete word model for the Schröder paths and counts its
adjacent U,D peaks, so the external triangle has an addressable formal object.

## Gap

The preregistration search surfaces dated 2026-09-13 were the current OEIS
entry and revision history (revision 145 still labels the formula Conjecture),
an arXiv exact-ID search with zero hits, and MathOverflow, where the only hit
was unrelated question 412573 mentioning the triangle without this identity.
Pinned Mathlib has single-variable large/small Schröder recurrences and
`DyckWord` first-return tools, but no peak-counted Schröder model or this
identity. OpenAlex and GitHub code search were not checked. The identity was
not found in the checked surfaces.

## Route

Represent a path by a U/D/H word with U and D of weight one, H of weight two,
total weight 2n, equal U and D counts, and every prefix having at least as
many U as D. The public `mem_schroeder_iff` identifies the first-return
generator `schroeder n` with exactly this `%C` path predicate. The public
`firstReturnEquiv` is the first-return decomposition, and the public
`first_return_peaks` is the peak law it carries: `peaks (U :: q ++ D :: p) = peaks q + peaks p + [i = 0]`.
Its injective case is discharged by the private `first_return_unique`. `T_first_return_recurrence`
then follows by `Fintype.card_congr` and finite-fiber counting. The signed zeroth, first, and second falling-moment recurrences are obtained directly from `firstReturnEquiv` and `first_return_peaks` through the local `hsum`, and they yield the alternating quadratic identity.

## Falsifier

A natural number n for which the signed sum differs from `n^2+n+1` would
falsify the formal statement. A mismatch between the `%C` path predicate and
the word model, or an error in the first-return peak decomposition, would
falsify the source-to-formal identification. The finite checks below are not
substitutes for the universal theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.lean`.
- Public definitions: `Step`, `stepWeight`, `weight`, `PrefixNonnegative`,
  `schroeder`, `peaks`, `T`, `SchroederPath`, and `firstReturnEquiv`.
- Public theorems: `mem_schroeder_iff`, `first_return_peaks`,
  `T_first_return_recurrence`, and `schulte_a060693`.
- The probe's exact integer check for n=0..30 had zero mismatches; it found
  `T(2,·)=[2,3,1]`, matching the `%C` example `T(2,1)=3`.
- The sympy generating-function check gave
  `F(x,-1)=1`, `F_y(x,-1)=x/(1-x)`, and
  `F_yy(x,-1)=2x^2/(1-x)^3`.
- The four public theorem axiom reports are std3:
  `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. The Lean proof establishes the universal alternating quadratic
moment identity, with an explicit public bridge from the recursive generator
to the external path predicate.

## ASSUMED-UNVERIFIED

The OEIS wording, attribution, revision date, and search-surface readings are
source readings rather than kernel facts. The bounded search does not establish
that no later proof exists, and OpenAlex and GitHub were not checked. The
correspondence between the OEIS natural-language path convention and the Lean
definitions is supported by `mem_schroeder_iff` but remains an interpretation
of the source text. The supplied finite and sympy checks are supporting evidence;
the universal result is established by the Lean kernel. No publication-priority
claim is made.
