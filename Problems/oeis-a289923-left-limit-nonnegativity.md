---
slug: oeis-a289923-left-limit-nonnegativity
bibkey: kimberling2017a289923
doi: null
url: https://oeis.org/A289923
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.result
---

# Nonnegativity of the A289923 left-limit sequence

## Problem

The source definition and conjecture are quoted in
`Library/RecurrenceAlgebraic/kimberling2017a289923.md`.

The complete target includes existence and uniqueness of an integer sequence
whose nth coefficient is eventually constant throughout a left neighborhood of
19/21, for each natural n including zero, and nonnegativity of every term.
Neighborhoods may depend on n. The source formal inverse is normalized by
constant coefficient one on the full domain 0 < r < 1.

## Motivation

This is the all-index nonnegativity conjecture explicitly recorded by OEIS.
The unique-sequence clause supplies source well-definedness, not an additional
external problem.

## Gap

The complete mathematical target is proved by
`D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.result`.
The literature search is bounded: the pinned OEIS entry retains the conjecture,
and the inspected repository, pinned Mathlib and GitHub identifier search supplied
no exact dominating theorem. The independently inspected MathOverflow answer
259978 reports observations and contains no A289923 identifier. This search does
not establish absence of another proof or publication priority.

## Route

The Lean declaration `A289923LeftLimitNonnegative.result` expresses all these
clauses without a generating-function hypothesis. Its denominator identity
is proved in every degree using the 21-step coefficient relation, and its
positivity conclusion follows by strong induction from a recurrence with
nonnegative forcing coefficients.

## Falsifier

An integer inverse coefficient that stabilizes to a negative value at any
natural index would contradict the target. Failure of the literal floor
denominator to have the claimed index-dependent stabilization would instead
invalidate the connection from the source to the proposed sequence.

## Evidence

The source module and its canonical Blueprint Scribe are
`D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.lean` and
`Blueprint/D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.scribe.cs`.
The audit mirror is
`Reg/D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.lean`.

The strict target is bound to
https://github.com/the-omega-institute/trureturing/issues/29510#issuecomment-6818246365.

The result establishes existence, uniqueness among all sequences satisfying
`IsLeftLimit`, and nonnegativity at every natural index, including zero. The
literal denominator and normalized inverse are retained. The proof directly
uses `AbsoluteReciprocalGeometricParity.agree_inv` to transport finite
coefficient agreement through inversion. The axiom closure is contained in
`Classical.choice`, `Quot.sound` and `propext`.

The Reg mirror reconstructs the whole source proposition by source equivalence.
Its rejected constant readout is negative at index zero; its actual readout
depends on the sequence and index. The continuation is unknown and asserts no
undecidability or inexhaustibility.

## Triage

`theorem`: the universal symbolic conjecture is the sole external target.
Existence and uniqueness supply its well-definedness. The admission basis is
`open-problem-resolution`, with the source conjecture acknowledged in the
repository-origin result's Scribe claim.

### What the settlement shows

- **Proved:** `A289923LeftLimitNonnegative.floor_stable` stabilizes the literal
  floor coefficients through degree n on an index-dependent left neighborhood.
  `limit_exists` transports this through the normalized inverse; `limit_unique`
  compares two candidates in the intersection of their neighborhoods. These
  are private helpers on the live route to `result`.
- **Proved:** the private `denominator_identity` gives $DP=Q$, where
  $P=(1+X)^2(1+X^{21})$ and $Q=1-X^{10}-X^{11}-X^{20}$. The private
  `positive_recurrence` proves nonnegativity for every integer formal series
  $F$ satisfying $QF=P$. Its recurrence adds the nonnegative coefficient of
  $P$ and the available coefficients at indices $n-10$, $n-11$ and $n-20$;
  strong induction applies at every natural index. `result` proves this
  identity for the source limit, without assuming Barker's known generating
  function or a fixed numerical parameter approximation.
- **Proved scope:** `positive_recurrence` needs only the displayed series
  identity, without a convergence hypothesis or a floor representation.
  Its application to the source remains at the left limit at 19/21 and on
  the domain $0<r<1$. No uniform neighborhood in all indices is asserted.
- **Open:** extensions to other rational endpoints, a right-hand limit,
  strict positivity, optimal bounds and asymptotic growth are not established
  by the delivered theorem. A single fixed approximation is not certified
  for all degrees.

The inspected source NAME, COMMENT and FORMULA state no further theorem as
depending on this conjecture. Barker's rational generating function remains
a known source formula; it is not separately counted as a new external result.
No consequence for uninspected literature, publication priority or timely
research credit is asserted.

## ASSUMED-UNVERIFIED

The identifier search on GitHub found no Lean match for `A289923`.
The pinned source and this bounded search do not establish first-publication
priority, absence of another proof or an exhaustive literature search. No
statistical-independence claim follows from this proof source.
