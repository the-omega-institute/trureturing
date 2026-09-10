---
slug: oeis-a380710-absolute-reciprocal-square-parity
bibkey: hanna2025a380710
doi: null
url: https://oeis.org/A380710
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity
---

# Absolute reciprocal squares and binary parity in A380710

## Problem

Paul D. Hanna, OEIS A380710, Feb 18 2025. The following NAME and COMMENT
are copied verbatim from the claim in `Library/Arith/hanna2025a380710.md`.

NAME:

> G.f. A(x) satisfies A(x) = 1 + x*A(x)*abs( 1/A(x)^2 ).

COMMENT:

> Conjecture: for n > 0, a(n) is odd iff n is a power of 2.

Here `abs` is the series of coefficientwise absolute values, as defined by
the entry's formulas and the sibling entry A383377. It is not a pointwise
absolute value of an analytic function.

## Motivation

This is a first-tier recent OEIS conjecture. The KPI is open problems resolved:
the target is the parity assertion for every positive index, together with
existence and uniqueness for the exact defining equation.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and searching arXiv, MathOverflow, and GitHub by
identifier. This Stage-B seat had no network access and did not repeat those
searches. The report is limited to that search scope, not an exhaustive
literature or priority claim.

## Route

`absSeries F = mk (fun n => |coeff n F|)`. The integer series A is constructed
by stabilized iteration of `Phi(F) = 1 + X * F * absSeries (invOfUnit (F ^ 2) 1)`.
The private `approximation` starts at 1; private agreement lemmas for powers,
products, the unit inverse, and coefficientwise absolute values show that
`step` gains one degree of agreement. Thus coefficient n stabilizes by step n+1.

`generating_equation` proves A(0) = 1 and
`A = 1 + X * A * absSeries (invOfUnit (A ^ 2) 1)`, exactly the OEIS equation
with coefficientwise abs. Since A has constant coefficient 1, `invOfUnit`
is the reciprocal of A squared. `generating_unique` covers every integer
series B with constant coefficient 1 satisfying the same equation.

Over ZMod 2, coefficientwise absolute values disappear. The mapped inverse
identity yields `Abar ^ 2 = Abar + X`. Unit cancellation identifies Abar with
`1 + K`, where K is the binary Catalan series from the frozen
`CatalanCompositionSquareParity` module (`mod_two_identity`). The public
`hanna_conjecture` reads off `Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k` for n > 0
using that module's frozen support theorem `binary_catalan`.

The target has generality I because it imports the frozen D5 module
`D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity`, itself generality G.
Its frozen statement identity is
`sha256:0033f4a50a501546a5f332ce1203c8cf1a936428e7a155a06a0443bb0f0f6232`.

## Falsifier

A positive index n for which a(n) is odd but n is not a power of two, or is
even while n is a power of two, would contradict the assertion. The
orchestrator's exact numerical check is supporting evidence only; a finite
prefix does not establish the universal conclusion.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_two_identity`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for all four public
  theorems, as reported by the implementation seat.

The coefficientwise operation is defined in Lean verbatim as:

```lean
noncomputable def absSeries (F : PowerSeries ℤ) : PowerSeries ℤ :=
  mk (fun n => |coeff n F|)
```

## Triage

`theorem`. The formal proof closes the positive-index parity conjecture for
the unique normalized integer solution of the stated generating equation.

## ASSUMED-UNVERIFIED

The quotations and their OEIS attribution were supplied by the orchestrator;
Stage-B copied them from the Library note. The interpretation of abs from the
OEIS formulas and A383377 was supplied in the dispatch. The OEIS revision
history was read by the search seat on 2026-09-09, not by this seat. The
literature search covered the OEIS entry/history and identifier searches on
arXiv, MathOverflow, and GitHub; Stage-B had no network access. Neither
exhaustive literature coverage nor first-publication priority is claimed.
Source-to-Lean identification and external search reports are not kernel facts.
