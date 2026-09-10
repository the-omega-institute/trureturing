---
slug: oeis-a363308-catalan-cubic-composition-parity
bibkey: hanna2023a363308
doi: null
url: https://oeis.org/A363308
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity
---

# Parity of the cubic Catalan composition A363308

## Problem

OEIS A363308 (Paul D. Hanna, May 28, 2023), quoted verbatim from
`Library/Arith/hanna2023a363308.md`:

NAME:

> Expansion of g.f. C(x*C(x)^3), where C(x) = 1 + x*C(x)^2 is the g.f. of the Catalan numbers (A000108).

COMMENT:

> Conjecture: a(n) is odd iff n is a power of 2 or n = 0.

## Motivation

This is the first-tier recent OEIS conjecture selected in the lane brief.
The KPI is open problems resolved. The target is the assertion for every
natural index, including zero.

## Gap

The supplied search report found no proof in the searched scope: the OEIS
entry and revision history read by the search seat on 2026-09-09, and
identifier searches on arXiv, MathOverflow, and GitHub. This Stage-B seat
had no network access and did not independently repeat those searches.
The missing mathematical bridge is the reduction of the cubic composition
to the binary Catalan series.

## Route

`catalanSeries` is `mk (fun n => (catalan n : ℤ))`.
`catalan_equation` gives C = 1 + X*C^2 by mapping Mathlib's
`PowerSeries.catalanSeries_sq_mul_X_add_one` to integer coefficients.
Thus C is the Catalan generating function specified by the NAME, not merely
an unspecified solution of a functional equation.

`generatingSeries` is `C.subst (X*C^3)`, and `a n` is its nth coefficient.
`generating_equation` proves A(0) = 1 and A = 1 + (X*C^3)*A^2 by
substitution into the Catalan equation.

Over ZMod 2, write c̄ for the reduction of C, k for the reduction of
K = `CatalanCompositionSquareParity.catalanSeries`, and ȳ = X*c̄^3.
`mod_two_identity` identifies the reduction of A with 1 + k. Its live
path identifies k = X*c̄, derives k(1+k) = X, and proves
X^2*ȳ*(1+k)^2 = k^3*(1+k)^2 = k*(k*(1+k))^2 = X^2*k.
Cancel X^2 to see that 1+k solves the quadratic equation; uniqueness
follows by cancelling the unit 1 - ȳ*(f+g) in the difference of two
solutions, since that unit has constant coefficient one.

`hanna_conjecture` then reads off
`Odd (a n) ↔ (n = 0 ∨ ∃ k : ℕ, n = 2 ^ k)` using the frozen
`CatalanCompositionSquareParity.binary_catalan` support theorem and a
separate zero-index case. Target generality is I because the proof imports
the frozen `D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity`,
itself generality G, with statement_id
`sha256:0033f4a50a501546a5f332ce1203c8cf1a936428e7a155a06a0443bb0f0f6232`.

## Falsifier

A natural index n for which the integer coefficient of C(x*C(x)^3) is odd
but n is neither zero nor a power of two, or is even at zero or a power of
two, would contradict the assertion. The orchestrator's exact check is
supporting evidence only, not a substitute for the unbounded theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `catalan_equation`, `generating_equation`, `mod_two_identity`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for each of
  the four public theorems, as reported by the implementation seat's
  `print_axioms` record; Stage-B did not rerun Lean.

## Triage

`theorem`. The formal proof closes the universal parity assertion recorded
by OEIS for the specified Catalan composition.

## ASSUMED-UNVERIFIED

The quotes, attribution, and date were supplied by the orchestrator.
The OEIS entry and revision history were read by the search seat on
2026-09-09, not by this Stage-B seat. The literature search scope was
the OEIS entry/history and identifier searches on arXiv, MathOverflow,
and GitHub; no exhaustive literature or first-publication priority claim
is made. This seat had no network access. Source-to-Lean identification
and literature coverage are not kernel-checked facts.
