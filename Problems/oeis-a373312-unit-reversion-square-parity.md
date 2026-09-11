---
slug: oeis-a373312-unit-reversion-square-parity
bibkey: hanna2024a373312
doi: null
url: https://oeis.org/A373312
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/UnitReversionSquareParity
---

# Square parity of the unit-reversion series A373312

## Problem

OEIS A373312, Paul D. Hanna, Jun 25 2024. The following NAME and COMMENT
are copied verbatim from the claim in `Library/Arith/hanna2024a373312.md`.

NAME:

> Expansion of g.f. A(x) satisfying A(x)^2 = A( x*A(x)/(1 - A(x))^2 ).

COMMENT:

> Conjecture: a(n) == 1 (mod 2) iff n = 2^k - 1 for k >= 1.

The formalization constructs the integer solution normalized by `A(0)=0`
and `a(1)=1` and proves the parity assertion for every positive index.

## Motivation

This is a first-tier recent OEIS conjecture. The KPI is open problems
resolved, and the target is the unbounded parity assertion.

## Gap

The supplied search report found no proof in the searched scope: the search
seat read the OEIS entry and revision history on 2026-09-08 and searched
arXiv, MathOverflow, and GitHub by identifier. This Stage-B seat has no
network access and did not independently repeat that search. The missing
argument is the passage from the normalized integer generating equation
to the exact mod-two coefficient support.

## Route

Write `A = X*B`. Stabilized iterates of a contracting equation for `B`
construct the integer series without coefficient division.
`generating_equation` proves the equation with the unit-denominator
`innerSeries`, and `generating_unique` proves uniqueness by degree induction.
Over `ZMod 2`, Frobenius, Mathlib compositional-inverse cancellation
(`subst_substInvOfIsUnit_left`), and clearing the unit denominator give
`F = X + X*F(X^2)` in `mod_two_fixed`. The private `lacunary_coeff` identifies
its support with the Mersenne indices `2^k - 1`, `k >= 1`, by strong induction,
giving `hanna_conjecture`. The module has only Mathlib imports, no D5 import,
and generality G.

## Falsifier

A positive index n for which the normalized integer coefficient a(n) is odd
but n is not `2^k - 1` for any `k >= 1`, or is even at such an index, would
contradict the assertion. The orchestrator's exact check is supporting
evidence only; a finite check does not establish the universal assertion.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/UnitReversionSquareParity.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_two_fixed`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), exactly as
  reported for all four public theorems by the implementation seat.
- The orchestrator reported `make lean`, `make lean-report`, and `make emit`
  verification before the Stage-B edits; this seat did not rerun those gates.

## Triage

`theorem`. The formal proof closes the universal parity assertion for the
normalized integer solution recorded by OEIS.

## ASSUMED-UNVERIFIED

The quotations, attribution, and date were supplied by the orchestrator and
recorded in the Library note. The OEIS revision history was read by the search
seat, not by this seat. The literature search scope was the OEIS entry and
revision history read on 2026-09-08 plus identifier searches on arXiv,
MathOverflow, and GitHub; it was not an exhaustive search of MathSciNet,
zbMATH, or all third-party Lean libraries. This seat has no network access.
First-publication priority and the source-to-Lean identification are not
kernel-checked facts. The implementation seat's axiom report and the
orchestrator's gate and exact-check results are attributed evidence, not
independent Stage-B measurements.
