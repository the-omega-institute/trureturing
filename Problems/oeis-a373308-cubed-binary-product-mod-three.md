---
slug: oeis-a373308-cubed-binary-product-mod-three
bibkey: hanna2024a373308
doi: null
url: https://oeis.org/A373308
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CubedBinaryProductModThree
---

# Divisibility modulo three of the A373308 coefficients

## Problem

OEIS A373308, Paul D. Hanna, Jun 20 2024, gives the following NAME and
COMMENT, quoted verbatim from `Library/Arith/hanna2024a373308.md`.

NAME:

> Expansion of Product_{n>=0} (1 - x^(2^n))^3.

COMMENT:

> Conjecture: a(3*n+1) and a(3*n+2) are divisible by 3 for n >= 0.

The entry's separate Thue-Morse congruence for a(3n) and zero-index
characterisation conjectures are context only; neither is claimed here.

## Motivation

This is a first-tier recent OEIS conjecture. The target is the divisibility
assertion for every natural index, with KPI = open problems resolved.

## Gap

The supplied search-seat record reports no proof found: the OEIS entry and
revision history were read on 2026-09-09, followed by identifier searches on
arXiv, MathOverflow, and GitHub. This Stage-B seat had no network access and
did not independently repeat those searches. No exhaustive literature search
or first-publication priority is asserted.

## Route

The infinite product in the NAME, Π_{n≥0}(1 − x^{2^n})³, is represented by its
defining functional equation `A = (1 - X)^3 * A.subst (X^2)` with `A(0) = 1`.
Mathlib has no infinite products of formal power series; the equation is the
exact characterising property, obtained by removing the first factor and
shifting the remaining factors. This is the honesty boundary: Lean proves
existence and uniqueness for that equation, not an identity involving a formal
infinite-product operator.

The integer sequence `a` is defined recursively with `a(0) = 1` (multiplier 1).
For positive n its recurrence is
`a(n) = Σ_{i=0}^{min(3,n)} C(3,i)(-1)^i [n-i even] a((n-i)/2)`.
The implementation sums through n using the coefficients of `(1 - X)^3`;
those beyond degree three vanish. Index subtraction and division are natural
number operations. `generatingSeries = PowerSeries.mk a` is the integer
formal power series A. `generating_equation` proves both `A(0) = 1` and
`A = (1 - X)^3 * A.subst (X^2)`. `generating_unique` uses strong induction
on coefficients to show that every B with constant coefficient 1 satisfying
that equation equals A.

Over `ZMod 3`, Frobenius gives `(1 - X)^3 = 1 - X^3`, so the reduced series
satisfies `Ā = (1 - X^3) * Ā.subst (X^2)`. `mod_three_support`, via the private
`solution_support` strong induction, proves `(a n : ZMod 3) = 0` whenever
`3 ∤ n`: both contributing halved indices n/2 and (n-3)/2 remain outside the
multiples of three and are smaller than n. The second contribution occurs
only when n is at least three and n-3 is even; the first requires n even.
`hanna_conjecture` then states `3 ∣ a (3*n+1) ∧ 3 ∣ a (3*n+2)` for every n.

The separate Thue-Morse and zero-index conjectures are not claimed. The module
has Mathlib-only imports, no D5 import, and generality G.

## Falsifier

A natural index n for which either `a(3*n+1)` or `a(3*n+2)` is not divisible
by three would contradict the assertion. The orchestrator's exact check is
supporting evidence only; a finite check does not establish this universal
statement and was not rerun by this seat.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/CubedBinaryProductModThree.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_three_support`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported for
  each public theorem by the implementation seat's `#print axioms` checks.
- The orchestrator reported verification of `make lean`, `make lean-report`,
  and `make emit` before this Stage-B edit; these were not rerun by this seat.

## Triage

`theorem`. The formal proof closes the quoted universal divisibility assertion
for the unique normalized functional-equation solution representing the NAME.

## ASSUMED-UNVERIFIED

The quotations, attribution, and date were supplied by the orchestrator and
copied from the Library note. The OEIS revision history was read by the search
seat on 2026-09-09, not by this network-disabled Stage-B seat. The reported
literature scope was the OEIS entry and its revision history plus identifier
searches on arXiv, MathOverflow, and GitHub; private MathSciNet and zbMATH
indexes and the third-party Lean ecosystem were not exhaustively checked by
this seat. First-publication priority and the external source's identification
with the normalized functional equation are not kernel-checked facts.
