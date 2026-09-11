---
slug: oeis-a396793-iterate-product-nine-mod-three
bibkey: hanna2026a396793
doi: null
url: https://oeis.org/A396793
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateProductNineModThree
---

# Divisibility of the A396793 coefficients

## Problem

OEIS A396793, Paul D. Hanna, Jun 07 2026, states:

NAME:
> G.f. A(x) satisfies A(x) * A(A(x)) = x^2 + 9*x^3.

COMMENT:
> Conjecture: a(n) == 0 (mod 3) for n > 1.

These verbatim quotations are recorded in `Library/Recurrence/hanna2026a396793.md`.
Here A is an integer formal power series normalized by A(0) = 0 and a(1) = 1,
and a(n) is its coefficient of x^n.

## Motivation

This is a first-tier OEIS conjecture from the 2026 entry. The target proves
the assertion for every index n > 1. KPI: open problems resolved.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not
independently repeat those searches. Absence of a proof in that search scope
does not establish first-publication priority.

## Route

The escape content is `lift_mod_nine`: if f(0) = 0 and f is coefficientwise
congruent to X modulo 3, then f * iterate f 2 is coefficientwise congruent
to X^2 modulo 9. Writing f = X + 3B gives f composed with f congruent to
X + 6B, and f times that composition congruent to X^2 modulo 9.

Together with the proved coefficient multiplier 3 (`product_top`), this
lift makes the degree-by-degree corrections exact integers divisible by 3.
Their stabilized limit proves existence; `generatingSeries` selects that
existential witness. `generating_equation` proves
A * iterate A 2 = X^2 + 9X^3, A(0) = 0, and a(1) = 1.
The NAME's A(A(x)) is the frozen compositional `iterate` at 2 from
`D5/S1/Recurrence/Invariants/CompositionalIterateCongruence`.
`generating_unique` covers every normalized integer solution.

`hanna_conjecture` proves n > 1 implies 3 divides a(n), by applying the lift
to truncated prefixes and comparing them with the solution using the
coefficient multiplier. The reduced series over ZMod 3 is X, selected by
the lift rather than by a characteristic-3 uniqueness claim.
The target has generality I because it imports the frozen
`D5/S1/Recurrence/Invariants/CompositionalIterateCongruence`, itself generality G.

## Falsifier

An index n > 1 for the normalized solution with 3 not dividing a(n) would
contradict the assertion. The orchestrator's exact numerical check is
supporting evidence only; the theorem has no finite index bound.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/IterateProductNineModThree.lean`.
- Main theorem: `hanna_conjecture`.
- Companion theorems: `lift_mod_nine`, `generating_equation`, `generating_unique`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat for each of the four public theorems.

## Triage

`theorem`. The formal proof closes the universal coefficient assertion for
the unique normalized integer solution of the quoted generating equation.

## ASSUMED-UNVERIFIED

The quotations were supplied by the orchestrator and copied from the Library
note. The OEIS revision history was read by the search seat, not by this
seat. The reported literature scope was the OEIS entry and revision history
on 2026-09-09 and identifier searches on arXiv, MathOverflow, and GitHub;
this seat had no network. No exhaustive literature search or first-publication
priority is claimed. Source-to-Lean identification is not a kernel-checked fact.
