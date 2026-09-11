---
slug: oeis-a374568-catalan-double-composition-powers-of-four
bibkey: hanna2024a374568
doi: null
url: https://oeis.org/A374568
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour
---

# Powers-of-four parity of the A374568 coefficients

## Problem

OEIS A374568 (Paul D. Hanna, Aug 14 2024) records the following NAME and
COMMENT, quoted verbatim from `Library/Arith/hanna2024a374568.md`:

NAME:

> Expansion of g.f. A(x) satisfying x = A(x - x^2) - A(x + x^2)^2.

COMMENT:

> Conjecture: a(n) is odd iff n = 4^k for k >= 0.

## Motivation

This is a first-tier recent OEIS conjecture. The KPI is open problems
resolved, rather than module counts or finite checks. The target is the
parity assertion for every positive coefficient index.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-08 and searching by identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did
not independently repeat that search. This bounded search report does not
establish first-publication priority or exhaust the literature.

## Route

Integer coefficient stabilization constructs `generatingSeries`.
`generating_equation` bridges its fixed-point recursion to the exact OEIS
equation and proves its constant and linear coefficients are 0 and 1.
`generating_unique` uses degree induction to identify every zero-constant
integer solution, without a separate linear-coefficient hypothesis.

Over `ZMod 2`, `mod_two_identity` identifies A(X + X^2) with the reduced
Catalan series C. The frozen module
`D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity` supplies
`catalan_equation` and `catalan_unique`. Its `binary_catalan` theorem gives
the single Catalan series' binary support, but the implemented proof does
not invoke it: that support alone does not compute double-composition
support. The local quadratic uniqueness argument identifies the reduced
series directly. `double_composition` then identifies A modulo 2 with C(C),
`double_quartic` proves C(C) = X + C(C)^4, and `quartic_support` uses
Frobenius and strong induction to give support exactly at powers of four.
The integer oddness bridge concludes `hanna_conjecture`.

The freeze prerequisite is that frozen Catalan module (generality G), with
`statement_id` `sha256:0033f4a50a501546a5f332ce1203c8cf1a936428e7a155a06a0443bb0f0f6232`.
The target module also has generality I.

## Falsifier

A positive index n for which a(n) is odd but n is not a power of four, or
for which n is a power of four but a(n) is even, would falsify the assertion.
The orchestrator's exact finite check is supporting evidence only; it does
not replace the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_two_identity`.
- Public definitions: `generatingSeries`, `a`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat for each of the four public theorems.

## Triage

`theorem`. The formal proof closes the stated parity assertion for every
positive index, with existence and uniqueness of the normalized integer
series supplied by the companion theorems.

## ASSUMED-UNVERIFIED

The quotations, attribution, and date were supplied by the orchestrator
and copied from the Library note. The OEIS revision history was read by
the search seat on 2026-09-08, not by this Stage-B seat. The reported
literature scope was the OEIS entry and revision history plus identifier
searches on arXiv, MathOverflow, and GitHub; this seat had no network and
did not exhaust private MathSciNet, zbMATH, or unlisted sources.
First-publication priority and the source-to-Lean identification are not
kernel-checked facts. The orchestrator's finite check and full build,
report, and emission checks were not independently rerun by this seat.
