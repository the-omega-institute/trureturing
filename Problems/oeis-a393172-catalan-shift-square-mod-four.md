---
slug: oeis-a393172-catalan-shift-square-mod-four
bibkey: hanna2026a393172
doi: null
url: https://oeis.org/A393172
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour
---

# The mod-four coefficients of the Catalan-shift square series

## Problem

OEIS A393172, Paul D. Hanna, Feb 04 2026. The following NAME and COMMENT
are copied verbatim from the claim in `Library/Arith/hanna2026a393172.md`.

NAME:
> G.f. A(x) satisfies A(x-x^2) = x + A(x)^2.

COMMENT:
> Conjecture: for n > 1, a(n) == 2 (mod 4) iff n is a power of 2, otherwise a(n) is divisible by 4.

## Motivation

This is a first-tier recent OEIS conjecture. The KPI is open problems resolved:
the target is the full assertion at every index greater than one, not a finite
coefficient check or a previously known special case.

## Gap

The supplied search report found no proof in the searched scope. The search
seat read the OEIS entry and revision history on 2026-09-09 and searched by
identifier on arXiv, MathOverflow, and GitHub. This Stage-B seat had no network
access and did not repeat those searches. This is a bounded literature claim,
not an exhaustive absence-of-proof or first-publication claim.

## Route

Integer coefficient stabilization constructs `generatingSeries` and `a`.
`generating_equation` supplies the equation bridge: A(0) = 0, a(1) = 1, and
A(X - X^2) = X + A^2. Degree contraction gives `generating_unique`, needing
only the zero constant coefficient and the equation; the linear coefficient
is forced rather than assumed.

Over ZMod 2, `mod_two_identity` proves A = X by a least-discrepant-coefficient
contradiction. In terms of D = A - X, a discrepancy would give
D(X + X^2) = D^2, impossible for a nonzero series of positive least degree.
The Lean proof expresses this contradiction through the Catalan-composed
fixed-point operator and its degree contraction.

Integral halving A - X = 2H turns the exact equation into
H(X - X^2) = X^2 + 2XH + 2H^2. Hence H(X + X^2) = X^2 modulo two.
Catalan inversion identifies H modulo two with the squared binary Catalan
series, reusing the frozen `binary_catalan` theorem of
`CatalanCompositionSquareParity`. Thus A = X + 2C^2 modulo four, and
`hanna_conjecture` reads off residue two exactly at powers of two for n > 1,
with residue zero at every other such index.

The sole freeze prerequisite is the frozen module
`D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity`, generality G (the target module is I because it imports it),
statement_id `sha256:0033f4a50a501546a5f332ce1203c8cf1a936428e7a155a06a0443bb0f0f6232`.

## Falsifier

A counterexample index n > 1 would have a(n) not congruent to two modulo four
at a power of two, or a(n) not divisible by four at another index. The
orchestrator's exact coefficient check is supporting evidence only; finite
checks do not prove the universal assertion.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_two_identity`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as recorded by
  the implementation seat for each of the four public theorems.
- The explicit integer series and its generating equation and uniqueness
  connect the coefficient definition to the OEIS statement.

## Triage

`theorem`. The formal proof closes the assertion for every n > 1.

## ASSUMED-UNVERIFIED

The OEIS quotes, attribution, and date were supplied by the orchestrator.
The OEIS entry and revision history were read by the search seat on
2026-09-09, not by this Stage-B seat, which had no network access. The
reported literature search covered the OEIS entry/history and identifier
searches on arXiv, MathOverflow, and GitHub; it did not establish an exhaustive
literature search or publication priority. Source-to-Lean identification is
a mathematical reading of the source, not a kernel-checked provenance fact.
