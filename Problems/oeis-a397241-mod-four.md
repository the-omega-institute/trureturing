---
slug: oeis-a397241-mod-four
bibkey: hanna2026a397241b
doi: null
url: https://oeis.org/A397241
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve
---

# OEIS A397241 coefficients modulo 4

## Problem

OEIS A397241 (Paul D. Hanna, Jun 19 2026) records the following NAME:

> G.f. A(x) satisfies n * [x^n] A(x)^n = (n-1) * [x^n] A(x)^(n+1) for n > 1.

The COMMENT targeted by this dossier is:

> Conjecture: a(n) == 3 (mod 4) for n > 2.

The entry's third COMMENT, "Conjecture: all terms are odd", was already proved
and frozen in this repository as
`D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.hanna_conjecture`.
It is NOT re-claimed here. This dossier claims only the modulo-4 conjecture.

## Motivation

This is a first-tier OEIS conjecture from the 2026 entry. The target is every
natural index greater than two. KPI = open problems resolved; no cumulative
repository count is claimed.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those searches.

## Route

`mod_three_identity` and `mod_four_identity` are the escape witnesses:
ternary coefficient extraction and binary square-zero lifting turn the
diagonal relation `n·[xⁿ]Aⁿ = (n−1)·[xⁿ]A^{n+1}` into contracting residual
recurrences, with coefficient-comparison multiplier exactly one. The binary
side proves transitions of five polynomial numerator states for arbitrary
index. Strong induction over both yields the unified statement
`hanna_conjecture_mod_twelve`: `n > 2 → a n % 12 = 11`.
`hanna_conjecture_mod_three` (`a n % 3 = 2`) and
`hanna_conjecture_mod_four` (`a n % 4 = 3`), each for `n > 2`, follow immediately;
both series identities lie on the live proof path of both conjectures.

The module imports the frozen `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd`
(statement_id `sha256:7cedf3a47480861dc1dec746d7444e4d3257091fc3b0d7100463aab68ec03944`) and reuses its sequence
`a` and `generatingSeries` rather than redefining them. The generating equation
and integer uniqueness are inherited verbatim from that module, whose
`hanna_conjecture` already proved oddness. Target generality: I.

## Falsifier

A natural index `n > 2` in that same normalized integer sequence with
`a n % 4 ≠ 3` would refute this claim. The orchestrator's exact numerical
check is supporting evidence only, not a proof of the universal statement.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/DiagonalPowerRatioModTwelve.lean`.
- Public theorem and sole resolution claim: `hanna_conjecture_mod_four`.
- Unified companion: `hanna_conjecture_mod_twelve`.
- Escape companions: `mod_three_identity`, `mod_four_identity`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat for all five public theorems.

## Triage

`theorem`. The formal statement resolves the quoted modulo-4 conjecture
for all natural indices greater than two.

## ASSUMED-UNVERIFIED

The OEIS quotations were supplied by the orchestrator and copied from
`Library/Recurrence/hanna2026a397241b.md`. The oddness quotation and the
2026-09-09 search report were supplied by the orchestrator. The OEIS revision
history was read by the search seat, not this seat. The reported literature
scope was the entry, its revision history, and identifier searches on arXiv,
MathOverflow, and GitHub; absence of a proof outside that scope and
first-publication priority are unverified. Source-to-Lean identification is
not a kernel-checked fact. This Stage-B seat had no network access.
