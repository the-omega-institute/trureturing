---
slug: oeis-a397241-diagonal-power-ratio-all-odd
bibkey: hanna2026a397241
doi: null
url: https://oeis.org/A397241
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd
---

# Oddness of all A397241 terms

## Problem

OEIS A397241, Paul D. Hanna, Jun 19 2026:

> G.f. A(x) satisfies n * [x^n] A(x)^n = (n-1) * [x^n] A(x)^(n+1) for n > 1.

The entry seeds are `a(0) = a(1) = 1`. Its first conjecture is:

> Conjecture: all terms are odd.

These NAME and COMMENT sentences are reproduced verbatim from the claim in
`Library/Recurrence/hanna2026a397241.md`. The two further entry comments,
"Conjecture: a(n) == 2 (mod 3) for n > 2." and
"Conjecture: a(n) == 3 (mod 4) for n > 2.", are not resolved by this dossier.
This dossier records one claim, on `hanna_conjecture` only.

## Motivation

This is a first-tier OEIS conjecture from the 2026 entry. The target is oddness
at every natural-number index, not a finite prefix. KPI = open problems resolved.

## Gap

The search seat reported no proof found after reading the OEIS entry and
revision history on 2026-09-09 and searching by identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those readings or searches. The report establishes only
that no proof was found within that stated literature scope.

## Route

For positive n and m, the coefficient multiplying a(n) in `[x^n] A^m` is
`m*a(0)^(m-1)`. With a(0) = 1, its multiplier in the residual
`n*[x^n]A^n - (n-1)*[x^n]A^(n+1)` is
`n^2 - (n^2-1) = 1`. The private `diagonal_multiplier` and
`residual_difference` lemmas make this precise for series agreeing below n.
The resulting correction stabilizes coefficients and constructs `a` and
`generatingSeries`. Thus `generating_equation` states a(0) = 1, a(1) = 1,
and, for all n > 1, `n*[x^n]A^n = (n-1)*[x^n]A^(n+1)`: the NAME with the
entry's seeds. `generating_unique` covers every integer-series solution with
those seeds.

The same multiplier-one argument gives uniqueness over ZMod 2.
`central_binom_even` proves `2 | C(2m,m)` for m > 0 by directly reusing
Mathlib's central-binomial evenness theorem. Lucas reduction in the private
`odd_diagonal_even` then gives evenness of `C(4m+1,2m)` for m > 0.
Together these show that the all-ones series `(1-X)^(-1)` satisfies the
reduced equation. In integer binomial notation its residual is
`(2-n)*C(2n-1,n)`, zero modulo 2 for n > 1; the Lean proof splits n by parity
and uses the two binomial evenness facts. Hence `mod_two_identity` identifies
`A mod 2 = mk 1`, and coefficient extraction gives `hanna_conjecture`,
`forall n, Odd (a n)`. Only the entry's FIRST conjecture is resolved;
the mod-3 and mod-4 conjectures are not resolved. Imports are Mathlib-only;
the module's declared generality is G.

## Falsifier

A counterexample index n whose coefficient in the normalized solution is
even would refute the assertion. The orchestrator's exact numerical check
is supporting evidence only; no finite check replaces the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/DiagonalPowerRatioAllOdd.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `central_binom_even`,
  `mod_two_identity`.
- The implementation seat reported axioms std3 for each public theorem:
  `propext`, `Classical.choice`, `Quot.sound`.

## Triage

`theorem`. The formal statement resolves the all-terms-odd assertion for the
unique normalized integer solution, not the two other conjectures.

## ASSUMED-UNVERIFIED

Quotes, attribution, date, and seeds were supplied by the orchestrator;
the NAME and oddness COMMENT were copied from the Library note. The OEIS
entry and revision history were read by the search seat on 2026-09-09, not
by this seat. The reported literature scope was that reading plus identifier
searches on arXiv, MathOverflow, and GitHub; no exhaustive literature search
or first-publication priority is claimed. This seat had no network access.
The orchestrator's exact numerical check and the implementation seat's
compilation and axiom reports were not independently rerun by Stage-B.
Source-to-Lean identification is explained by the equation and uniqueness,
but external source fidelity is not a kernel-checked fact.
