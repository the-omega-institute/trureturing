---
slug: oeis-a372577-double-composition-mod-four
bibkey: hanna2024a372577
doi: null
url: https://oeis.org/A372577
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification
---

# Modulo-four classification of the A372577 coefficients

## Problem

OEIS A372577, Paul D. Hanna, May 30, 2024:

NAME:

> Expansion of g.f. A(x) satisfying A(x)^2 = A(A( x*A(x) + x*A(x)^2 )).

COMMENT (target):

> Conjecture: a(6*n - 3) == 3 (mod 4) and a(6*n - k) == 1 (mod 4) when k = {0,1,2,4,5} for n >= 1.

Separate COMMENT (a derived corollary, not a second resolution):

> All terms appear to be odd.

The normalized generating series has constant coefficient zero and linear
coefficient one; `a(n) = [x^n]A(x)` for positive indices.

## Motivation

This first-tier OEIS conjecture was recorded in 2024. KPI: open problems
resolved. The modulo-four classification resolves one conjecture; oddness is
its corollary and is not counted as a second result.

## Gap

The supplied search report found no proof: the search seat read the OEIS entry
and revision history on 2026-09-09 and searched the identifier on arXiv,
MathOverflow, and GitHub. Stage B had no network access and did not repeat
these searches. Absence within this scope does not establish publication priority.

## Route

Normalize `A = X·U` and cancel `X²·U` to turn the double composition into a
contracting operator. Induction proves coefficient stabilization and constructs
the normalized solution. Two homogenized polynomial identities certify the
rational reduction's double composition over `ZMod 4`, and uniqueness identifies
it with the integer solution's reduction.

The equivalent complete classification is
`a n % 4 = if n % 6 = 3 then 3 else 1` for `n > 0`. It covers every residue
class modulo six. The entry's two clauses cover exactly the same positive
index set. The orchestrator reported that the clauses accounted for all 39
computed positions without gaps; this finite check is supporting evidence only.

`odd_coefficients` is proved from `hanna_conjecture` by case split: both residues
1 and 3 are odd. It is a derived corollary, not a separate resolution.
The module imports only Mathlib, so its generality is G. Frozen public
fixed-point theorems concern different operators; minimal private agreement
and stabilization lemmas were re-proved, as recorded in the implementation
seat's plan deviations. No frozen D5 module is a direct proof dependency.

## Falsifier

A positive index `n` with `a n % 4 ≠ (if n % 6 = 3 then 3 else 1)` would
contradict the classification. The orchestrator's exact 39-position check is
supporting evidence only, not a proof of the universal assertion.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`.
- Derived corollary: `odd_coefficients`, proved from `hanna_conjecture`.
- Public definitions: `generatingSeries`, `a`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat's `#print axioms` for all six declarations.

## Triage

`theorem`. The complete classification proves the two conjectured clauses;
oddness follows as a corollary of this one resolution.

## ASSUMED-UNVERIFIED

Quotes were supplied by the orchestrator. The NAME and target COMMENT were
copied verbatim from `Library/ArithSums/hanna2024a372577.md`; that note paraphrases
the separate oddness comment, whose verbatim wording was supplied in the brief.
The OEIS revision history was read by the search seat on 2026-09-09, not by
this seat. Literature scope: OEIS entry and revision history, plus identifier
searches on arXiv, MathOverflow, and GitHub. Stage B had no network access.
No exhaustive literature search or first-publication priority is claimed.
Source-to-Lean identification and the orchestrator's exact computational check
are external evidence, not kernel-checked facts.
