---
slug: oeis-a397242-mod-three-sums
bibkey: hanna2026a397242b
doi: null
url: https://oeis.org/A397242
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport
---

# The residue-two conjecture of OEIS A397242

## Problem

OEIS A397242 (Paul D. Hanna, Jun 19 2026), NAME:

> O.g.f. satisfies A(x) = exp( x + Sum_{n>=2} (n^2-1) * a(n)*x^n / n^2 ).

COMMENT (the sole resolution target of this dossier):

> Conjecture: for n > 0, a(n) == 2 (mod 3) iff n+2 is a sum of 2 distinct powers of 3 (A038464).

The entry's parity COMMENT was already proved and frozen here as
`D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.hanna_conjecture`.
It is NOT re-claimed. This module imports that frozen module and reuses its
sequence rather than redefining it. The other mod-three COMMENT has its own dossier.

## Motivation

This is a first-tier OEIS conjecture from the 2026 entry. The KPI is open
problems resolved; this dossier concerns one universally quantified conjecture.

## Gap

No proof was found in the supplied search: the search seat read the OEIS entry
and revision history on 2026-09-09 and performed identifier searches on arXiv,
MathOverflow, and GitHub. This Stage-B seat has no network and did not repeat
those searches. This is a bounded literature-search report, not a priority proof.

## Route

The frozen recurrence is decimated modulo three to `U = 1 + xVU` and
`V = U − xV²`, giving `V = 1 + x²V³`. Setting `T = xV` and `F = xU` gives
`T = x + T³`, `F = T + T²`, and `F = x + x²A` over ZMod(3). Strong induction
on ternary index classes proves the complete coefficient classification
`ternary_support_classification`; the private lemma `supports_disjoint`
separately proves disjointness of the two supports. The classification is the
escape witness on the live paths of both `hanna_conjecture_one` and
`hanna_conjecture_two`. The first is the iff between `a n % 3 = 1` and `n+2`
being `3^k` or `2·3^k`; the second is the iff between `a n % 3 = 2` and `n+2`
being a sum of two distinct powers of 3 (OEIS A038464). Both directions are
proved. Disjointness is additionally used by `hanna_conjecture_two`.

The sequence itself is NOT redefined: `a`, `d`, the recurrence, and the
uniqueness theorem `generating_unique` are imported verbatim from the frozen
`D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity`
(statement_id `sha256:a4963d2999ab1b65b9a13aa0e30c25f39b115bbe426ea881628c80eaaf23e370`),
which proved the entry's parity conjecture. Target generality: I.

## Falsifier

A positive counterexample index n for which a(n) % 3 = 2 and n+2 is not a sum of two distinct powers of 3, or n+2 is such a sum and a(n) % 3 is not 2 would falsify this
iff. The orchestrator's exact numerical check is supporting evidence only;
the formal theorem has no finite index bound.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.lean`.
- Public theorem (sole claimed resolution): `hanna_conjecture_two`.
- Companion and escape witness: `ternary_support_classification`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat's axiom audit.

## Triage

`theorem`. The formal proof closes the quoted mod-three iff for every positive
natural index; the classification also includes index zero.

## ASSUMED-UNVERIFIED

The quotes and attribution were supplied by the orchestrator and copied from
`Library/Recurrence/hanna2026a397242b.md`. The OEIS revision history was read
by the search seat, not by this seat. Literature scope was the OEIS entry and
history plus identifier searches on arXiv, MathOverflow, and GitHub as of
2026-09-09; this seat has no network. The absence of a proof outside that
scope, publication priority, and the source-to-Lean identification are not
kernel-checked facts.
