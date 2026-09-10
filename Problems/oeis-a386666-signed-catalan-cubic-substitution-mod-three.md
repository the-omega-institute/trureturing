---
slug: oeis-a386666-signed-catalan-cubic-substitution-mod-three
bibkey: hanna2025a386666
doi: null
url: https://oeis.org/A386666
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree
---

# Signed Catalan cubic substitution modulo three

## Problem

OEIS A386666 (Paul D. Hanna, Sep 07 2025) states:

> G.f. A(x) satisfies: A(x)^2 = A( x^2 + 4*A(x)^3 ).
>
> Conjecture: a(3*n) (mod 3) == 2*a(3*n+1) (mod 3) == a(3*n+2) (mod 3) == 2*A039966(n) for n > 0, where A039966(n) equals the number of partitions of n into distinct powers of 3.

The conjecture is formalized with `distinctPowersOfThree n` standing for A039966(n).

## Motivation

This is a first-tier recent OEIS conjecture. KPI: open problems resolved.

## Gap

No proof was found in the OEIS entry or revision history, or by identifier searches on arXiv, MathOverflow, and GitHub, as reported by the search seat on 2026-09-08. This seat has no network access.

## Route

`generatingSeries` is constructed directly over ℤ by even residual corrections and compositional inversion. `generating_equation` proves `A(0) = 0`, `a(1) = 1`, and `A² = A(X² + 4A³)`, with integrality requiring no extra hypothesis. `generating_unique` proves uniqueness among normalized solutions by the private agreement/divisibility equivalence. Over `ZMod 3`, `signedCatalanSeries` satisfies `S + S² = X` and the reduced cubic equation. The ternary digit-support series has the self-similarity `D = (1 + X) · D(X³)`; Frobenius and unit cancellation give `(1 + X) · D² = 1`, yielding the three coefficient residues in `signed_catalan_mod_three`. First-difference uniqueness of normalized compositional inverses identifies `A` modulo 3 with `S`, and `hanna_conjecture` reads off the stated residues for `p = distinctPowersOfThree`, for `n > 0`. There is no D5 import; generality is G.

## Falsifier

A counterexample index `n > 0` at which any of the three asserted congruences fails would falsify the conjecture. The orchestrator's exact finite check is supporting evidence only.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree.lean`.
- Main theorem: `hanna_conjecture`.
- Companion theorems: `generating_equation`, `generating_unique`, `signed_catalan_mod_three`.
- Definition: `def distinctPowersOfThree (n : ℕ) : ℕ := if (Nat.digits 3 n).all (· != 2) then 1 else 0`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` (std3).

## Triage

`theorem`.

## ASSUMED-UNVERIFIED

The OEIS quotations are supplied by the orchestrator. The OEIS revision history was read by the search seat, not by this seat. The literature search scope is limited to the sources named above and the supplied report.
