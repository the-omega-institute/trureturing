---
slug: lichtenfelz-modin-preston-2026-zeitlin-sixj-identities
bibkey: lichtenfelz2026zeitlin
doi: 10.1007/s00220-025-05533-w
url: https://arxiv.org/abs/2508.09833v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.result
---

# Lichtenfelz–Modin–Preston Conjecture 1: four Zeitlin six-j identities

## Problem

Conjecture 1 of Lichtenfelz, Modin and Preston, arXiv:2508.09833v1, section 2.2, asserts all four identities (2.10)–(2.13). The complete quotation and the two Wigner-symbol conventions are in the literature note `lichtenfelz2026zeitlin`. The domain is every integer N ≥ 2, with 1 ≤ j,l < N; only (2.10) assumes j ≠ l. The sums traverse i = 1,...,N−1, λ(i) = i(i+1), and H(j) is the j-th harmonic number. The preregistration is issue #11604.

## Motivation

The four identities supply the hypothesis of the source's Theorem 3 on Ricci curvature of the Zeitlin approximation to hydrodynamics on the sphere. `D5/S3/Quantum/Algebra/ZeitlinSixJ/SumRules.result` proves the full conjunction for the Racah definition of the Wigner six-j symbol, with doubled spin labels and zero outside triangle admissibility.

## Gap

The source reports numerical verification up to N = 2048. The claimed settlement is universal, rather than a finite certificate. The bounded literature check in #11604 found no proof in its searched scope; journal sentence-by-sentence comparison and citation-index completeness are unverified. No exhaustive novelty or priority claim is made.

## Route

The factorial-kernel recurrence identifies the terminating Racah polynomial. An exact four-spin WZ identity produces the finite Jacobi action, and endpoint WZ normalization fixes the orthogonality constant. A constructed two-sided Green inverse gives (2.10); the parity intertwiner gives (2.11); the central Jacobi diagonal gives (2.12); the harmonic binomial identity and factorial antidifference give (2.13). The eleven-module chain keeps these actual shared matrices, supports, phase factors and finite sums in one dependency graph.

## Falsifier

A tuple satisfying the stated domain but violating any conjunct would contradict `SumRules.result` in its formal system. A mismatch between the doubled-spin Racah formula and the source's symbol convention would invalidate source fidelity. A primary publication already proving the exact conjecture would change the bounded provenance assessment.

## Evidence

`SumRules.claim` is the conjunction of the four fully quantified identities. `SumRules.result : SumRules.claim` proves it using the Racah finite sum, with no postulated recurrence, orthogonality or symbol identities. The public foundation results supply the actual arbitrary-spin action and endpoint normalization, the physical spectral inverse and the signed addition identity. The axiom boundary is the Lean standard three axioms, not an additional six-j assumption.

## Triage

Tier 2: a published mathematical-physics research problem. This dossier records the whole Conjecture 1 as Proved for the stated definition and domain. Conjecture 2 is a separate asymptotic target.

### What the settlement shows

- **Proved in this chain:** exact endpoint normalization and the Jacobi action connect the actual Racah sums to an orthogonal finite matrix; no abstract orthogonality hypothesis substitutes for these identities.
- **Proved in this module:** the central inverse diagonal, signed Casimir moment, ordinary Casimir moment and harmonic sum have the exact values in (2.10)–(2.13) for all N ≥ 2. The j ≠ l restriction belongs solely to the inverse-Casimir identity.
- **Proved in this chain:** the Green inverse and parity constructions apply to every admissible channel in their displayed foundation statements; the final source identities are their central-channel consequences.
- **Open in Lean:** the paper's Ricci-curvature Theorem 3 and the analytic passage to its hydrodynamical interpretation are not formalized here. The source explicitly conditions Theorem 3 on these four identities, so this settlement supplies that mathematical hypothesis under the stated source correspondence.
- **Open:** Conjecture 2's sharper asymptotic bound for the positive Ricci contribution is not a consequence asserted by this module. Generalizations beyond the stated spin configuration require separate hypotheses and proofs.

## ASSUMED-UNVERIFIED

The journal text has not been compared sentence by sentence with arXiv v1, and citation-index completeness is unverified. The literature conclusion remains not-found-in-searched-scope. No claim of worldwide absence, priority, exhaustive sharpness or resolution of Conjecture 2 follows from the formal result.
