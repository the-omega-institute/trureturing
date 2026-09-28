---
bibkey: kitware2026rectangular
authors: Jon Crall, Claude Fable 5, Claude Opus 4.8, GPT-5.6 Thinking, and GPT-5.6 High
year: 2026
title: Formal rectangular singular-value variational bounds
doi: null
url: https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace
claim: Ky Fan variational bounds for finite rectangular linear maps follow from singular-value and polar-decomposition constructions.
strata_touched:
  - D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational
license: Apache-2.0
triage: anchor
---

# Rectangular singular-value variational bounds

The pinned source contains `KyFan`, `PositiveSqrt`,
`SelfAdjointFunctionalCalculus`, `Polar/Decomposition`,
`RectangularSingularValues`, `ZeroExtension`, and `CourantFischer` Lean
modules under `ForTauCeti/Analysis/InnerProductSpace`. The local rectangular
variational bound selects and adapts these arguments to the repository's
pinned Lean and Mathlib interfaces. It does not attribute the finite-sector
channel optimum to this source.

The source headers identify the contributors above. The copyright, exact
revision, modifications, and full Apache-2.0 license text are retained in
`docs/reports/licenses/finite-sector-channel-third-party.md`. Retire the port
when this repository's pinned Mathlib supplies equivalent declarations.

## Verified locator

The pinned source is
https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/64e234954217f3ca907ac980c8cbde2900109a66/ForTauCeti/Analysis/InnerProductSpace.
The `KyFan`, `PositiveSqrt`, `SelfAdjointFunctionalCalculus`,
`Polar/Decomposition`, `RectangularSingularValues`, `ZeroExtension`, and
`CourantFischer` modules in that directory supply the rectangular
singular-value and variational arguments cited here.
