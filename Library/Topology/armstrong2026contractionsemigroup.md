---
bibkey: armstrong2026contractionsemigroup
authors: Scott Armstrong
year: 2026
title: Strongly continuous contraction semigroups and their generators
doi: null
url: https://github.com/scottnarmstrong/MarkovProcess/tree/dbade0d12c4f84179441a9df7d7147df7a8bcaa0/Semigroup
claim: The strong right generator is closed and determines a strongly continuous contraction semigroup.
strata_touched:
  - D5/S3/Quantum/Analysis/PhysicalHeatGenerator
  - D5/S3/Quantum/Analysis/DiagonalHeat
license: Apache-2.0
triage: anchor
---

# Strong contraction semigroup generators

The immutable source is Scott Armstrong's MarkovProcess revision
`dbade0d12c4f84179441a9df7d7147df7a8bcaa0`, in
`Semigroup/{Basic,StrongOperatorLimit,Generator,OrbitContinuity,GeneratorClosed,GeneratorUniqueness}`.
The selected repository proofs and full copyright attribution are in
`D5/S3/Quantum/Analysis/PhysicalHeatGenerator.lean`. The full license is
`docs/reports/heat-suppliers/markovprocess-LICENSE.txt`.
The upstream tree has no NOTICE file.

`StronglyContinuousContractionSemigroup.tendsto_differenceQuotient_of_tendsto_generator`
passes a convergent graph family to the full right-generator graph.
`StronglyContinuousContractionSemigroup.ext_of_generator` identifies semigroups
with equal full generator domains and actions. The diagonal heat consumer uses
both public declarations directly. Its local right-slope argument adapts the
private selected `tendsto_slope_add_of_hasDerivAt` proof while preserving arbitrary
Hilbert-space universes. The generic private heat construction in the same
repository source supplies the multiplier, finite expansion and strong
continuity arguments.

These standard semigroup facts identify the positive full-basis heat with the
same actual finite-span self-adjoint closure. They supply no heat-trace
summability, quantum-state reference, entropy inequality or state-family
compactness theorem. Replace the selected proofs when the repository's actual
pinned Mathlib supplies equivalent directly applicable results.

## Verified locator

https://github.com/scottnarmstrong/MarkovProcess/tree/dbade0d12c4f84179441a9df7d7147df7a8bcaa0/Semigroup
