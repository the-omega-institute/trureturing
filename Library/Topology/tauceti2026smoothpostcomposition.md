---
bibkey: tauceti2026smoothpostcomposition
authors: The Tau Ceti contributors
year: 2026
title: Calculus on spaces of continuous maps
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/3924e3ef4afb8102b6a8e9893043c2c1a303f0d1/TauCeti/Analysis/Calculus/ContinuousMap.lean
claim: Nonlinear postcomposition by a finite-order or smooth map preserves that order on continuous maps from any compact topological space, with its pointwise Frechet derivative.
strata_touched:
  - D5/S3/Topology/CompactSmoothPostcomposition
license: Apache-2.0
triage: anchor
---

# Smooth nonlinear postcomposition on compact domains

The immutable source is TauCetiProject/TauCeti revision
`3924e3ef4afb8102b6a8e9893043c2c1a303f0d1`, file
`TauCeti/Analysis/Calculus/ContinuousMap.lean`, SHA-256
`883d419db06673f626fd506e107eef7b211747c40c7b0d0208120dc25fd2c318`.
The selected original declarations are `ContinuousMap.applyContinuousLinearMap`,
`ContinuousMap.applyContinuousLinearMap_apply`,
`ContinuousMap.hasFDerivAt_postcomp`, the private finite-order induction
`ContinuousMap.contDiff_postcomp_nat`, and `ContinuousMap.contDiff_postcomp`.
The interval-extension and Volterra integration declarations are excluded.
No original proof body or theorem telescope is changed. Module/export syntax,
the repository header, and imports are adapted to the receiving project.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors.
The complete source Apache-2.0 license is retained at
[the Tau Ceti license](../../docs/reports/polarization-suppliers/tauceti-LICENSE.txt),
SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The complete selected upstream Git tree contains no NOTICE file; the selected
file imports only Mathlib modules. No additional own-package attribution chain
is required for these declarations.

The source pins Lean 4.35.0 and Mathlib
`074063781836922cb02701cd12943c9f51731afa`; the receiving project pins
Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
These unequal pins exclude dependency-form reuse. This is original-proof
source reuse under the repository's source-port rule, with no claim of new
mathematical authorship.

For every compact topological K, real-or-complex-like nontrivially normed
field k, normed k-spaces E and F, and n in NatInfinity, the map sending g to
f composed with g is ContDiff of order n whenever f is. The codomain universe
is max(u,v), exactly as in the source, so the induction also covers the
continuous-linear-map-valued derivative. Zero and infinite order, infinite or
empty K, and zero spaces are included. Neither completeness, finite dimension,
global derivative bounds nor linearity of f is assumed.

The derivative proof first obtains a uniform neighborhood estimate for the
derivative along the compact image of g. A segment mean-value estimate then
bounds the nonlinear remainder uniformly by an arbitrary positive constant
times the input distance. Induction transfers finite derivative orders; the
infinite-order criterion supplies smoothness.

The original `TauCeti/Analysis/ODE/SmoothParameter.lean` theorem
`contDiff_picardResidual` uses `contDiff_postcomp` on its parameter-path
pairing. This reference asserts no ODE, global-flow, half-density group,
strong-continuity, generator or self-adjointness theorem in the receiving
project.

## Retirement

Remove the selected local port when the project's own upgraded pinned Mathlib
contains declarations equivalent at the complete original telescopes, and
checked direct substitutions for those declarations discharge every live local
consumer. An upstream proposal or acceptance alone does not meet this condition.

## Verified locator

https://github.com/TauCetiProject/TauCeti/blob/3924e3ef4afb8102b6a8e9893043c2c1a303f0d1/TauCeti/Analysis/Calculus/ContinuousMap.lean
