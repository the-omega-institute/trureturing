---
bibkey: mathlib433thermalrecovery
authors: The Mathlib Community; Remy Degenne; Lorenzo Luccioli
year: 2026
title: Pinned measure KL, disintegration, and finite-dimensional linear algebra for predictive thermal recovery
doi: null
url: https://github.com/leanprover-community/mathlib4/tree/v4.33.0
claim: The pinned library supplies genuine measure-level KL chain and data-processing theorems, constructed standard Borel conditional kernels, and injective-endomorphism surjectivity; these do not imply quantum recovery or short-window asymptotics.
strata_touched:
  - D5/S3/Quantum/Thermal/ClassicalProductRecovery
  - D5/S3/Quantum/Thermal/ExactPartitionCounting
  - D5/S3/Quantum/Thermal/HiddenExperimentRisk
  - D5/S3/Quantum/Algebra/WeylReconstruction
  - D5/S3/Observer/Linear/PredictiveEnergySplitting
  - D5/S3/Observer/Linear/OscillatorSensorJets
license: citation-only
triage: anchor
---

# Library-first proof dependencies for PR8899

## Exact source pin

The PR's `lean-toolchain` is `leanprover/lean4:v4.33.0`; its Mathlib dependency
is the `v4.33.0` tag. The APIs below were inspected at that tag, not inferred
from the newer rolling documentation.

- `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`:
  `InformationTheory.klDiv_compProd_eq_add` and `klDiv_compProd_left`.
  KL has its actual absolute-continuity/integrability branch and values in
  `ENNReal`. Replacing this with an arbitrary real-valued function would lose
  the recovery equality's measure semantics.
- `Mathlib/InformationTheory/KullbackLeibler/DataProcessing.lean`:
  `InformationTheory.klDiv_map_le`. Data processing in both directions proves
  measurable-equivalence invariance, including infinite KL values.
- `Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean` and `Basic.lean`:
  `Measure.condKernel`, its Markov instance, and
  `Measure.disintegrate`. The main arbitrary-joint recovery declarations
  construct this kernel from the joint law; they do not require the caller
  to provide a disintegration witness. The hidden space is standard Borel
  and nonempty.
- `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`:
  `LinearMap.surjective_of_injective`. Applied to the explicitly defined
  square-matrix synthesis endomorphism, this closes the span gap in the
  repository's finite Weyl trace-pairing result.
- `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` and `PosDef.lean`:
  actual nonsingular inverse identities and positive-definite congruences.
  These provide the covariance inverses and the positive Gram matrix used
  to rule out a radical of the visible Poisson form.

## Existing repository truth sources consumed

`D5/S3/Quantum/Algebra/WeylDisplacementTrace.lean` provides the actual matrix
pairing `displacement_trace_orthogonal`. It explicitly does not establish
spanning. The new `WeylReconstruction` module uses that exact theorem and
constructs the missing linear-algebra bridge, rather than replacing the
finite Weyl matrices with an assumed complete abstract frame.

`D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy.lean` already exists on
the target PR branch. It defines support inclusion and a `WithTop Real`
quantum trace-log divergence. Its documentation explicitly leaves positivity,
DPI, and Petz equality as further theorems. The older
`QuantumRelativeEntropyDefectComposition` is only a real-valued telescoping
identity. Neither file is evidence that the quantum recovery/Pinsker part of
this PR has been completed.

## Other constructed components

`ExactPartitionCounting` starts from CNF syntax and proves a rational counting
recovery statement with explicit local Boolean projections. It does not take
an already-known count or an already-proved small tail as its sole input.
`HiddenExperimentRisk` constructs complete adaptive Kraus histories and uses
nonnegative integrals for randomized estimation risk. `OscillatorSensorJets`
computes actual `C B^k/k!` rows and polynomial moment determinants; it is not
an assumed asymptotic-equivalence interface.

## Scope and verification boundary

The source candidates and their paired Scribes are described in
`Evidence/PR8899/README.md`. At this delivery, they have not been elaborated by
Lean or checked by its kernel, and the Scribes have not been compiled. Finite
checks and source scans are independently reproducible, but do not replace
those checks. This note is explanatory provenance, not a freeze declaration,
proof of all fourteen paper results, or a new theory volume.
