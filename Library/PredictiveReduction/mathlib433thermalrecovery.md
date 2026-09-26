---
bibkey: mathlib433thermalrecovery
authors: The Mathlib Community; Remy Degenne; Lorenzo Luccioli
year: 2026
title: Pinned KL, spectral calculus, exponential remainders and Gaussian precision for predictive thermal recovery
doi: null
url: https://github.com/leanprover-community/mathlib4/tree/v4.33.0
claim: Pinned measure KL and disintegration, concrete matrix spectral calculus, analytic exponential remainders and Gaussian moment identities support separate proof modules; none alone establishes the complete quantum recovery or short-window theorem.
strata_touched:
  - D5/S3/Quantum/Thermal/ClassicalProductRecovery
  - D5/S3/Quantum/Thermal/ExactPartitionCounting
  - D5/S3/Quantum/Thermal/HiddenExperimentRisk
  - D5/S3/Quantum/Algebra/WeylReconstruction
  - D5/S3/Observer/Linear/PredictiveEnergySplitting
  - D5/S3/Observer/Linear/OscillatorSensorJets
  - D5/S3/Quantum/Divergence/SpectralKlein
  - D5/S3/Quantum/Thermal/GibbsFreeEnergyStability
  - D5/S3/Observer/Linear/GradedExponentialRemainder
  - D5/S3/Observer/Linear/GaussianObservationPrecision
license: citation-only
triage: anchor
---

# Library-first proof dependencies for PR8899

## Exact source pin

The PR uses `leanprover/lean4:v4.33.0` and the Mathlib `v4.33.0` tag. The
following APIs were read at that tag. Search results from the rolling branch
were used for navigation only and were followed by pinned source reads.

## Measure recovery and the initial modules

`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean` supplies
`InformationTheory.klDiv_compProd_eq_add` and `klDiv_compProd_left`. KL has
its actual absolute-continuity/integrability branch and ENNReal codomain.
`DataProcessing.lean` supplies `klDiv_map_le`. Applying it in both directions
proves measurable-equivalence invariance, including infinite values.

`Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean` and `Basic.lean`
supply `Measure.condKernel`, its Markov instance and `Measure.disintegrate`.
The arbitrary-joint recovery module constructs this kernel from the joint
measure; it does not assume a disintegration witness. The hidden space is
standard Borel and nonempty.

`Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean` supplies
`LinearMap.surjective_of_injective`. The actual square-matrix synthesis
endomorphism promotes the repository finite Weyl trace pairing to spanning.
The imported `WeylDisplacementTrace.displacement_trace_orthogonal` theorem
explicitly did not already prove this spanning result.

`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` and `PosDef.lean`
supply actual inverse identities and positive-definite congruences. They
support the covariance lift, the positive Gram matrix ruling out a visible
Poisson radical, and the constructed Gaussian observation precision.

`ExactPartitionCounting` begins with CNF syntax and builds Boolean clause
penalties and the rational Gibbs partition. `HiddenExperimentRisk` constructs
adaptive Kraus histories and uses nonnegative integration for randomized
risk. `OscillatorSensorJets` computes actual derivative rows and polynomial
moment determinants; these are not an assumed exponential asymptotic.

## Spectral Klein and free-energy continuation, 2026-09-26

Pinned `Mathlib/Analysis/Matrix/Spectrum.lean` constructs the eigenvalues,
eigenvector unitary and `Matrix.IsHermitian.spectral_theorem`.
`HermitianFunctionalCalculus.lean` identifies `cfc f A` with the actual
spectral synthesis for every real function f on the finite spectrum.
`Mathlib/Analysis/Matrix/PosDef.lean` supplies nonnegative/positive eigenvalues.

`SpectralKlein` uses those actual spectral matrices, constructs their squared
overlap weights and derives Klein from the scalar log tangent inequality.
No packaged quantum relative-entropy inequality is assumed. The first matrix
may be singular; the reference must be positive definite. This is a
formalization of a classical finite-matrix inequality, not a novelty claim.

`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unique.lean`
supplies `StarAlgHom.map_cfc`, including the continuity and selfadjointness
hypotheses. The log restriction is continuous on the finite spectrum.
`Mathlib/Analysis/CStarAlgebra/Spectrum.lean` supplies preservation of the
C-star norm by a star algebra equivalence. The norm in the new raw matrix
calculation is the Euclidean operator norm, not an entrywise norm.

The repository `GibbsVariationalIdentity` already constructs the normalized
matrix exponential and proves its positive definiteness and trace-log identity.
`GibbsFreeEnergyStability` reuses that object and adds the actual nonnegativity
and two-state variational comparison. The imported convention is exp(H);
the physical free-energy argument explicitly substitutes -beta H.

The existing `SupportAwareRelativeEntropy` defines reverse-nullspace support
inclusion and extends the trace-log expression to WithTop Real. The old
`QuantumRelativeEntropyDefectComposition` proves only a real telescoping
identity. The new faithful-reference Klein theorem does not turn either file
into a general singular-reference DPI, Petz equality or Pinsker proof.

## Actual exponential remainder and Gaussian construction

`Mathlib/Analysis/Normed/Algebra/Exponential.lean` supplies the actual
exponential formal power series and its infinite radius.
`Mathlib/Analysis/Analytic/Basic.lean`,
`HasFPowerSeriesOnBall.uniform_geometric_approx'`, gives a uniform remainder
on a smaller ball. `GradedExponentialRemainder` instantiates it and derives
the first visible coefficient and uniform O(T) normalized error. It does not
assume a Taylor remainder as a field in a certificate.

`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` constructs
`multivariateGaussian` by an actual affine pushforward of the standard
Gaussian and proves `integral_id_multivariateGaussian` and
`covariance_eval_multivariateGaussian`. The new observation module proves
positive definiteness of beta I plus tau M-transpose M before using its inverse
as a covariance. The candidate conditional distribution is a real Gaussian
measure, but its equality to the observation conditional law is still open.

Pinned `Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean` was also read.
It provides Rodrigues, degree and symmetry identities for the integer
polynomials, but does not supply the L2 orthogonality/normalization theorem
required by this PR. The new batch does not label that missing theorem proved.

## Verification boundary

Current coverage and actual finite diagnostics are in `docs/reports/pr8899`.
Historical initial reports are preserved there. The four continuation sources
and Scribes have not been elaborated/compiled in this environment. Numerical
checks, source hashes and textual Scribe-anchor resolution do not establish
kernel proof, admission, independent review, or closure of the fourteen
original results. This note supplies provenance, not a new theory volume.
