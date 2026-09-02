/- GID: D5/S3/Quantum/Divergence/LegacyRelativeEntropyBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/LegacyRelativeEntropyBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen scalar quantum relative entropy is identified as the finite support-conditioned branch. -/

import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

/- Library-search audit trail (2026-09-01):
   * The imported frozen node defines a real-valued total trace-log expression
     together with local density-state and channel carriers.
   * `SupportAwareRelativeEntropy` supplies the canonical downward carriers and
     the missing top branch outside support inclusion.
   * This additive correction leaves the frozen theorem unchanged, supplies
     lossless state and channel adapters, and states the exact semantic boundary
     of the legacy scalar expression. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary

open scoped CStarAlgebra ComplexOrder MatrixOrder

/-- Convert a canonical density state to the frozen local carrier without
changing its matrix or proofs. -/
def toLegacyDensityState
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho :
      D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState n) :
    D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState n :=
  ⟨rho.1, rho.2⟩

/-- Convert the frozen local density-state carrier back to the canonical owner. -/
def fromLegacyDensityState
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho :
      D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState n) :
    D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState n :=
  ⟨rho.1, rho.2⟩

@[simp]
theorem fromLegacy_toLegacy_densityState
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho :
      D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState n) :
    fromLegacyDensityState (toLegacyDensityState rho) = rho := by
  cases rho
  rfl

@[simp]
theorem toLegacy_fromLegacy_densityState
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho :
      D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.DensityState n) :
    toLegacyDensityState (fromLegacyDensityState rho) = rho := by
  cases rho
  rfl

/-- Convert a canonical channel to the frozen local channel carrier. -/
def toLegacyQuantumChannel
    {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (channel :
      D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel a b) :
    D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.QuantumChannel a b where
  toCompletelyPositiveMap := channel.toCompletelyPositiveMap
  trace_preserving := channel.trace_preserving

/-- Convert the frozen local channel carrier to the canonical owner. -/
def fromLegacyQuantumChannel
    {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (channel :
      D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.QuantumChannel a b) :
    D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel a b where
  toCompletelyPositiveMap := channel.toCompletelyPositiveMap
  trace_preserving := channel.trace_preserving

@[simp]
theorem toLegacyQuantumChannel_apply
    {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (channel :
      D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel a b)
    (matrix : CStarMatrix a a ℂ) :
    (toLegacyQuantumChannel channel).toCompletelyPositiveMap matrix =
      channel.toCompletelyPositiveMap matrix := rfl

/-- The frozen real-valued expression is definitionally the finite trace-log
branch of the support-aware construction. -/
theorem legacy_quantumRelativeEntropy_eq_finite_branch
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma :
      D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState n) :
    D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.quantumRelativeEntropy
        (toLegacyDensityState rho) (toLegacyDensityState sigma) =
      D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy.finiteTraceLogRelativeEntropy
        rho sigma := by
  rfl

/-- On an unsupported pair the corrected semantics is infinite, while the
frozen scalar expression remains exactly the finite trace-log branch. -/
theorem unsupported_pair_semantic_boundary
    {n : Type*} [Fintype n] [DecidableEq n]
    {rho sigma :
      D5.S3.Quantum.Foundation.FiniteStateChannel.DensityState n}
    (supportFailure :
      ¬D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy.SupportContained
        rho sigma) :
    D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy
        rho sigma = ⊤ /\
      D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition.quantumRelativeEntropy
          (toLegacyDensityState rho) (toLegacyDensityState sigma) =
        D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy.finiteTraceLogRelativeEntropy
          rho sigma := by
  refine ⟨?_, legacy_quantumRelativeEntropy_eq_finite_branch rho sigma⟩
  exact
    D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy.extendedQuantumRelativeEntropy_eq_top_of_not_support
      supportFailure

#print axioms legacy_quantumRelativeEntropy_eq_finite_branch
#print axioms unsupported_pair_semantic_boundary

end D5.S3.Quantum.Divergence.LegacyRelativeEntropyBoundary
