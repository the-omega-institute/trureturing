/- GID: D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize all local effect readouts by equality of reduced states. -/

import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import Mathlib.LinearAlgebra.Matrix.PosDef

/- Library-search audit trail (2026-08-27):
   * Pinned Mathlib searches found no finite-matrix partial-trace characterization.
     Exact hit `Matrix.trace_mul_conjTranspose_self_eq_zero_iff` supplies the
     nondegeneracy step for the Hermitian reduced-state difference.
   * The body-shape search `fun i j => ∑ a, joint (a, i) (a, j)` found only
     `LocalMarginalCorrelationBlindSpot.traceFirstFactor`, fixed to two qubits.
     The definition below is its carrier-general construction, not a duplicate
     on the same family carrier.
   * The canonical repository `DensityState` is imported rather than redeclared.
     Local observations are quantified inline over every Hermitian matrix. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open scoped BigOperators ComplexOrder

/-- Trace out the first factor of a finite bipartite complex matrix. -/
noncomputable def partialTraceFirst {A B : Type*} [Fintype A]
    (joint : Matrix (A × B) (A × B) Complex) : Matrix B B Complex :=
  fun i j => ∑ a, joint (a, i) (a, j)

private theorem partialTraceFirst_isHermitian {A B : Type*} [Fintype A]
    (joint : Matrix (A × B) (A × B) Complex) (hjoint : joint.IsHermitian) :
    (partialTraceFirst joint).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [partialTraceFirst]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact hjoint.apply (a, i) (a, j)

/-- Two finite bipartite density states give identical expectations for every
Hermitian effect local to the second factor exactly when tracing out the first
factor gives the same reduced state. -/
theorem local_observation_partial_trace_equivalence
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho sigma : DensityState (A × B)) :
    (forall effect : Matrix B B Complex, effect.IsHermitian ->
      Matrix.trace
          (partialTraceFirst (CStarMatrix.ofMatrix.symm rho.1) * effect) =
        Matrix.trace
          (partialTraceFirst (CStarMatrix.ofMatrix.symm sigma.1) * effect)) <->
      partialTraceFirst (CStarMatrix.ofMatrix.symm rho.1) =
        partialTraceFirst (CStarMatrix.ofMatrix.symm sigma.1) := by
  have rhoHermitian : (CStarMatrix.ofMatrix.symm rho.1).IsHermitian :=
    congrArg CStarMatrix.ofMatrix.symm rho.2.1.isSelfAdjoint.star_eq
  have sigmaHermitian : (CStarMatrix.ofMatrix.symm sigma.1).IsHermitian :=
    congrArg CStarMatrix.ofMatrix.symm sigma.2.1.isSelfAdjoint.star_eq
  constructor
  · intro sameReadout
    let difference : Matrix B B Complex :=
      partialTraceFirst (CStarMatrix.ofMatrix.symm rho.1) -
        partialTraceFirst (CStarMatrix.ofMatrix.symm sigma.1)
    have differenceHermitian : difference.IsHermitian :=
      (partialTraceFirst_isHermitian _ rhoHermitian).sub
        (partialTraceFirst_isHermitian _ sigmaHermitian)
    have readoutDifference := sameReadout difference differenceHermitian
    have traceDifference : Matrix.trace (difference * difference) = 0 := by
      change Matrix.trace
          ((partialTraceFirst (CStarMatrix.ofMatrix.symm rho.1) -
              partialTraceFirst (CStarMatrix.ofMatrix.symm sigma.1)) * difference) = 0
      rw [sub_mul, Matrix.trace_sub, readoutDifference, sub_self]
    have traceNorm :
        Matrix.trace (difference * Matrix.conjTranspose difference) = 0 := by
      rw [differenceHermitian.eq]
      exact traceDifference
    have differenceZero : difference = 0 :=
      Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp traceNorm
    exact sub_eq_zero.mp differenceZero
  · intro sameReduced effect _
    rw [sameReduced]

#print axioms local_observation_partial_trace_equivalence

end D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence
