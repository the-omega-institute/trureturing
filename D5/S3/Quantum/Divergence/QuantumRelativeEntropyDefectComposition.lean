/- GID: D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quantum relative-entropy loss telescopes along composable matrix channels. -/

import D5.S3.Quantum.ChannelFixedState
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n 'PosSemidef.*trace|trace.*= 1|structure .*Channel' D5/S3`
     found the established finite-dimensional matrix setup in
     `D5.S3.Quantum.ChannelFixedState`, but no named density-state carrier or
     general quantum-channel structure to import.
   * `rg -n 'QuantumRelative|RelativeEntropy|Umegaki|vonNeumann'` over pinned
     Mathlib found no packaged quantum relative entropy.
   * `CompletelyPositiveMap` is the pinned bundled completely positive linear
     map, `CStarMatrix.map_map` supplies its composition calculation, and
     `CFC.log` is the pinned matrix logarithm. They are used directly below.
   * The pre-existing sibling `RelativeEntropyDefectComposition` quantifies
     over arbitrary carrier types and arbitrary functions, so it does not
     provide the density matrices or quantum channels required here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition

open scoped ComplexOrder CStarAlgebra MatrixOrder

/-- A finite-dimensional density state is a positive semidefinite complex
matrix of trace one. -/
def DensityState (n : Type*) [Fintype n] [DecidableEq n] :=
  {rho : CStarMatrix n n ℂ // 0 ≤ rho ∧ Matrix.trace rho = 1}

/-- A finite-dimensional quantum channel is a completely positive linear map
that preserves the matrix trace. -/
structure QuantumChannel (a b : Type*)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] where
  toCompletelyPositiveMap :
    CompletelyPositiveMap (CStarMatrix a a ℂ) (CStarMatrix b b ℂ)
  trace_preserving : ∀ rho : CStarMatrix a a ℂ,
    Matrix.trace (toCompletelyPositiveMap rho) = Matrix.trace rho

namespace QuantumChannel

/-- A quantum channel sends density states to density states. -/
noncomputable def mapState
    {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (channel : QuantumChannel a b) (rho : DensityState a) :
    DensityState b := by
  refine ⟨channel.toCompletelyPositiveMap rho.1, ?_,
    (channel.trace_preserving rho.1).trans rho.2.2⟩
  exact map_nonneg channel.toCompletelyPositiveMap rho.2.1

/-- Composition of completely positive trace-preserving matrix channels. -/
noncomputable def comp
    {a b c : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (second : QuantumChannel b c) (first : QuantumChannel a b) :
    QuantumChannel a c where
  toCompletelyPositiveMap :=
    { toLinearMap := second.toCompletelyPositiveMap.toLinearMap.comp
        first.toCompletelyPositiveMap.toLinearMap
      map_cstarMatrix_nonneg' := by
        intro k matrix hmatrix
        have hfirst :=
          first.toCompletelyPositiveMap.map_cstarMatrix_nonneg matrix hmatrix
        have hsecond := second.toCompletelyPositiveMap.map_cstarMatrix_nonneg
          (matrix.map first.toCompletelyPositiveMap) hfirst
        have hmap :
            (matrix.map first.toCompletelyPositiveMap).map
                second.toCompletelyPositiveMap =
              matrix.map (fun x => second.toCompletelyPositiveMap
                (first.toCompletelyPositiveMap x)) := by
          ext i j
          rfl
        change 0 ≤ matrix.map (fun x =>
          second.toCompletelyPositiveMap (first.toCompletelyPositiveMap x))
        rw [← hmap]
        exact hsecond }
  trace_preserving rho := by
    change Matrix.trace (second.toCompletelyPositiveMap
      (first.toCompletelyPositiveMap rho)) = Matrix.trace rho
    rw [second.trace_preserving, first.trace_preserving]

@[simp]
theorem comp_apply
    {a b c : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (second : QuantumChannel b c) (first : QuantumChannel a b)
    (rho : CStarMatrix a a ℂ) :
    (second.comp first).toCompletelyPositiveMap rho =
      second.toCompletelyPositiveMap (first.toCompletelyPositiveMap rho) := by
  rfl

end QuantumChannel

/-- The finite-dimensional quantum relative-entropy trace expression. -/
noncomputable def quantumRelativeEntropy
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : DensityState n) : ℝ :=
  (Matrix.trace (rho.1 * (CFC.log rho.1 - CFC.log sigma.1))).re

/-- Relative-entropy distinguishability lost through a quantum channel. -/
noncomputable def relativeEntropyDefect
    {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (channel : QuantumChannel a b) (rho sigma : DensityState a) : ℝ :=
  quantumRelativeEntropy rho sigma -
    quantumRelativeEntropy (channel.mapState rho) (channel.mapState sigma)

/-- Relative-entropy loss telescopes exactly along two composable quantum
channels acting on positive trace-one matrix states. -/
theorem relative_entropy_defect_composition
    {a b c : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (first : QuantumChannel a b) (second : QuantumChannel b c)
    (rho sigma : DensityState a) :
    relativeEntropyDefect (second.comp first) rho sigma =
      relativeEntropyDefect first rho sigma +
        relativeEntropyDefect second (first.mapState rho) (first.mapState sigma) := by
  unfold relativeEntropyDefect quantumRelativeEntropy QuantumChannel.mapState
  simp only [QuantumChannel.comp_apply]
  ring

#print axioms relative_entropy_defect_composition

end D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
