/- GID: D5/S3/Quantum/Foundation/FiniteStateChannel
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteStateChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical finite density states and completely positive trace-preserving channels. -/

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Order

/- Library-search audit trail (2026-09-01):
   * Pinned Mathlib supplies `CStarMatrix` and bundled completely positive maps,
     but no finite density-state or trace-preserving quantum-channel structure.
   * The repository had one local copy of both carriers inside
     `QuantumRelativeEntropyDefectComposition`. That frozen node remains
     historical. This file becomes the downward canonical owner for future
     quantum-information developments.
   * The channel composition proof reuses Mathlib's amplified positivity and
     `CStarMatrix.map_map`; no independent positivity notion is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Foundation.FiniteStateChannel

open scoped CStarAlgebra ComplexOrder MatrixOrder

/-- A finite-dimensional density state is a positive semidefinite complex
matrix of trace one. -/
def DensityState (n : Type*) [Fintype n] [DecidableEq n] :=
  {rho : CStarMatrix n n ℂ // 0 <= rho /\ Matrix.trace rho = 1}

namespace DensityState

@[simp]
theorem nonnegative
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho : DensityState n) : 0 <= rho.1 :=
  rho.2.1

@[simp]
theorem trace_eq_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho : DensityState n) : Matrix.trace rho.1 = 1 :=
  rho.2.2

end DensityState

/-- A finite-dimensional quantum channel is a completely positive linear map
that preserves the matrix trace. -/
structure QuantumChannel (a b : Type*)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] where
  toCompletelyPositiveMap :
    CompletelyPositiveMap (CStarMatrix a a ℂ) (CStarMatrix b b ℂ)
  trace_preserving : forall rho : CStarMatrix a a ℂ,
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

@[simp]
theorem mapState_value
    {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (channel : QuantumChannel a b) (rho : DensityState a) :
    (channel.mapState rho).1 = channel.toCompletelyPositiveMap rho.1 := rfl

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
        change 0 <= matrix.map (fun x =>
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
      second.toCompletelyPositiveMap
        (first.toCompletelyPositiveMap rho) := by
  rfl

@[simp]
theorem comp_mapState
    {a b c : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (second : QuantumChannel b c) (first : QuantumChannel a b)
    (rho : DensityState a) :
    (second.comp first).mapState rho =
      second.mapState (first.mapState rho) := by
  apply Subtype.ext
  rfl

end QuantumChannel

/-- Top-level restatement: applying a composed channel to a density state is
sequential state evolution. -/
theorem channel_comp_mapState
    {a b c : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    (second : QuantumChannel b c) (first : QuantumChannel a b)
    (rho : DensityState a) :
    (second.comp first).mapState rho =
      second.mapState (first.mapState rho) :=
  QuantumChannel.comp_mapState second first rho

#print axioms QuantumChannel.comp_apply
#print axioms QuantumChannel.comp_mapState
#print axioms channel_comp_mapState

end D5.S3.Quantum.Foundation.FiniteStateChannel
