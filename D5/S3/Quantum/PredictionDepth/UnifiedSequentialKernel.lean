/- GID: D5/S3/Quantum/PredictionDepth/UnifiedSequentialKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/UnifiedSequentialKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: All allowed word statistics agree exactly on the sequential residual. -/

import D5.S3.Quantum.Completion.SequentialWordObservationResidual

/- Library-search audit trail (2026-08-27):
   * Exact family hit `sequentialWordEffect` is the canonical source-order
     Heisenberg fold and is imported rather than redeclared.
   * `sequential_observation_iff` covers only words bounded by one fixed length;
     it is not an exact hit for an arbitrary allowed-word family.
   * Pinned-Mathlib hits `Submodule.span_induction`,
     `Submodule.sub_mem_orthogonal_of_inner_left`, and
     `Submodule.inner_left_of_mem_orthogonal` supply the proof. Searches found
     no exact arbitrary allowed-word kernel theorem. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.PredictionDepth.UnifiedSequentialKernel

open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Completion.SequentialWordObservationResidual

variable {d : Nat}

local instance matrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

local instance hermitianRealInnerProductSpace :
    InnerProductSpace ℝ (HermitianSpace d) :=
  Submodule.innerProductSpace (HermitianSpace d)

/-- Equality of every allowed sequential word statistic is exactly membership
of the represented state difference in the orthogonal residual of the real
span of those word effects. -/
theorem unified_sequential_kernel
    {Alphabet State : Type*}
    (allowed : Set (List Alphabet))
    (instrumentDual : Alphabet → HermitianSpace d →ₗ[ℝ] HermitianSpace d)
    (stateRepresentation : State → HermitianSpace d)
    (rho sigma : State) :
    ((∀ word : List Alphabet, word ∈ allowed →
        inner ℝ (stateRepresentation rho)
            (sequentialWordEffect instrumentDual word) =
          inner ℝ (stateRepresentation sigma)
            (sequentialWordEffect instrumentDual word)) ↔
      stateRepresentation rho - stateRepresentation sigma ∈
        (Submodule.span ℝ
          (sequentialWordEffect instrumentDual '' allowed))ᗮ) := by
  constructor
  · intro hword
    apply Submodule.sub_mem_orthogonal_of_inner_left
    intro effect
    refine Submodule.span_induction
      (p := fun effect _ =>
        inner ℝ (stateRepresentation rho) effect =
          inner ℝ (stateRepresentation sigma) effect)
      ?_ ?_ ?_ ?_ effect.property
    · rintro _ ⟨word, hallowed, rfl⟩
      exact hword word hallowed
    · simp
    · intro first second _ _ hfirst hsecond
      simp only [inner_add_right, hfirst, hsecond]
    · intro scalar value _ hvalue
      simp only [inner_smul_right, hvalue]
  · intro hresidual word hallowed
    have hinner := Submodule.inner_left_of_mem_orthogonal
      (Submodule.subset_span
        (show sequentialWordEffect instrumentDual word ∈
            sequentialWordEffect instrumentDual '' allowed from
          ⟨word, hallowed, rfl⟩)) hresidual
    simpa only [inner_sub_left, sub_eq_zero] using hinner

#print axioms unified_sequential_kernel

end D5.S3.Quantum.PredictionDepth.UnifiedSequentialKernel
