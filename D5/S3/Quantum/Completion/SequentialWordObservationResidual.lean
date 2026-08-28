/- GID: D5/S3/Quantum/Completion/SequentialWordObservationResidual
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/SequentialWordObservationResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Instrument word expectations agree exactly on the generated orthogonal residual. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Algebra.FutureWordOrthogonalResidual

/- Library-search audit trail (2026-08-27):
   * No exact D5 theorem states the source's free-word instrument claim.
   * The existing FutureWordOrthogonalResidual.future_word_orthogonal_residual
     covers finite indexed families; this module needs arbitrary List words and
     therefore proves the corresponding span induction directly.
   * Pinned Mathlib hits Submodule.span_induction,
     Submodule.sub_mem_orthogonal_of_inner_left, and
     Submodule.inner_left_of_mem_orthogonal supply the complete argument.
   * Body-shape grep for List.foldr and instrument found no canonical
     word-effect construction; the fold below is the source primitive
     construction, not a target-shaped alias.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Completion.SequentialWordObservationResidual

open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition

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

/- The fold is the Heisenberg composition
   I*_{g1} (... (I*_{gn} I) ...) from the source semantics. -/
def sequentialWordEffect {Alphabet : Type*}
    (instrumentDual : Alphabet → HermitianSpace d →ₗ[ℝ] HermitianSpace d)
    (word : List Alphabet) : HermitianSpace d :=
  word.foldr (fun generator effect => instrumentDual generator effect)
    (identityHermitian d)

set_option maxHeartbeats 4000000 in
-- The dependent span over all finite words needs extra elaboration budget.
/-- All bounded instrument words agree exactly when the state difference is
orthogonal to the span of their Heisenberg effects. -/
theorem sequential_observation_iff
    {Alphabet State : Type*}
    (instrumentDual : Alphabet → HermitianSpace d →ₗ[ℝ] HermitianSpace d)
    (stateRepresentation : State → HermitianSpace d)
    (rho sigma : State) (n : Nat) :
    ((∀ word : List Alphabet, word.length ≤ n →
        inner ℝ (stateRepresentation rho) (sequentialWordEffect instrumentDual word) =
          inner ℝ (stateRepresentation sigma) (sequentialWordEffect instrumentDual word)) ↔
      stateRepresentation rho - stateRepresentation sigma ∈
        (Submodule.span ℝ {effect | ∃ word : List Alphabet,
          word.length ≤ n ∧ effect = sequentialWordEffect instrumentDual word})ᗮ) := by
  let effectSet : Set (HermitianSpace d) := {effect | ∃ word : List Alphabet,
    word.length ≤ n ∧ effect = sequentialWordEffect instrumentDual word}
  change ((∀ word : List Alphabet, word.length ≤ n →
      inner ℝ (stateRepresentation rho) (sequentialWordEffect instrumentDual word) =
        inner ℝ (stateRepresentation sigma) (sequentialWordEffect instrumentDual word)) ↔
    stateRepresentation rho - stateRepresentation sigma ∈
      (Submodule.span ℝ effectSet)ᗮ)
  constructor
  · intro hword
    apply Submodule.sub_mem_orthogonal_of_inner_left
    intro v
    refine Submodule.span_induction
      (p := fun effect _ =>
        inner ℝ (stateRepresentation rho) effect =
          inner ℝ (stateRepresentation sigma) effect)
      ?_ ?_ ?_ ?_ v.property
    · rintro effect ⟨word, hlength, rfl⟩
      exact hword word hlength
    · simp
    · intro u v _ _ hu hv
      simp only [inner_add_right, hu, hv]
    · intro scalar effect _ heffect
      simp only [inner_smul_right, heffect]
  · intro hresidual word hlength
    have hinner := Submodule.inner_left_of_mem_orthogonal
      (Submodule.subset_span (show sequentialWordEffect instrumentDual word ∈ effectSet from
        ⟨word, hlength, rfl⟩)) hresidual
    simpa only [inner_sub_left, sub_eq_zero] using hinner

#print axioms sequential_observation_iff

end D5.S3.Quantum.Completion.SequentialWordObservationResidual
