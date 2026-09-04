/- GID: D5/S3/Zeros/ShiftOperators/InverseBlaschkeHistoryDeletion
   generality: G
   mirror-B: D5/B/S3/Zeros/ShiftOperators/InverseBlaschkeHistoryDeletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [inverse_blaschke_history_deletion]
   digest: An inner isometry has a coisometric adjoint with a finite deleted-history space. -/

import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic

/-!
# Inverse-inner history deletion

The Hardy-space construction of finite Blaschke multiplication is not yet available in the
repository.  This module isolates the exact operator-theoretic data it supplies: an isometry `V`
whose orthogonal range complement has finite dimension `m`.  Its adjoint is the inverse-inner
Toeplitz operator.  The results below identify its coisometry, defect projection, kernel,
cokernel, and index without postulating any of those conclusions.

The exact Mathlib results reused here are
`ContinuousLinearMap.isometry_iff_adjoint_comp_self`,
`ContinuousLinearMap.orthogonal_range`, `ContinuousLinearMap.ker_self_comp_adjoint`, and
`Submodule.quotientEquivOrthogonal`.
-/

noncomputable section

open scoped InnerProductSpace

namespace D5.S3.Zeros.ShiftOperators.InverseBlaschkeHistoryDeletion

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The inverse-inner Toeplitz operator associated to an isometric inner multiplier. -/
def inverseInnerToeplitz (V : H →L[𝕜] H) : H →L[𝕜] H :=
  ContinuousLinearMap.adjoint V

/-- The model space is the orthogonal complement of the forward inner range. -/
def modelSpace (V : H →L[𝕜] H) : Submodule 𝕜 H :=
  V.rangeᗮ

/-- The projection onto histories deleted by the inverse-inner operator. -/
def modelProjection (V : H →L[𝕜] H) : H →L[𝕜] H :=
  1 - V.comp (ContinuousLinearMap.adjoint V)

/-- Isometry of the forward inner multiplier is exactly the first coisometry identity. -/
theorem adjoint_comp_forward_eq_one (V : H →L[𝕜] H) (hV : Isometry V) :
    (inverseInnerToeplitz V).comp V = 1 := by
  exact ContinuousLinearMap.isometry_iff_adjoint_comp_self V |>.mp hV

/-- The inverse-inner operator is a coisometry. -/
theorem inverse_comp_adjoint_eq_one (V : H →L[𝕜] H) (hV : Isometry V) :
    (inverseInnerToeplitz V).comp
        (ContinuousLinearMap.adjoint (inverseInnerToeplitz V)) = 1 := by
  rw [inverseInnerToeplitz, ContinuousLinearMap.adjoint_adjoint]
  exact adjoint_comp_forward_eq_one V hV

/-- The forward range projection `VV†` is an orthogonal projection. -/
theorem forwardRangeProjection_isStarProjection (V : H →L[𝕜] H)
    (hV : Isometry V) :
    IsStarProjection (V.comp (ContinuousLinearMap.adjoint V)) := by
  have hstar : (ContinuousLinearMap.adjoint V).comp V = 1 :=
    adjoint_comp_forward_eq_one V hV
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun A : H →L[𝕜] H => A (ContinuousLinearMap.adjoint V x)) hstar
    simpa using congrArg V hx
  · simp [ContinuousLinearMap.isSelfAdjoint_iff']

/-- The deleted-history operator is itself an orthogonal projection. -/
theorem modelProjection_isStarProjection (V : H →L[𝕜] H) (hV : Isometry V) :
    IsStarProjection (modelProjection V) := by
  exact (forwardRangeProjection_isStarProjection V hV).one_sub

/-- Escape witness: the range of the nontrivial defect `I - VV†` is exactly the kernel of `V†`,
hence exactly the histories invisible to the forward inner range. -/
theorem range_modelProjection_eq_modelSpace (V : H →L[𝕜] H) (hV : Isometry V) :
    LinearMap.range (modelProjection V : H →ₗ[𝕜] H) = modelSpace V := by
  have hP : IsIdempotentElem
      ((V.comp (ContinuousLinearMap.adjoint V) : H →L[𝕜] H) : H →ₗ[𝕜] H) :=
    ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mpr
      (forwardRangeProjection_isStarProjection V hV).isIdempotentElem
  calc
    LinearMap.range (modelProjection V : H →ₗ[𝕜] H) =
        LinearMap.ker
          ((V.comp (ContinuousLinearMap.adjoint V) : H →L[𝕜] H) : H →ₗ[𝕜] H) := by
      simpa [modelProjection] using
        LinearMap.IsIdempotentElem.ker_eq_range_one_sub hP |>.symm
    _ = LinearMap.ker
        (ContinuousLinearMap.adjoint V : H →ₗ[𝕜] H) := by
      exact ContinuousLinearMap.ker_self_comp_adjoint V
    _ = modelSpace V := by
      exact (ContinuousLinearMap.orthogonal_range V).symm

/-- The initial projection of the inverse-inner operator is `I - P_K`. -/
theorem adjoint_inverse_comp_inverse (V : H →L[𝕜] H) :
    (ContinuousLinearMap.adjoint (inverseInnerToeplitz V)).comp
        (inverseInnerToeplitz V) = 1 - modelProjection V := by
  simp [inverseInnerToeplitz, modelProjection]

/-- The inverse-inner operator kills exactly the model space. -/
theorem ker_inverseInnerToeplitz (V : H →L[𝕜] H) :
    LinearMap.ker (inverseInnerToeplitz V : H →ₗ[𝕜] H) = modelSpace V := by
  exact (ContinuousLinearMap.orthogonal_range V).symm

/-- Every future output has a forward-inner preimage. -/
theorem inverseInnerToeplitz_surjective (V : H →L[𝕜] H) (hV : Isometry V) :
    Function.Surjective (inverseInnerToeplitz V) := by
  intro y
  refine ⟨V y, ?_⟩
  have h := congrArg (fun A : H →L[𝕜] H => A y) (adjoint_comp_forward_eq_one V hV)
  simpa using h

/-- The cokernel of the forward inner multiplier is canonically the model space. -/
def cokernelEquivModelSpace (V : H →L[𝕜] H) (hV : Isometry V) :
    (H ⧸ V.range) ≃ₗᵢ[𝕜] modelSpace V := by
  letI : CompleteSpace V.range :=
    hV.isClosedEmbedding.isClosed_range.completeSpace_coe
  exact V.range.quotientEquivOrthogonal

/-- A finite model space makes the inverse-inner operator Fredholm. -/
theorem inverseInnerToeplitz_isFredholm (V : H →L[𝕜] H) (hV : Isometry V)
    [FiniteDimensional 𝕜 (modelSpace V)] :
    (inverseInnerToeplitz V).IsFredholm := by
  let T := inverseInnerToeplitz V
  have hsurj : Function.Surjective T := inverseInnerToeplitz_surjective V hV
  have hright : Function.RightInverse V T := by
    intro x
    exact congrArg (fun A : H →L[𝕜] H => A x) (adjoint_comp_forward_eq_one V hV)
  refine ⟨(T.isOpenMap hsurj).isStrictMap T.continuous, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.range_eq_top.mpr hsurj]
    exact isClosed_univ
  · rw [show T.ker = modelSpace V by exact ker_inverseInnerToeplitz V]
    infer_instance
  · rw [LinearMap.range_eq_top.mpr hsurj]
    infer_instance
  · exact T.closedComplemented_ker_of_rightInverse V hright

/-- The index is the number of deleted history dimensions. -/
theorem inverseInnerToeplitz_index (V : H →L[𝕜] H) (hV : Isometry V) (m : ℕ)
    [FiniteDimensional 𝕜 (modelSpace V)]
    (hm : Module.finrank 𝕜 (modelSpace V) = m) :
    (inverseInnerToeplitz V : H →ₗ[𝕜] H).index = m := by
  rw [LinearMap.index_of_surjective (inverseInnerToeplitz_surjective V hV),
    ker_inverseInnerToeplitz V, hm]

/-- Finite-inner inverse Toeplitz operators delete precisely their finite model-space histories. -/
theorem inverse_blaschke_history_deletion (V : H →L[𝕜] H) (hV : Isometry V) (m : ℕ)
    [FiniteDimensional 𝕜 (modelSpace V)]
    (hm : Module.finrank 𝕜 (modelSpace V) = m) :
    (inverseInnerToeplitz V).comp
          (ContinuousLinearMap.adjoint (inverseInnerToeplitz V)) = 1 ∧
      (ContinuousLinearMap.adjoint (inverseInnerToeplitz V)).comp
          (inverseInnerToeplitz V) = 1 - modelProjection V ∧
      IsStarProjection (modelProjection V) ∧
      LinearMap.range (modelProjection V : H →ₗ[𝕜] H) = modelSpace V ∧
      LinearMap.ker (inverseInnerToeplitz V : H →ₗ[𝕜] H) = modelSpace V ∧
      Function.Surjective (inverseInnerToeplitz V) ∧
      (inverseInnerToeplitz V).IsFredholm ∧
      (inverseInnerToeplitz V : H →ₗ[𝕜] H).index = m ∧
      Nonempty ((H ⧸ V.range) ≃ₗᵢ[𝕜] modelSpace V) := by
  exact ⟨inverse_comp_adjoint_eq_one V hV,
    adjoint_inverse_comp_inverse V,
    modelProjection_isStarProjection V hV,
    range_modelProjection_eq_modelSpace V hV,
    ker_inverseInnerToeplitz V,
    inverseInnerToeplitz_surjective V hV,
    inverseInnerToeplitz_isFredholm V hV,
    inverseInnerToeplitz_index V hV m hm,
    ⟨cokernelEquivModelSpace V hV⟩⟩

#print axioms range_modelProjection_eq_modelSpace
#print axioms cokernelEquivModelSpace
#print axioms inverseInnerToeplitz_isFredholm
#print axioms inverse_blaschke_history_deletion

end D5.S3.Zeros.ShiftOperators.InverseBlaschkeHistoryDeletion
