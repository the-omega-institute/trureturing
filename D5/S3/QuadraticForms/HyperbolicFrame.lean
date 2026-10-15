/- GID: D5/S3/QuadraticForms/HyperbolicFrame
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/HyperbolicFrame
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A literal hyperbolic pair extends to an invertible frame with both dual rows. -/

import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.QuadraticForms.HyperbolicFrame

open Module Submodule LinearMap.BilinForm
open scoped BigOperators

universe scalarUniverse

variable {Scalar : Type scalarUniverse} [Field Scalar] {dimension : ℕ}

theorem exists_frame_with_literal_duals
    (form : LinearMap.BilinForm Scalar (Fin dimension → Scalar))
    (symmetric : LinearMap.IsSymm form)
    (first second : Fin dimension → Scalar)
    (firstNull : form first first = 0) (secondNull : form second second = 0)
    (paired : form second first = 1) :
    ∃ (frame inverse : Matrix (Fin dimension) (Fin dimension) Scalar)
      (firstAxis secondAxis : Fin dimension),
      inverse * frame = 1 ∧ frame * inverse = 1 ∧ firstAxis ≠ secondAxis ∧
      frame firstAxis = first ∧ frame secondAxis = second ∧
      (∀ row, form (frame secondAxis) (frame row) = if row = firstAxis then 1 else 0) ∧
      (∀ row, form (frame firstAxis) (frame row) = if row = secondAxis then 1 else 0) := by
  classical
  have opposite : form first second = 1 := (symmetric.eq first second).trans paired
  have firstNonzero : first ≠ 0 := by
    intro zero
    simpa [zero] using paired
  have independent : LinearIndependent Scalar ![first, second] := by
    rw [LinearIndependent.pair_iff' firstNonzero]
    intro scalar equality
    have contradiction := congrArg (form first) equality
    simp only [map_smul, smul_eq_mul, firstNull, mul_zero, opposite] at contradiction
    exact zero_ne_one contradiction
  let plane := span Scalar (Set.range ![first, second])
  have firstMember : first ∈ plane := subset_span ⟨0, rfl⟩
  have secondMember : second ∈ plane := subset_span ⟨1, rfl⟩
  have reflexive : LinearMap.IsRefl form := symmetric.isRefl
  have planeNondegenerate : LinearMap.Nondegenerate (form.restrict plane) := by
    apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (reflexive.domRestrict plane)).mpr
    intro vector vanished
    obtain ⟨coefficients, expansion⟩ :=
      (mem_span_range_iff_exists_fun Scalar).mp vector.property
    have firstCoefficient : coefficients 0 = 0 := by
      have equation := vanished ⟨second, secondMember⟩
      change form (vector : Fin dimension → Scalar) second = 0 at equation
      rw [← expansion] at equation
      simpa [Fin.sum_univ_two, opposite, secondNull] using equation
    have secondCoefficient : coefficients 1 = 0 := by
      have equation := vanished ⟨first, firstMember⟩
      change form (vector : Fin dimension → Scalar) first = 0 at equation
      rw [← expansion] at equation
      simpa [Fin.sum_univ_two, firstNull, paired] using equation
    apply Subtype.ext
    rw [← expansion]
    simp [Fin.sum_univ_two, firstCoefficient, secondCoefficient]
  have complementary : IsCompl plane (form.orthogonal plane) :=
    isCompl_orthogonal_of_restrict_nondegenerate reflexive planeNondegenerate
  let complement := form.orthogonal plane
  let planeBasis := Basis.span independent
  have planeRows (index : Fin 2) : (planeBasis index : Fin dimension → Scalar) =
      ![first, second] index := congrArg Subtype.val (Basis.span_apply independent index)
  let complementBasis := Module.finBasis Scalar complement
  let combined := (planeBasis.prod complementBasis).map
    (Submodule.prodEquivOfIsCompl plane complement complementary)
  have planeRow (index : Fin 2) : combined (Sum.inl index) = ![first, second] index := by
    simp [combined, Basis.map_apply, Basis.prod_apply, planeRows]
  have complementRow (index : Fin (finrank Scalar complement)) :
      combined (Sum.inr index) = (complementBasis index : Fin dimension → Scalar) := by
    simp [combined, Basis.map_apply, Basis.prod_apply]
  have firstOrthogonal (index : Fin (finrank Scalar complement)) :
      form first (combined (Sum.inr index)) = 0 := by
    rw [complementRow]
    exact mem_orthogonal_iff.mp (complementBasis index).property first firstMember
  have secondOrthogonal (index : Fin (finrank Scalar complement)) :
      form second (combined (Sum.inr index)) = 0 := by
    rw [complementRow]
    exact mem_orthogonal_iff.mp (complementBasis index).property second secondMember
  have firstDual (row : Fin 2 ⊕ Fin (finrank Scalar complement)) :
      form second (combined row) = if row = Sum.inl 0 then 1 else 0 := by
    rcases row with index | index
    · fin_cases index <;> simp [planeRow, paired, secondNull]
    · simp [secondOrthogonal]
  have secondDual (row : Fin 2 ⊕ Fin (finrank Scalar complement)) :
      form first (combined row) = if row = Sum.inl 1 then 1 else 0 := by
    rcases row with index | index
    · fin_cases index <;> simp [planeRow, firstNull, opposite]
    · simp [firstOrthogonal]
  have cardinality : Fintype.card (Fin 2 ⊕ Fin (finrank Scalar complement)) = dimension := by
    rw [← Module.finrank_eq_card_basis combined, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  let indices := Fintype.equivFinOfCardEq cardinality
  let basis := combined.reindex indices
  let firstAxis := indices (Sum.inl 0)
  let secondAxis := indices (Sum.inl 1)
  have firstRow : basis firstAxis = first := by
    simp [basis, firstAxis, Basis.reindex_apply, planeRow]
  have secondRow : basis secondAxis = second := by
    simp [basis, secondAxis, Basis.reindex_apply, planeRow]
  let standard := Pi.basisFun Scalar (Fin dimension)
  let frame := (LinearMap.toMatrix basis standard LinearMap.id).transpose
  let inverse := (LinearMap.toMatrix standard basis LinearMap.id).transpose
  have rowEquation (row : Fin dimension) : frame row = basis row := by
    ext column
    change LinearMap.toMatrix basis standard LinearMap.id column row = basis row column
    rw [LinearMap.toMatrix_apply]
    simp [standard, Pi.basisFun_repr]
  have leftInverse : inverse * frame = 1 := by
    change (LinearMap.toMatrix standard basis LinearMap.id).transpose *
      (LinearMap.toMatrix basis standard LinearMap.id).transpose = 1
    rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp standard basis standard]
    simp [LinearMap.toMatrix_id]
  have rightInverse : frame * inverse = 1 := by
    change (LinearMap.toMatrix basis standard LinearMap.id).transpose *
      (LinearMap.toMatrix standard basis LinearMap.id).transpose = 1
    rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp basis standard basis]
    simp [LinearMap.toMatrix_id]
  refine ⟨frame, inverse, firstAxis, secondAxis, leftInverse, rightInverse, ?_,
    (rowEquation firstAxis).trans firstRow, (rowEquation secondAxis).trans secondRow, ?_, ?_⟩
  · intro equality
    have same := indices.injective equality
    simpa using same
  · intro row
    rw [rowEquation, secondRow, rowEquation]
    have dual := firstDual (indices.symm row)
    simpa [basis, Basis.reindex_apply, firstAxis, indices.symm_apply_eq] using dual
  · intro row
    rw [rowEquation, firstRow, rowEquation]
    have dual := secondDual (indices.symm row)
    simpa [basis, Basis.reindex_apply, secondAxis, indices.symm_apply_eq] using dual

end D5.S3.QuadraticForms.HyperbolicFrame
