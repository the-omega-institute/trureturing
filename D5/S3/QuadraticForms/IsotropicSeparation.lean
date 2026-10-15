/- GID: D5/S3/QuadraticForms/IsotropicSeparation
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/IsotropicSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Null vectors separate nonzero linear forms over algebraically closed fields. -/

import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.QuadraticForms.IsotropicSeparation

open Module LinearMap

universe scalarUniverse vectorUniverse

variable {Scalar : Type scalarUniverse} {Space : Type vectorUniverse}
variable [Field Scalar] [CharZero Scalar] [IsAlgClosed Scalar]
variable [AddCommGroup Space] [Module Scalar Space] [FiniteDimensional Scalar Space]

theorem exists_null_detected_by_linear_form (form : LinearMap.BilinForm Scalar Space)
    (symmetric : LinearMap.IsSymm form) (separating : LinearMap.SeparatingLeft form)
    (dimension : 2 ≤ finrank Scalar Space) (functional : Space →ₗ[Scalar] Scalar)
    (functional_nonzero : functional ≠ 0) :
    ∃ direction : Space, form direction direction = 0 ∧ functional direction ≠ 0 := by
  classical
  letI : Invertible (2 : Scalar) := invertibleOfNonzero (by norm_num)
  obtain ⟨basis, orthogonal⟩ := LinearMap.BilinForm.exists_orthogonal_basis symmetric
  obtain ⟨first, detected⟩ : ∃ index, functional (basis index) ≠ 0 := by
    by_contra missing
    push_neg at missing
    apply functional_nonzero
    apply basis.ext
    intro index
    simpa using missing index
  obtain ⟨second, distinct⟩ : ∃ index : Fin (finrank Scalar Space), first ≠ index := by
    let zeroIndex : Fin (finrank Scalar Space) := ⟨0, by omega⟩
    let oneIndex : Fin (finrank Scalar Space) := ⟨1, by omega⟩
    by_cases firstZero : first = zeroIndex
    · refine ⟨oneIndex, ?_⟩
      rw [firstZero]
      exact Fin.ne_of_val_ne (by norm_num [zeroIndex, oneIndex])
    · exact ⟨zeroIndex, firstZero⟩
  have secondSquare : form (basis second) (basis second) ≠ 0 :=
    orthogonal.not_isOrtho_basis_self_of_separatingLeft separating second
  obtain ⟨root, square⟩ := IsAlgClosed.exists_eq_mul_self
    (-form (basis first) (basis first) / form (basis second) (basis second))
  have cancellation : root * root * form (basis second) (basis second) =
      -form (basis first) (basis first) := by
    rw [← square, div_mul_cancel₀ _ secondSquare]
  have forward : form (basis first) (basis second) = 0 := orthogonal distinct
  have backward : form (basis second) (basis first) = 0 := orthogonal distinct.symm
  have plusNull : form (basis first + root • basis second)
      (basis first + root • basis second) = 0 := by
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, forward, backward, mul_zero, zero_add, add_zero]
    linear_combination cancellation
  have minusNull : form (basis first - root • basis second)
      (basis first - root • basis second) = 0 := by
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, forward, backward, mul_zero, zero_sub, sub_zero]
    linear_combination cancellation
  by_cases plusDetected : functional (basis first + root • basis second) ≠ 0
  · exact ⟨_, plusNull, plusDetected⟩
  · refine ⟨_, minusNull, ?_⟩
    intro minusZero
    have plusZero := not_ne_iff.mp plusDetected
    simp only [map_add, map_sub, map_smul, smul_eq_mul] at plusZero minusZero
    have firstZero : functional (basis first) = 0 := by
      linear_combination (plusZero + minusZero) / 2
    exact detected firstZero

end D5.S3.QuadraticForms.IsotropicSeparation
