/- GID: D5/S3/VertexAlgebra/OriginalTensorCB0
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/OriginalTensorCB0
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual physical b0 contracts every tensor c-field mode on unrestricted algebraic states. -/

import D5.S3.VertexAlgebra.OriginalCartanFaithfulness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.OriginalTensorCB0

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge BcGhostFockSupport
open BcGhostSuperGenerators VertexOperatorTensorProduct
open scoped TensorProduct VertexOperator BigOperators

theorem tensor_c_B0 (D : LatticeData) (matterField : VertexOperator ℂ (Carrier D))
    (mode : ℤ) (matter : Carrier D) (ghost : Fock ℂ) :
    B D 0 (((field matterField (currentField .c))[[mode]]) (matter ⊗ₜ[ℂ] ghost)) +
      ((field matterField (currentField .c))[[mode]]) (B D 0 (matter ⊗ₜ[ℂ] ghost)) =
      ((matterField)[[mode + 1]]) matter ⊗ₜ[ℂ] ghost := by
  have mapped := (B D 0).toAddMonoidHom.map_finsum
    (diagonal_finite matterField (currentField .c) mode matter ghost)
  simp only [LinearMap.toAddMonoidHom_coe, diagonal] at mapped
  rw [field_mode, mode_tmul, mapped]
  simp only [B, TensorProduct.map_tmul, LinearMap.id_apply]
  change (∑ᶠ index : ℤ, ((matterField)[[index]]) matter ⊗ₜ[ℂ]
      b 0 (((currentField .c)[[mode - 1 - index]]) ghost)) +
    (∑ᶠ index : ℤ, ((matterField)[[index]]) matter ⊗ₜ[ℂ]
      ((currentField .c)[[mode - 1 - index]]) (b 0 ghost)) = _
  have firstFinite : Function.HasFiniteSupport (fun index : ℤ =>
      ((matterField)[[index]]) matter ⊗ₜ[ℂ]
        b 0 (((currentField .c)[[mode - 1 - index]]) ghost)) := by
    exact (diagonal_finite matterField (currentField .c) mode matter ghost).fun_comp
      (g := B D 0) (by simp)
  have joined :
      (∑ᶠ index : ℤ, ((matterField)[[index]]) matter ⊗ₜ[ℂ]
        b 0 (((currentField .c)[[mode - 1 - index]]) ghost)) +
      (∑ᶠ index : ℤ, ((matterField)[[index]]) matter ⊗ₜ[ℂ]
        ((currentField .c)[[mode - 1 - index]]) (b 0 ghost)) =
      ∑ᶠ index : ℤ, ((((matterField)[[index]]) matter ⊗ₜ[ℂ]
        b 0 (((currentField .c)[[mode - 1 - index]]) ghost)) +
        (((matterField)[[index]]) matter ⊗ₜ[ℂ]
          ((currentField .c)[[mode - 1 - index]]) (b 0 ghost))) := by
    exact (finsum_add_distrib firstFinite
      (diagonal_finite matterField (currentField .c) mode matter (b 0 ghost))).symm
  rw [joined]
  simp only [← TensorProduct.tmul_add, currentField_modes, currentMode]
  have anticommutator (index : ℤ) :
      b 0 (c (mode - 1 - index + 2) ghost) +
        c (mode - 1 - index + 2) (b 0 ghost) =
      if index = mode + 1 then ghost else 0 := by
    have equality := LinearMap.congr_fun
      (BcGhostStressCurrent.b_c (K := ℂ) 0 (mode - 1 - index + 2)) ghost
    simp only [Module.End.mul_apply, LinearMap.add_apply] at equality
    by_cases same : index = mode + 1
    · have zeroMode : (0 : ℤ) + (mode - 1 - index + 2) = 0 := by omega
      rw [if_pos zeroMode] at equality
      simpa only [Module.End.one_apply, if_pos same] using equality
    · have different : (0 : ℤ) + (mode - 1 - index + 2) ≠ 0 := by omega
      rw [if_neg different] at equality
      simpa only [LinearMap.zero_apply, if_neg same] using equality
  simp_rw [anticommutator]
  rw [finsum_eq_single _ (mode + 1)]
  · simp
  · intro index different
    simp [different]

#print axioms tensor_c_B0

end D5.S3.VertexAlgebra.OriginalTensorCB0
