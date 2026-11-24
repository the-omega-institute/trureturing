/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechBRSTComplexification
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechBRSTComplexification
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Complex scalar extension recovers the native momentum Lie algebra and BPZ form. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechBRSTRealLie
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Complexification of the native BRST Lie algebra

The signed relative BPZ form and the original momentum bracket are recovered by extending
scalars from the fixed Lie algebra of coefficient conjugation.

proof_shape: momentumRealComplexification, momentumRealComplexification_tmul,
  momentumRealComplexification_preserves_BPZ: content
admission_basis: escape-witness
escape_witness: The two real coordinates of a complex scalar give a two-term tensor
decomposition. Uniqueness of the fixed and imaginary parts detects the kernel, and
the original momentum bracket and relative BPZ evaluation determine the operations on tensors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

attribute [local instance] realLieStateAddCommGroup realLieShellAddCommGroup
  realLieCyclesAddCommGroup

private def momentumComplexificationLift :
    (ℂ ⊗[ℝ] momentumRealLie) →ₗ[ℝ] RestrictScalars ℝ ℂ MomentumH1 :=
  TensorProduct.lift
    ((RestrictScalars.lsmul ℝ ℂ MomentumH1).toLinearMap.compl₂ momentumRealLie.toSubmodule.subtype)

private def momentumComplexificationLinear : (ℂ ⊗[ℝ] momentumRealLie) →ₗ[ℂ] MomentumH1 where
  toFun t := momentumComplexificationLift t
  map_add' := momentumComplexificationLift.map_add
  map_smul' := by
    intro z t
    let evaluate : (ℂ ⊗[ℝ] momentumRealLie) →+ MomentumH1 :=
      (RestrictScalars.addEquiv ℝ ℂ MomentumH1).toAddMonoidHom.comp
        momentumComplexificationLift.toAddMonoidHom
    change evaluate (z • t) = z • evaluate t
    induction t using TensorProduct.inductionOn with
    | tmul w x => exact mul_smul z w (momentumRealValue x)
    | add t u ht hu =>
      simp only [smul_add, map_add, ht, hu]

private theorem momentumComplexificationLinear_tmul (z : ℂ) (x : momentumRealLie) :
    momentumComplexificationLinear (z ⊗ₜ[ℝ] x) = z • momentumRealValue x :=
  rfl

private theorem tensor_real_decomposition (t : ℂ ⊗[ℝ] momentumRealLie) :
    ∃ a b : momentumRealLie, t = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b := by
  induction t using TensorProduct.inductionOn with
  | tmul z x =>
    refine ⟨z.re • x, z.im • x, ?_⟩
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    change z ⊗ₜ[ℝ] x = (((z.re : ℂ) * 1) + (z.im : ℂ) * Complex.I) ⊗ₜ[ℝ] x
    rw [mul_one, Complex.re_add_im]
  | add t u ht hu =>
    obtain ⟨a, b, rfl⟩ := ht
    obtain ⟨c, d, rfl⟩ := hu
    refine ⟨a + c, b + d, ?_⟩
    simp only [TensorProduct.tmul_add]
    exact add_add_add_comm _ _ _ _

private def momentumComplexificationHom : (ℂ ⊗[ℝ] momentumRealLie) →ₗ⁅ℂ⁆ MomentumH1 where
  toLinearMap := momentumComplexificationLinear
  map_lie' := by
    intro t u
    change momentumComplexificationLinear ⁅t, u⁆ =
      ⁅momentumComplexificationLinear t, momentumComplexificationLinear u⁆
    induction t using TensorProduct.inductionOn with
    | tmul z x =>
      induction u using TensorProduct.inductionOn with
      | tmul w y =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, momentumComplexificationLinear_tmul,
          smul_lie, lie_smul, smul_smul]
        rw [mul_comm w z]
        rfl
      | add u v hu hv => simp only [LieRing.lie_add, map_add, hu, hv]
    | add t v ht hv => simp only [LieRing.add_lie, map_add, ht, hv]

/-- The canonical complexification of the fixed real BRST Lie algebra. -/
def momentumRealComplexification : (ℂ ⊗[ℝ] momentumRealLie) ≃ₗ⁅ℂ⁆ MomentumH1 := by
  refine LieEquiv.ofBijective momentumComplexificationHom ⟨?_, ?_⟩
  · change Function.Injective momentumComplexificationLinear
    intro t u h
    obtain ⟨a, b, rfl⟩ := tensor_real_decomposition t
    obtain ⟨c, d, rfl⟩ := tensor_real_decomposition u
    simp only [map_add, momentumComplexificationLinear_tmul, one_smul] at h
    have hparts := momentumH1_real_decomposition_unique a b c d h
    exact congrArg (fun p : momentumRealLie × momentumRealLie => (1 : ℂ) ⊗ₜ[ℝ] p.1 +
      Complex.I ⊗ₜ[ℝ] p.2) hparts
  · change Function.Surjective momentumComplexificationLinear
    intro x
    refine ⟨(1 : ℂ) ⊗ₜ[ℝ] momentumRealPart x + Complex.I ⊗ₜ[ℝ] momentumImaginaryPart x, ?_⟩
    simpa only [map_add, momentumComplexificationLinear_tmul, one_smul] using
      (momentumH1_real_decomposition x).symm

/-- On a pure tensor the canonical map is scalar multiplication of the native real class. -/
@[simp] theorem momentumRealComplexification_tmul (z : ℂ) (x : momentumRealLie) :
    momentumRealComplexification (z ⊗ₜ[ℝ] x) = z • momentumRealValue x :=
  momentumComplexificationLinear_tmul z x

/-- The inverse sends the real and imaginary parts to the two corresponding tensors. -/
theorem momentumRealComplexification_symm_apply (x : MomentumH1) :
    momentumRealComplexification.symm x =
      (1 : ℂ) ⊗ₜ[ℝ] momentumRealPart x + Complex.I ⊗ₜ[ℝ] momentumImaginaryPart x := by
  apply momentumRealComplexification.toLinearEquiv.injective
  change momentumRealComplexification (momentumRealComplexification.symm x) =
    momentumRealComplexification ((1 : ℂ) ⊗ₜ[ℝ] momentumRealPart x +
      Complex.I ⊗ₜ[ℝ] momentumImaginaryPart x)
  rw [LieEquiv.apply_symm_apply]
  simpa only [map_add, momentumRealComplexification_tmul, one_smul] using
    momentumH1_real_decomposition x

/-- The native signed relative BPZ form is the scalar extension of the real BPZ form. -/
theorem momentumRealComplexification_preserves_BPZ (t u : ℂ ⊗[ℝ] momentumRealLie) :
    nativeRelativeBPZ (momentumRealComplexification t) (momentumRealComplexification u) =
      momentumRealBPZ.baseChange ℂ t u := by
  induction t using TensorProduct.inductionOn with
  | tmul z x =>
    induction u using TensorProduct.inductionOn with
    | tmul w y =>
      simp only [momentumRealComplexification_tmul, map_smul, LinearMap.smul_apply,
        LinearMap.BilinForm.baseChange_tmul, ← ofReal_momentumRealBPZ, smul_eq_mul,
        Complex.real_smul]
      ac_rfl
    | add u v hu hv => simp only [map_add, hu, hv]
  | add t v ht hv => simp only [map_add, LinearMap.add_apply, ht, hv]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
