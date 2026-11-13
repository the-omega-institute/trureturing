/- GID: D5/S3/Quantum/Foundation/HermitianExclusionKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/HermitianExclusionKernel
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Full proper-functional exclusion in a complex PSD cone is the orthogonal support face. -/

import D5.S3.Quantum.Foundation.SectionROGFrame
import D5.S3.Quantum.Foundation.FacetZeroGluing
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The complete PSD cone, trace unit, and all original real-linear effects. -/

noncomputable section
open scoped Matrix ComplexOrder RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.HermitianExclusionKernel

open CircuitBalancedConfirmation FacetZeroGluing SectionROGFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full positive semidefinite cone in the real Hermitian carrier. -/
def cone : PointedCone ℝ (HermitianMat ι ℂ) := PointedCone.positive ℝ _

/-- The original trace unit, represented by pairing with the identity. -/
def unit : HermitianMat ι ℂ →ₗ[ℝ] ℝ := HermitianMat.innerₗ 1

private theorem positive_representative (f : HermitianMat ι ℂ →ₗ[ℝ] ℝ)
    (hf : ∀ X ∈ cone, 0 ≤ f X) :
    ∃ A : HermitianMat ι ℂ, 0 ≤ A ∧ ∀ X, f X = ⟪A, X⟫_ℝ := by
  let A := (InnerProductSpace.toDual ℝ (HermitianMat ι ℂ)).symm
    f.toContinuousLinearMap
  have hrep (X) : f X = ⟪A, X⟫_ℝ :=
    (InnerProductSpace.toDual_symm_apply).symm
  refine ⟨A, HermitianMat.zero_le_iff.mpr ?_, hrep⟩
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨A.H, fun z => ?_⟩
  rw [← pair_rankOne, ← hrep]
  exact Complex.ofReal_nonneg.mpr (hf _ (rankOne_nonneg z))

/-- For every unit complex vector, exclusion by any original proper real-linear
effect is exactly annihilation of that vector by the whole mixed state. -/
theorem exclusion_iff_kernel (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1)
    (X : HermitianMat ι ℂ) :
    X ∈ exclusion cone unit (rankOne v) ↔
      0 ≤ X ∧ X.trace = 1 ∧ X.mat *ᵥ (v : ι → ℂ) = 0 := by
  have hnorm : star (v : ι → ℂ) ⬝ᵥ (v : ι → ℂ) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hv]
    simp
  constructor
  · rintro ⟨hX, f, ⟨hf, hfp⟩, hfX⟩
    obtain ⟨A, hA, hrep⟩ := positive_representative f (fun Y hY => (hf Y hY).1)
    have hcomp : 0 ≤ (1 : HermitianMat ι ℂ) - A := by
      apply HermitianMat.zero_le_iff.mpr
      apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      refine ⟨(1 - A).H, fun z => ?_⟩
      rw [← pair_rankOne]
      have h := (hf (rankOne z) (rankOne_nonneg z)).2
      rw [hrep] at h
      have hz : 0 ≤ ⟪(1 : HermitianMat ι ℂ) - A, rankOne z⟫_ℝ := by
        simpa only [inner_sub_left, HermitianMat.one_inner, unit] using sub_nonneg.mpr h
      exact Complex.ofReal_nonneg.mpr hz
    have hAv : A.mat *ᵥ (v : ι → ℂ) = v := by
      have hp : ⟪A, rankOne v⟫_ℝ = 1 := by rw [← hrep, hfp]
      have hc : star (v : ι → ℂ) ⬝ᵥ
          ((1 - A).mat *ᵥ (v : ι → ℂ)) = 0 := by
        rw [← pair_rankOne, inner_sub_left, HermitianMat.one_inner,
          rankOne_trace_norm, hv, hp]
        simp
      have hk := (HermitianMat.zero_le_iff.mp hcomp).dotProduct_mulVec_zero_iff.mp hc
      simpa only [HermitianMat.mat_sub, HermitianMat.mat_one,
        Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using hk
    have hsupport : A.support ≤ X.ker :=
      (HermitianMat.inner_zero_iff hA hX.1).mp (by rw [← hrep, hfX])
    have hvs : v ∈ A.support := by
      refine ⟨v, ?_⟩
      apply WithLp.ext
      exact hAv
    exact ⟨hX.1, hX.2, (X.mem_ker_iff_mulVec_zero v).mp (hsupport hvs)⟩
  · rintro ⟨hX, ht, hXv⟩
    refine ⟨⟨hX, ht⟩, HermitianMat.innerₗ (rankOne v), ⟨?_, ?_⟩, ?_⟩
    · intro Y hY
      refine ⟨HermitianMat.inner_ge_zero (rankOne_nonneg v) hY, ?_⟩
      simpa only [rankOne_trace_norm, hv, one_pow, one_mul, unit,
        HermitianMat.one_inner] using
        HermitianMat.inner_le_mul_trace (rankOne_nonneg v) hY
    · apply Complex.ofReal_injective
      rw [pair_rankOne]
      change star (v : ι → ℂ) ⬝ᵥ
        (Matrix.vecMulVec (v : ι → ℂ) (star (v : ι → ℂ)) *ᵥ (v : ι → ℂ)) = _
      simp [Matrix.vecMulVec_mulVec, hnorm]
    · apply Complex.ofReal_injective
      rw [real_inner_comm, pair_rankOne, hXv]
      simp

end D5.S3.Quantum.Foundation.HermitianExclusionKernel
