/- GID: D5/S3/Arith/Robin/ForwardKernel/JointBrownianKernel
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/JointBrownianKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed fourth kernels integrate into energies and squared cross forms. -/

import D5.S3.Arith.Robin.ForwardKernel.BrownianFourthKernel

/-! Integration of the three pairings in a mixed Brownian fourth moment. -/

namespace D5.S3.Arith.Robin.ForwardKernel.JointBrownianKernel

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs MomentTransferDefs BrownianFourthKernel DyadicMacroMoments

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The profile-weighted integral of a cross covariance kernel on the unit square. -/
def crossKernelForm (g₁ g₂ : ℝ → ℝ) (C : ℝ × ℝ → ℝ) : ℝ :=
  ∫ z, g₁ z.1 * g₂ z.2 * C z ∂unitMeasure.prod unitMeasure

/-- The marginal pairing and the two cross pairings of a mixed fourth moment. -/
def brownianW22 (κ₁ κ₂ : ℝ) (C : ℝ × ℝ → ℝ) (s : Fin 4 → ℝ) : ℝ :=
  κ₁ * κ₂ * min (s 0) (s 1) * min (s 2) (s 3) +
    C (s 0, s 2) * C (s 1, s 3) + C (s 0, s 3) * C (s 1, s 2)

/-- The second and mixed fourth Brownian limits on the closed unit cubes. -/
def JointBrownianFourthInterface (E : ℝ → ℝ) (a b : ℝ)
    (C : ℝ × ℝ → ℝ) : Prop :=
  (∀ s : Fin 2 → ℝ, (∀ i, s i ∈ Icc (0 : ℝ) 1) →
    Tendsto (fun X : ℝ => jointDyadicMixedMoment E ![a, b] X s) atTop
      (𝓝 (dyadicMacroMoment (dyadicR a + dyadicR b) * C (s 0, s 1)))) ∧
  (∀ s : Fin 4 → ℝ, (∀ i, s i ∈ Icc (0 : ℝ) 1) →
    Tendsto (fun X : ℝ => jointDyadicMixedMoment E ![a, a, b, b] X s) atTop
      (𝓝 (dyadicMacroMoment (kappa a + kappa b) *
        brownianW22 (kappa a) (kappa b) C s)))

/-- The mixed fourth integral factors into marginal energies and squared cross forms. -/
theorem brownianW22_integral
    {g₁ g₂ : ℝ → ℝ} {C : ℝ × ℝ → ℝ}
    {κ₁ κ₂ A : ℝ}
    (hg₁ : ProfileIntegrable g₁)
    (hg₂ : ProfileIntegrable g₂)
    (hC : Measurable C)
    (hA : 0 ≤ A)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1,
      ∀ v ∈ Icc (0 : ℝ) 1, |C (u, v)| ≤ A) :
    (∫ s : Fin 4 → ℝ,
      (g₁ (s 0) * g₁ (s 1) * g₂ (s 2) * g₂ (s 3)) *
        brownianW22 κ₁ κ₂ C s ∂cubeMeasure 4) =
      κ₁ * κ₂ * Q g₁ * Q g₂ + 2 * crossKernelForm g₁ g₂ C ^ 2 := by
  let K (u : Fin 2 → ℝ) := g₁ (u 0) * g₂ (u 1) * C (u 0, u 1)
  have hprod : Integrable (fun z : ℝ × ℝ => g₁ z.1 * g₂ z.2 * C z)
      (unitMeasure.prod unitMeasure) := by
    apply (hg₁.2.mul_prod hg₂.2).mul_bdd (c := |A|) hC.aestronglyMeasurable
    have hmem : ∀ᵐ z : ℝ × ℝ ∂unitMeasure.prod unitMeasure,
        z ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hmem] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg hA] using
      hbound z.1 ⟨hz.1.1.le, hz.1.2⟩ z.2 ⟨hz.2.1.le, hz.2.2⟩
  have hK : Integrable K (cubeMeasure 2) :=
    (measurePreserving_finTwoArrow unitMeasure).integrable_comp_of_integrable hprod
  have hKI : (∫ u, K u ∂cubeMeasure 2) = crossKernelForm g₁ g₂ C :=
    (measurePreserving_finTwoArrow unitMeasure).integral_comp'
      (fun z : ℝ × ℝ => g₁ z.1 * g₂ z.2 * C z)
  have h₁ := pair_product_integrable_and_integral
    (pairKernel_integrable hg₁) (pairKernel_integrable hg₂) (Equiv.refl _)
  rw [integral_pairKernel hg₁, integral_pairKernel hg₂] at h₁
  simp only [Equiv.refl_apply, pairKernel, Matrix.cons_val_zero, Matrix.cons_val_one] at h₁
  have h₂ := pair_product_integrable_and_integral hK hK (Equiv.swap 1 2)
  have h₃ := pair_product_integrable_and_integral hK hK
    ((Equiv.swap 1 3).trans (Equiv.swap 1 2))
  rw [hKI] at h₂ h₃
  norm_num [Equiv.swap_apply_def, K] at h₂ h₃
  have he (s : Fin 4 → ℝ) :
      (g₁ (s 0) * g₁ (s 1) * g₂ (s 2) * g₂ (s 3)) *
          brownianW22 κ₁ κ₂ C s =
      (κ₁ * κ₂) *
        ((g₁ (s 0) * g₁ (s 1) * min (s 0) (s 1)) *
          (g₂ (s 2) * g₂ (s 3) * min (s 2) (s 3))) +
      (g₁ (s 0) * g₂ (s 2) * C (s 0, s 2)) *
        (g₁ (s 1) * g₂ (s 3) * C (s 1, s 3)) +
      (g₁ (s 0) * g₂ (s 3) * C (s 0, s 3)) *
        (g₁ (s 1) * g₂ (s 2) * C (s 1, s 2)) := by
    dsimp [brownianW22]
    ring
  simp_rw [he]
  have hadd := integral_add ((h₁.1.const_mul (κ₁ * κ₂)).add h₂.1) h₃.1
  have hadd12 := integral_add (h₁.1.const_mul (κ₁ * κ₂)) h₂.1
  simp only [Pi.add_apply] at hadd hadd12
  rw [hadd, hadd12, integral_const_mul, h₁.2, h₂.2, h₃.2]
  ring

end
end D5.S3.Arith.Robin.ForwardKernel.JointBrownianKernel
