/- GID: D5/S3/Arith/Robin/ForwardKernel/CrossExponentOrthogonalityCommonBand
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CrossExponentOrthogonalityCommonBand
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common variance band yields the sharper cross-exponent profile orthogonality rate. -/

import D5.S3.Arith.Robin.ForwardKernel.CommonBandCovariance
import D5.S3.Arith.Robin.ForwardKernel.ProfileCrossIntegral

namespace D5.S3.Arith.Robin.ForwardKernel.CrossExponentOrthogonalityCommonBand

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs ProfileKernelDefs CrossExponentDefs

noncomputable section

/-- A common variance band gives the short-exponent scale bound for arbitrary integrable profiles. -/
theorem profile_cross_exponent_common_band
    {E : ℝ → ℝ} {α a b β : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α a β)
    (hab : a < b) (hbβ : b < β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ g₁ g₂ : ℝ → ℝ,
        ProfileIntegrable g₁ → ProfileIntegrable g₂ →
        |∫ x in X..(2 * X),
            profileResponse E a g₁ x * profileResponse E b g₂ x / x| ≤
          C * profileL1 g₁ * profileL1 g₂ *
            X ^ (1 - b) * Real.log X * (1 + (b - a) * Real.log X) ^ 2 := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have hb : 0 < b := ha.trans hab
  have ha1 : a < 1 := hBa.2.2.1.trans hBa.2.2.2
  have hb1 : b < 1 := hbβ.trans hBa.2.2.2
  obtain ⟨C₀, _, hCov⟩ := CommonBandCovariance.common_band_covariance_bound hE hBa hab hbβ hV
  let B := fun X : ℝ => max (X * X ^ a * Real.log X * (1 + (b - a) * Real.log X) ^ 2) 0
  have hCov' : ∃ C : ℝ, ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc X (2 * X),
        |∫ x in X..y, movingIncrement E a s x * movingIncrement E b t x| ≤ C * B X := by
    refine ⟨|C₀| + 1, ?_⟩
    filter_upwards [hCov, eventually_ge_atTop (1 : ℝ)] with X hCov hX
    intro s hs t ht y hy
    have hP : 0 ≤ X * X ^ a * Real.log X * (1 + (b - a) * Real.log X) ^ 2 := by
      positivity [Real.log_nonneg hX]
    exact (hCov s hs t ht X ⟨le_rfl, by linarith⟩ y hy).trans
      (by
        dsimp [B]
        rw [max_eq_left hP]
        have h := mul_le_mul_of_nonneg_right (show C₀ ≤ |C₀| + 1 by linarith [le_abs_self C₀]) hP
        nlinarith only [h])
  obtain ⟨C, hC, hbound⟩ := ProfileCrossIntegral.profile_cross_integral_of_covariance_bound
    hE ha ha1 hb hb1 (fun X => le_max_right _ _) hCov'
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with X hbound hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have heB : B X = X * X ^ a * Real.log X * (1 + (b - a) * Real.log X) ^ 2 :=
    max_eq_left (by positivity [Real.log_nonneg hX])
  have heP : X ^ (-a - b) * X * X ^ a = X ^ (1 - b) := by
    calc
      _ = X ^ ((-a - b) + 1 + a) := by
        rw [Real.rpow_add hX0, Real.rpow_add hX0, Real.rpow_one]
      _ = _ := by congr 1; ring
  intro g₁ g₂ hg₁ hg₂
  have h := hbound g₁ g₂ hg₁ hg₂
  change _ ≤ C * profileL1 g₁ * profileL1 g₂ * X ^ (-a - b) * B X at h
  rw [heB] at h
  calc
    _ ≤ C * profileL1 g₁ * profileL1 g₂ * X ^ (-a - b) *
        (X * X ^ a * Real.log X * (1 + (b - a) * Real.log X) ^ 2) := h
    _ = C * profileL1 g₁ * profileL1 g₂ * (X ^ (-a - b) * X * X ^ a) *
        Real.log X * (1 + (b - a) * Real.log X) ^ 2 := by ring
    _ = _ := by rw [heP]

end
end D5.S3.Arith.Robin.ForwardKernel.CrossExponentOrthogonalityCommonBand
