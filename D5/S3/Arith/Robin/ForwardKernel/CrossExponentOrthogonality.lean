/- GID: D5/S3/Arith/Robin/ForwardKernel/CrossExponentOrthogonality
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CrossExponentOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separate variance bands give a power saving for cross integrals of moving profiles. -/

import D5.S3.Arith.Robin.ForwardKernel.FourScaleCovariance
import D5.S3.Arith.Robin.ForwardKernel.ProfileCrossIntegral

/-! Separate variance bands imply a quantitative cross-profile power saving. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CrossExponentOrthogonality

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs ProfileKernelDefs CrossExponentDefs

noncomputable section

private lemma power_isBigO {a b : ℝ} (hab : a ≤ b) :
    Asymptotics.IsBigO atTop (fun X : ℝ => X ^ a) (fun X : ℝ => X ^ b) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) a),
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) b), one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hX hab

private lemma root_power_ratio_le {X p q d : ℝ} (hX : 1 ≤ X) (hd : d ≤ q - p) :
    Real.sqrt (X ^ p / X ^ q) ≤ X ^ (-(d / 2)) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  rw [← Real.rpow_sub hX0, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
  exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- Separate variance bands yield a uniform power saving for every pair of integrable profiles. -/
theorem profile_cross_exponent_two_bands
    {E : ℝ → ℝ} {α₁ a β₁ α₂ b β₂ μ ν : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hBa : ValidBand α₁ a β₁) (hBb : ValidBand α₂ b β₂)
    (hab : a < b)
    (hVa : CumulativeVarianceBandAsymptoticFor E α₁ β₁)
    (hVb : CumulativeVarianceBandAsymptoticFor E α₂ β₂)
    (haμ : a < μ) (hμν : μ < ν) (hν : ν < min β₁ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ g₁ g₂ : ℝ → ℝ, ProfileIntegrable g₁ → ProfileIntegrable g₂ →
        |∫ x in X..(2 * X), profileResponse E a g₁ x * profileResponse E b g₂ x / x| ≤
          C * profileL1 g₁ * profileL1 g₂ *
            (X ^ (1 - (a + b) / 2) * Real.log X) *
            X ^ (-(min (μ - a) (min (ν - μ) (b - ν)) / 2)) := by
  have ha : 0 < a := hBa.1.trans hBa.2.1
  have hb : 0 < b := hBb.1.trans hBb.2.1
  have ha1 : a < 1 := hBa.2.2.1.trans hBa.2.2.2
  have hb1 : b < 1 := hBb.2.2.1.trans hBb.2.2.2
  have hνβ : ν < β₁ := hν.trans_le (min_le_left _ _)
  have hνb : ν < b := hν.trans_le (min_le_right _ _)
  have hBμ : ValidBand α₁ μ β₁ :=
    ⟨hBa.1, hBa.2.1.trans haμ, hμν.trans hνβ, hBa.2.2.2⟩
  have hBν : ValidBand α₁ ν β₁ :=
    ⟨hBa.1, hBa.2.1.trans (haμ.trans hμν), hνβ, hBa.2.2.2⟩
  obtain ⟨C₀, hC₀, hCov⟩ := FourScaleCovariance.four_scale_covariance_bound hE ha hab hb1
    (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBa hVa)
    (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBμ hVa)
    (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBν hVa)
    (TranslationStripBounds.comparableLengthVarianceUpper_of_band hE hBb hVb)
    (power_isBigO haμ.le) (power_isBigO hμν.le) (power_isBigO hνb.le)
  let d := min (μ - a) (min (ν - μ) (b - ν))
  let B : ℝ → ℝ := fun X =>
    max ((X * Real.log X) * Real.sqrt (X ^ a * X ^ b) * X ^ (-(d / 2))) 0
  have hCov' : ∃ C : ℝ, ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc X (2 * X),
        |∫ x in X..y, movingIncrement E a s x * movingIncrement E b t x| ≤ C * B X := by
    refine ⟨3 * C₀, ?_⟩
    filter_upwards [hCov, eventually_ge_atTop (1 : ℝ)] with X hCov hX
    intro s hs t ht y hy
    have hsum : Real.sqrt (X ^ a / X ^ μ) + Real.sqrt (X ^ μ / X ^ ν) +
        Real.sqrt (X ^ ν / X ^ b) ≤ 3 * X ^ (-(d / 2)) := by
      have h₁ := root_power_ratio_le (p := a) (q := μ) (d := d) hX (min_le_left _ _)
      have h₂ := root_power_ratio_le (p := μ) (q := ν) (d := d) hX
        ((min_le_right _ _).trans (min_le_left _ _))
      have h₃ := root_power_ratio_le (p := ν) (q := b) (d := d) hX
        ((min_le_right _ _).trans (min_le_right _ _))
      dsimp [d] at *
      linarith
    calc
      _ ≤ C₀ * (X * Real.log X) * Real.sqrt (X ^ a * X ^ b) *
          (Real.sqrt (X ^ a / X ^ μ) + Real.sqrt (X ^ μ / X ^ ν) +
            Real.sqrt (X ^ ν / X ^ b)) :=
        hCov s hs t ht X ⟨le_rfl, by linarith⟩ y hy
      _ ≤ C₀ * (X * Real.log X) * Real.sqrt (X ^ a * X ^ b) *
          (3 * X ^ (-(d / 2))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity [Real.log_nonneg hX])
      _ = (3 * C₀) *
          ((X * Real.log X) * Real.sqrt (X ^ a * X ^ b) * X ^ (-(d / 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  obtain ⟨C, hC, hbound⟩ := ProfileCrossIntegral.profile_cross_integral_of_covariance_bound
    hE ha ha1 hb hb1 (fun X => le_max_right _ _) hCov'
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with X hbound hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have heB : B X = (X * Real.log X) * Real.sqrt (X ^ a * X ^ b) * X ^ (-(d / 2)) :=
    max_eq_left (by positivity [Real.log_nonneg hX])
  have heS : Real.sqrt (X ^ a * X ^ b) = X ^ ((a + b) / 2) := by
    rw [← Real.rpow_add hX0, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
    congr 1
    ring
  have heP : X ^ (-a - b) * X * X ^ ((a + b) / 2) = X ^ (1 - (a + b) / 2) := by
    calc
      _ = X ^ ((-a - b) + 1 + (a + b) / 2) := by
        rw [Real.rpow_add hX0, Real.rpow_add hX0, Real.rpow_one]
      _ = _ := by congr 1; ring
  intro g₁ g₂ hg₁ hg₂
  have h := hbound g₁ g₂ hg₁ hg₂
  change _ ≤ C * profileL1 g₁ * profileL1 g₂ * X ^ (-a - b) * B X at h
  rw [heB, heS] at h
  calc
    _ ≤ C * profileL1 g₁ * profileL1 g₂ * X ^ (-a - b) *
        ((X * Real.log X) * X ^ ((a + b) / 2) * X ^ (-(d / 2))) := h
    _ = C * profileL1 g₁ * profileL1 g₂ *
        (X ^ (-a - b) * X * X ^ ((a + b) / 2)) * Real.log X * X ^ (-(d / 2)) := by ring
    _ = _ := by rw [heP]; ring

end
end D5.S3.Arith.Robin.ForwardKernel.CrossExponentOrthogonality
