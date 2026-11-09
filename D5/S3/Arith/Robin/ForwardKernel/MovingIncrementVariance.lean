/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Averaging comparable increments bounds moving increments uniformly in the profile parameter. -/

import D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Uniform square bounds for the increments with length `s x^θ`. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingIncrementVariance

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer MovingLengthVariance

noncomputable section

/-- The moving-increment square bound has a threshold independent of its parameter in `[0,1]`. -/
theorem moving_increment_square_bound {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ s ∈ Icc (0 : ℝ) 1,
        (∫ x in X..(2 * X), increment E (s * x ^ θ) x ^ 2) ≤
          C * X * X ^ θ * Real.log X := by
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hθ1 : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hpow : Continuous (fun x : ℝ => x ^ θ) := Real.continuous_rpow_const hθ0.le
  obtain ⟨K, hK, hKv⟩ := comparable_length_variance_bound hE hB hV
    (A := 1) (B := 4) (d := 3) (by norm_num) (by norm_num) (by norm_num)
  have hband := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ1
    (c := 1) (d := 1) (q := 2) (r := 0) zero_lt_one zero_lt_one (by norm_num) le_rfl
  refine ⟨8 * K, by positivity, ?_⟩
  filter_upwards [hKv, hband, eventually_ge_atTop (1 : ℝ)] with X hKv hband hX
  simp only [one_mul] at hKv
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hXX : X ≤ 2 * X := by linarith
  let h := X ^ θ
  have hh : 0 < h := Real.rpow_pos_of_pos hX0 θ
  have h2h : 2 * h ≤ X := by
    simp only [fixedLength, one_mul, zero_mul, add_zero] at hband
    exact hband.2.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX hB.2.2.2.le)
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  let φ : ℝ → ℝ := fun x => x + s * x ^ θ
  have hφ : Continuous φ := continuous_id.add (continuous_const.mul hpow)
  have hL : ∀ x ∈ Icc X (2 * X), s * x ^ θ ∈ Icc (0 : ℝ) (2 * h) := by
    intro x hx
    have hx0 : 0 < x := hX0.trans_le hx.1
    refine ⟨by positivity, ?_⟩
    calc
      s * x ^ θ ≤ x ^ θ := mul_le_of_le_one_left (Real.rpow_pos_of_pos hx0 θ).le hs.2
      _ ≤ (2 * X) ^ θ := Real.rpow_le_rpow hx0.le hx.2 hθ0.le
      _ = (2 : ℝ) ^ θ * h := Real.mul_rpow (by norm_num) hX0.le
      _ ≤ 2 * h := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ1.le
  have hφbound : ∀ x ∈ Icc X (2 * X), x + s * x ^ θ ≤ 3 * X := by
    intro x hx
    linarith [(hL x hx).2, hx.2]
  have hφder : ∀ x ∈ Icc X (2 * X),
      HasDerivWithinAt φ (1 + s * (θ * x ^ (θ - 1))) (Icc X (2 * X)) x := by
    intro x hx
    exact ((hasDerivAt_id x).add
      ((Real.hasDerivAt_rpow_const
        (Or.inl (by linarith [hx.1] : x ≠ 0))).const_mul s)).hasDerivWithinAt
  have hb := MovingEndpointVariance.two_endpoint_increment_square_le
    (p := fun x => x) (q := φ)
    (p' := fun _ => 1) (q' := fun x => 1 + s * (θ * x ^ (θ - 1)))
    (l := X) (r := 2 * X) (Y := 3 * X) (R := h) (C₀ := 2) (m := 1)
    (K := K * X * h * Real.log X)
    hE hXX hh (by norm_num) zero_lt_one
    (by positivity [Real.log_nonneg hX])
    continuous_id.continuousOn hφ.continuousOn
    (fun x _ => (hasDerivAt_id x).hasDerivWithinAt) hφder
    (fun _ _ => le_rfl)
    (by
      intro x hx
      have hx0 : 0 < x := hX0.trans_le hx.1
      have : 0 ≤ s * (θ * x ^ (θ - 1)) := by positivity
      linarith)
    (by
      intro x hx
      exact ⟨⟨hX.trans hx.1, by linarith [hx.2]⟩,
        ⟨by dsimp [φ]; linarith [(hL x hx).1, hx.1], hφbound x hx⟩⟩)
    (by intro x hx; simpa only [φ, add_sub_cancel_left] using hL x hx)
    (fun w hw => hKv w (by norm_num [h] at hw ⊢; exact hw))
  simpa only [increment, φ, h, show (2 * (2 + 2) / 1 : ℝ) = 8 by norm_num,
    mul_assoc] using hb

end
end D5.S3.Arith.Robin.ForwardKernel.MovingIncrementVariance
