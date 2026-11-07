/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingLengthVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform band variance controls comparable lengths and all shorter increments. -/

import D5.S3.Arith.Robin.ForwardKernel.FixedLengthCovariance
import D5.S3.Arith.Robin.ForwardKernel.MovingEndpointVariance

/-! Uniform variance estimates at comparable lengths and below a fixed comparison length. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer

noncomputable section

variable {E : ℝ → ℝ} {α θ β : ℝ}

/-- One threshold controls the cumulative variance at every comparable length. -/
theorem comparable_length_variance_bound (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β) (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {A B d : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (A * X ^ θ) (B * X ^ θ),
        cumulativeVariance E (d * X) u ≤ C * X * X ^ θ * Real.log X := by
  have hθ : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hBpos : 0 < B := hA.trans_le hAB
  have hY : Tendsto (fun X : ℝ => d * X) atTop atTop :=
    tendsto_id.const_mul_atTop hd
  have hlo := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ
    (c := A) (d := d) (q := 1) (r := 0) hA hd zero_lt_one le_rfl
  have hhi := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ
    (c := B) (d := d) (q := 1) (r := 0) (hA.trans_le hAB) hd zero_lt_one le_rfl
  refine ⟨2 * d * B * (1 + |Real.log d|), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    hY.eventually (eventually_gt_atTop (1 : ℝ)), hlo, hhi,
    hY.eventually (hV 1 zero_lt_one)] with X hX hY1 hlo hhi hV'
  simp only [fixedLength, one_mul, zero_mul, add_zero] at hlo hhi
  intro u hu
  have hX0 : 0 < X := (Real.exp_pos _).trans_le hX
  have hlogX : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hband : (d * X) ^ α ≤ u ∧ u ≤ (d * X) ^ β :=
    ⟨hlo.1.trans hu.1, hu.2.trans hhi.2⟩
  have hu1 : 1 ≤ u :=
    (Real.one_le_rpow hY1.le hB.1.le).trans hband.1
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have huY : u < d * X := by
    calc
      u ≤ (d * X) ^ β := hband.2
      _ < (d * X) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hY1 hB.2.2.2
      _ = _ := Real.rpow_one _
  have hlogpos : 0 < Real.log (d * X / u) :=
    Real.log_pos ((one_lt_div hu0).mpr huY)
  have hlog : Real.log (d * X / u) ≤ (1 + |Real.log d|) * Real.log X := by
    calc
      _ ≤ Real.log (d * X) := Real.log_le_log (by positivity)
        (div_le_self (by positivity) hu1)
      _ = Real.log d + Real.log X := Real.log_mul hd.ne' hX0.ne'
      _ ≤ _ := by nlinarith [le_abs_self (Real.log d), abs_nonneg (Real.log d)]
  have hv := (abs_sub_le_iff.mp (hV' u hband.1 hband.2)).1
  have hv' : cumulativeVariance E (d * X) u ≤
      2 * ((d * X) * u * Real.log (d * X / u)) := by
    apply (div_le_iff₀ (by positivity : 0 < (d * X) * u * Real.log (d * X / u))).mp
    linarith
  calc
    _ ≤ 2 * ((d * X) * u * Real.log (d * X / u)) := hv'
    _ ≤ 2 * ((d * X) * (B * X ^ θ) * ((1 + |Real.log d|) * Real.log X)) := by
      gcongr
      exact hu.2
    _ = _ := by ring

/-- Every shorter increment has a square integral bounded at the comparison-length scale. -/
theorem shorter_increment_square_bound (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β) (hV : CumulativeVarianceBandAsymptoticFor E α β)
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ∀ u ∈ Icc (0 : ℝ) (fixedLength θ c X),
        (∫ x in X..(2 * X), increment E u x ^ 2) ≤
          C * X * fixedLength θ c X * lengthLog θ c X := by
  have hθ : θ < 1 := hB.2.2.1.trans hB.2.2.2
  obtain ⟨K, hK, hKv⟩ := comparable_length_variance_bound hE hB hV
    (A := c) (B := 3 * c) (d := 3) hc (by linarith) (by norm_num)
  have hband := FixedLengthCovariance.shifted_band hB.2.1 hB.2.2.1 hθ
    (c := c) (d := 1) (q := 1) (r := 0) hc zero_lt_one zero_lt_one le_rfl
  refine ⟨12 * K / (c * (1 - θ)), by positivity, ?_⟩
  filter_upwards [hKv, hband, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * Real.log c / (1 - θ)))]
    with X hKv hband hX hlog
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hh : 0 < fixedLength θ c X := by unfold fixedLength; positivity
  have hhX : fixedLength θ c X ≤ X := by
    simp only [one_mul, zero_mul, add_zero] at hband
    exact hband.2.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hX hB.2.2.2.le)
  have hell : (1 - θ) / 2 * Real.log X ≤ lengthLog θ c X := by
    rw [lengthLog, Real.log_div hX0.ne' hh.ne', fixedLength,
      Real.log_mul hc.ne' (Real.rpow_pos_of_pos hX0 _).ne', Real.log_rpow hX0]
    have := (div_le_iff₀ (sub_pos.mpr hθ)).mp hlog
    linarith
  intro u hu
  have hb := MovingEndpointVariance.two_endpoint_increment_square_le
    (p := fun x => x) (q := fun x => x + u)
    (p' := fun _ => 1) (q' := fun _ => 1)
    (l := X) (r := 2 * X) (Y := 3 * X) (R := fixedLength θ c X) (C₀ := 1) (m := 1)
    (K := K * X * X ^ θ * Real.log X)
    hE (by linarith) hh (by norm_num) zero_lt_one
    (by positivity [Real.log_nonneg hX])
    continuous_id.continuousOn (continuous_id.add continuous_const).continuousOn
    (fun x _ => (hasDerivAt_id x).hasDerivWithinAt)
    (fun x _ => ((hasDerivAt_id x).add_const u).hasDerivWithinAt)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (by
      intro x hx
      exact ⟨⟨hX.trans hx.1, by linarith [hx.2]⟩,
        ⟨by linarith [hx.1, hu.1], by linarith [hx.2, hu.2]⟩⟩)
    (by intro x _; simpa only [add_sub_cancel_left, one_mul] using hu)
    (by
      intro v hv
      apply hKv v
      dsimp [fixedLength] at *
      constructor <;> nlinarith [hv.1, hv.2])
  have hb' : (∫ x in X..(2 * X), increment E u x ^ 2) ≤
      6 * K * X * X ^ θ * Real.log X := by
    simpa only [increment, show (2 * (1 + 2) / 1 : ℝ) = 6 by norm_num,
      mul_assoc] using hb
  calc
    _ ≤ 6 * K * X * X ^ θ * Real.log X := hb'
    _ ≤ _ := by
      have hscale := mul_le_mul_of_nonneg_left hell
        (show 0 ≤ 12 * K * X * X ^ θ / (1 - θ) by positivity)
      dsimp [fixedLength]
      field_simp at hscale ⊢
      nlinarith

end
end D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance
