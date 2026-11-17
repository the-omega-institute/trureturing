/- GID: D5/S3/Arith/Robin/ForwardKernel/CuspMovingLengths
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CuspMovingLengths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Moving averaging lengths and slowly varying weights preserve cusp cross energy. -/

import D5.S3.Arith.Robin.ForwardKernel.CuspCrossEnergy

/-! Abstract transport of cusp cross energy under changes of length and weight. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

private lemma product_comparison {h k q₁ q₂ δ y : ℝ}
    (hh : 0 < h) (hhk : h < k) (hδ : 0 ≤ δ)
    (hq₁ : h ≤ q₁ ∧ q₁ ≤ h * (1 + δ))
    (hq₂ : k ≤ q₂ ∧ q₂ ≤ k * (1 + δ)) (hy : h ≤ y) :
    let P := cuspAverage h k h y * cuspAverage h k k y
    let M := cuspAverage h k q₁ y * cuspAverage h k q₂ y
    P ≤ M ∧ M ≤ (1 + δ) ^ 2 * P := by
  dsimp
  have hk := hh.trans hhk
  have hA := cuspAverage_bounds hh hhk hh.le (hh.le.trans hy)
  have hB := cuspAverage_bounds hh hhk hk.le (hh.le.trans hy)
  have h₁ := cuspAverage_length_comparison hh hhk hh hq₁.1 hy
  have h₂ := cuspAverage_length_comparison hh hhk hk hq₂.1 hy
  have hu₁ : cuspAverage h k q₁ y ≤ (1 + δ) * cuspAverage h k h y :=
    h₁.2.trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ hh).2 (by nlinarith [hq₁.2])) hA.1)
  have hu₂ : cuspAverage h k q₂ y ≤ (1 + δ) * cuspAverage h k k y :=
    h₂.2.trans (mul_le_mul_of_nonneg_right ((div_le_iff₀ hk).2 (by nlinarith [hq₂.2])) hB.1)
  constructor
  · exact mul_le_mul h₁.1 h₂.1 hB.1 (hA.1.trans h₁.1)
  · calc
      _ ≤ ((1 + δ) * cuspAverage h k h y) * ((1 + δ) * cuspAverage h k k y) :=
        mul_le_mul hu₁ hu₂ (hB.1.trans h₂.1) (mul_nonneg (by linarith) hA.1)
      _ = _ := by ring

private lemma lower_product_bounds {h k q₁ q₂ y : ℝ}
    (hh : 0 < h) (hhk : h < k) (hq₁ : 0 ≤ q₁) (hq₁' : q₁ ≤ 2 * h)
    (hq₂ : 0 ≤ q₂) (hy : y ∈ Icc (0 : ℝ) h) :
    0 ≤ cuspAverage h k q₁ y * cuspAverage h k q₂ y ∧
      cuspAverage h k q₁ y * cuspAverage h k q₂ y ≤ 2 * Real.log (k / h) := by
  have hA := cuspAverage_bounds hh hhk hq₁ hy.1
  have hB := cuspAverage_bounds hh hhk hq₂ hy.1
  have hs := cuspAverage_short_bound hh hhk hq₁ hq₁' hy
  have hl : Real.log (3 : ℝ) ≤ 2 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3) using 1; norm_num
  exact ⟨mul_nonneg hA.1 hB.1,
    mul_le_mul (hs.trans hl) hB.2 hB.1 (by norm_num)⟩

/-- Moving lengths in their relative intervals and a nonnegative weight between
`(1-ε)W` and `W` change the frozen energy by a relative error and a lower-interval error.
Consumed by `movingCuspEnergy_estimate` and `CommonBandSharpnessTransport`. -/
theorem cuspCrossEnergy_weighted_moving_lengths {h k δ ε W : ℝ}
    {q₁ q₂ w : ℝ → ℝ} (hh : 0 < h) (hhk : h < k)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hε : 0 ≤ ε) (hW : 0 ≤ W)
    (hq₁ : ∀ y ∈ Icc (0 : ℝ) k, h ≤ q₁ y ∧ q₁ y ≤ h * (1 + δ))
    (hq₂ : ∀ y ∈ Icc (0 : ℝ) k, k ≤ q₂ y ∧ q₂ y ≤ k * (1 + δ))
    (hw : ∀ y ∈ Icc (0 : ℝ) k,
      0 ≤ w y ∧ (1 - ε) * W ≤ w y ∧ w y ≤ W)
    (hi : IntervalIntegrable
      (fun y => w y * (cuspAverage h k (q₁ y) y * cuspAverage h k (q₂ y) y))
      volume 0 k) :
    |(∫ y in (0 : ℝ)..k,
        w y * (cuspAverage h k (q₁ y) y * cuspAverage h k (q₂ y) y)) -
        W * cuspCrossEnergy h k| ≤
      (3 * δ + ε) * W * cuspCrossEnergy h k + 2 * W * h * Real.log (k / h) := by
  let P := fun y => cuspAverage h k h y * cuspAverage h k k y
  let M := fun y => w y * (cuspAverage h k (q₁ y) y * cuspAverage h k (q₂ y) y)
  have hk := hh.trans hhk
  have hL : 0 ≤ Real.log (k / h) := Real.log_nonneg ((one_le_div hh).2 hhk.le)
  have hPi : ∀ a b, IntervalIntegrable P volume a b := fun a b =>
    ((cuspAverage_continuous hh hhk h).mul (cuspAverage_continuous hh hhk k)).intervalIntegrable a b
  have hP₀ (y : ℝ) (hy : 0 ≤ y) : 0 ≤ P y :=
    mul_nonneg (cuspAverage_bounds hh hhk hh.le hy).1
      (cuspAverage_bounds hh hhk hk.le hy).1
  have hd : IntervalIntegrable (fun y => M y - W * P y) volume 0 k :=
    hi.sub ((hPi 0 k).const_mul W)
  have hlow : |∫ y in (0 : ℝ)..h, M y - W * P y| ≤
      2 * W * h * Real.log (k / h) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := h) (C := 2 * W * Real.log (k / h))
      (f := fun y => M y - W * P y) ?_
    · simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hh,
        mul_assoc, mul_left_comm, mul_comm] using hb
    intro y hy
    rw [uIoc_of_le hh.le] at hy
    have hy' : y ∈ Icc (0 : ℝ) h := ⟨hy.1.le, hy.2⟩
    have hyk : y ∈ Icc (0 : ℝ) k := ⟨hy'.1, hy'.2.trans hhk.le⟩
    obtain ⟨hw0, _, hw1⟩ := hw y hyk
    have hq1 := hq₁ y hyk
    have hq2 := hq₂ y hyk
    have hMp := lower_product_bounds hh hhk (hh.le.trans hq1.1)
      (hq1.2.trans (by nlinarith)) (hk.le.trans hq2.1) hy'
    have hPp := lower_product_bounds hh hhk hh.le (by linarith) hk.le hy'
    have hm0 : 0 ≤ M y := mul_nonneg hw0 hMp.1
    have hm1 : M y ≤ 2 * W * Real.log (k / h) := by
      dsimp [M]
      nlinarith [mul_le_mul hw1 hMp.2 hMp.1 hW]
    have hp0 : 0 ≤ W * P y := mul_nonneg hW (hP₀ y hy'.1)
    have hp1 : W * P y ≤ 2 * W * Real.log (k / h) := by
      have := mul_le_mul_of_nonneg_left hPp.2 hW
      dsimp [P] at *; nlinarith
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have htail : |∫ y in h..k, M y - W * P y| ≤
      (3 * δ + ε) * W * (∫ y in h..k, P y) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le hhk.le
      (f := fun y => M y - W * P y) (g := fun y => (3 * δ + ε) * W * P y) ?_
      ((hPi h k).const_mul ((3 * δ + ε) * W))
    · simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using hb
    apply Filter.Eventually.of_forall
    intro y hy
    have hyk : y ∈ Icc (0 : ℝ) k := ⟨hh.le.trans hy.1.le, hy.2⟩
    obtain ⟨hw0, hwlo, hwhi⟩ := hw y hyk
    obtain ⟨hlo, hhi⟩ := product_comparison hh hhk hδ (hq₁ y hyk) (hq₂ y hyk) hy.1.le
    change P y ≤ _ at hlo
    change _ ≤ (1 + δ) ^ 2 * P y at hhi
    have hp := hP₀ y hyk.1
    have hmp := mul_le_mul_of_nonneg_left hlo hw0
    have hup := mul_le_mul hwhi hhi (hp.trans hlo) hW
    have hdn := mul_le_mul_of_nonneg_right hwlo hp
    have hsq : (1 + δ) ^ 2 ≤ 1 + 3 * δ := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ₁)]
    have hsq' := mul_le_mul_of_nonneg_right hsq (mul_nonneg hW hp)
    have heps := mul_nonneg hε (mul_nonneg hW hp)
    have hdel := mul_nonneg (by positivity : 0 ≤ 3 * δ) (mul_nonneg hW hp)
    rw [Real.norm_eq_abs, abs_le]
    dsimp [M]
    constructor <;> nlinarith
  have htailE : (∫ y in h..k, P y) ≤ cuspCrossEnergy h k := by
    have hs := intervalIntegral.integral_add_adjacent_intervals (hPi 0 h) (hPi h k)
    have h0 : 0 ≤ ∫ y in (0 : ℝ)..h, P y :=
      intervalIntegral.integral_nonneg hh.le (fun y hy => hP₀ y hy.1)
    change _ = cuspCrossEnergy h k at hs
    linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hd.mono_set (by rw [uIcc_of_le hh.le, uIcc_of_le hk.le]; exact Icc_subset_Icc le_rfl hhk.le))
    (hd.mono_set (by rw [uIcc_of_le hhk.le, uIcc_of_le hk.le]; exact Icc_subset_Icc hh.le le_rfl))
  have heq : (∫ y in (0 : ℝ)..k, M y - W * P y) =
      (∫ y in (0 : ℝ)..k, M y) - W * cuspCrossEnergy h k := by
    rw [intervalIntegral.integral_sub hi ((hPi 0 k).const_mul W),
      intervalIntegral.integral_const_mul]
    rfl
  rw [← heq, ← hsplit]
  have := abs_add_le (∫ y in (0 : ℝ)..h, M y - W * P y)
    (∫ y in h..k, M y - W * P y)
  have ht := mul_le_mul_of_nonneg_left htailE (by positivity : 0 ≤ (3 * δ + ε) * W)
  linarith

/-- The cusp cross integral with the original power lengths and power weight.
Consumed by `CommonBandSharpnessTransport` and `movingCuspEnergy_estimate`. -/
def movingCuspEnergy (a b X : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..(X ^ b),
    (X + y) ^ (-a - b) *
      cuspAverage (X ^ a) (X ^ b) ((X + y) ^ a) y *
      cuspAverage (X ^ a) (X ^ b) ((X + y) ^ b) y

lemma power_length_bounds {X k θ y : ℝ} (hX : 0 < X)
    (hθ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hy : y ∈ Icc (0 : ℝ) k) :
    X ^ θ ≤ (X + y) ^ θ ∧ (X + y) ^ θ ≤ X ^ θ * (1 + k / X) := by
  have ht : 0 ≤ y / X := div_nonneg hy.1 hX.le
  have hfac : X + y = X * (1 + y / X) := by field_simp
  constructor
  · exact Real.rpow_le_rpow hX.le (by linarith [hy.1]) hθ
  · rw [hfac, Real.mul_rpow hX.le (by positivity)]
    exact mul_le_mul_of_nonneg_left
      ((Real.rpow_le_self_of_one_le (by linarith) hθ₁).trans
        (by linarith [div_le_div_of_nonneg_right hy.2 hX.le]))
      (Real.rpow_nonneg hX.le θ)

private lemma power_weight_bounds {a b X k y : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hX : 0 < X)
    (hy : y ∈ Icc (0 : ℝ) k) :
    0 ≤ (X + y) ^ (-a - b) ∧
      (1 - 2 * (k / X)) * X ^ (-a - b) ≤ (X + y) ^ (-a - b) ∧
      (X + y) ^ (-a - b) ≤ X ^ (-a - b) := by
  have ht : 0 ≤ y / X := div_nonneg hy.1 hX.le
  have hu : 0 < 1 + y / X := by positivity
  have hp : -a - b ≤ 0 := by linarith
  have hp₂ : -2 ≤ -a - b := by linarith
  refine ⟨Real.rpow_nonneg (by linarith [hy.1]) _, ?_,
    Real.rpow_le_rpow_of_nonpos hX (by linarith [hy.1]) hp⟩
  have hlog₀ : 0 ≤ Real.log (1 + y / X) := Real.log_nonneg (by linarith)
  have hlog₁ : Real.log (1 + y / X) ≤ y / X := by
    have := Real.log_le_sub_one_of_pos hu
    linarith
  have he := Real.add_one_le_exp (Real.log (1 + y / X) * (-a - b))
  rw [← Real.rpow_def_of_pos hu] at he
  have hpow : 1 - 2 * (k / X) ≤ (1 + y / X) ^ (-a - b) := by
    have hm := mul_le_mul_of_nonneg_right hp₂ hlog₀
    have ht' := div_le_div_of_nonneg_right hy.2 hX.le
    nlinarith
  have hfac : X + y = X * (1 + y / X) := by field_simp
  rw [hfac, Real.mul_rpow hX.le hu.le]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hX.le (-a - b))

lemma power_average_continuous {h k X θ : ℝ}
    (hh : 0 < h) (hhk : h < k) (hθ : 0 ≤ θ) :
    Continuous (fun y => cuspAverage h k ((X + y) ^ θ) y) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((clippedLog_continuous hh hhk).comp
    (continuous_fst.add (continuous_snd.mul
      ((Real.continuous_rpow_const hθ).comp (continuous_const.add continuous_fst))))).sub
    ((clippedLog_continuous hh hhk).comp continuous_fst)

/-- The original power lengths and weight preserve the cusp main term, with
errors of order `hL` and `(k/X)hL²`. Consumed by `CommonBandSharpnessTransport`. -/
theorem movingCuspEnergy_estimate {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      let h := X ^ a
      let k := X ^ b
      let L := Real.log (k / h)
      |movingCuspEnergy a b X - X ^ (-a - b) * (h * L ^ 2 / 4)| ≤
        C * X ^ (-a - b) * (h * L + (k / X) * (h * L ^ 2)) := by
  obtain ⟨C₀, hC₀, henergy⟩ := cuspCrossEnergy_estimate
  refine ⟨6 * C₀ + 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (eventually_ge_atTop (2 : ℝ))]
    with X hX₁ hratio
  have hX : 0 < X := by linarith
  let h := X ^ a
  let k := X ^ b
  let L := Real.log (k / h)
  let W := X ^ (-a - b)
  let δ := k / X
  have hh : 0 < h := Real.rpow_pos_of_pos hX a
  have hk : 0 < k := Real.rpow_pos_of_pos hX b
  have h₂ : 2 * h ≤ k := by
    have hr : k / h = X ^ (b - a) := (Real.rpow_sub hX _ _).symm
    rw [← hr] at hratio
    exact (le_div_iff₀ hh).1 hratio
  have hhk : h < k := by linarith
  have hδ : 0 ≤ δ := div_nonneg hk.le hX.le
  have hδ₁ : δ ≤ 1 := (div_le_one hX).2 (Real.rpow_le_self_of_one_le hX₁ hb.le)
  have hW : 0 ≤ W := Real.rpow_nonneg hX.le _
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div hh).2 hhk.le)
  have hq₁ (y : ℝ) (hy : y ∈ Icc (0 : ℝ) k) :=
    power_length_bounds hX ha.le (hab.trans hb).le hy
  have hq₂ (y : ℝ) (hy : y ∈ Icc (0 : ℝ) k) :=
    power_length_bounds hX (ha.trans hab).le hb.le hy
  have hw (y : ℝ) (hy : y ∈ Icc (0 : ℝ) k) :=
    power_weight_bounds ha hab hb hX hy
  have hi : IntervalIntegrable (fun y => (X + y) ^ (-a - b) *
      (cuspAverage h k ((X + y) ^ a) y * cuspAverage h k ((X + y) ^ b) y))
      volume 0 k := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hk.le]
    apply ContinuousOn.mul _
      (((power_average_continuous hh hhk ha.le).mul
        (power_average_continuous hh hhk (ha.trans hab).le)).continuousOn)
    exact (continuousOn_const.add continuousOn_id).rpow_const
      (fun y hy => Or.inl (by linarith [hy.1] : X + y ≠ 0))
  have ht := cuspCrossEnergy_weighted_moving_lengths hh hhk hδ hδ₁
    (by positivity : 0 ≤ 2 * δ) hW hq₁ hq₂ hw hi
  have hm : (∫ y in (0 : ℝ)..k, (X + y) ^ (-a - b) *
      (cuspAverage h k ((X + y) ^ a) y * cuspAverage h k ((X + y) ^ b) y)) =
      movingCuspEnergy a b X := by
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [movingCuspEnergy] at *
    ring
  rw [hm] at ht
  have he := henergy h k hh h₂
  change |cuspCrossEnergy h k - h * L ^ 2 / 4| ≤ C₀ * h * L at he
  have he' := (abs_le.mp he).2
  have hscaled : |W * cuspCrossEnergy h k - W * (h * L ^ 2 / 4)| ≤
      W * (C₀ * h * L) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hW]
    exact mul_le_mul_of_nonneg_left he hW
  have hrel : 5 * δ * W * cuspCrossEnergy h k ≤
      5 / 4 * W * (δ * (h * L ^ 2)) + 5 * C₀ * W * (h * L) := by
    calc
      _ ≤ 5 * δ * W * (h * L ^ 2 / 4 + C₀ * h * L) :=
        mul_le_mul_of_nonneg_left (by linarith [he']) (by positivity)
      _ ≤ 5 / 4 * W * (δ * (h * L ^ 2)) + 5 * C₀ * W * (h * L) := by
        have hd := mul_le_mul_of_nonneg_left hδ₁
          (show 0 ≤ 5 * W * C₀ * h * L by positivity)
        nlinarith only [hd]
  have habs := (abs_sub_le (movingCuspEnergy a b X) (W * cuspCrossEnergy h k)
    (W * (h * L ^ 2 / 4))).trans (add_le_add ht hscaled)
  change |movingCuspEnergy a b X - W * (h * L ^ 2 / 4)| ≤
    (6 * C₀ + 4) * W * (h * L + δ * (h * L ^ 2))
  have hU : 0 ≤ W * (h * L) := by positivity
  have hV : 0 ≤ W * (δ * (h * L ^ 2)) := by positivity
  nlinarith only [habs, hrel, hU, hV,
    mul_nonneg hC₀.le hV]

end
end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
