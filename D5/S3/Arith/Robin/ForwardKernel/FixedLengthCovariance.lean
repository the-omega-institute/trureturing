/- GID: D5/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FixedLengthCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform cumulative variance asymptotics imply fixed-length increment covariance asymptotics. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Variance at shifted endpoints and polarization of fixed-length increments. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FixedLengthCovariance

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs
open VarianceTransfer (increment_product_comp_integrableOn)

noncomputable section

lemma length_div_tendsto_zero {θ : ℝ} (hθ : θ < 1) (c : ℝ) :
    Tendsto (fun X => fixedLength θ c X / X) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hθ)).const_mul c
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  dsimp [fixedLength]
  rw [mul_div_assoc, show X ^ θ / X = X ^ (-(1 - θ)) by
    calc
      _ = X ^ θ / X ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hX]; congr 1 <;> ring]

private lemma endpoint_div_tendsto {θ : ℝ} (hθ : θ < 1) (c d r : ℝ) :
    Tendsto (fun X => (d * X + r * fixedLength θ c X) / X) atTop (𝓝 d) := by
  have h := (tendsto_const_nhds (x := d)).add ((length_div_tendsto_zero hθ c).const_mul r)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  field_simp

theorem length_log_tendsto {θ c : ℝ} (hθ : θ < 1) (hc : 0 < c) :
    Tendsto (lengthLog θ c) atTop atTop := by
  have h : Tendsto (fun X : ℝ => (1 - θ) * Real.log X - Real.log c) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-Real.log c)
      (Real.tendsto_log_atTop.const_mul_atTop (sub_pos.mpr hθ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [lengthLog, Real.log_div hX.ne' (by dsimp [fixedLength]; positivity : fixedLength θ c X ≠ 0),
    fixedLength, Real.log_mul hc.ne' (Real.rpow_pos_of_pos hX _).ne', Real.log_rpow hX]
  ring

private lemma endpoint_power_ratio {θ c d r : ℝ} (hθ : θ < 1) (hc : 0 < c) (hd : 0 < d)
    (hr : 0 ≤ r) (p : ℝ) :
    Tendsto (fun X => (d * X + r * fixedLength θ c X) ^ p / X ^ p)
      atTop (𝓝 (d ^ p)) := by
  have h := (endpoint_div_tendsto hθ c d r).rpow_const (p := p) (Or.inl hd.ne')
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [Real.div_rpow (by dsimp [fixedLength]; positivity : 0 ≤ d * X + r * fixedLength θ c X) hX.le]

theorem shifted_band {α θ β c d q r : ℝ}
    (hαθ : α < θ) (hθβ : θ < β) (hθ : θ < 1) (hc : 0 < c) (hd : 0 < d)
    (hq : 0 < q) (hr : 0 ≤ r) :
    ∀ᶠ X : ℝ in atTop,
      (d * X + r * fixedLength θ c X) ^ α ≤ q * fixedLength θ c X ∧
      q * fixedLength θ c X ≤ (d * X + r * fixedLength θ c X) ^ β := by
  have hlo : Tendsto (fun X =>
      (d * X + r * fixedLength θ c X) ^ α / (q * fixedLength θ c X))
      atTop (𝓝 0) := by
    have h := ((endpoint_power_ratio hθ hc hd hr α).mul
      (tendsto_rpow_neg_atTop (sub_pos.mpr hαθ))).div_const (q * c)
    simp only [mul_zero, zero_div] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [show -(θ - α) = α - θ by ring,
      Real.rpow_sub hX]
    dsimp [fixedLength]
    field_simp
  have hhi : Tendsto (fun X =>
      q * fixedLength θ c X / (d * X + r * fixedLength θ c X) ^ β)
      atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (sub_pos.mpr hθβ)).const_mul
      (q * c)).div (endpoint_power_ratio hθ hc hd hr β)
        (Real.rpow_pos_of_pos hd _).ne'
    simp only [mul_zero, zero_div] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    dsimp only [Pi.div_apply]
    rw [show -(β - θ) = θ - β by ring,
      Real.rpow_sub hX]
    dsimp [fixedLength]
    field_simp
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlo.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hhi.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with X hX hlo hhi
  have hY : 0 < d * X + r * fixedLength θ c X := by dsimp [fixedLength]; positivity
  exact ⟨((div_lt_one (by dsimp [fixedLength]; positivity)).mp hlo).le,
    ((div_lt_one (Real.rpow_pos_of_pos hY _)).mp hhi).le⟩

private lemma shifted_log_ratio {θ c d q r : ℝ} (hθ : θ < 1) (hc : 0 < c) (hd : 0 < d)
    (hq : 0 < q) (hr : 0 ≤ r) :
    Tendsto (fun X => Real.log ((d * X + r * fixedLength θ c X) /
        (q * fixedLength θ c X)) / lengthLog θ c X) atTop (𝓝 1) := by
  have hz := (((endpoint_div_tendsto hθ c d r).div_const q).log (div_pos hd hq).ne').div_atTop
    (length_log_tendsto hθ hc)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add hz
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (length_log_tendsto hθ hc).eventually (eventually_gt_atTop (0 : ℝ))] with X hX hL
  have hH : 0 < fixedLength θ c X := by dsimp [fixedLength]; positivity
  have hY : 0 < d * X + r * fixedLength θ c X := by positivity
  have he : (d * X + r * fixedLength θ c X) / (q * fixedLength θ c X) =
      X / fixedLength θ c X * (((d * X + r * fixedLength θ c X) / X) / q) := by
    field_simp
  rw [he, Real.log_mul (div_pos hX hH).ne' (div_pos (div_pos hY hX) hq).ne']
  dsimp [lengthLog] at *
  field_simp

/-- Cumulative variance at a linearly shifted endpoint has its natural fixed-length limit. -/
theorem shifted_variance_tendsto
    {E : ℝ → ℝ} {α θ β : ℝ} (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (hGM : CumulativeVarianceBandAsymptoticFor E α β)
    {c d q r : ℝ} (hc : 0 < c) (hd : 0 < d) (hq : 0 < q) (hr : 0 ≤ r) :
    Filter.Tendsto
      (fun X => cumulativeVariance E (d * X + r * fixedLength θ c X) (q * fixedLength θ c X) /
        (X * fixedLength θ c X * lengthLog θ c X))
      Filter.atTop (nhds (d * q)) := by
  have hθ : θ < 1 := hB.2.2.1.trans hB.2.2.2
  have hY : Tendsto (fun X => d * X + r * fixedLength θ c X) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (tendsto_id.const_mul_atTop hd)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have : 0 ≤ r * fixedLength θ c X := by dsimp [fixedLength]; positivity
    change d * X ≤ _
    linarith
  have hV : Tendsto (fun X =>
      cumulativeVariance E (d * X + r * fixedLength θ c X) (q * fixedLength θ c X) /
        ((d * X + r * fixedLength θ c X) * (q * fixedLength θ c X) *
          Real.log ((d * X + r * fixedLength θ c X) / (q * fixedLength θ c X))))
      atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hY.eventually (hGM (ε / 2) (by positivity)), shifted_band hB.2.1 hB.2.2.1 hθ hc hd hq hr]
      with X hbound hband
    simpa only [Real.dist_eq] using (hbound _ hband.1 hband.2).trans_lt (by linarith)
  have h := hV.mul (((endpoint_div_tendsto hθ c d r).mul_const q).mul
    (shifted_log_ratio hθ hc hd hq hr))
  simp only [one_mul, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (shifted_log_ratio hθ hc hd hq hr).eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with X hX hlog
  have hH : 0 < fixedLength θ c X := by dsimp [fixedLength]; positivity
  have hYpos : 0 < d * X + r * fixedLength θ c X := by positivity
  have hlogne : Real.log ((d * X + r * fixedLength θ c X) /
      (q * fixedLength θ c X)) ≠ 0 := by
    intro hz
    simp only [hz, zero_div] at hlog
    exact (lt_irrefl (0 : ℝ)) hlog
  have hlogne' : Real.log ((d * X + r * fixedLength θ c X) /
      (fixedLength θ c X * q)) ≠ 0 := by
    simpa only [mul_comm] using hlogne
  field_simp [hX.ne', hH.ne', hYpos.ne', hq.ne', hlogne, hlogne']

private lemma shifted_square_tendsto {E : ℝ → ℝ} {α θ β : ℝ} (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (hGM : CumulativeVarianceBandAsymptoticFor E α β)
    {a b c q r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hq : 0 ≤ q) (hr : 0 ≤ r) :
    Tendsto (fun X =>
      (∫ x in (a * X + r * fixedLength θ c X)..(b * X + r * fixedLength θ c X),
        increment E (q * fixedLength θ c X) x ^ 2) /
          (X * fixedLength θ c X * lengthLog θ c X)) atTop (𝓝 ((b - a) * q)) := by
  rcases eq_or_lt_of_le hq with hq | hq
  · subst q
    simp [increment]
  · have h := (shifted_variance_tendsto hE hB hGM hc hb hq hr).sub
      (shifted_variance_tendsto hE hB hGM hc ha hq hr)
    convert h using 1
    · ext X
      have hi (Y : ℝ) : IntervalIntegrable
          (fun x => increment E (q * fixedLength θ c X) x ^ 2) volume 1 Y := by
        simpa only [pow_two, id_eq] using
          (increment_product_comp_integrableOn hE isCompact_uIcc
            continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
      rw [← intervalIntegral.integral_interval_sub_left
        (hi (b * X + r * fixedLength θ c X)) (hi (a * X + r * fixedLength θ c X)),
        sub_div]
      rfl
    · ring

private lemma ordered_covariance_tendsto {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E) (hB : ValidBand α θ β) (hGM : CumulativeVarianceBandAsymptoticFor E α β)
    {a b c s t : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ht : 0 ≤ t) (hts : t ≤ s) :
    Tendsto (fun X =>
      (∫ x in (a * X)..(b * X),
        increment E (s * fixedLength θ c X) x * increment E (t * fixedLength θ c X) x) /
        (X * fixedLength θ c X * lengthLog θ c X)) atTop (𝓝 ((b - a) * t)) := by
  have hs : 0 ≤ s := ht.trans hts
  have hS := shifted_square_tendsto hE hB hGM ha hb hc hs (le_refl (0 : ℝ))
  have hT := shifted_square_tendsto hE hB hGM ha hb hc ht (le_refl (0 : ℝ))
  have hD := shifted_square_tendsto hE hB hGM ha hb hc (sub_nonneg.mpr hts) ht
  simp only [zero_mul, add_zero] at hS hT
  have hid (X x : ℝ) :
      increment E (s * fixedLength θ c X) x - increment E (t * fixedLength θ c X) x =
        increment E ((s - t) * fixedLength θ c X) (x + t * fixedLength θ c X) := by
    dsimp [increment]
    rw [show x + t * fixedLength θ c X + (s - t) * fixedLength θ c X =
      x + s * fixedLength θ c X by ring]
    ring
  have hdiff (X : ℝ) :
      (∫ x in (a * X)..(b * X),
        (increment E (s * fixedLength θ c X) x - increment E (t * fixedLength θ c X) x) ^ 2) =
      ∫ x in (a * X + t * fixedLength θ c X)..(b * X + t * fixedLength θ c X),
        increment E ((s - t) * fixedLength θ c X) x ^ 2 := by
    simp_rw [hid]
    exact intervalIntegral.integral_comp_add_right
      (fun x : ℝ => increment E ((s - t) * fixedLength θ c X) x ^ 2) _
  have h := ((hS.add hT).sub hD).div_const 2
  convert h using 1
  · ext X
    rw [← hdiff]
    have hsi : IntervalIntegrable (fun x => increment E (s * fixedLength θ c X) x ^ 2)
        volume (a * X) (b * X) := by
      simpa only [pow_two, id_eq] using
        (increment_product_comp_integrableOn hE isCompact_uIcc
          continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
    have hti : IntervalIntegrable (fun x => increment E (t * fixedLength θ c X) x ^ 2)
        volume (a * X) (b * X) := by
      simpa only [pow_two, id_eq] using
        (increment_product_comp_integrableOn hE isCompact_uIcc
          continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
    have hpi : IntervalIntegrable (fun x => increment E (s * fixedLength θ c X) x *
        increment E (t * fixedLength θ c X) x) volume (a * X) (b * X) :=
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
    have hi : IntervalIntegrable (fun x =>
        (increment E (s * fixedLength θ c X) x - increment E (t * fixedLength θ c X) x) ^ 2)
        volume (a * X) (b * X) := by
      convert (hsi.add hti).sub (hpi.const_mul 2) using 1
      ext x
      ring
    rw [← add_div, ← sub_div, ← intervalIntegral.integral_add hsi hti,
      ← intervalIntegral.integral_sub (hsi.add hti) hi]
    have he : (fun x => increment E (s * fixedLength θ c X) x ^ 2 +
        increment E (t * fixedLength θ c X) x ^ 2 -
        (increment E (s * fixedLength θ c X) x - increment E (t * fixedLength θ c X) x) ^ 2) =
        (fun x => 2 * (increment E (s * fixedLength θ c X) x *
          increment E (t * fixedLength θ c X) x)) := by ext x; ring
    rw [he, intervalIntegral.integral_const_mul]
    ring
  · ring

/-- The normalized covariance of two fixed increment lengths tends to their overlap length. -/
theorem fixed_length_covariance_tendsto
    {E : ℝ → ℝ} {α θ β : ℝ} (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (hGM : CumulativeVarianceBandAsymptoticFor E α β)
    {a b c s t : ℝ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2) (hc : 0 < c)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun X => (∫ x in (a * X)..(b * X),
          increment E (s * fixedLength θ c X) x * increment E (t * fixedLength θ c X) x) /
        (X * fixedLength θ c X * lengthLog θ c X))
      Filter.atTop (nhds ((b - a) * min s t)) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hb0 : 0 < b := ha0.trans hab
  rcases le_total t s with hts | hst
  · simpa only [min_eq_right hts] using
      ordered_covariance_tendsto hE hB hGM ha0 hb0 hc ht.1 hts
  · simpa only [min_eq_left hst, mul_comm] using
      ordered_covariance_tendsto hE hB hGM ha0 hb0 hc hs.1 hst

end
end D5.S3.Arith.Robin.ForwardKernel.FixedLengthCovariance
