/- GID: D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse cusp energies transport to the original moving price-weighted responses. -/

import D5.S3.Arith.Robin.ForwardKernel.CuspMovingLengths
import D5.S3.Arith.Robin.ForwardKernel.SparseLogSpikes
import D5.S3.Arith.Robin.ForwardKernel.WeightRemoval

/-! Transport of isolated sparse cusps through the moving price-weighted kernel. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory Filter
open VarianceTransferDefs ProfileKernelDefs
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The cross energy of the two constant-profile responses. -/
def profileCross (E : ℝ → ℝ) (a b X : ℝ) : ℝ :=
  ∫ x in X..(2 * X),
    profileResponse E a (fun _ => 1) x * profileResponse E b (fun _ => 1) x / x

private def priceCuspAverage (h k q x y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1,
    (clippedLog h k (y + s * q) - clippedLog h k y) * priceRatio x (s * q)

private lemma forward_power_bound {X x θ b : ℝ} (hX : 1 ≤ X)
    (hx : x ∈ Icc X (2 * X)) (hθ : 0 ≤ θ) (hθb : θ ≤ b) (hb : b ≤ 1) :
    x ^ θ ≤ 2 * X ^ b := by
  have hX0 : 0 < X := by linarith
  have H := power_length_bounds (θ := θ) (k := X) hX0 hθ (hθb.trans hb)
    (show x - X ∈ Icc (0 : ℝ) X from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hp := Real.rpow_le_rpow_of_exponent_le hX hθb
  have hq : x ^ θ ≤ 2 * X ^ θ := by
    simpa only [add_sub_cancel, div_self hX0.ne',
      show (1 : ℝ) + 1 = 2 by norm_num, mul_comm] using H.2
  exact hq.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

/-- Throughout the complete forward range the normalized response is the
price-weighted average of the single isolated cusp. -/
theorem profileResponse_spike_normalized {a b θ : ℝ} {n₀ n : ℕ}
    (hs : AdmissibleStart b n₀) (hn : n₀ ≤ n)
    (hθ : 0 ≤ θ) (hθb : θ ≤ b) (hb : b ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (center n) (2 * center n)) :
    profileResponse (perturbation a b n₀) θ (fun _ => 1) x / Real.sqrt x =
      amplitude n / x ^ θ *
        (∫ s in (0 : ℝ)..1,
          (clippedLog (center n ^ a) (center n ^ b)
              (x - center n + s * x ^ θ) -
            clippedLog (center n ^ a) (center n ^ b) (x - center n)) *
            priceRatio x (s * x ^ θ)) := by
  have hX := center_pos n
  have hx0 : 0 < x := hX.trans_le hx.1
  have hX₁ : 1 ≤ center n := by
    exact one_le_pow₀ (by norm_num) 
  have hx₁ : 1 ≤ x := hX₁.trans hx.1
  have hq : x ^ θ ≤ 2 * center n ^ b :=
    forward_power_bound hX₁ hx hθ hθb hb
  rw [WeightRemoval.normalized_eq hx0]
  simp only [one_mul]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have he : (∫ s in (0 : ℝ)..1,
      increment (perturbation a b n₀) (s * x ^ θ) x * priceRatio x (s * x ^ θ)) =
      amplitude n * priceCuspAverage (center n ^ a) (center n ^ b) (x ^ θ) x
        (x - center n) := by
    rw [priceCuspAverage, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs'
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs'
    have hu : s * x ^ θ ∈ Icc (0 : ℝ) (2 * center n ^ b) :=
      ⟨mul_nonneg hs'.1 (Real.rpow_nonneg hx0.le _),
        (mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) hs'.2).trans hq⟩
    dsimp only
    unfold increment
    rw [perturbation_forward_eq_spike hs hn hx hu,
      perturbation_eq_spike_on hs hn ⟨hx.1, by linarith [hx.2]⟩]
    simp only [spike]
    rw [show x + s * x ^ θ - center n = x - center n + s * x ^ θ by ring]
    ring
  rw [he]
  dsimp [priceCuspAverage]
  ring

private lemma priceCuspAverage_bounds {h k q x y : ℝ}
    (hh : 0 < h) (hhk : h < k) (hx : 4 ≤ x) (hq : 0 ≤ q) (hy : 0 ≤ y) :
    0 ≤ priceCuspAverage h k q x y ∧
      (1 - 4 * q / x) * cuspAverage h k q y ≤ priceCuspAverage h k q x y ∧
      priceCuspAverage h k q x y ≤ cuspAverage h k q y := by
  let D := fun s => clippedLog h k (y + s * q) - clippedLog h k y
  have hD := jump_integrable hh hhk q y 0 1
  have hm : Measurable (fun s => priceRatio x (s * q)) :=
    WeightRemoval.price_measurable.comp
      (measurable_const.prodMk (measurable_id.mul_const q))
  have hi : IntervalIntegrable (fun s => D s * priceRatio x (s * q)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hD ⊢
    apply hD.mul_bdd hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    obtain ⟨h0, h1⟩ := WeightControl.price_bounds (by linarith : 3 ≤ x)
      (mul_nonneg hs.1.le hq)
    simpa only [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have hp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      0 ≤ D s ∧ 0 ≤ priceRatio x (s * q) ∧
        1 - 4 * q / x ≤ priceRatio x (s * q) ∧ priceRatio x (s * q) ≤ 1 := by
    have hu := mul_nonneg hs.1 hq
    have hρ := WeightControl.price_bounds (by linarith : 3 ≤ x) hu
    have hdiff := (WeightControl.priceRatio_sub_one hx hu).2
    have hstep : 4 * (s * q) / x ≤ 4 * q / x :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hq hs.2) (by norm_num))
        (by linarith)
    exact ⟨sub_nonneg.mpr (clip_mono hh hhk hy (by nlinarith)), hρ.1,
      by linarith, hρ.2⟩
  refine ⟨intervalIntegral.integral_nonneg (by norm_num) (fun s hs =>
    mul_nonneg (hp s hs).1 (hp s hs).2.1), ?_, ?_⟩
  · rw [cuspAverage, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on (by norm_num) (hD.const_mul _) hi
      (fun s hs => by
        have H := hp s hs
        dsimp [D] at *
        nlinarith [mul_le_mul_of_nonneg_left H.2.2.1 H.1])
  · exact intervalIntegral.integral_mono_on (by norm_num) hi hD
      (fun s hs => mul_le_of_le_one_right (hp s hs).1 (hp s hs).2.2.2)

/-- Products of two possibly different normalized responses are integrable on
compact intervals above three. -/
theorem profileCross_integrable {E F : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E) (hF : LocallyBoundedMeasurable F)
    (a b : ℝ) {l r : ℝ} (hl : 3 ≤ l) (hlr : l ≤ r) :
    IntervalIntegrable (fun x =>
      profileResponse E a (fun _ => 1) x * profileResponse F b (fun _ => 1) x / x)
      volume l r := by
  have hg : ProfileIntegrable (fun _ : ℝ => (1 : ℝ)) :=
    ⟨measurable_const, integrable_const _⟩
  have h := (WeightRemoval.profileResponse_normalized_memLp hE hg a hl hlr).integrable_mul
    (WeightRemoval.profileResponse_normalized_memLp hF hg b hl hlr)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlr]
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx0 : 0 ≤ x := by linarith [hx.1]
  simp only [Pi.mul_apply]
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hx0]


private lemma cuspAverage_zero_of_outer {h k q y : ℝ} (hk : 0 < k)
    (hq : 0 ≤ q) (hy : k ≤ y) : cuspAverage h k q y = 0 := by
  have hy0 : 0 ≤ y := hk.le.trans hy
  unfold cuspAverage
  apply intervalIntegral.integral_zero_ae
  apply Eventually.of_forall
  intro s hs
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  rw [clippedLog_eq_zero hk (by
        rw [abs_of_nonneg (add_nonneg hy0 (mul_nonneg hs.1.le hq))]
        nlinarith [hs.1.le]),
    clippedLog_eq_zero hk (by simpa only [abs_of_nonneg hy0] using hy), sub_self]

private lemma price_product_error {h k q₁ q₂ X x y : ℝ}
    (hh : 0 < h) (hhk : h < k) (hX : 4 ≤ X) (hXx : X ≤ x)
    (hq₁ : 0 ≤ q₁) (hq₁' : q₁ ≤ 2 * k)
    (hq₂ : 0 ≤ q₂) (hq₂' : q₂ ≤ 2 * k)
    (hy : 0 ≤ y) (hsmall : 8 * (k / X) ≤ 1) :
    |priceCuspAverage h k q₁ x y * priceCuspAverage h k q₂ x y -
        cuspAverage h k q₁ y * cuspAverage h k q₂ y| ≤
      16 * (k / X) * (cuspAverage h k q₁ y * cuspAverage h k q₂ y) := by
  have hx : 4 ≤ x := hX.trans hXx
  have hX0 : 0 < X := by linarith
  have hx0 : 0 < x := by linarith
  have hk := hh.trans hhk
  have hA := cuspAverage_bounds hh hhk hq₁ hy
  have hB := cuspAverage_bounds hh hhk hq₂ hy
  obtain ⟨hp0, hpL, hpU⟩ := priceCuspAverage_bounds hh hhk hx hq₁ hy
  obtain ⟨hr0, hrL, hrU⟩ := priceCuspAverage_bounds hh hhk hx hq₂ hy
  have hqbound (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 2 * k) :
      4 * q / x ≤ 8 * (k / X) := by
    calc
      _ ≤ 4 * (2 * k) / X := by gcongr
      _ = _ := by ring
  have hp : (1 - 8 * (k / X)) * cuspAverage h k q₁ y ≤ priceCuspAverage h k q₁ x y :=
    (mul_le_mul_of_nonneg_right (by linarith [hqbound q₁ hq₁ hq₁']) hA.1).trans hpL
  have hr : (1 - 8 * (k / X)) * cuspAverage h k q₂ y ≤ priceCuspAverage h k q₂ x y :=
    (mul_le_mul_of_nonneg_right (by linarith [hqbound q₂ hq₂ hq₂']) hB.1).trans hrL
  have hprodU := mul_le_mul hpU hrU hr0 hA.1
  have hprodL := mul_le_mul hp hr (by positivity [hB.1]) hp0
  rw [abs_of_nonpos (sub_nonpos.mpr hprodU)]
  have hNN : 0 ≤ (8 * (k / X)) ^ 2 *
      (cuspAverage h k q₁ y * cuspAverage h k q₂ y) := by positivity [hA.1, hB.1]
  nlinarith only [hprodL, hNN]

/-- Removing the price ratios changes the isolated spike cross energy by a
relative error at most sixteen times its relative outer radius. -/
theorem profileCross_spike_price_error {a b : ℝ} {n₀ n : ℕ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hs : AdmissibleStart b n₀) (hn : n₀ ≤ n)
    (hX : 4 ≤ center n) (hsmall : 8 * (center n ^ b / center n) ≤ 1) :
    |profileCross (perturbation a b n₀) a b (center n) -
        amplitude n ^ 2 * movingCuspEnergy a b (center n)| ≤
      16 * (center n ^ b / center n) *
        (amplitude n ^ 2 * movingCuspEnergy a b (center n)) := by
  let X := center n
  change 4 ≤ X at hX
  let h := X ^ a
  let k := X ^ b
  let A := amplitude n
  let U := fun y => (X + y) ^ (-a - b) *
    cuspAverage h k ((X + y) ^ a) y * cuspAverage h k ((X + y) ^ b) y
  let T := fun y => profileResponse (perturbation a b n₀) a (fun _ => 1) (X + y) *
    profileResponse (perturbation a b n₀) b (fun _ => 1) (X + y) / (X + y)
  have hX0 : 0 < X := center_pos n
  have hX₁ : 1 ≤ X := by dsimp [X]; linarith
  have hh : 0 < h := Real.rpow_pos_of_pos hX0 a
  have hk : 0 < k := Real.rpow_pos_of_pos hX0 b
  have hhk : h < k := Real.rpow_lt_rpow_of_exponent_lt (by dsimp [X]; linarith) hab
  have hkX : k ≤ X := Real.rpow_le_self_of_one_le hX₁ hb.le
  have hUi : IntervalIntegrable U volume 0 X := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hX0.le]
    exact ((continuousOn_const.add continuousOn_id).rpow_const
      (fun y hy => Or.inl (by linarith [hy.1] : X + y ≠ 0))).mul
      (power_average_continuous hh hhk ha.le).continuousOn |>.mul
      (power_average_continuous hh hhk (ha.trans hab).le).continuousOn
  have hTi : IntervalIntegrable T volume 0 X := by
    have H := (profileCross_integrable (perturbation_locallyBoundedMeasurable hs)
      (perturbation_locallyBoundedMeasurable hs) a b (by dsimp [X]; linarith)
      (show X ≤ 2 * X by linarith)).comp_add_left X
    convert H using 1 <;> simp only [sub_self, show 2 * X - X = X by ring]
  have hpoint (y : ℝ) (hy : y ∈ Icc (0 : ℝ) X) :
      |T y - A ^ 2 * U y| ≤ 16 * (k / X) * (A ^ 2 * U y) := by
    have hxy : X + y ∈ Icc X (2 * X) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hx0 : 0 < X + y := by linarith [hy.1]
    have hna := profileResponse_spike_normalized (a := a) hs hn ha.le hab.le hb.le hxy
    have hnb := profileResponse_spike_normalized (a := a) hs hn (ha.trans hab).le le_rfl hb.le hxy
    have hprod : T y = A ^ 2 * (X + y) ^ (-a - b) *
        (priceCuspAverage h k ((X + y) ^ a) (X + y) y *
          priceCuspAverage h k ((X + y) ^ b) (X + y) y) := by
      have hp : (X + y) ^ (-a - b) =
          ((X + y) ^ a * (X + y) ^ b)⁻¹ := by
        rw [← Real.rpow_add hx0, ← Real.rpow_neg hx0.le]; congr 1; ring
      have hsqrt := Real.sq_sqrt hx0.le
      calc
        T y = (profileResponse (perturbation a b n₀) a (fun _ => 1) (X + y) /
            Real.sqrt (X + y)) *
          (profileResponse (perturbation a b n₀) b (fun _ => 1) (X + y) /
            Real.sqrt (X + y)) := by rw [div_mul_div_comm, ← pow_two, hsqrt]
        _ = _ := by
          rw [hna, hnb, hp]
          dsimp [priceCuspAverage, A, h, k, X] at *
          simp only [add_sub_cancel_left]
          ring
    have hbnd := price_product_error (X := X) (x := X + y) hh hhk hX (by linarith [hy.1])
      (Real.rpow_nonneg hx0.le a) (forward_power_bound hX₁ hxy ha.le hab.le hb.le)
      (Real.rpow_nonneg hx0.le b)
      (forward_power_bound hX₁ hxy (ha.trans hab).le le_rfl hb.le) hy.1 hsmall
    rw [hprod]
    have hfac : 0 ≤ A ^ 2 * (X + y) ^ (-a - b) := by positivity
    calc
      _ = (A ^ 2 * (X + y) ^ (-a - b)) *
          |priceCuspAverage h k ((X + y) ^ a) (X + y) y *
              priceCuspAverage h k ((X + y) ^ b) (X + y) y -
            cuspAverage h k ((X + y) ^ a) y * cuspAverage h k ((X + y) ^ b) y| := by
        calc
          _ = |(A ^ 2 * (X + y) ^ (-a - b)) *
              (priceCuspAverage h k ((X + y) ^ a) (X + y) y *
                  priceCuspAverage h k ((X + y) ^ b) (X + y) y -
                cuspAverage h k ((X + y) ^ a) y * cuspAverage h k ((X + y) ^ b) y)| := by
            congr 1
            dsimp [U]; ring
          _ = _ := by rw [abs_mul, abs_of_nonneg hfac]
      _ ≤ _ := (mul_le_mul_of_nonneg_left hbnd hfac).trans_eq (by dsimp [U]; ring)
  have hUint : (∫ y in (0 : ℝ)..X, U y) = movingCuspEnergy a b X := by
    have hspl := intervalIntegral.integral_add_adjacent_intervals
      (hUi.mono_set (by
        rw [uIcc_of_le hk.le, uIcc_of_le hX0.le]
        exact Icc_subset_Icc le_rfl hkX))
      (hUi.mono_set (by
        rw [uIcc_of_le hkX, uIcc_of_le hX0.le]
        exact Icc_subset_Icc hk.le le_rfl))
    have hz : (∫ y in k..X, U y) = 0 := by
      apply intervalIntegral.integral_zero_ae
      apply Eventually.of_forall
      intro y hy
      rw [uIoc_of_le hkX] at hy
      dsimp [U]
      rw [cuspAverage_zero_of_outer hk (Real.rpow_nonneg (by linarith [hy.1]) _) hy.1.le]
      ring
    change (∫ y in (0 : ℝ)..k, U y) + _ = _ at hspl
    rw [hz, add_zero] at hspl
    exact hspl.symm
  have hTint : (∫ y in (0 : ℝ)..X, T y) =
      profileCross (perturbation a b n₀) a b X := by
    dsimp [T, profileCross]
    rw [intervalIntegral.integral_comp_add_left
      (fun x => profileResponse (perturbation a b n₀) a (fun _ => 1) x *
        profileResponse (perturbation a b n₀) b (fun _ => 1) x / x) X]
    simp only [add_zero, show X + X = 2 * X by ring]
  have H := intervalIntegral.norm_integral_le_of_norm_le hX0.le
    (f := fun y => T y - A ^ 2 * U y)
    (g := fun y => 16 * (k / X) * (A ^ 2 * U y))
    (Eventually.of_forall fun y hy => by
      simpa only [Real.norm_eq_abs] using hpoint y ⟨hy.1.le, hy.2⟩)
    ((hUi.const_mul (A ^ 2)).const_mul _)
  rw [intervalIntegral.integral_sub hTi (hUi.const_mul _),
    intervalIntegral.integral_const_mul, hTint, hUint,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hUint,
    Real.norm_eq_abs] at H
  exact H

/-- The original moving response has the cusp main term and the two geometric
and logarithmic error terms. -/
theorem profileCross_spike_estimate {a b : ℝ} {n₀ : ℕ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hs : AdmissibleStart b n₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      let X := center n
      let h := X ^ a
      let k := X ^ b
      let L := Real.log (k / h)
      |profileCross (perturbation a b n₀) a b X -
          amplitude n ^ 2 * X ^ (-a - b) * (h * L ^ 2 / 4)| ≤
        C * amplitude n ^ 2 * X ^ (-a - b) *
          (h * L + (k / X) * (h * L ^ 2)) := by
  obtain ⟨C, hC, hM⟩ := movingCuspEnergy_estimate ha hab hb
  have hδ : Tendsto (fun X : ℝ => X ^ b / X) atTop (𝓝 0) := by
    have H := tendsto_rpow_neg_atTop (by linarith : 0 < 1 - b)
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [show -(1 - b) = b - 1 by ring, Real.rpow_sub hX, Real.rpow_one]
  refine ⟨17 * C + 4, by positivity, ?_⟩
  filter_upwards [center_tendsto.eventually hM,
    (hδ.comp center_tendsto).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    center_tendsto.eventually (eventually_ge_atTop (4 : ℝ)), eventually_ge_atTop n₀]
    with n hm hd hX hn
  let X := center n
  let h := X ^ a
  let k := X ^ b
  let L := Real.log (k / h)
  let W := X ^ (-a - b)
  let δ := k / X
  let P := W * (h * L)
  let Q := W * (δ * (h * L ^ 2))
  have hX0 : 0 < X := center_pos n
  change 4 ≤ X at hX
  change δ < 1 / 8 at hd
  have hh : 0 < h := Real.rpow_pos_of_pos hX0 _
  have hk : 0 < k := Real.rpow_pos_of_pos hX0 _
  have hhk : h < k := Real.rpow_lt_rpow_of_exponent_lt (by dsimp [X]; linarith) hab
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_div hh).2 hhk.le)
  have hδ0 : 0 ≤ δ := div_nonneg hk.le hX0.le
  have hδ1 : δ ≤ 1 := by dsimp [δ, k, X]; linarith
  have hP : 0 ≤ P := by positivity
  have hQ : 0 ≤ Q := by positivity
  have hm' : |movingCuspEnergy a b X - W * (h * L ^ 2 / 4)| ≤ C * (P + Q) := by
    convert hm using 1 <;> dsimp [P, Q, W, δ, h, k, L, X] <;> ring
  have hupper := (abs_le.mp hm').2
  have hscaled := mul_le_mul_of_nonneg_left hupper hδ0
  have hcap : δ * (C * (P + Q)) ≤ C * (P + Q) :=
    mul_le_of_le_one_left (by positivity) hδ1
  have hmain : δ * (W * (h * L ^ 2 / 4)) = Q / 4 := by dsimp [Q]; ring
  have hrel : 16 * δ * movingCuspEnergy a b X ≤ 4 * Q + 16 * C * (P + Q) := by
    rw [mul_sub] at hscaled
    rw [hmain] at hscaled
    linarith
  have hp := profileCross_spike_price_error ha hab hb hs hn hX (by dsimp [δ, k, X] at hd ⊢; linarith)
  have hA : 0 ≤ amplitude n ^ 2 := sq_nonneg _
  have herr : |amplitude n ^ 2 * movingCuspEnergy a b X -
      amplitude n ^ 2 * (W * (h * L ^ 2 / 4))| ≤ amplitude n ^ 2 * (C * (P + Q)) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left hm' hA
  have ht := (abs_sub_le (profileCross (perturbation a b n₀) a b X)
    (amplitude n ^ 2 * movingCuspEnergy a b X)
    (amplitude n ^ 2 * (W * (h * L ^ 2 / 4)))).trans (add_le_add hp herr)
  have hrelA := mul_le_mul_of_nonneg_left hrel hA
  have hP' := mul_nonneg hA hP
  have hQ' := mul_nonneg hA hQ
  change |profileCross (perturbation a b n₀) a b X -
    amplitude n ^ 2 * W * (h * L ^ 2 / 4)| ≤
      (17 * C + 4) * amplitude n ^ 2 * W * (h * L + δ * (h * L ^ 2))
  calc
    _ = |profileCross (perturbation a b n₀) a b X -
        amplitude n ^ 2 * (W * (h * L ^ 2 / 4))| := by congr 1; ring
    _ ≤ _ := ht
    _ ≤ amplitude n ^ 2 * (4 * Q + 17 * C * (P + Q)) := by
      convert add_le_add_right hrelA (amplitude n ^ 2 * (C * (P + Q))) using 1 <;>
        (try dsimp only [X, δ, k]) <;> ring
    _ ≤ (17 * C + 4) * amplitude n ^ 2 * (P + Q) := by nlinarith only [hP']
    _ = _ := by dsimp [P, Q]; ring

/-- Along the spike centers the actual cross energy has coefficient
`(b-a)^2/4` at the near-optimal scale. -/
theorem profileCross_spike_asymptotic {a b : ℝ} {n₀ : ℕ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hs : AdmissibleStart b n₀) :
    Tendsto (fun n : ℕ =>
      profileCross (perturbation a b n₀) a b (center n) / nearOptScale b (center n))
      atTop (𝓝 ((b - a) ^ 2 / 4)) := by
  obtain ⟨C, hC, hbound⟩ := profileCross_spike_estimate ha hab hb hs
  have hδ : Tendsto (fun n : ℕ => center n ^ b / center n) atTop (𝓝 0) := by
    have H := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - b)).comp center_tendsto
    apply H.congr'
    filter_upwards [Eventually.of_forall center_pos] with n hn
    change center n ^ (-(1 - b)) = _
    rw [show -(1 - b) = b - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
  have herrlim : Tendsto (fun n : ℕ => C *
      ((b - a) / Real.log (center n) +
        (center n ^ b / center n) * (b - a) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_mul, add_zero, mul_zero, zero_add] using
      (((tendsto_const_nhds (x := b - a)).div_atTop
        (Real.tendsto_log_atTop.comp center_tendsto)).add
        (hδ.mul_const ((b - a) ^ 2))).const_mul C
  have he : ∀ᶠ n : ℕ in atTop,
      |profileCross (perturbation a b n₀) a b (center n) / nearOptScale b (center n) -
        (b - a) ^ 2 / 4| ≤ C * ((b - a) / Real.log (center n) +
          (center n ^ b / center n) * (b - a) ^ 2) := by
    filter_upwards [hbound,
      center_tendsto.eventually (eventually_gt_atTop (Real.exp 1))] with n hn hX
    let X := center n
    have hx := center_pos n
    have hl₁ : 1 < Real.log X := (Real.lt_log_iff_exp_lt hx).2 hX
    have hl : 0 < Real.log X := by linarith
    have hll : 0 < Real.log (Real.log X) := Real.log_pos hl₁
    have hR : 0 < nearOptScale b X := by unfold nearOptScale; positivity
    have hL : Real.log (X ^ b / X ^ a) = (b - a) * Real.log X := by
      rw [← Real.rpow_sub hx, Real.log_rpow hx]
    have hp : X * X ^ (-a - b) * X ^ a = X ^ (1 - b) := by
      calc
        _ = X ^ (1 + (-a - b) + a) := by
          rw [Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one]
        _ = _ := by congr 1; ring
    have hA : amplitude n ^ 2 * X ^ (-a - b) * X ^ a =
        X ^ (1 - b) * Real.log X / Real.log (Real.log X) := by
      have hsq : amplitude n ^ 2 = X * Real.log X / Real.log (Real.log X) :=
        Real.sq_sqrt (by positivity)
      rw [hsq]
      calc
        _ = (X * X ^ (-a - b) * X ^ a) * Real.log X / Real.log (Real.log X) := by ring
        _ = _ := by rw [hp]
    have hm : amplitude n ^ 2 * X ^ (-a - b) *
        (X ^ a * (Real.log (X ^ b / X ^ a)) ^ 2 / 4) =
        ((b - a) ^ 2 / 4) * nearOptScale b X := by
      calc
        _ = (amplitude n ^ 2 * X ^ (-a - b) * X ^ a) *
          ((Real.log (X ^ b / X ^ a)) ^ 2 / 4) := by ring
        _ = _ := by rw [hA, hL]; unfold nearOptScale; ring
    have heq : C * amplitude n ^ 2 * X ^ (-a - b) *
        (X ^ a * Real.log (X ^ b / X ^ a) +
          (X ^ b / X) * (X ^ a * (Real.log (X ^ b / X ^ a)) ^ 2)) /
        nearOptScale b X =
        C * ((b - a) / Real.log X + (X ^ b / X) * (b - a) ^ 2) := by
      calc
        _ = C * (amplitude n ^ 2 * X ^ (-a - b) * X ^ a) *
          (Real.log (X ^ b / X ^ a) + (X ^ b / X) * (Real.log (X ^ b / X ^ a)) ^ 2) /
            nearOptScale b X := by ring
        _ = _ := by
          rw [hA, hL]
          unfold nearOptScale
          have hp0 : X ^ (1 - b) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
          generalize X ^ (1 - b) = Z at *
          field_simp [hl.ne', hll.ne', hp0]
          <;> ring
    change |profileCross (perturbation a b n₀) a b X / nearOptScale b X -
      (b - a) ^ 2 / 4| ≤ _
    have hdif : profileCross (perturbation a b n₀) a b X / nearOptScale b X -
        (b - a) ^ 2 / 4 =
        (profileCross (perturbation a b n₀) a b X -
          ((b - a) ^ 2 / 4) * nearOptScale b X) / nearOptScale b X := by
      field_simp
    rw [hdif, ← hm, abs_div, abs_of_pos hR]
    exact (div_le_div_of_nonneg_right hn hR.le).trans_eq heq
  have hz : Tendsto (fun n : ℕ =>
      |profileCross (perturbation a b n₀) a b (center n) / nearOptScale b (center n) -
        (b - a) ^ 2 / 4|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) he herrlim
  have H : Tendsto (fun n : ℕ =>
      profileCross (perturbation a b n₀) a b (center n) / nearOptScale b (center n) -
        (b - a) ^ 2 / 4) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by
    simpa only [Real.norm_eq_abs] using hz)
  convert H.add_const ((b - a) ^ 2 / 4) using 1 <;> simp

end
end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
