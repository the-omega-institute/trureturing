/- GID: D5/S3/Analytic/Oscillation/SpectrumThreeBandRecurrence
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SpectrumThreeBandRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-band averaging improves the asymptotic loss bound for sine recurrence. -/

import D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff
import D5.S3.Fourier.HarmonicScoreLocalAverage

/-! Uniform recurrence for full-cutoff scores from a short average after a head hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace D5.S3.Analytic.Oscillation.SpectrumThreeBandRecurrence

open D5.S3.Analytic.Oscillation.OrdinateCounting (Spectrum)
open D5.S3.Analytic.Oscillation.SpectrumPhaseCutoff (mass sine)
open D5.S3.Fourier.HarmonicScoreLocalAverage (cutoffMass cutoffScore exists_cutoffScore_ge)

private theorem choose_bands {q : ℝ → ℝ} {m ε : ℝ} (hm : 0 < m)
    (hq : ContinuousAt q m) (hε : 1 - q m < ε) :
    ∃ α κ ν e : ℝ, 0 < α ∧ α < κ ∧ κ < ν ∧ ν < m ∧
      0 < e ∧ 1 + q ν - 2 * q α + e * q α < ε := by
  let δ := (ε - (1 - q m)) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨R, hR, hnear⟩ := Metric.continuousAt_iff.mp hq δ hδ
  let d := min (m / 4) (R / 4)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdm : d ≤ m / 4 := min_le_left _ _
  have hdR : d ≤ R / 4 := min_le_right _ _
  let α := m - 2 * d
  let ν := m - d
  have hα : 0 < α := by dsimp [α]; linarith
  have hαν : α < ν := by dsimp [α, ν]; linarith
  have hν : ν < m := sub_lt_self _ hd
  obtain ⟨κ, hακ, hκν⟩ := exists_between hαν
  have hqα : |q α - q m| < δ := by
    apply hnear
    rw [Real.dist_eq, show α - m = -(2 * d) by dsimp [α]; ring, abs_neg,
      abs_of_pos (by positivity : 0 < 2 * d)]
    linarith
  have hqν : |q ν - q m| < δ := by
    apply hnear
    rw [Real.dist_eq, show ν - m = -d by dsimp [ν]; ring, abs_neg, abs_of_pos hd]
    linarith
  let e := min 1 (δ / (|q m| + 1))
  have he : 0 < e := lt_min zero_lt_one (by positivity)
  have he₁ : e ≤ 1 := min_le_left _ _
  have heq : e * q m ≤ δ := by
    have hquot : e ≤ δ / (|q m| + 1) := min_le_right _ _
    exact (mul_le_mul_of_nonneg_left (by linarith [le_abs_self (q m)]) he.le).trans
      ((le_div_iff₀ (by positivity : 0 < |q m| + 1)).mp hquot)
  have hαerr : (2 - e) * (q m - q α) < 2 * δ := by
    calc
      _ < (2 - e) * δ := mul_lt_mul_of_pos_left (by linarith [(abs_lt.mp hqα).1])
        (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
  refine ⟨α, κ, ν, e, hα, hακ, hκν, hν, he, ?_⟩
  have hνerr := (abs_lt.mp hqν).2
  have hsum : 1 + q ν - 2 * q α + e * q α =
      1 - q m + (q ν - q m) + (2 - e) * (q m - q α) + e * q m := by ring
  rw [hsum]
  dsimp [δ] at hνerr hαerr heq
  linarith

private theorem filter_cut (S : Spectrum) {Z T : ℝ} (hZT : Z ≤ T) :
    (S.cut T).filter (fun j => S.gamma j ≤ Z) = S.cut Z := by
  classical
  ext j
  have hmem (U : ℝ) : j ∈ S.cut U ↔ S.gamma j ≤ U :=
    (S.finite_le U).mem_toFinset
  rw [Finset.mem_filter, hmem T, hmem Z]
  exact ⟨And.right, fun hz => ⟨hz.trans hZT, hz⟩⟩

private theorem eventual_window_bound {α κ β : ℝ}
    (hα : 0 < α) (hκ : 0 < κ) (hαβ : α < β) :
    ∀ᶠ T : ℝ in atTop, Real.exp (T ^ α) + T ^ (-κ) ≤ Real.exp (T ^ β) := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hαβ)).eventually_ge_atTop 2,
    eventually_ge_atTop (1 : ℝ)] with T hpower hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hX : 1 ≤ T ^ α := Real.one_le_rpow hT hα.le
  have hh : T ^ (-κ) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hT
      (neg_nonpos.mpr hκ.le)
  have hdiff : 1 ≤ T ^ β - T ^ α := by
    rw [Real.rpow_sub hTpos] at hpower
    linarith only [(le_div_iff₀ (Real.rpow_pos_of_pos hTpos α)).mp hpower, hX]
  have hbudget : 1 + T ^ (-κ) / Real.exp (T ^ α) ≤
      Real.exp (T ^ β - T ^ α) := by
    apply le_trans _ (Real.add_one_le_exp _)
    have hquot : T ^ (-κ) / Real.exp (T ^ α) ≤ 1 :=
      (div_le_iff₀ (Real.exp_pos _)).mpr (by
        rw [one_mul]
        exact hh.trans (Real.one_le_exp_iff.mpr (zero_le_one.trans hX)))
    linarith
  apply (div_le_div_iff_of_pos_right (Real.exp_pos (T ^ α))).mp
  rwa [add_div, div_self (Real.exp_ne_zero _), ← Real.exp_sub]

/-- Local averaging improves the limiting loss from a low-frequency hit to the
complement of the limiting mass at the available power cutoff. -/
theorem eventual_sine_three_band_recurrence (S : Spectrum) (w : S.index → ℝ)
    (hw : ∀ j, 0 ≤ w j) (q : ℝ → ℝ) {r β ε : ℝ} (hr : 0 < r) (hβ : 0 < β)
    (hq : ContinuousAt q (min β 1))
    (hratio : ∀ p : ℝ, 0 < p → p < 1 →
      Tendsto (fun T : ℝ => mass S w (T ^ p) / mass S w T) atTop (nhds (q p)))
    (hhead : ∀ e : ℝ, 0 < e → ∀ᶠ X : ℝ in atTop, 0 < mass S w X ∧
      ∀ a : ℝ, ∃ b ∈ Icc a (a + Real.exp X),
        1 - sine S w X (b / r) / mass S w X < e)
    (hε : 1 - q (min β 1) < ε) :
    ∀ᶠ T : ℝ in atTop, 0 < mass S w T ∧
      ∀ a : ℝ, ∃ u ∈ Icc a (a + Real.exp (T ^ β)),
        1 - sine S w T (u / r) / mass S w T < ε := by
  obtain ⟨α, κ, ν, e, hα, hακ, hκν, hν, he, hbudget⟩ :=
    choose_bands (lt_min hβ zero_lt_one) hq hε
  have hκ := hα.trans hακ
  have hαν := hακ.trans hκν
  have hν₁ := hν.trans_le (min_le_right _ _)
  have hαβ := (hαν.trans hν).trans_le (min_le_left _ _)
  let x (T : ℝ) := mass S w (T ^ α) / mass S w T
  let y (T : ℝ) := mass S w (T ^ ν) / mass S w T
  let low (T : ℝ) := T ^ (-κ) * T ^ α / r
  let high (T : ℝ) := 2 * r / (T ^ (-κ) * T ^ ν)
  have hx : Tendsto x atTop (nhds (q α)) := hratio α hα (hαν.trans hν₁)
  have hy : Tendsto y atTop (nhds (q ν)) := hratio ν (hα.trans hαν) hν₁
  have hlow : Tendsto low atTop (nhds 0) := by
    refine ((tendsto_rpow_neg_atTop (sub_pos.mpr hακ)).div_const r).congr' ?_
      |>.trans_eq (by rw [zero_div])
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    dsimp [low]
    rw [← Real.rpow_add hT, show -(κ - α) = -κ + α by ring]
  have hhigh : Tendsto high atTop (nhds 0) := by
    have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hκν)).const_mul (2 * r)
    rw [mul_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    dsimp [high]
    rw [← Real.rpow_add hT, div_eq_mul_inv, ← Real.rpow_neg hT.le,
      show -κ + ν = ν - κ by ring]
  have hlimit := (((((tendsto_const_nhds (x := (1 : ℝ))).add hy).sub
    (hx.const_mul 2)).add (hx.const_mul e)).add (hlow.mul hx)).add
    (hhigh.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hy))
  simp only [zero_mul, add_zero] at hlimit
  have hsmall := hlimit.eventually (gt_mem_nhds hbudget)
  classical
  filter_upwards [(tendsto_rpow_atTop hα).eventually (hhead e he), hhead e he,
    eventually_ge_atTop (1 : ℝ), eventual_window_bound hα hκ hαβ, hsmall]
    with T hheadX hheadT hT htime hsmallT
  obtain ⟨hWX, hhits⟩ := hheadX
  have hWT := hheadT.1
  refine ⟨hWT, fun a => ?_⟩
  obtain ⟨b, hb, hloss⟩ := hhits a
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hXY : T ^ α ≤ T ^ ν := Real.rpow_le_rpow_of_exponent_le hT hαν.le
  have hYT : T ^ ν ≤ T := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT hν₁.le
  have hm (Z : ℝ) (hZT : Z ≤ T) : cutoffMass (S.cut T) S.gamma w Z = mass S w Z := by
    change ∑ j ∈ (S.cut T).filter (fun j => S.gamma j ≤ Z), w j = _
    rw [filter_cut S hZT, mass]
  have hs (Z : ℝ) (hZT : Z ≤ T) (v : ℝ) :
      cutoffScore (S.cut T) S.gamma w Z v = sine S w Z v := by
    change ∑ j ∈ (S.cut T).filter (fun j => S.gamma j ≤ Z),
      w j * Real.sin (S.gamma j * v) = _
    rw [filter_cut S hZT, sine]
  obtain ⟨u, hu, hscore⟩ := exists_cutoffScore_ge (S.cut T) S.gamma w
    (Real.rpow_pos_of_pos hTpos α) hXY hYT hr (Real.rpow_pos_of_pos hTpos (-κ))
    (b := b) (fun j _ => S.gamma_pos j) (fun j _ => hw j)
  rw [hm _ (hXY.trans hYT), hm _ hYT, hm _ le_rfl, hs _ (hXY.trans hYT),
    hs _ le_rfl] at hscore
  have hheadScore : (1 - e) * mass S w (T ^ α) < sine S w (T ^ α) (b / r) :=
    (lt_div_iff₀ hWX).mp (by linarith only [hloss])
  have hfull : (1 - e) * mass S w (T ^ α) - low T * mass S w (T ^ α) -
      (mass S w (T ^ ν) - mass S w (T ^ α)) -
      high T * (mass S w T - mass S w (T ^ ν)) < sine S w T (u / r) := by
    dsimp only [low, high]
    linarith only [hscore, hheadScore]
  have hnormalized := div_lt_div_of_pos_right hfull hWT
  rw [sub_div, sub_div, sub_div, mul_div_assoc, mul_div_assoc, sub_div,
    mul_div_assoc, sub_div, div_self hWT.ne'] at hnormalized
  change 1 + y T - 2 * x T + e * x T + low T * x T + high T * (1 - y T) < ε at hsmallT
  refine ⟨u, ⟨hb.1.trans hu.1, ?_⟩, ?_⟩
  · linarith only [hb.2, hu.2, htime]
  · change (1 - e) * x T - low T * x T - (y T - x T) -
      high T * (1 - y T) < _ at hnormalized
    linarith only [hnormalized, hsmallT, show (1 - e) * x T = x T - e * x T by ring]

end D5.S3.Analytic.Oscillation.SpectrumThreeBandRecurrence
