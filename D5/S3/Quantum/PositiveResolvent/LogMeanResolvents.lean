/- GID: D5/S3/Quantum/PositiveResolvent/LogMeanResolvents
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive logarithmic mean and three-node resolvent integrals with their confluent values. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace D5.S3.Quantum.PositiveResolvent.LogMeanResolvents

open Set MeasureTheory Filter
open scoped Topology

noncomputable def L (x y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, 1 / ((1 - s) * x + s * y)

noncomputable def m (x y z : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), 1 / ((x + t) * (y + t) * (z + t))

private lemma affine_pos {x y s : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 < (1 - s) * x + s * y := by
  by_cases h : s = 0
  · simp [h, hx]
  · have : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm h)
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs.2) hx.le)
      (mul_pos this hy)

private lemma L_continuous_integrand {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ContinuousOn (fun s : ℝ => 1 / ((1 - s) * x + s * y)) (Icc 0 1) := by
  exact continuousOn_const.div (by fun_prop) (fun s hs => (affine_pos hx hy hs).ne')

theorem L_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < L x y := by
  apply intervalIntegral.integral_pos zero_lt_one (L_continuous_integrand hx hy)
  · intro s hs
    exact (one_div_pos.mpr (affine_pos hx hy ⟨hs.1.le, hs.2⟩)).le
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [hx]⟩

theorem L_self (x : ℝ) : L x x = 1 / x := by
  unfold L
  simp_rw [show ∀ s : ℝ, (1 - s) * x + s * x = x by intro s; ring]
  simp

theorem L_eq_of_ne {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : x ≠ y) :
    L x y = (Real.log x - Real.log y) / (x - y) := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Real.log ((1 - s) * x + s * y) / (y - x))
        (1 / ((1 - s) * x + s * y)) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have hn := (affine_pos hx hy hs).ne'
    have h := ((((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const x).add
      ((hasDerivAt_id s).mul_const y)).log hn |>.div_const (y - x)
    convert! h using 1 <;> (try dsimp) <;> (try rfl) <;> field_simp [hn, sub_ne_zero.mpr (Ne.symm hne)] <;> ring
  have hcont : ContinuousOn (fun s : ℝ => 1 / ((1 - s) * x + s * y)) (uIcc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using L_continuous_integrand hx hy
  have hint : IntervalIntegrable (fun s : ℝ => 1 / ((1 - s) * x + s * y)) volume 0 1 := hcont.intervalIntegrable
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  try dsimp at hi
  simp only [sub_zero, mul_one, zero_mul, mul_zero, zero_add, add_zero, sub_self] at hi
  rw [L, hi]
  field_simp [sub_ne_zero.mpr hne, sub_ne_zero.mpr (Ne.symm hne)]
  <;> ring

theorem L_symm (x y : ℝ) : L x y = L y x := by
  unfold L
  have h := intervalIntegral.integral_comp_sub_left
    (fun s : ℝ => 1 / ((1 - s) * x + s * y)) (a := 0) (b := 1) 1
  simp only [sub_self, sub_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s hs
  congr 1
  ring

private lemma inv_pow_integrable {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 1 < n) :
    IntegrableOn (fun t : ℝ => 1 / (r + t) ^ n) (Ioi 0) := by
  have h := integrableOn_add_rpow_Ioi_of_lt
    (a := -(n : ℝ)) (c := 0) (m := r) (by
      have h : (1 : ℝ) < n := by exact_mod_cast hn
      linarith) (by linarith)
  simpa [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, one_div, add_comm] using h

private lemma pair_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => 1 / ((x + t) * (y + t))) (Ioi 0) := by
  have hr : 0 < min x y := lt_min hx hy
  apply (inv_pow_integrable hr (by norm_num : 1 < (2 : ℕ))).mono'
  · exact (continuousOn_const.div
      ((continuousOn_const.add continuousOn_id).mul (continuousOn_const.add continuousOn_id))
      (fun t ht => mul_ne_zero (by linarith [mem_Ioi.mp ht] : x + t ≠ 0)
        (by linarith [mem_Ioi.mp ht] : y + t ≠ 0))).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    have hp : 0 < min x y + t := by linarith [ht]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [min_le_left x y, min_le_right x y]

private lemma pair_self_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), 1 / ((r + t) * (r + t))) = 1 / r := by
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => -(r + t)⁻¹)
      (1 / ((r + t) * (r + t))) t := by
    intro t ht
    simp only [mem_Ioi, mem_Ici] at ht
    have h := (((hasDerivAt_const t r).add (hasDerivAt_id t)).inv
      (by linarith [ht] : r + t ≠ 0)).neg
    convert! h using 1 <;> simp [one_div, pow_two, mul_inv, neg_div]
  have ht : Tendsto (fun t : ℝ => -(r + t)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ r tendsto_id)).neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd (pair_integrable hr hr) ht
  simpa using h

theorem L_eq_integral_Ioi {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    L x y = ∫ t in Ioi (0 : ℝ), 1 / ((x + t) * (y + t)) := by
  by_cases hne : x = y
  · subst y
    rw [L_self, pair_self_integral hx]
  rw [L_eq_of_ne hx hy hne]
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (Real.log (x + t) - Real.log (y + t)) / (y - x))
        (1 / ((x + t) * (y + t))) t := by
    intro t ht
    simp only [mem_Ioi, mem_Ici] at ht
    have hn1 : x + t ≠ 0 := by linarith [ht]
    have hn2 : y + t ≠ 0 := by linarith [ht]
    have h := ((((hasDerivAt_const t x).add (hasDerivAt_id t)).log hn1).sub
      (((hasDerivAt_const t y).add (hasDerivAt_id t)).log hn2)).div_const (y - x)
    convert! h using 1 <;> (try dsimp) <;> (try rfl) <;> field_simp [hn1, hn2, sub_ne_zero.mpr (Ne.symm hne)] <;> ring
  have ht : Tendsto (fun t : ℝ =>
      (Real.log (x + t) - Real.log (y + t)) / (y - x)) atTop (𝓝 0) := by
    have h := ((Real.tendsto_log_comp_add_sub_log (x - y)).comp
      (tendsto_atTop_add_const_left _ y tendsto_id)).div_const (y - x)
    simpa [show ∀ t : ℝ, y + t + (x - y) = x + t by intro t; ring] using h
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd (pair_integrable hx hy) ht
  try dsimp at h
  simp only [add_zero] at h
  rw [h]
  field_simp [sub_ne_zero.mpr hne, sub_ne_zero.mpr (Ne.symm hne)]
  <;> ring

theorem m_integrable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => 1 / ((x + t) * (y + t) * (z + t))) (Ioi 0) := by
  have hr : 0 < min x (min y z) := lt_min hx (lt_min hy hz)
  apply (inv_pow_integrable hr (by norm_num : 1 < (3 : ℕ))).mono'
  · exact (continuousOn_const.div
      (((continuousOn_const.add continuousOn_id).mul
        (continuousOn_const.add continuousOn_id)).mul (continuousOn_const.add continuousOn_id))
      (fun t ht => by
        simp only [mem_Ioi] at ht
        have h1 : 0 < x + t := by linarith [ht]
        have h2 : 0 < y + t := by linarith [ht]
        have h3 : 0 < z + t := by linarith [ht]
        exact mul_ne_zero (mul_ne_zero h1.ne' h2.ne') h3.ne')).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    have hp : 0 < min x (min y z) + t := by linarith [ht]
    have h1 : min x (min y z) + t ≤ x + t := by linarith [min_le_left x (min y z)]
    have h2 : min x (min y z) + t ≤ y + t :=
      by linarith [(min_le_right x (min y z)).trans (min_le_left y z)]
    have h3 : min x (min y z) + t ≤ z + t :=
      by linarith [(min_le_right x (min y z)).trans (min_le_right y z)]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    calc
      (min x (min y z) + t) ^ 3 =
        (min x (min y z) + t) * (min x (min y z) + t) * (min x (min y z) + t) := by ring
      _ ≤ (x + t) * (y + t) * (z + t) :=
        mul_le_mul (mul_le_mul h1 h2 hp.le (by linarith)) h3 hp.le
          (mul_nonneg (by linarith) (by linarith))

theorem m_pos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 < m x y z := by
  have hp : ∀ t ∈ Ioi (0 : ℝ), 0 < 1 / ((x + t) * (y + t) * (z + t)) := by
    intro t ht
    simp only [mem_Ioi, mem_Ici] at ht
    have h1 : 0 < x + t := by linarith [ht]
    have h2 : 0 < y + t := by linarith [ht]
    have h3 : 0 < z + t := by linarith [ht]
    positivity
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun t ht => (hp t ht).le)))
    (m_integrable hx hy hz)).mpr
  have he : Function.support (fun t : ℝ => 1 / ((x + t) * (y + t) * (z + t))) ∩ Ioi 0 = Ioi 0 := by
    ext t
    simp only [mem_inter_iff, Function.mem_support]
    exact ⟨fun h => h.2, fun h => ⟨(hp t h).ne', h⟩⟩
  rw [he]
  simp

theorem L_sub_L_eq_m {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    L x z - L x y = (y - z) * m x y z := by
  rw [L_eq_integral_Ioi hx hz, L_eq_integral_Ioi hx hy,
    ← integral_sub (pair_integrable hx hz) (pair_integrable hx hy), m, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [mem_Ioi] at ht
  have h1 : x + t ≠ 0 := by linarith [ht]
  have h2 : y + t ≠ 0 := by linarith [ht]
  have h3 : z + t ≠ 0 := by linarith [ht]
  field_simp
  <;> ring

theorem m_symm (x y z : ℝ) : m x y z = m y x z := by
  unfold m
  congr 1
  ext t
  rw [mul_comm (x + t) (y + t)]

theorem m_symm_right (x y z : ℝ) : m x y z = m x z y := by
  unfold m
  congr 1
  ext t
  congr 1
  ring

theorem m_self {r : ℝ} (hr : 0 < r) : m r r r = 1 / (2 * r ^ 2) := by
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => -(1 / (2 * (r + t) ^ 2)))
        (1 / ((r + t) * (r + t) * (r + t))) t := by
    intro t ht
    simp only [mem_Ioi, mem_Ici] at ht
    have hn : r + t ≠ 0 := by linarith [ht]
    have h := (((((hasDerivAt_const t r).add (hasDerivAt_id t)).pow 2).const_mul 2).inv
      (by positivity : 2 * (r + t) ^ 2 ≠ 0)).neg
    convert! h using 1 <;> (try dsimp) <;>
      first | (ext a; simp [one_div]) | (field_simp <;> ring)
  have ht : Tendsto (fun t : ℝ => -(1 / (2 * (r + t) ^ 2))) atTop (𝓝 0) := by
    have h := ((tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ r tendsto_id)).pow 2).const_mul (-(1 / 2 : ℝ))
    convert! h using 1 <;> simp [one_div, mul_inv, inv_pow] <;> ring
  simpa [m] using integral_Ioi_of_hasDerivAt_of_tendsto' hd (m_integrable hr hr hr) ht

theorem L_homog (c x y : ℝ) (hc : 0 < c) : L (c * x) (c * y) = c⁻¹ * L x y := by
  unfold L
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp
  rw [show (1 - s) * (c * x) + s * (c * y) = c * ((1 - s) * x + s * y) by ring]
  simp [div_eq_mul_inv, mul_inv, mul_comm]

theorem m_homog (c x y z : ℝ) (hc : 0 < c) :
    m (c * x) (c * y) (c * z) = c⁻¹ ^ 2 * m x y z := by
  have h := integral_comp_mul_left_Ioi
    (fun t : ℝ => 1 / ((c * x + t) * (c * y + t) * (c * z + t))) 0 hc
  simp only [mul_zero, smul_eq_mul] at h
  have he : (∫ t in Ioi (0 : ℝ),
      1 / ((c * x + c * t) * (c * y + c * t) * (c * z + c * t))) = c⁻¹ ^ 3 * m x y z := by
    rw [m, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [mem_Ioi, mem_Ici] at ht
    simp only [← mul_add, div_eq_mul_inv, mul_inv]
    ring
  rw [he] at h
  calc
    m (c * x) (c * y) (c * z) = c * (c⁻¹ ^ 3 * m x y z) := by
      rw [h]
      simp [m, hc.ne']
    _ = c⁻¹ ^ 2 * m x y z := by field_simp <;> ring

/-- Joint continuity of the logarithmic resolvent, including its diagonal. -/
theorem L_continuousAt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ContinuousAt (fun p : ℝ × ℝ => L p.1 p.2) (x, y) := by
  let r := min x y / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrx : r < x := by dsimp [r]; linarith [min_le_left x y, lt_min hx hy]
  have hry : r < y := by dsimp [r]; linarith [min_le_right x y, lt_min hx hy]
  have he : ∀ᶠ p : ℝ × ℝ in 𝓝 (x, y), r < p.1 ∧ r < p.2 :=
    (continuousAt_fst.tendsto.eventually (eventually_gt_nhds hrx)).and
      (continuousAt_snd.tendsto.eventually (eventually_gt_nhds hry))
  unfold L
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => 1 / r)
  · exact Eventually.of_forall (fun p =>
      (by fun_prop : Measurable (fun s : ℝ => 1 / ((1 - s) * p.1 + s * p.2))).aestronglyMeasurable)
  · filter_upwards [he] with p hp
    apply ae_of_all
    intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    have hd : r ≤ (1 - s) * p.1 + s * p.2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hp.1.le),
        mul_nonneg hs.1.le (sub_nonneg.mpr hp.2.le)]
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hr.trans_le hd))]
    exact one_div_le_one_div_of_le hr hd
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    exact continuousAt_const.div (by fun_prop) (affine_pos hx hy ⟨hs.1.le, hs.2⟩).ne'

/-- Joint continuity of the three-node integral on the positive orthant. -/
theorem m_continuousAt {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => m p.1 p.2.1 p.2.2) (x, y, z) := by
  let r := min x (min y z) / 2
  have hmin : 0 < min x (min y z) := lt_min hx (lt_min hy hz)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrx : r < x := by dsimp [r]; linarith [min_le_left x (min y z)]
  have hry : r < y := by
    dsimp [r]
    linarith [(min_le_right x (min y z)).trans (min_le_left y z)]
  have hrz : r < z := by
    dsimp [r]
    linarith [(min_le_right x (min y z)).trans (min_le_right y z)]
  have he : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (x, y, z), r < p.1 ∧ r < p.2.1 ∧ r < p.2.2 :=
    (continuousAt_fst.tendsto.eventually (eventually_gt_nhds hrx)).and
      (((continuousAt_fst.comp continuousAt_snd).tendsto.eventually (eventually_gt_nhds hry)).and
        ((continuousAt_snd.comp continuousAt_snd).tendsto.eventually (eventually_gt_nhds hrz)))
  unfold m
  apply MeasureTheory.continuousAt_of_dominated (bound := fun t : ℝ => 1 / (r + t) ^ 3)
  · exact Eventually.of_forall (fun p =>
      (by fun_prop : Measurable (fun t : ℝ =>
        1 / ((p.1 + t) * (p.2.1 + t) * (p.2.2 + t)))).aestronglyMeasurable)
  · filter_upwards [he] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hrt : 0 < r + t := by positivity
    have h1 : r + t ≤ p.1 + t := by linarith [hp.1]
    have h2 : r + t ≤ p.2.1 + t := by linarith [hp.2.1]
    have h3 : r + t ≤ p.2.2 + t := by linarith [hp.2.2]
    have hd : 0 < (p.1 + t) * (p.2.1 + t) * (p.2.2 + t) :=
      mul_pos (mul_pos (hrt.trans_le h1) (hrt.trans_le h2)) (hrt.trans_le h3)
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd)]
    apply one_div_le_one_div_of_le (by positivity)
    calc
      (r + t) ^ 3 = (r + t) * (r + t) * (r + t) := by ring
      _ ≤ (p.1 + t) * (p.2.1 + t) * (p.2.2 + t) :=
        mul_le_mul (mul_le_mul h1 h2 hrt.le (hrt.trans_le h1).le) h3 hrt.le
          (mul_nonneg (hrt.trans_le h1).le (hrt.trans_le h2).le)
  · exact inv_pow_integrable hr (by norm_num)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    exact continuousAt_const.div (by fun_prop)
      (mul_ne_zero (mul_ne_zero (by positivity : x + t ≠ 0)
        (by positivity : y + t ≠ 0)) (by positivity : z + t ≠ 0))

end D5.S3.Quantum.PositiveResolvent.LogMeanResolvents
