/- GID: D5/S3/Arith/Robin/OriginalMovingCutRow
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalMovingCutRow
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal moving-cut kernel retains its complete signed rows and measurable selection. -/

import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g activationDensity)
open D5.S3.Arith.Robin.OriginalMovingWindowMoment


namespace D5.S3.Arith.Robin.OriginalMovingCutRow

open scoped ENNReal NNReal BigOperators

/-- The right-limit height at the strict lower end of the original window. -/
def lowerHeight (t : ℝ) : ℝ :=
  (g t - g (endpoint t)) / (weight t * t ^ (11 / 10 : ℝ))

/-- The original window averaged over the complete reference interval. -/
def windowMass (ell R x : ℝ) : ℝ := ∫ s in Icc ell R, kernel s x

/-- The part of that same mass before the actual divisor activation clock. -/
def beforeMass (ell R : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  ∫ s in Icc ell R ∩ Iio ((d : ℝ) ^ (500 / 151 : ℝ)), kernel s x

/-- The ratio is zero when the normalizer vanishes. -/
def beforeRatio (ell R : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  beforeMass ell R d x / windowMass ell R x

/-- The weighted moving-cut discrepancy on its literal integer row. -/
def cutRow (ell R t : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  Real.log (x / d) * kernel t x *
    ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) - beforeRatio ell R d x)

private lemma endpoint_le_twice {t : ℝ} (ht : 1 ≤ t) : endpoint t ≤ 2 * t := by
  have hw : width t ≤ t := by
    unfold width
    simpa using Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (4 / 5 : ℝ) ≤ 1)
  dsimp [endpoint]
  linarith

lemma endpoint_strictMonoOn : StrictMonoOn endpoint (Ici (1 : ℝ)) := by
  intro s hs t ht hst
  change 1 ≤ s at hs
  change 1 ≤ t at ht
  have hw : width s ≤ width t := Real.rpow_le_rpow (by linarith [hs] : 0 ≤ s)
    hst.le (by norm_num)
  dsimp [endpoint]
  linarith

lemma kernel_nonneg {t x : ℝ} (ht : 4 ≤ t) : 0 ≤ kernel t x := by
  have hden : 0 < weight t * t ^ (11 / 10 : ℝ) :=
    mul_pos (weight_pos (by linarith)) (Real.rpow_pos_of_pos (by linarith) _)
  unfold kernel
  split_ifs with hx
  · apply div_nonneg _ hden.le
    have h := (price_drop ht hx.1.le hx.2).1
    have hwb : 0 ≤ weight (endpoint t) := (weight_pos (by linarith [hx.1, hx.2])).le
    exact (mul_nonneg hwb (sub_nonneg.mpr hx.2)).trans h
  · exact le_rfl

private lemma height_bounds {t : ℝ} (ht : 4 ≤ t) :
    0 ≤ lowerHeight t ∧ lowerHeight t ≤ t ^ (-3 / 10 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _)
  have hw := weight_pos (by linarith : 1 < t)
  have hp := price_drop ht (le_refl t) htb
  have hden := mul_pos hw (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ))
  constructor
  · exact div_nonneg ((mul_nonneg (weight_pos (by linarith : 1 < endpoint t)).le
      (sub_nonneg.mpr htb)).trans hp.1) hden.le
  · unfold lowerHeight
    apply (div_le_iff₀ hden).2
    calc
      _ ≤ weight t * width t := by simpa [endpoint] using hp.2
      _ = t ^ (-3 / 10 : ℝ) * (weight t * t ^ (11 / 10 : ℝ)) := by
        unfold width
        rw [show t ^ (-3 / 10 : ℝ) * (weight t * t ^ (11 / 10 : ℝ)) =
          weight t * (t ^ (-3 / 10 : ℝ) * t ^ (11 / 10 : ℝ)) by ring,
          ← Real.rpow_add ht0]
        norm_num

private lemma kernel_le_height {t x : ℝ} (ht : 4 ≤ t) :
    kernel t x ≤ lowerHeight t := by
  have ht0 : 0 < t := by linarith
  have hden := mul_pos (weight_pos (by linarith : 1 < t))
    (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ))
  unfold kernel
  split_ifs with hx
  · apply (div_le_div_iff_of_pos_right hden).2
    have h := (price_drop ht (le_refl t) hx.1.le).1
    have hw := weight_pos (by linarith [hx.1] : 1 < x)
    linarith [mul_nonneg hw.le (sub_nonneg.mpr hx.1.le)]
  · exact (height_bounds ht).1

private lemma kernel_pos_iff {t x : ℝ} (ht : 4 ≤ t) :
    0 < kernel t x ↔ t < x ∧ x < endpoint t := by
  have ht0 : 0 < t := by linarith
  have hden := mul_pos (weight_pos (by linarith : 1 < t))
    (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ))
  unfold kernel
  constructor
  · intro h
    split_ifs at h with hx
    · refine ⟨hx.1, hx.2.lt_of_ne ?_⟩
      intro he
      simpa [he] using h
    · exact (lt_irrefl _ h).elim
  · rintro ⟨hx, hxb⟩
    rw [if_pos ⟨hx, hxb.le⟩]
    apply div_pos _ hden
    exact (mul_pos (weight_pos (by linarith : 1 < endpoint t))
      (sub_pos.mpr hxb)).trans_le (price_drop ht hx.le hxb.le).1

private lemma kernel_zero_of_outside {t x : ℝ}
    (hx : x ≤ t ∨ endpoint t ≤ x) : kernel t x = 0 := by
  unfold kernel
  rcases hx with hx | hx
  · rw [if_neg (by simp [not_lt.mpr hx])]
  · by_cases he : x = endpoint t
    · simp [he]
    · rw [if_neg (by grind)]

lemma kernel_le_one {t x : ℝ} (ht : 4 ≤ t) : kernel t x ≤ 1 := by
  exact (kernel_le_height ht).trans ((height_bounds ht).2.trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)))

private lemma measurable_kernel_left (x : ℝ) : Measurable (fun t : ℝ => kernel t x) := by
  unfold kernel g weight endpoint width
  apply Measurable.ite
  · exact (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const
        (show Measurable (fun t : ℝ => t + t ^ (4 / 5 : ℝ)) from
          (continuous_id.add (Real.continuous_rpow_const (by norm_num))).measurable))
  · fun_prop
  · exact measurable_const

lemma kernel_integrableOn {ell R x : ℝ} (hell : 4 ≤ ell) :
    IntegrableOn (fun t => kernel t x) (Icc ell R) := by
  apply (integrableOn_const (C := (1 : ℝ)) (by simp : volume (Icc ell R) ≠ ⊤)).mono'
    (measurable_kernel_left x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg (hell.trans ht.1))]
  exact kernel_le_one (hell.trans ht.1)

private lemma kernel_cross_product {s t x y : ℝ}
    (hs : 4 ≤ s) (hst : s ≤ t) (hx : 4 ≤ x) (hxy : x ≤ y) :
    kernel s y * kernel t x ≤ kernel s x * kernel t y := by
  have ht : 4 ≤ t := hs.trans hst
  have hn : 0 ≤ kernel s x * kernel t y := mul_nonneg (kernel_nonneg hs) (kernel_nonneg ht)
  by_cases hsy : s < y ∧ y ≤ endpoint s
  · by_cases htx : t < x ∧ x ≤ endpoint t
    · have hB : endpoint s ≤ endpoint t :=
        endpoint_strictMonoOn.monotoneOn (by simpa using (show 1 ≤ s by linarith))
          (by simpa using (show 1 ≤ t by linarith)) hst
      have hsx : s < x ∧ x ≤ endpoint s := ⟨lt_of_le_of_lt hst htx.1, hxy.trans hsy.2⟩
      have hty : t < y ∧ y ≤ endpoint t := ⟨htx.1.trans_le hxy, hsy.2.trans hB⟩
      have hs0 : 0 < weight s * s ^ (11 / 10 : ℝ) :=
        mul_pos (weight_pos (by linarith)) (Real.rpow_pos_of_pos (by linarith) _)
      have ht0 : 0 < weight t * t ^ (11 / 10 : ℝ) :=
        mul_pos (weight_pos (by linarith)) (Real.rpow_pos_of_pos (by linarith) _)
      have hgxy : 0 ≤ g x - g y := by
        have h := (price_drop hx (le_refl x) hxy).1
        exact (mul_nonneg (weight_pos (by linarith : 1 < y)).le
          (sub_nonneg.mpr hxy)).trans h
      have hgB : 0 ≤ g (endpoint s) - g (endpoint t) := by
        have hbs : 4 ≤ endpoint s := hs.trans
          (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith : 0 ≤ s) _))
        have h := (price_drop hbs (le_refl _) hB).1
        exact (mul_nonneg (weight_pos (by linarith : 1 < endpoint t)).le
          (sub_nonneg.mpr hB)).trans h
      simp only [kernel, if_pos hsy, if_pos htx, if_pos hsx, if_pos hty]
      rw [div_mul_div_comm, div_mul_div_comm]
      apply (div_le_div_iff_of_pos_right (mul_pos hs0 ht0)).2
      nlinarith [mul_nonneg hgxy hgB]
    · simpa only [kernel, if_neg htx, mul_zero] using hn
  · simpa only [kernel, if_neg hsy, zero_mul] using hn

private def afterMass (ell R : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  ∫ s in Icc ell R \ Iio ((d : ℝ) ^ (500 / 151 : ℝ)), kernel s x

private lemma mass_split {ell R x : ℝ} (hell : 4 ≤ ell) (d : ℕ) :
    beforeMass ell R d x + afterMass ell R d x = windowMass ell R x :=
  integral_inter_add_sdiff measurableSet_Iio (kernel_integrableOn hell)

private lemma beforeRatio_bounds {ell R x : ℝ} (hell : 4 ≤ ell) (d : ℕ)
    (hK : 0 < windowMass ell R x) :
    0 ≤ beforeRatio ell R d x ∧ beforeRatio ell R d x ≤ 1 := by
  have hN : 0 ≤ beforeMass ell R d x := by
    apply setIntegral_nonneg (measurableSet_Icc.inter measurableSet_Iio)
    intro t ht
    exact kernel_nonneg (hell.trans ht.1.1)
  have hL : 0 ≤ afterMass ell R d x := by
    apply setIntegral_nonneg (measurableSet_Icc.diff measurableSet_Iio)
    intro t ht
    exact kernel_nonneg (hell.trans ht.1.1)
  constructor
  · exact div_nonneg hN hK.le
  · apply (div_le_one hK).2
    linarith [mass_split hell d (R := R) (x := x)]

private lemma beforeRatio_antitoneOn_positive {ell R x y : ℝ}
    (hell : 4 ≤ ell) (d : ℕ) (hx : 4 ≤ x) (hxy : x ≤ y)
    (hKx : 0 < windowMass ell R x) (hKy : 0 < windowMass ell R y) :
    beforeRatio ell R d y ≤ beforeRatio ell R d x := by
  let A := Icc ell R ∩ Iio ((d : ℝ) ^ (500 / 151 : ℝ))
  let L := Icc ell R \ Iio ((d : ℝ) ^ (500 / 151 : ℝ))
  have hAx : IntegrableOn (fun t => kernel t x) A :=
    (kernel_integrableOn hell).mono_set inter_subset_left
  have hAy : IntegrableOn (fun t => kernel t y) A :=
    (kernel_integrableOn hell).mono_set inter_subset_left
  have hLx : IntegrableOn (fun t => kernel t x) L :=
    (kernel_integrableOn hell).mono_set sdiff_subset
  have hLy : IntegrableOn (fun t => kernel t y) L :=
    (kernel_integrableOn hell).mono_set sdiff_subset
  have hpoint : ∀ s ∈ A,
      kernel s y * afterMass ell R d x ≤ kernel s x * afterMass ell R d y := by
    intro s hs
    dsimp [afterMass]
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_mono_on (hLx.const_mul _) (hLy.const_mul _)
      (measurableSet_Icc.diff measurableSet_Iio)
    intro t ht
    exact kernel_cross_product (hell.trans hs.1.1)
      (show s ≤ t by dsimp [A, L] at hs ht; exact hs.2.le.trans (not_lt.mp ht.2)) hx hxy
  have hprod : beforeMass ell R d y * afterMass ell R d x ≤
      beforeMass ell R d x * afterMass ell R d y := by
    dsimp [beforeMass]
    rw [← integral_mul_const, ← integral_mul_const]
    exact setIntegral_mono_on (hAy.mul_const _) (hAx.mul_const _)
      (measurableSet_Icc.inter measurableSet_Iio) hpoint
  unfold beforeRatio
  apply (div_le_div_iff₀ hKy hKx).2
  rw [← mass_split hell d (x := x), ← mass_split hell d (x := y)]
  nlinarith only [hprod]

private lemma endpoint_continuous : Continuous endpoint :=
  continuous_id.add (Real.continuous_rpow_const (by norm_num))

private lemma windowMass_pos_of_kernel_pos {ell R t x : ℝ}
    (hell : 4 ≤ ell) (horder : ell < R) (ht : t ∈ Icc ell R)
    (hk : 0 < kernel t x) : 0 < windowMass ell R x := by
  let U : Set ℝ := {s | s < x ∧ x < endpoint s}
  have hU : IsOpen U := (isOpen_lt continuous_id continuous_const).inter
    (isOpen_lt continuous_const endpoint_continuous)
  have htU : t ∈ U := (kernel_pos_iff (hell.trans ht.1)).mp hk
  have htcl : t ∈ closure (Ioo ell R) := by
    rw [closure_Ioo horder.ne]
    exact ht
  have hne : (U ∩ Ioo ell R).Nonempty :=
    mem_closure_iff.mp htcl U hU htU
  have hp : 0 < volume (U ∩ Ioo ell R) := (hU.inter isOpen_Ioo).measure_pos volume hne
  have hsub : U ∩ Ioo ell R ⊆ Function.support (fun s => kernel s x) ∩ Icc ell R := by
    intro s hs
    exact ⟨Function.mem_support.mpr ((kernel_pos_iff (hell.trans hs.2.1.le)).mpr hs.1).ne',
      ⟨hs.2.1.le, hs.2.2.le⟩⟩
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ (kernel_integrableOn hell)).2
  · exact hp.trans_le (measure_mono hsub)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact kernel_nonneg (hell.trans hs.1)

private def logBody (t : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  (Real.log x - Real.log d) *
    (g x - g (endpoint t)) / (weight t * t ^ (11 / 10 : ℝ))

private lemma crossing_label_small {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) : (d : ℝ) ≤ t / 4 := by
  have hB : 1 ≤ endpoint t := by
    have h : t ≤ endpoint t := le_add_of_nonneg_right
      (Real.rpow_nonneg (by linarith : 0 ≤ t) (4 / 5 : ℝ))
    linarith
  calc
    (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ) := hd
    _ ≤ endpoint t ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
    _ ≤ (2 * t) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (endpoint_le_twice (by linarith)) (by norm_num)
    _ ≤ t / 4 := by
      rw [← Real.sqrt_eq_rpow]
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith

private lemma logBody_antitone {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) :
    AntitoneOn (logBody t d) (Icc t (endpoint t)) := by
  have ht0 : 0 < t := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hden : 0 < weight t * t ^ (11 / 10 : ℝ) :=
    mul_pos (weight_pos (by linarith)) (Real.rpow_pos_of_pos ht0 _)
  have hsmall := crossing_label_small ht hcut
  have hD : ∀ x ∈ Icc t (endpoint t), HasDerivAt (logBody t d)
      ((1 / x * (g x - g (endpoint t)) - (Real.log x - Real.log d) * weight x) /
        (weight t * t ^ (11 / 10 : ℝ))) x := by
    intro x hx
    have hx1 : 1 < x := by linarith [hx.1]
    simpa only [logBody, activationDensity, weight, one_div, sub_eq_add_neg, mul_neg] using!
      (((Real.hasDerivAt_log (by linarith : x ≠ 0)).sub_const (Real.log d)).mul
        ((ActualRobinClockCovariance.g_has_deriv_at hx1).sub_const (g (endpoint t)))).div_const
          (weight t * t ^ (11 / 10 : ℝ))
  have hN : ∀ x ∈ Icc t (endpoint t),
      (1 / x * (g x - g (endpoint t)) - (Real.log x - Real.log d) * weight x) /
        (weight t * t ^ (11 / 10 : ℝ)) ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := ht0.trans_le hx.1
    have hx1 : 1 < x := by linarith [hx.1]
    have hlx := Real.log_pos hx1
    have hlog : 1 ≤ Real.log x - Real.log d := by
      rw [← Real.log_div hx0.ne' hd0.ne']
      apply log_large
      exact (le_div_iff₀ hd0).2 (by linarith [hx.1])
    have hw := weight_pos hx1
    have hprice : 0 ≤ g (endpoint t) := by
      unfold g
      exact div_nonneg (by norm_num) (mul_nonneg (hx0.trans_le hx.2).le
        (Real.log_pos (show 1 < endpoint t by linarith [hx.2])).le)
    have hidentity : weight x = (1 / x) * g x + 1 / (x ^ 2 * Real.log x ^ 2) := by
      unfold weight g
      field_simp [hx0.ne', hlx.ne']
    have hder : (1 / x) * g x ≤ weight x := by
      rw [hidentity]
      exact le_add_of_nonneg_right (by positivity)
    apply div_nonpos_of_nonpos_of_nonneg _ hden.le
    nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / x) hprice,
      mul_le_mul_of_nonneg_right hlog hw.le]
  exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    (HasDerivAt.continuousOn hD)
    (fun x hx => (hD x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hN x (interior_subset hx))

private lemma logBody_bounds {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ))
    {x : ℝ} (hx : x ∈ Icc t (endpoint t)) :
    0 ≤ logBody t d x ∧ logBody t d x ≤ lowerHeight t * Real.log (2 * t) := by
  have ht0 : 0 < t := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _)
  have ha := logBody_antitone ht hd hcut
  have hzero : logBody t d (endpoint t) = 0 := by simp [logBody]
  constructor
  · rw [← hzero]
    exact ha hx (right_mem_Icc.mpr htb) hx.2
  · have hlo := ha (left_mem_Icc.mpr htb) hx hx.1
    have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd)
    have hlogt := Real.log_le_log ht0 (show t ≤ 2 * t by linarith)
    have hh := (height_bounds (show 4 ≤ t by linarith)).1
    have hbase : logBody t d t = lowerHeight t * (Real.log t - Real.log d) := by
      unfold logBody lowerHeight
      ring
    rw [hbase] at hlo
    exact hlo.trans (mul_le_mul_of_nonneg_left (by linarith) hh)

private def clampedLogBody (t : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  logBody t d (max t (min x (endpoint t)))

private lemma clampedLogBody_antitone {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) :
    Antitone (clampedLogBody t d) := by
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)
  intro x y hxy
  apply logBody_antitone ht hd hcut
  · exact ⟨le_max_left _ _, max_le htb (min_le_right _ _)⟩
  · exact ⟨le_max_left _ _, max_le htb (min_le_right _ _)⟩
  · exact max_le_max_left _ (min_le_min_right _ hxy)

private lemma clampedLogBody_bounds {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) (x : ℝ) :
    0 ≤ clampedLogBody t d x ∧
      clampedLogBody t d x ≤ lowerHeight t * Real.log (2 * t) := by
  apply logBody_bounds ht hd hcut
  exact ⟨le_max_left _ _, max_le
    (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)) (min_le_right _ _)⟩

private lemma log_kernel_decomposition {t : ℝ} (ht : 256 ≤ t) {d : ℕ} (hd : 1 ≤ d)
    (x : ℝ) : Real.log (x / d) * kernel t x =
      clampedLogBody t d x - (if x ≤ t then logBody t d t else 0) := by
  have ht0 : 0 < t := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have htb : t ≤ endpoint t := le_add_of_nonneg_right (Real.rpow_nonneg ht0.le _)
  by_cases hxt : x ≤ t
  · rw [kernel_zero_of_outside (Or.inl hxt), if_pos hxt]
    simp [clampedLogBody, max_eq_left (le_trans (min_le_left _ _) hxt)]
  · rw [if_neg hxt]
    by_cases hxb : x ≤ endpoint t
    · rw [kernel, if_pos ⟨not_le.mp hxt, hxb⟩,
        Real.log_div (by linarith : x ≠ 0) hd0.ne']
      simp only [clampedLogBody, min_eq_left hxb, max_eq_right (not_le.mp hxt).le,
        logBody, sub_zero]
      ring
    · rw [kernel_zero_of_outside (Or.inr (not_le.mp hxb).le)]
      simp [clampedLogBody, min_eq_right (not_le.mp hxb).le, max_eq_right htb, logBody]


private lemma log_kernel_variation {t : ℝ} (ht : 256 ≤ t) {d : ℕ}
    (hd : 1 ≤ d) (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) :
    eVariationOn (fun x => Real.log (x / d) * kernel t x) univ ≤
      2 * ENNReal.ofReal (lowerHeight t * Real.log (2 * t)) := by
  let Q := lowerHeight t * Real.log (2 * t)
  let h := clampedLogBody t d
  let j : ℝ → ℝ := fun x => if x ≤ t then logBody t d t else 0
  have hjbounds : ∀ x, j x ∈ Icc 0 Q := by
    intro x
    have hb := logBody_bounds ht hd hcut (x := t)
      (left_mem_Icc.mpr (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)))
    dsimp [j]
    split_ifs
    · exact hb
    · exact ⟨le_rfl, (clampedLogBody_bounds ht hd hcut t).1.trans
        (clampedLogBody_bounds ht hd hcut t).2⟩
  have hjanti : Antitone j := by
    intro x y hxy
    dsimp [j]
    split_ifs <;> grind [hjbounds t]
  have hhvar : eVariationOn h univ ≤ ENNReal.ofReal Q := by
    have hbound := eVariationOn.comp_le_of_antitoneOn id (s := Icc 0 Q) h
      ((clampedLogBody_antitone ht hd hcut).antitoneOn univ)
      (fun x _ => clampedLogBody_bounds ht hd hcut x)
    simpa only [Function.id_comp, eVariationOn_id_Icc, sub_zero] using hbound
  have hjvar : eVariationOn j univ ≤ ENNReal.ofReal Q := by
    have hbound := eVariationOn.comp_le_of_antitoneOn id (s := Icc 0 Q) j (hjanti.antitoneOn univ)
      (fun x _ => hjbounds x)
    simpa only [Function.id_comp, eVariationOn_id_Icc, sub_zero] using hbound
  have heq : (fun x => Real.log (x / d) * kernel t x) = fun x => h x - j x := by
    funext x
    exact log_kernel_decomposition ht hd x
  rw [heq, eVariationOn]
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  calc
    _ ≤ (∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i))) +
        ∑ i ∈ Finset.range n, edist (j (u (i + 1))) (j (u i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      simpa only [sub_eq_add_neg, edist_neg_neg] using
        edist_add_add_le (h (u (i + 1))) (-j (u (i + 1))) (h (u i)) (-j (u i))
    _ ≤ ENNReal.ofReal Q + ENNReal.ofReal Q := add_le_add
      ((eVariationOn.sum_le hu hus).trans hhvar) ((eVariationOn.sum_le hu hus).trans hjvar)
    _ = _ := by rw [two_mul]

private def localRatio (ell R t : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  if x ≤ t then 1 else if endpoint t ≤ x then 0 else beforeRatio ell R d x

private lemma localRatio_bounds {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) (d : ℕ) (x : ℝ) : localRatio ell R t d x ∈ Icc 0 1 := by
  unfold localRatio
  split_ifs with hx hB
  · norm_num
  · norm_num
  · have hk : 0 < kernel t x := (kernel_pos_iff (by linarith [ht.1])).mpr
      ⟨not_le.mp hx, not_le.mp hB⟩
    exact beforeRatio_bounds (by linarith) d (windowMass_pos_of_kernel_pos (by linarith)
      horder ht hk)

private lemma localRatio_antitone {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) (d : ℕ) : Antitone (localRatio ell R t d) := by
  intro x y hxy
  by_cases hx : x ≤ t
  · simpa [localRatio, hx] using (localRatio_bounds hell horder ht d y).2
  by_cases hy : endpoint t ≤ y
  · simpa [localRatio, hy, show ¬y ≤ t by
      have hw : 0 < width t := Real.rpow_pos_of_pos (by linarith [ht.1]) _
      dsimp [endpoint] at hy
      linarith] using (localRatio_bounds hell horder ht d x).1
  have hyL : ¬y ≤ t := not_le.mpr ((not_le.mp hx).trans_le hxy)
  have hxR : ¬endpoint t ≤ x := not_le.mpr (hxy.trans_lt (not_le.mp hy))
  simp only [localRatio, if_neg hx, if_neg hyL, if_neg hxR, if_neg hy]
  have hKx := windowMass_pos_of_kernel_pos (by linarith : 4 ≤ ell) horder ht
    ((kernel_pos_iff (by linarith [ht.1] : 4 ≤ t)).mpr ⟨not_le.mp hx, not_le.mp hxR⟩)
  have hKy := windowMass_pos_of_kernel_pos (by linarith : 4 ≤ ell) horder ht
    ((kernel_pos_iff (by linarith [ht.1] : 4 ≤ t)).mpr ⟨not_le.mp hyL, not_le.mp hy⟩)
  exact beforeRatio_antitoneOn_positive (by linarith) d (by linarith [ht.1, not_le.mp hx])
    hxy hKx hKy

private lemma cutRow_eq_local {ell R t : ℝ} (d : ℕ) (x : ℝ) :
    cutRow ell R t d x = Real.log (x / d) * kernel t x *
      ((if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0) - localRatio ell R t d x) := by
  unfold cutRow localRatio
  by_cases hx : x ≤ t
  · simp [hx, kernel_zero_of_outside (Or.inl hx)]
  by_cases hB : endpoint t ≤ x
  · simp [hB, hx, kernel_zero_of_outside (Or.inr hB)]
  · simp [hx, hB]

private lemma cutRow_single_variation {ell R t : ℝ} (hell : 256 ≤ ell) (horder : ell < R)
    (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d)
    (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) :
    eVariationOn (cutRow ell R t d) univ ≤
      ENNReal.ofReal (3 * lowerHeight t * Real.log (2 * t)) := by
  let q : ℝ → ℝ := fun x => Real.log (x / d) * kernel t x
  let c : ℝ := if t < (d : ℝ) ^ (500 / 151 : ℝ) then 1 else 0
  let r := localRatio ell R t d
  let Q : ℝ := lowerHeight t * Real.log (2 * t)
  have ht256 : 256 ≤ t := hell.trans ht.1
  have hQ : 0 ≤ Q := mul_nonneg (height_bounds (by linarith : 4 ≤ t)).1
    (Real.log_nonneg (by linarith))
  have hq : ∀ x ∈ univ, ‖q x‖ₑ ≤ ENNReal.ofReal Q := by
    intro x _
    rw [Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    change |Real.log (x / d) * kernel t x| ≤ Q
    have hb := clampedLogBody_bounds ht256 hd hcut x
    by_cases hx : x ≤ t
    · have hz := kernel_zero_of_outside (t := t) (Or.inl hx)
      change |Real.log (x / d) * kernel t x| ≤ Q
      simp only [hz, mul_zero, abs_zero]
      exact hQ
    · rw [log_kernel_decomposition ht256 hd]
      simpa only [if_neg hx, sub_zero, abs_of_nonneg hb.1] using hb.2
  have hr : ∀ x ∈ univ, ‖c - r x‖ₑ ≤ (1 : ℝ≥0∞) := by
    intro x _
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hb := localRatio_bounds hell horder ht d x
    change 0 ≤ localRatio ell R t d x ∧ localRatio ell R t d x ≤ 1 at hb
    dsimp [c, r]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hrvar : eVariationOn r univ ≤ (1 : ℝ≥0∞) := by
    have hv := eVariationOn.comp_le_of_antitoneOn id (s := Icc 0 1) r
      ((localRatio_antitone hell horder ht d).antitoneOn univ)
      (fun x _ => localRatio_bounds hell horder ht d x)
    simpa only [Function.id_comp, eVariationOn_id_Icc, sub_zero, ENNReal.ofReal_one] using hv
  have hcvar : eVariationOn (fun x => c - r x) univ = eVariationOn r univ := by
    unfold eVariationOn
    congr 1
    funext p
    apply Finset.sum_congr rfl
    intro i _
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      show (c - r (p.2.1 (i + 1))) - (c - r (p.2.1 i)) =
        r (p.2.1 i) - r (p.2.1 (i + 1)) by ring, abs_sub_comm]
  have hprod := eVariation_mul_le hq hr
  have hrow : cutRow ell R t d = q * (fun x => c - r x) := by
    funext x
    exact cutRow_eq_local d x
  rw [hrow]
  apply hprod.trans
  rw [hcvar]
  calc
    _ ≤ ENNReal.ofReal Q * 1 + 1 * (2 * ENNReal.ofReal Q) :=
      by
        gcongr <;> exact log_kernel_variation ht256 hd hcut
    _ = ENNReal.ofReal (3 * lowerHeight t * Real.log (2 * t)) := by
      rw [mul_one, one_mul, show ENNReal.ofReal Q + 2 * ENNReal.ofReal Q =
        3 * ENNReal.ofReal Q by ring, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp [Q]
      ring

private lemma boundedVariation_intervalIntegrable {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (a b : ℝ) : IntervalIntegrable f volume a b := by
  obtain ⟨p, q, hp, hq, heq⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  rw [monotoneOn_univ] at hp hq
  rw [heq]
  exact hp.intervalIntegrable.sub hq.intervalIntegrable

private lemma lattice_cell_error {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    {d : ℝ} (hd : 0 < d) (i : ℕ) :
    |d * f (d * i) - ∫ x in d * i..d * (i + 1), f x| ≤
      d * (eVariationOn f (Icc (d * i) (d * (i + 1)))).toReal := by
  have hi := boundedVariation_intervalIntegrable hf (d * i) (d * (i + 1))
  have hab : d * i ≤ d * (i + 1) := by nlinarith
  let V := (eVariationOn f (Icc (d * i) (d * (i + 1)))).toReal
  have hbd : ∀ x ∈ Icc (d * i) (d * (i + 1)), |f (d * i) - f x| ≤ V := by
    intro x hx
    exact (Real.dist_eq _ _).symm ▸
      (hf.mono (subset_univ _)).dist_le
        (left_mem_Icc.mpr hab) hx
  calc
    _ = |∫ x in d * i..d * (i + 1), f (d * i) - f x| := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const]
      congr 1
      simp only [smul_eq_mul]
      ring
    _ ≤ ∫ x in d * i..d * (i + 1), |f (d * i) - f x| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ _x in d * i..d * (i + 1), V :=
      intervalIntegral.integral_mono_on hab (intervalIntegrable_const.sub hi).abs
        intervalIntegrable_const hbd
    _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]; dsimp [V]; ring

private lemma lattice_error_variation {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    {d : ℝ} (hd : 0 < d) (N : ℕ) :
    |(∑ i ∈ Finset.range N, f (d * i)) - (∫ x in 0..d * N, f x) / d| ≤
      (eVariationOn f univ).toReal := by
  have hstep : Monotone (fun i : ℕ => d * i) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hd.le
  have hsum := eVariationOn.sum' f hstep (n := N)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero] at hsum
  have hfinite : ∀ i ∈ Finset.range N,
      eVariationOn f (Icc (d * i) (d * (i + 1))) ≠ ⊤ :=
    fun i _ => hf.mono (subset_univ _)
  have hsumreal : (∑ i ∈ Finset.range N,
      (eVariationOn f (Icc (d * i) (d * (i + 1)))).toReal) ≤
      (eVariationOn f univ).toReal := by
    rw [← ENNReal.toReal_sum hfinite, hsum]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ (subset_univ _))
  have hpieces : (∑ i ∈ Finset.range N, ∫ x in d * i..d * (i + 1), f x) =
      ∫ x in 0..d * N, f x := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero] using
      intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => d * (i : ℝ)) (n := N)
      (fun i (_hi : i < N) => by
        simpa only [Nat.cast_add, Nat.cast_one] using
          boundedVariation_intervalIntegrable hf (d * i) (d * (i + 1)))
  have htotal : |d * (∑ i ∈ Finset.range N, f (d * i)) - ∫ x in 0..d * N, f x| ≤
      d * (eVariationOn f univ).toReal := by
    rw [← hpieces, Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ Finset.range N, |d * f (d * i) - ∫ x in d * i..d * (i + 1), f x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N,
          d * (eVariationOn f (Icc (d * i) (d * (i + 1)))).toReal :=
        Finset.sum_le_sum (fun i _ => lattice_cell_error hf hd i)
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsumreal hd.le
  have heq : |d * (∑ i ∈ Finset.range N, f (d * i)) - ∫ x in 0..d * N, f x| =
      d * |(∑ i ∈ Finset.range N, f (d * i)) - (∫ x in 0..d * N, f x) / d| := by
    calc
      _ = |d * ((∑ i ∈ Finset.range N, f (d * i)) -
          (∫ x in 0..d * N, f x) / d)| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hd]
  rw [heq] at htotal
  exact (mul_le_mul_iff_right₀ hd).mp htotal

/- The complete small-label row has a definite sign.  This isolates the
   only sign change in a moving-cut row at the actual cutoff clock, while
   retaining the literal posterior ratio. -/
theorem cutRow_sign_of_small_label {ell R t : ℝ} (hell : 256 ≤ ell)
    (horder : ell < R) (ht : t ∈ Icc ell R) {d : ℕ} (hd : 1 ≤ d)
    (hcut : (d : ℝ) ≤ endpoint t ^ (151 / 500 : ℝ)) (x : ℝ) :
    (t < (d : ℝ) ^ (500 / 151 : ℝ) → 0 ≤ cutRow ell R t d x) ∧
      (¬t < (d : ℝ) ^ (500 / 151 : ℝ) → cutRow ell R t d x ≤ 0) := by
  have ht256 : 256 ≤ t := hell.trans ht.1
  have ht4 : 4 ≤ t := by linarith
  have hK : 0 ≤ kernel t x := kernel_nonneg ht4
  by_cases hz : kernel t x = 0
  · simp [cutRow, hz]
  have hk : 0 < kernel t x := lt_of_le_of_ne hK (Ne.symm hz)
  have hpos := (kernel_pos_iff ht4).mp hk
  have hsmall := crossing_label_small ht256 hcut
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hx0 : 0 < x := by linarith [hpos.1]
  have hxd : (1 : ℝ) ≤ x / d := by
    apply (le_div_iff₀ hd0).2
    nlinarith [hsmall, hpos.1, ht4]
  have hlog : 0 ≤ Real.log (x / d) := Real.log_nonneg hxd
  have hratio := localRatio_bounds hell horder ht d x
  constructor
  · intro hactive
    rw [cutRow_eq_local]
    simp only [if_pos hactive]
    exact mul_nonneg (mul_nonneg hlog hK) (sub_nonneg.mpr hratio.2)
  · intro hinactive
    rw [cutRow_eq_local]
    simp only [if_neg hinactive, zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hlog hK)
      (neg_nonpos.mpr hratio.1)


end D5.S3.Arith.Robin.OriginalMovingCutRow
