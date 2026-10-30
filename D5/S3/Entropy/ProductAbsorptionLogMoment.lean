/- GID: D5/S3/Entropy/ProductAbsorptionLogMoment
   generality: G
   mirror-B: D5/B/S3/Entropy/ProductAbsorptionLogMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nonnegative exact logarithmic first moment for binary product absorption. -/

import D5.S3.Entropy.ProductAbsorptionLogIntegral
import D5.S3.Entropy.BinaryEntropyLogIntegral
import D5.S3.QuantumChannels.ContractionSpectrumOrder
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

noncomputable section
namespace D5.S3.Entropy.ProductAbsorptionLogMoment
open Set Filter MeasureTheory
open scoped Topology
open D5.S3.Entropy.ProductAbsorptionLogIntegral
open D5.S3.Entropy.BinaryEntropyLogIntegral
open D5.S3.QuantumChannels.ContractionSpectrumOrder (hasDerivAt_artanh)

private def artanhRemainder (r : ℝ) : ℝ :=
  (r - (2 / 3 : ℝ) * r ^ 3) / (1 - r ^ 2) - Real.artanh r

private lemma artanh_remainder_hasDerivAt {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt artanhRemainder
      ((2 / 3 : ℝ) * r ^ 4 / (1 - r ^ 2) ^ 2) r := by
  have hden : 0 < 1 - r ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 + r by linarith [hr.1])
      (show 0 < 1 - r by linarith [hr.2])]
  have h := (((hasDerivAt_id r).sub
    (((hasDerivAt_id r).pow 3).const_mul (2 / 3 : ℝ))).div
    ((hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2)) hden.ne').sub
    (hasDerivAt_artanh hr)
  convert h using 1
  · rfl
  · field_simp [hden.ne']
    <;> ring

private lemma artanh_cubic_gap {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    (2 / 3 : ℝ) * r ^ 3 ≤ r - (1 - r ^ 2) * Real.artanh r := by
  have hd : ∀ t ∈ Icc (0 : ℝ) r,
      HasDerivAt artanhRemainder ((2 / 3 : ℝ) * t ^ 4 / (1 - t ^ 2) ^ 2) t := by
    intro t ht
    exact artanh_remainder_hasDerivAt ⟨by linarith [ht.1], ht.2.trans_lt hr.2⟩
  have hm : MonotoneOn artanhRemainder (Icc 0 r) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    positivity
  have hh := hm ⟨le_rfl, hr.1⟩ ⟨hr.1, le_rfl⟩ hr.1
  have hzero : artanhRemainder 0 = 0 := by simp [artanhRemainder]
  rw [hzero] at hh
  have hden : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hupper : Real.artanh r ≤ (r - (2 / 3 : ℝ) * r ^ 3) / (1 - r ^ 2) := by
    dsimp [artanhRemainder] at hh
    linarith
  have hh' := (le_div_iff₀ hden).mp hupper
  nlinarith

private def pairLog (d s : ℝ) : ℝ :=
  let q := Real.sqrt (s ^ 2 - d ^ 2)
  ((s + q) * Real.log (s + q) + (s - q) * Real.log (s - q)) / 2

private def pairSlope (d s : ℝ) : ℝ :=
  if d = 0 then Real.log (2 * s) + 1 else
    1 + Real.log d + (s / Real.sqrt (s ^ 2 - d ^ 2)) *
      Real.artanh (Real.sqrt (s ^ 2 - d ^ 2) / s)

private def pairCurvature (d s : ℝ) : ℝ :=
  if d = 0 then 1 / s else
    let r := Real.sqrt (s ^ 2 - d ^ 2) / s
    (r - (1 - r ^ 2) * Real.artanh r) / (s * r ^ 3)

private lemma pair_continuous (d : ℝ) : Continuous (pairLog d) := by
  have hq : Continuous (fun s : ℝ => Real.sqrt (s ^ 2 - d ^ 2)) := by fun_prop
  exact (((continuous_id.add hq).mul_log).add ((continuous_id.sub hq).mul_log)).div_const 2

private lemma pair_zero {s : ℝ} (hs : 0 ≤ s) : pairLog 0 s = s * Real.log (2 * s) := by
  simp only [pairLog, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hs, sub_self, zero_mul, add_zero]
  ring

private lemma pair_positive_data {d s : ℝ} (hd : 0 < d) (hs : d < s) :
    let q := Real.sqrt (s ^ 2 - d ^ 2)
    0 < s ∧ 0 < q ∧ q < s ∧ q ^ 2 = s ^ 2 - d ^ 2 ∧
      q / s ∈ Ioo (0 : ℝ) 1 := by
  have hsp : 0 < s := hd.trans hs
  have hdisc : 0 < s ^ 2 - d ^ 2 := by nlinarith
  have hq := Real.sqrt_pos.mpr hdisc
  have hq2 := Real.sq_sqrt hdisc.le
  have hqs : Real.sqrt (s ^ 2 - d ^ 2) < s := by nlinarith [sq_pos_of_pos hd]
  exact ⟨hsp, hq, hqs, hq2, div_pos hq hsp, (div_lt_one hsp).mpr hqs⟩

private lemma root_hasDerivAt {d s : ℝ} (hd : 0 < d) (hs : d < s) :
    HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 - d ^ 2))
      (s / Real.sqrt (s ^ 2 - d ^ 2)) s := by
  obtain ⟨_, hq, _, hq2, _⟩ := pair_positive_data hd hs
  have h := (((hasDerivAt_id s).pow 2).sub_const (d ^ 2)).sqrt
    (show s ^ 2 - d ^ 2 ≠ 0 by rw [← hq2]; positivity)
  convert h using 1
  · field_simp [hq.ne']
    <;> ring

private lemma root_artanh_identity {d s : ℝ} (hd : 0 < d) (hs : d < s) :
    let q := Real.sqrt (s ^ 2 - d ^ 2)
    Real.artanh (q / s) = (Real.log (s + q) - Real.log (s - q)) / 2 := by
  obtain ⟨hsp, hq, hqs, _, hr⟩ := pair_positive_data hd hs
  let q := Real.sqrt (s ^ 2 - d ^ 2)
  have hp : 0 < s + q := by dsimp [q]; linarith
  have hm : 0 < s - q := by dsimp [q]; linarith
  have hp' : 0 < 1 + q / s := by dsimp [q]; positivity
  have hm' : 0 < 1 - q / s := by dsimp [q]; linarith [hr.2]
  change Real.artanh (q / s) = _
  rw [Real.artanh_eq_half_log ⟨by linarith [hr.1], hr.2.le⟩,
    Real.log_div hp'.ne' hm'.ne',
    show 1 + q / s = (s + q) / s by field_simp [hsp.ne']; ring,
    show 1 - q / s = (s - q) / s by field_simp [hsp.ne']; ring,
    Real.log_div hp.ne' hsp.ne', Real.log_div hm.ne' hsp.ne']
  ring

private lemma pair_hasDerivAt {d s : ℝ} (hd : 0 ≤ d) (hs : d < s) :
    HasDerivAt (pairLog d) (pairSlope d s) s := by
  by_cases hd0 : d = 0
  · subst d
    have hsp : 0 < s := hs
    have h := (((hasDerivAt_id s).mul_const (Real.log 2)).add
      (Real.hasDerivAt_mul_log hsp.ne'))
    have he : pairLog 0 =ᶠ[𝓝 s]
        (fun t : ℝ => t * Real.log 2 + t * Real.log t) := by
      filter_upwards [eventually_gt_nhds hsp] with t ht
      rw [pair_zero ht.le, Real.log_mul (by norm_num) ht.ne']
      ring
    apply (h.congr_of_eventuallyEq he).congr_deriv
    simp only [pairSlope, if_pos rfl]
    rw [Real.log_mul (by norm_num) hsp.ne']
    ring
  · have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    obtain ⟨hsp, hq, hqs, hq2, _⟩ := pair_positive_data hdp hs
    let q := Real.sqrt (s ^ 2 - d ^ 2)
    have hp : 0 < s + q := by dsimp [q]; linarith
    have hm : 0 < s - q := by dsimp [q]; linarith
    have hplus := (Real.hasDerivAt_mul_log hp.ne').comp s
      ((hasDerivAt_id s).add (root_hasDerivAt hdp hs))
    have hminus := (Real.hasDerivAt_mul_log hm.ne').comp s
      ((hasDerivAt_id s).sub (root_hasDerivAt hdp hs))
    have hprod : (s + q) * (s - q) = d ^ 2 := by dsimp [q]; nlinarith
    have hsum : Real.log (s + q) + Real.log (s - q) = 2 * Real.log d := by
      rw [← Real.log_mul hp.ne' hm.ne', hprod, Real.log_pow]
    have ha := root_artanh_identity hdp hs
    convert (hplus.add hminus).div_const 2 using 1
    · rfl
    · dsimp only [pairSlope]
      rw [if_neg hd0, ha]
      have hlm : Real.log (s - q) = 2 * Real.log d - Real.log (s + q) := by
        linarith
      rw [hlm]
      field_simp [hq.ne']
      ring

private lemma pair_slope_hasDerivAt {d s : ℝ} (hd : 0 ≤ d) (hs : d < s) :
    HasDerivAt (pairSlope d) (pairCurvature d s) s := by
  by_cases hd0 : d = 0
  · subst d
    have hsp : 0 < s := hs
    have h := ((((hasDerivAt_id s).const_mul 2).log
      (show (2 : ℝ) * s ≠ 0 by positivity)).add_const 1)
    convert h using 1
    · funext t
      simp [pairSlope]
    · dsimp [pairCurvature]
      field_simp [hsp.ne']
      <;> ring
  · have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    obtain ⟨hsp, hq, hqs, hq2, hr⟩ := pair_positive_data hdp hs
    let q := Real.sqrt (s ^ 2 - d ^ 2)
    have hden : 0 < 1 - (q / s) ^ 2 := by
      dsimp [q]
      nlinarith [hr.1, hr.2]
    have hroot := root_hasDerivAt hdp hs
    have hquot := (hasDerivAt_id s).div hroot hq.ne'
    have hratio := hroot.div (hasDerivAt_id s) hsp.ne'
    have hat := (hasDerivAt_artanh ⟨by linarith [hr.1], hr.2⟩).comp s hratio
    have h := ((hasDerivAt_const s (1 + Real.log d)).add (hquot.mul hat))
    convert h using 1
    · funext t
      simp only [pairSlope, if_neg hd0]
    · dsimp only [pairCurvature]
      rw [if_neg hd0]
      dsimp only
      field_simp [hsp.ne', hq.ne', hden.ne']
      have hd2 : d ^ 2 = s ^ 2 - q ^ 2 := by dsimp [q]; linarith
      rw [hd2]
      ring

private lemma pair_curvature_lower {d s : ℝ} (hd : 0 ≤ d) (hs : d < s) :
    (2 : ℝ) / (3 * s) ≤ pairCurvature d s := by
  have hsp : 0 < s := hd.trans_lt hs
  by_cases hd0 : d = 0
  · simp only [pairCurvature, if_pos hd0]
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * s) hsp).mpr
    linarith
  · have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    obtain ⟨_, _, _, _, hr⟩ := pair_positive_data hdp hs
    let r := Real.sqrt (s ^ 2 - d ^ 2) / s
    have hb := artanh_cubic_gap ⟨hr.1.le, hr.2⟩
    have hden : 0 < s * r ^ 3 := mul_pos hsp (pow_pos hr.1 3)
    have he : (2 : ℝ) / (3 * s) * (s * r ^ 3) = (2 / 3 : ℝ) * r ^ 3 := by
      field_simp [hsp.ne']
      <;> ring
    dsimp only [pairCurvature]
    rw [if_neg hd0]
    apply (le_div_iff₀ hden).mpr
    rw [he]
    exact hb

private lemma entropy_linear_lower {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    x * Real.log 2 ≤ Real.binEntropy ((1 + Real.sqrt (1 - x)) / 2) := by
  have hxI := binEntropy_sqrt_log_integral hx
  have h1I := binEntropy_sqrt_log_integral (x := 1) (by norm_num)
  have he1 : Real.binEntropy ((1 + Real.sqrt (1 - (1 : ℝ))) / 2) = Real.log 2 := by
    norm_num
  rw [he1] at h1I
  have hlog : ∀ s ∈ Ioi (0 : ℝ),
      x * Real.log (1 + 1 / s) ≤ Real.log (1 + x / s) := by
    intro s hs
    have hp : (1 : ℝ) ∈ Ioi 0 := by norm_num
    have hq : 1 + 1 / s ∈ Ioi (0 : ℝ) := by positivity
    have hj := Real.concaveOn_log.2 hp hq (sub_nonneg.mpr hx.2) hx.1
      (show (1 - x) + x = (1 : ℝ) by ring)
    have he : (1 - x) * 1 + x * (1 + 1 / s) = 1 + x / s := by ring
    simpa only [smul_eq_mul, Real.log_one, mul_zero, zero_add, he] using hj
  have hm : (∫ s in Ioi (0 : ℝ), x * (Real.log (1 + 1 / s) / Real.sqrt (1 + s))) ≤
      ∫ s in Ioi (0 : ℝ), Real.log (1 + x / s) / Real.sqrt (1 + s) := by
    apply integral_mono_ae (h1I.1.const_mul x) hxI.1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right (hlog s hs) (Real.sqrt_nonneg (1 + s))
  rw [integral_const_mul] at hm
  have he := congrArg (fun z : ℝ => x * z) h1I.2
  nlinarith [hxI.2]

private def normalizedGap (p t : ℝ) : ℝ :=
  Real.binEntropy p + 2 * ((1 - t) * Real.log (1 - t)) - pairLog (1 - 2 * p) (1 - 2 * t)

private def gapSlope (p t : ℝ) : ℝ :=
  -2 * (Real.log (1 - t) + 1) + 2 * pairSlope (1 - 2 * p) (1 - 2 * t)

private def gapCurvature (p t : ℝ) : ℝ :=
  2 / (1 - t) - 4 * pairCurvature (1 - 2 * p) (1 - 2 * t)

private lemma gap_continuous (p : ℝ) : Continuous (normalizedGap p) := by
  have hml := Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  have hp := (pair_continuous (1 - 2 * p)).comp
    (continuous_const.sub (continuous_id.const_mul 2))
  exact (continuous_const.add (hml.const_mul 2)).sub hp

private lemma gap_hasDerivAt {p t : ℝ} (hp : p ∈ Ioc (0 : ℝ) (1 / 2))
    (ht : t ∈ Ioo (0 : ℝ) p) : HasDerivAt (normalizedGap p) (gapSlope p t) t := by
  have hpt : 0 < 1 - t := by linarith [hp.2, ht.2]
  have hd : 0 ≤ 1 - 2 * p := by linarith [hp.2]
  have hst : 1 - 2 * p < 1 - 2 * t := by linarith [ht.2]
  have hml := (Real.hasDerivAt_mul_log hpt.ne').comp t ((hasDerivAt_id t).const_sub 1)
  have hpair := (pair_hasDerivAt hd hst).comp t (((hasDerivAt_id t).const_mul 2).const_sub 1)
  have h := ((hasDerivAt_const t (Real.binEntropy p)).add (hml.const_mul 2)).sub hpair
  convert h using 1
  · rfl
  · dsimp only [gapSlope]
    ring

private lemma gap_slope_hasDerivAt {p t : ℝ} (hp : p ∈ Ioc (0 : ℝ) (1 / 2))
    (ht : t ∈ Ioo (0 : ℝ) p) : HasDerivAt (gapSlope p) (gapCurvature p t) t := by
  have hpt : 0 < 1 - t := by linarith [hp.2, ht.2]
  have hd : 0 ≤ 1 - 2 * p := by linarith [hp.2]
  have hst : 1 - 2 * p < 1 - 2 * t := by linarith [ht.2]
  have hlog := (((hasDerivAt_id t).const_sub 1).log hpt.ne').add_const 1
  have hpair := (pair_slope_hasDerivAt hd hst).comp t
    (((hasDerivAt_id t).const_mul 2).const_sub 1)
  have h := (hlog.const_mul (-2)).add (hpair.const_mul 2)
  convert h using 1
  · rfl
  · dsimp only [gapCurvature]
    ring

private lemma gap_concave {p : ℝ} (hp : p ∈ Ioc (0 : ℝ) (1 / 2)) :
    ConcaveOn ℝ (Icc 0 p) (normalizedGap p) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 p) (gap_continuous p).continuousOn
    (fun t ht => (gap_hasDerivAt hp (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
    (fun t ht => (gap_slope_hasDerivAt hp (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
  intro t ht
  have ht' : t ∈ Ioo (0 : ℝ) p := by simpa only [interior_Icc] using ht
  have hpt : 0 < 1 - t := by linarith [hp.2, ht'.2]
  have hst : 0 < 1 - 2 * t := by linarith [hp.2, ht'.2]
  have hb := pair_curvature_lower (show 0 ≤ 1 - 2 * p by linarith [hp.2])
    (show 1 - 2 * p < 1 - 2 * t by linarith [ht'.2])
  have hf : (2 : ℝ) / (1 - t) ≤ 8 / (3 * (1 - 2 * t)) := by
    apply (div_le_div_iff₀ hpt (show 0 < 3 * (1 - 2 * t) by positivity)).mpr
    nlinarith [ht'.1]
  have he : (4 : ℝ) * (2 / (3 * (1 - 2 * t))) = 8 / (3 * (1 - 2 * t)) := by ring
  dsimp only [gapCurvature]
  linarith

private lemma mul_log_scale {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (a * x) * Real.log (a * x) = a * (x * Real.log x) + a * x * Real.log a := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_mul ha.ne' hx]
    ring

private lemma bias_entropy_identity (r : ℝ) :
    ((1 + r) * Real.log (1 + r) + (1 - r) * Real.log (1 - r)) / 2 =
      Real.log 2 - Real.binEntropy ((1 + r) / 2) := by
  have hp := mul_log_scale (a := 2) (by norm_num) ((1 + r) / 2)
  have hm := mul_log_scale (a := 2) (by norm_num) ((1 - r) / 2)
  rw [show 2 * ((1 + r) / 2) = 1 + r by ring] at hp
  rw [show 2 * ((1 - r) / 2) = 1 - r by ring] at hm
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1 - (1 + r) / 2 = (1 - r) / 2 by ring]
  simp only [Real.negMulLog_def]
  linarith

private lemma gap_zero_nonneg {p : ℝ} (hp : p ∈ Ioc (0 : ℝ) (1 / 2)) :
    0 ≤ normalizedGap p 0 := by
  let d := 1 - 2 * p
  have hd : 0 ≤ d := by dsimp [d]; linarith [hp.2]
  have hd1 : d ≤ 1 := by dsimp [d]; linarith [hp.1]
  have hsq : d ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg _, by nlinarith⟩
  have hcomp : 1 - d ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hsq.2], by nlinarith⟩
  have hleft := entropy_linear_lower hcomp
  have hright := entropy_linear_lower hsq
  have hsqrt : Real.sqrt (1 - (1 - d ^ 2)) = d := by
    rw [show 1 - (1 - d ^ 2) = d ^ 2 by ring, Real.sqrt_sq hd]
  rw [hsqrt, show (1 + d) / 2 = 1 - p by dsimp [d]; ring,
    Real.binEntropy_one_sub] at hleft
  have he := bias_entropy_identity (Real.sqrt (1 - d ^ 2))
  dsimp only [normalizedGap, pairLog]
  simp only [mul_zero, sub_zero, Real.log_one, mul_one, zero_mul, add_zero,
    one_pow]
  change 0 ≤ Real.binEntropy p -
    ((1 + Real.sqrt (1 - d ^ 2)) * Real.log (1 + Real.sqrt (1 - d ^ 2)) +
      (1 - Real.sqrt (1 - d ^ 2)) * Real.log (1 - Real.sqrt (1 - d ^ 2))) / 2
  linarith

private lemma gap_endpoint_nonneg {p : ℝ} (hp : p ∈ Ioc (0 : ℝ) (1 / 2)) :
    0 ≤ normalizedGap p p := by
  let m := 1 - p
  let d := 1 - 2 * p
  have hm : 0 < m := by dsimp [m]; linarith [hp.2]
  have hd : 0 ≤ d := by dsimp [d]; linarith [hp.2]
  have hr : p / m ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hp.1.le hm.le, (div_le_one hm).mpr (by dsimp [m]; linarith [hp.2])⟩
  have hscale1 := mul_log_scale hm (p / m)
  have hscale2 := mul_log_scale hm (1 - p / m)
  have he1 : m * (p / m) = p := by field_simp [hm.ne']
  have he2 : m * (1 - p / m) = d := by dsimp [d, m] at *; field_simp [hm.ne']; ring
  rw [he1] at hscale1
  rw [he2] at hscale2
  have hpair : pairLog d d = d * Real.log d := by
    simp only [pairLog, sub_self, Real.sqrt_zero, add_zero, sub_zero]
    ring
  change 0 ≤ Real.binEntropy p + 2 * ((1 - p) * Real.log (1 - p)) - pairLog d d
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  rw [hpair]
  have he : m * Real.binEntropy (p / m) =
      -(p * Real.log p) + m * Real.log m - d * Real.log d := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog_def]
    calc
      _ = -(p * Real.log p) - d * Real.log d + (p + d) * Real.log m := by
        nlinarith [hscale1, hscale2]
      _ = _ := by dsimp [m, d]; ring
  have hnonneg : 0 ≤ -(p * Real.log p) + m * Real.log m - d * Real.log d := by
    rw [← he]
    exact mul_nonneg hm.le (Real.binEntropy_nonneg hr.1 hr.2)
  dsimp [m] at hnonneg
  linarith

private lemma gap_nonneg {p t : ℝ} (hp : p ∈ Ioc (0 : ℝ) (1 / 2))
    (ht : t ∈ Icc (0 : ℝ) p) : 0 ≤ normalizedGap p t := by
  have h := (gap_concave hp).min_le_of_mem_Icc
    (show (0 : ℝ) ∈ Icc 0 p from ⟨le_rfl, hp.1.le⟩)
    (show p ∈ Icc (0 : ℝ) p from ⟨hp.1.le, le_rfl⟩) ht
  exact (le_min (gap_zero_nonneg hp) (gap_endpoint_nonneg hp)).trans h

private lemma interior_moment_nonneg {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1)
    (hv : v ∈ Ioo (0 : ℝ) 1) (huv : u ≤ v) : 0 ≤ productLogMoment u v := by
  let A := u + v
  let B := u * v
  let p := u / A
  let t := B / A
  let d := 1 - 2 * p
  let s := 1 - 2 * t
  let q := Real.sqrt (B * (1 - A + B))
  let r := Real.sqrt (s ^ 2 - d ^ 2)
  let L := A - B
  let mp := A - 2 * B + 2 * q
  let mm := A - 2 * B - 2 * q
  have hA : 0 < A := add_pos hu.1 hv.1
  have hB : 0 < B := mul_pos hu.1 hv.1
  have hp : p ∈ Ioc (0 : ℝ) (1 / 2) := by
    refine ⟨div_pos hu.1 hA, (div_le_iff₀ hA).mpr ?_⟩
    dsimp [A]
    linarith
  have ht : t ∈ Icc (0 : ℝ) p := by
    refine ⟨(div_pos hB hA).le, ?_⟩
    apply (div_le_div_iff_of_pos_right hA).mpr
    dsimp [B]
    nlinarith [mul_pos hu.1 (sub_pos.mpr hv.2)]
  have hd : 0 ≤ d := by dsimp [d]; linarith [hp.2]
  have hds : d ≤ s := by dsimp [d, s]; linarith [ht.2]
  have hs : 0 ≤ s := hd.trans hds
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = s ^ 2 - d ^ 2 := Real.sq_sqrt (by nlinarith)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = B * (1 - A + B) := by
    apply Real.sq_sqrt
    apply mul_nonneg hB.le
    have h := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2)
    dsimp [A, B]
    nlinarith
  have hAr2 : (A * r) ^ 2 = (2 * q) ^ 2 := by
    rw [mul_pow, hr2, mul_pow, hq2]
    dsimp [s, d, p, t, A, B]
    field_simp [hA.ne']
    <;> ring
  have hAr : A * r = 2 * q := by nlinarith [mul_nonneg hA.le hr]
  have hAp : A * p = u := by dsimp [p]; field_simp [hA.ne']
  have hAm : A * (1 - p) = v := by dsimp [p, A]; field_simp [hA.ne']; ring
  have hAt : A * (1 - t) = L := by dsimp [t, L]; field_simp [hA.ne']; ring
  have hAs : A * s = A - 2 * B := by dsimp [s, t]; field_simp [hA.ne']; ring
  have hplus : A * (s + r) = mp := by dsimp [mp]; nlinarith
  have hminus : A * (s - r) = mm := by dsimp [mm]; nlinarith
  have hpLog := mul_log_scale hA p
  have hmLog := mul_log_scale hA (1 - p)
  have htLog := mul_log_scale hA (1 - t)
  have hplusLog := mul_log_scale hA (s + r)
  have hminusLog := mul_log_scale hA (s - r)
  rw [hAp] at hpLog
  rw [hAm] at hmLog
  rw [hAt] at htLog
  rw [hplus] at hplusLog
  rw [hminus] at hminusLog
  have he : productLogMoment u v = A * normalizedGap p t := by
    change 2 * L * Real.log L - u * Real.log u - v * Real.log v -
      (mp * Real.log mp + mm * Real.log mm) / 2 =
      A * (Real.binEntropy p + 2 * ((1 - t) * Real.log (1 - t)) -
        ((s + r) * Real.log (s + r) + (s - r) * Real.log (s - r)) / 2)
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog_def]
    have hsum : u + v = A := rfl
    have hcancel : -A + 2 * L - (mp + mm) / 2 = 0 := by dsimp [L, mp, mm]; ring
    have hlogcancel : (u + v - 2 * L + (mp + mm) / 2) * Real.log A = 0 := by
      rw [hsum]
      have hcoeff : A - 2 * L + (mp + mm) / 2 = 0 := by linarith
      rw [hcoeff, zero_mul]
    nlinarith [hpLog, hmLog, htLog, hplusLog, hminusLog, hlogcancel]
  rw [he]
  exact mul_nonneg hA.le (gap_nonneg hp ht)

private lemma moment_symm (u v : ℝ) : productLogMoment u v = productLogMoment v u := by
  unfold productLogMoment
  rw [show v + u = u + v by ring, show v * u = u * v by ring]
  ring

private lemma moment_zero_left (v : ℝ) : productLogMoment 0 v = 0 := by
  simp only [productLogMoment, zero_add, zero_mul, Real.sqrt_zero, mul_zero,
    add_zero, sub_zero]
  ring

private lemma moment_one_left (v : ℝ) : productLogMoment 1 v = Real.binEntropy v := by
  simp only [productLogMoment, one_mul,
    show v * (1 - (1 + v) + v) = 0 by ring,
    Real.sqrt_zero, mul_zero, add_zero, sub_zero,
    show 1 + v - v = 1 by ring, show 1 + v - 2 * v = 1 - v by ring,
    Real.log_one, mul_one]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  ring

/-- The exact logarithmic first moment of the five-term product kernel is
nonnegative on the entire closed parameter square. In particular, zero roots,
coincident roots and all four edges are included without a rank assumption. -/
theorem product_log_moment_nonneg {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) : 0 ≤ productLogMoment u v := by
  by_cases hu0 : u = 0
  · subst u
    rw [moment_zero_left]
  by_cases hu1 : u = 1
  · subst u
    rw [moment_one_left]
    exact Real.binEntropy_nonneg hv.1 hv.2
  by_cases hv0 : v = 0
  · subst v
    rw [moment_symm, moment_zero_left]
  by_cases hv1 : v = 1
  · subst v
    rw [moment_symm, moment_one_left]
    exact Real.binEntropy_nonneg hu.1 hu.2
  have hu' : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), lt_of_le_of_ne hu.2 hu1⟩
  have hv' : v ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), lt_of_le_of_ne hv.2 hv1⟩
  rcases le_total u v with huv | hvu
  · exact interior_moment_nonneg hu' hv' huv
  · rw [moment_symm]
    exact interior_moment_nonneg hv' hu' hvu

#print axioms product_log_moment_nonneg

end D5.S3.Entropy.ProductAbsorptionLogMoment
