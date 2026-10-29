/- GID: D5/S3/Arith/Robin/ForwardKernel/Remainder
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/Remainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inverse coordinates retain quantitative scale control for the forward Robin kernel. -/

import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Arith.Robin.ForwardKernel.Remainder

open OriginalMovingWindowMoment (width endpoint)
open MellinWeightedVariation (weight)

private def coordinateMap (z x : ℝ) : ℝ := x + z * width (max x 0)

/-- The inverse coordinate in t=x+z*x^(4/5), on the positive half-line. -/
def coordinate (t z : ℝ) : ℝ := Function.invFun (coordinateMap z) t

private lemma map_strictMono {z : ℝ} (hz : 0 ≤ z) : StrictMono (coordinateMap z) := by
  intro x y hxy
  have hp : width (max x 0) ≤ width (max y 0) :=
    Real.rpow_le_rpow (le_max_right x 0) (max_le_max hxy.le le_rfl) (by norm_num)
  dsimp [coordinateMap]
  linarith [mul_le_mul_of_nonneg_left hp hz]

private lemma map_surjective {z : ℝ} (hz : 0 ≤ z) : Function.Surjective (coordinateMap z) := by
  intro t
  by_cases ht : t ≤ 0
  · refine ⟨t, ?_⟩
    simp [coordinateMap, max_eq_right ht, width, Real.zero_rpow (by norm_num : (4 / 5 : ℝ) ≠ 0)]
  · have ht0 : 0 ≤ t := (lt_of_not_ge ht).le
    have hc : ContinuousOn (coordinateMap z) (Icc 0 t) := by
      unfold coordinateMap width
      exact (continuous_id.add (continuous_const.mul
        ((continuous_id.max continuous_const).rpow_const
          (fun _ => Or.inr (by norm_num))))).continuousOn
    have h0 : coordinateMap z 0 = 0 := by
      simp [coordinateMap, width, Real.zero_rpow (by norm_num : (4 / 5 : ℝ) ≠ 0)]
    have ht' : t ≤ coordinateMap z t := by
      exact le_add_of_nonneg_right (mul_nonneg hz (Real.rpow_nonneg (by positivity) _))
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc ht0 hc ⟨by simpa [h0] using ht0, ht'⟩
    exact ⟨x, hx⟩

private lemma coordinate_spec {z : ℝ} (hz : 0 ≤ z) (t : ℝ) :
    coordinateMap z (coordinate t z) = t :=
  Function.rightInverse_invFun (map_surjective hz) t

private lemma coordinate_strictMono {z : ℝ} (hz : 0 ≤ z) :
    StrictMono (fun t => coordinate t z) := by
  intro a b hab
  by_contra h
  have h' := (map_strictMono hz).monotone (le_of_not_gt h)
  rw [coordinate_spec hz, coordinate_spec hz] at h'
  exact (not_lt_of_ge h') hab

private lemma coordinate_continuous {z : ℝ} (hz : 0 ≤ z) :
    Continuous (fun t => coordinate t z) :=
  (coordinate_strictMono hz).monotone.continuous_of_surjective
    (Function.invFun_surjective (map_strictMono hz).injective)

private lemma coordinate_zero {z : ℝ} (hz : 0 ≤ z) : coordinate 0 z = 0 := by
  apply (map_strictMono hz).injective
  rw [coordinate_spec hz]
  simp [coordinateMap, width, Real.zero_rpow (by norm_num : (4 / 5 : ℝ) ≠ 0)]

lemma coordinate_pos {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) : 0 < coordinate t z := by
  simpa only [coordinate_zero hz] using coordinate_strictMono hz ht

lemma coordinate_equation {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) :
    t = coordinate t z + z * width (coordinate t z) := by
  have h := coordinate_spec hz t
  simpa only [coordinateMap, max_eq_left (coordinate_pos ht hz).le] using h.symm

private lemma coordinate_le {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) : coordinate t z ≤ t := by
  conv_rhs => rw [coordinate_equation ht hz]
  exact le_add_of_nonneg_right (mul_nonneg hz (Real.rpow_nonneg (coordinate_pos ht hz).le _))

private lemma coordinate_decreases {t z v : ℝ} (ht : 0 < t) (hz : 0 ≤ z)
    (hzv : z ≤ v) : coordinate t v ≤ coordinate t z := by
  have hv : 0 ≤ v := hz.trans hzv
  have hx := coordinate_pos ht hv
  have he := coordinate_equation ht hv
  have hlow : coordinateMap z (coordinate t v) ≤ t := by
    dsimp [coordinateMap]
    rw [max_eq_left hx.le]
    have hm := mul_le_mul_of_nonneg_right hzv (Real.rpow_nonneg hx.le (4 / 5 : ℝ))
    change z * width (coordinate t v) ≤ v * width (coordinate t v) at hm
    linarith
  by_contra hn
  have hstrict := map_strictMono hz (lt_of_not_ge hn)
  rw [coordinate_spec hz] at hstrict
  linarith

private lemma coordinate_parameter_difference {t z v : ℝ} (ht : 0 < t)
    (hz : 0 ≤ z) (hzv : z ≤ v) :
    coordinate t z - coordinate t v ≤ width t * (v - z) := by
  have hv := hz.trans hzv
  have hxv := coordinate_pos ht hv
  have hxz := coordinate_pos ht hz
  have horder := coordinate_decreases ht hz hzv
  have hw : width (coordinate t v) ≤ width (coordinate t z) :=
    Real.rpow_le_rpow hxv.le horder (by norm_num)
  have hwt : width (coordinate t v) ≤ width t :=
    Real.rpow_le_rpow hxv.le (coordinate_le ht hv) (by norm_num)
  have he1 := coordinate_equation ht hz
  have he2 := coordinate_equation ht hv
  have hdrop := mul_nonneg hz (sub_nonneg.mpr hw)
  have hcap := mul_le_mul_of_nonneg_right hwt (sub_nonneg.mpr hzv)
  nlinarith

/-- The inverse coordinate is continuous in the normalized window position. -/
lemma coordinate_continuousOn_parameter {t : ℝ} (ht : 0 < t) :
    ContinuousOn (coordinate t) (Icc (0 : ℝ) 1) := by
  have hw0 : 0 ≤ width t := Real.rpow_nonneg ht.le _
  have hlip : LipschitzOnWith ⟨width t, hw0⟩ (coordinate t) (Icc (0 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz v hv
    change |coordinate t z - coordinate t v| ≤ width t * |z - v|
    rcases le_total z v with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr (coordinate_decreases ht hz.1 h)),
        abs_of_nonpos (sub_nonpos.mpr h)]
      simpa only [neg_sub] using coordinate_parameter_difference ht hz.1 h
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (coordinate_decreases ht hv.1 h)),
        abs_of_nonneg (sub_nonneg.mpr h)]
      exact coordinate_parameter_difference ht hv.1 h
  exact hlip.continuousOn

lemma coordinate_parameter_hasDerivAt {t z : ℝ} (ht : 0 < t)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (coordinate t)
      (-width (coordinate t z) /
        (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))) z := by
  have hx := coordinate_pos ht hz.1.le
  have hz0 : 0 ≤ z := hz.1.le
  have hw : 0 < width (coordinate t z) := Real.rpow_pos_of_pos hx _
  have he := coordinate_equation ht hz.1.le
  have hc : ContinuousAt (coordinate t) z :=
    (coordinate_continuousOn_parameter ht).continuousAt (Icc_mem_nhds hz.1 hz.2)
  have hp := (Real.hasDerivAt_rpow_const (p := (4 / 5 : ℝ)) (Or.inl hx.ne'))
  have hD : 0 < 1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ) := by positivity
  have hd : HasDerivAt (fun x => (t - x) / width x)
      (-(1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)) /
        width (coordinate t z)) (coordinate t z) := by
    convert (((hasDerivAt_const (coordinate t z) t).sub
      (hasDerivAt_id (coordinate t z))).div hp hw.ne') using 1
    · rfl
    · simp only [zero_sub, neg_mul, one_mul, Pi.sub_apply, id_eq]
      symm
      change (-(width (coordinate t z)) -
        (t - coordinate t z) * ((4 / 5 : ℝ) * coordinate t z ^ (4 / 5 - 1 : ℝ))) /
          width (coordinate t z) ^ 2 = _
      rw [show t - coordinate t z = z * width (coordinate t z) by linarith]
      norm_num only [show (4 / 5 : ℝ) - 1 = -1 / 5 by norm_num]
      field_simp [hw.ne']
      <;> ring
  have hfg : ∀ᶠ y in 𝓝 z, (t - coordinate t y) / width (coordinate t y) = y := by
    filter_upwards [Ioi_mem_nhds hz.1] with y hy
    have hy0 : 0 < y := hy
    have hey := coordinate_equation ht hy0.le
    have hwy : 0 < width (coordinate t y) :=
      Real.rpow_pos_of_pos (coordinate_pos ht hy0.le) _
    apply (div_eq_iff hwy.ne').2
    linarith
  have hi := hd.of_local_left_inverse hc (div_ne_zero (neg_ne_zero.mpr hD.ne') hw.ne') hfg
  apply hi.congr_deriv
  field_simp [hw.ne', hD.ne']

lemma coordinate_parameter_zero {t : ℝ} (ht : 0 < t) : coordinate t 0 = t := by
  have he := coordinate_equation ht (le_refl (0 : ℝ))
  simpa using he.symm

/-- The time derivative keeps the exact moving-endpoint Jacobian. -/
lemma coordinate_hasDerivAt {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) :
    HasDerivAt (fun y => coordinate y z)
      (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))⁻¹ t := by
  have hx := coordinate_pos ht hz
  have hd : HasDerivAt (fun x : ℝ => x + z * width x)
      (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)) (coordinate t z) := by
    convert (hasDerivAt_id (coordinate t z)).add
      ((Real.hasDerivAt_rpow_const (p := (4 / 5 : ℝ)) (Or.inl hx.ne')).const_mul z) using 1
    · rfl
    · norm_num
      ring
  have he : coordinateMap z =ᶠ[𝓝 (coordinate t z)] (fun x : ℝ => x + z * width x) := by
    filter_upwards [Ioi_mem_nhds hx] with x hx'
    simp only [coordinateMap, max_eq_left (show 0 ≤ x from le_of_lt hx')]
  exact (hd.congr_of_eventuallyEq he).of_local_left_inverse
    (coordinate_continuous hz).continuousAt
    (ne_of_gt (by positivity)) (Eventually.of_forall (coordinate_spec hz))

/-- Quantitative geometric control of the inverse coordinate. -/
theorem coordinate_scale_bounds {t z : ℝ} (ht : 1 ≤ t) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 < coordinate t z ∧ coordinate t z ≤ t ∧
      0 ≤ 1 - coordinate t z / t ∧
      1 - coordinate t z / t ≤ t ^ (-1 / 5 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hx := coordinate_pos ht0 hz.1
  have hxt := coordinate_le ht0 hz.1
  have he := coordinate_equation ht0 hz.1
  have hp : width (coordinate t z) ≤ width t :=
    Real.rpow_le_rpow hx.le hxt (by norm_num)
  have hscale : width t / t = t ^ (-1 / 5 : ℝ) := by
    unfold width
    simpa only [show (4 / 5 : ℝ) - 1 = -1 / 5 by norm_num] using
      (Real.rpow_sub_one ht0.ne' (4 / 5 : ℝ)).symm
  refine ⟨hx, hxt, sub_nonneg.mpr ((div_le_one ht0).mpr hxt), ?_⟩
  rw [← hscale]
  apply (le_div_iff₀ ht0).2
  have hmul : z * width (coordinate t z) ≤ width t :=
    (mul_le_mul_of_nonneg_left hp hz.1).trans
      (mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) hz.2)
  have hc : coordinate t z / t * t = coordinate t z := div_mul_cancel₀ _ ht0.ne'
  nlinarith

private lemma coordinate_ge_one {t z : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) : 1 ≤ coordinate t z := by
  by_contra h
  have hm := map_strictMono hz.1 (lt_of_not_ge h)
  rw [coordinate_spec hz.1] at hm
  have h1 : coordinateMap z 1 = 1 + z := by simp [coordinateMap, width]
  rw [h1] at hm
  linarith [hz.2]

lemma coordinate_half {t z : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) : t / 2 ≤ coordinate t z := by
  have ht0 : 0 < t := by linarith
  have hx1 := coordinate_ge_one ht hz
  have hp : width (coordinate t z) ≤ coordinate t z := by
    simpa only [width, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx1 (show (4 / 5 : ℝ) ≤ 1 by norm_num)
  have hz' := mul_le_of_le_one_left (by linarith : 0 ≤ coordinate t z) hz.2
  have he := coordinate_equation ht0 hz.1
  have hmul := (mul_le_mul_of_nonneg_left hp hz.1).trans hz'
  linarith

/-- Differentiating the relative coordinate cancels its constant main term. -/
lemma coordinate_fraction_hasDerivAt {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) :
    HasDerivAt (fun y => coordinate y z / y)
      ((z / 5 * width (coordinate t z)) /
        (t ^ 2 * (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)))) t := by
  have hx := coordinate_pos ht hz
  have he := coordinate_equation ht hz
  have hp : coordinate t z * coordinate t z ^ (-1 / 5 : ℝ) =
      width (coordinate t z) := by
    simpa only [width, Real.rpow_one, show (1 : ℝ) + -1 / 5 = 4 / 5 by norm_num] using
      (Real.rpow_add hx (1 : ℝ) (-1 / 5 : ℝ)).symm
  have hD : 0 < 1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ) := by positivity
  apply ((coordinate_hasDerivAt ht hz).div (hasDerivAt_id t) ht.ne').congr_deriv
  simp only [id_eq]
  field_simp [ht.ne', hD.ne']
  nlinarith [hp]

/-- The normalized inverse coordinate has a derivative of order t^(-6/5). -/
theorem coordinate_fraction_derivative_bound {t z : ℝ} (ht : 1 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    0 ≤ deriv (fun y => coordinate y z / y) t ∧
      deriv (fun y => coordinate y z / y) t ≤ t ^ (-6 / 5 : ℝ) / 5 := by
  have ht0 : 0 < t := by linarith
  have hx := coordinate_pos ht0 hz.1
  have hz0 := hz.1
  have hxt := coordinate_le ht0 hz.1
  rw [(coordinate_fraction_hasDerivAt ht0 hz.1).deriv]
  have hp : width (coordinate t z) ≤ width t :=
    Real.rpow_le_rpow hx.le hxt (by norm_num)
  have hnum : z / 5 * width (coordinate t z) ≤ width t / 5 := by
    have hmul := (mul_le_mul_of_nonneg_left hp hz.1).trans
      (mul_le_of_le_one_left (Real.rpow_nonneg ht0.le _) hz.2)
    nlinarith
  have hD : 1 ≤ 1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ) :=
    le_add_of_nonneg_right (by positivity)
  have hden : t ^ 2 ≤ t ^ 2 *
      (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)) :=
    le_mul_of_one_le_right (sq_nonneg t) hD
  have hpow : width t / t ^ 2 = t ^ (-6 / 5 : ℝ) := by
    simpa only [width, Real.rpow_two,
      show (4 / 5 : ℝ) - 2 = -6 / 5 by norm_num] using
      (Real.rpow_sub ht0 (4 / 5 : ℝ) (2 : ℝ)).symm
  have hw0 : 0 ≤ width (coordinate t z) := Real.rpow_nonneg hx.le _
  have hwt0 : 0 ≤ width t := Real.rpow_nonneg ht0.le _
  constructor
  · positivity
  · calc
      _ ≤ (width t / 5) / t ^ 2 :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by rw [show width t / 5 / t ^ 2 = (width t / t ^ 2) / 5 by ring, hpow]

/-- The relative complex power after factoring out t^(-s-1/2). -/
def normalizedPower (t z : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((-s - 1 / 2) * (Real.log (coordinate t z / t) : ℂ))

lemma log_fraction_bound {t z : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    |Real.log (coordinate t z / t)| ≤ 2 * t ^ (-1 / 5 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hx := coordinate_pos ht0 hz.1
  have hb := coordinate_scale_bounds (by linarith : 1 ≤ t) hz
  have hv : (1 / 2 : ℝ) ≤ coordinate t z / t :=
    (le_div_iff₀ ht0).2 (by linarith [coordinate_half ht hz])
  have hv0 : 0 < coordinate t z / t := div_pos hx ht0
  have hv1 : coordinate t z / t ≤ 1 := (div_le_one ht0).2 hb.2.1
  have hl0 := Real.log_nonpos hv0.le hv1
  have hδ0 : 0 ≤ 1 - coordinate t z / t := sub_nonneg.mpr hv1
  have hδ1 : 1 - coordinate t z / t ≤ 1 / 2 := by linarith
  have hl := D5.S3.Arith.Lattices.Klartag.neg_log_one_sub_le hδ0 hδ1
  rw [sub_sub_cancel] at hl
  rw [abs_of_nonpos hl0]
  have hlin : -(Real.log (coordinate t z / t)) ≤ 2 * (1 - coordinate t z / t) := by
    nlinarith
  exact hlin.trans (mul_le_mul_of_nonneg_left hb.2.2.2 (by norm_num))

private lemma epsilon_le_one {t : ℝ} (ht : 1 ≤ t) : t ^ (-1 / 5 : ℝ) ≤ 1 := by
  simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one ht (show (-1 / 5 : ℝ) ≤ 0 by norm_num)

/-- Relative complex powers have a uniform first-order error in the window scale. -/
theorem normalizedPower_bounds {t z : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) (s : ℂ) :
    ‖normalizedPower t z s‖ ≤ Real.exp (2 * ‖-s - 1 / 2‖) ∧
      ‖normalizedPower t z s - 1‖ ≤
        (2 * ‖-s - 1 / 2‖ * Real.exp (2 * ‖-s - 1 / 2‖)) * t ^ (-1 / 5 : ℝ) := by
  let v : ℂ := (-s - 1 / 2) * (Real.log (coordinate t z / t) : ℂ)
  have hε := epsilon_le_one (show 1 ≤ t by linarith)
  have hn : ‖v‖ ≤ 2 * ‖-s - 1 / 2‖ * t ^ (-1 / 5 : ℝ) := by
    dsimp [v]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ‖-s - 1 / 2‖ * (2 * t ^ (-1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left (log_fraction_bound ht hz) (norm_nonneg _)
      _ = _ := by ring
  have hn' : ‖v‖ ≤ 2 * ‖-s - 1 / 2‖ := by
    exact hn.trans (mul_le_of_le_one_right (by positivity) hε)
  have hexp : Real.exp ‖v‖ ≤ Real.exp (2 * ‖-s - 1 / 2‖) := Real.exp_le_exp.mpr hn'
  constructor
  · exact (Complex.norm_exp_le_exp_norm v).trans hexp
  · have h := Complex.norm_exp_sub_sum_le_norm_mul_exp v 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      pow_one] at h
    change ‖Complex.exp v - 1‖ ≤ _
    calc
      _ ≤ ‖v‖ * Real.exp ‖v‖ := h
      _ ≤ (2 * ‖-s - 1 / 2‖ * t ^ (-1 / 5 : ℝ)) *
          Real.exp (2 * ‖-s - 1 / 2‖) :=
        mul_le_mul hn hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by ring

/-- The derivative of the relative power differentiates only its small scale change. -/
lemma normalizedPower_hasDerivAt {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) (s : ℂ) :
    HasDerivAt (fun y => normalizedPower y z s)
      (normalizedPower t z s * (-s - 1 / 2) *
        (((z / 5 * width (coordinate t z)) /
          (t ^ 2 * (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))) /
            (coordinate t z / t) : ℝ) : ℂ)) t := by
  have hd := ((coordinate_fraction_hasDerivAt ht hz).log
    (div_pos (coordinate_pos ht hz) ht).ne').ofReal_comp
  have he := (hd.const_mul (-s - 1 / 2)).cexp
  simpa only [normalizedPower, Complex.ofReal_div, mul_assoc] using he

/-- The time derivative has the same small factor as the relative-power error. -/
theorem normalizedPower_derivative_bound {t z : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) (s : ℂ) :
    ‖deriv (fun y => normalizedPower y z s) t‖ ≤
      (2 * ‖-s - 1 / 2‖ * Real.exp (2 * ‖-s - 1 / 2‖)) * t ^ (-6 / 5 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hv0 : 0 < coordinate t z / t := div_pos (coordinate_pos ht0 hz.1) ht0
  have hv : (1 / 2 : ℝ) ≤ coordinate t z / t :=
    (le_div_iff₀ ht0).2 (by linarith [coordinate_half ht hz])
  have hfrac := coordinate_fraction_derivative_bound (by linarith : 1 ≤ t) hz
  rw [(coordinate_fraction_hasDerivAt ht0 hz.1).deriv] at hfrac
  have hdiv : ((z / 5 * width (coordinate t z)) /
      (t ^ 2 * (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)))) /
      (coordinate t z / t) ≤ 2 * t ^ (-6 / 5 : ℝ) := by
    apply (div_le_iff₀ hv0).2
    nlinarith [Real.rpow_pos_of_pos ht0 (-6 / 5 : ℝ)]
  rw [(normalizedPower_hasDerivAt ht0 hz.1 s).deriv, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hfrac.1 hv0.le)]
  calc
    _ ≤ (Real.exp (2 * ‖-s - 1 / 2‖) * ‖-s - 1 / 2‖) *
        (2 * t ^ (-6 / 5 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (normalizedPower_bounds ht hz s).1
        (norm_nonneg _)) hdiv (div_nonneg hfrac.1 hv0.le) (by positivity)
    _ = _ := by ring

lemma coordinate_neg_power {t z c : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c) :
    coordinate t z ^ (-c) ≤ (2 : ℝ) ^ c * t ^ (-c) := by
  have ht0 : 0 < t := by linarith
  calc
    _ ≤ (t / 2) ^ (-c) := Real.rpow_le_rpow_of_nonpos
      (div_pos ht0 (by norm_num)) (coordinate_half ht hz) (neg_nonpos.mpr hc)
    _ = _ := by
      rw [Real.div_rpow ht0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [div_eq_mul_inv, inv_inv]
      ring

/-- The inverse Jacobian from the exact coordinate change. -/
def jacobianFactor (t z : ℝ) : ℝ :=
  (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))⁻¹

/-- The inverse Jacobian is between zero and one, with a first-order window error. -/
theorem jacobianFactor_bounds {t z : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    0 < jacobianFactor t z ∧ jacobianFactor t z ≤ 1 ∧
      |jacobianFactor t z - 1| ≤ 2 * t ^ (-1 / 5 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hx := coordinate_pos ht0 hz.1
  have hz0 := hz.1
  have hD : 1 ≤ 1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ) :=
    le_add_of_nonneg_right (by positivity)
  have hD0 : 0 < 1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ) := by linarith
  have hJ0 : 0 < jacobianFactor t z := inv_pos.mpr hD0
  have hJ1 : jacobianFactor t z ≤ 1 := (inv_le_one₀ hD0).2 hD
  refine ⟨hJ0, hJ1, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hJ1)]
  have hpow := coordinate_neg_power ht hz (show (0 : ℝ) ≤ 1 / 5 by norm_num)
  have htwo : (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (1 / 5 : ℝ) ≤ 1 by norm_num)
  have hxbound : coordinate t z ^ (-1 / 5 : ℝ) ≤ 2 * t ^ (-1 / 5 : ℝ) := by
    convert hpow.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg ht0.le _)) using 1 <;> norm_num
  have hsmall : (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ) ≤
      2 * t ^ (-1 / 5 : ℝ) := by
    have hcoef : (4 / 5 : ℝ) * z ≤ 1 := by linarith [hz.2]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hx.le _) hcoef).trans hxbound
  change -( (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))⁻¹ - 1) ≤ _
  apply (mul_le_mul_iff_left₀ hD0).mp
  have hinv := mul_inv_cancel₀ hD0.ne'
  nlinarith [mul_nonneg (sub_nonneg.mpr hD)
    (Real.rpow_nonneg ht0.le (-1 / 5 : ℝ))]

lemma jacobianFactor_hasDerivAt {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) :
    HasDerivAt (fun y => jacobianFactor y z)
      ((4 / 25 : ℝ) * z * coordinate t z ^ (-6 / 5 : ℝ) *
        jacobianFactor t z ^ 3) t := by
  have hx := coordinate_pos ht hz
  have hd := ((Real.hasDerivAt_rpow_const (p := (-1 / 5 : ℝ))
    (Or.inl hx.ne')).comp t (coordinate_hasDerivAt ht hz)).const_mul ((4 / 5 : ℝ) * z)
  have hD0 : 0 < 1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ) := by positivity
  have he := (hd.const_add 1).inv hD0.ne'
  apply he.congr_deriv
  change -((4 / 5 : ℝ) * z * (-1 / 5 * coordinate t z ^ (-1 / 5 - 1 : ℝ) *
      (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))⁻¹)) /
      (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)) ^ 2 = _
  simp only [show (-1 / 5 : ℝ) - 1 = -6 / 5 by norm_num, jacobianFactor]
  field_simp [hD0.ne']
  <;> ring

/-- The Jacobian derivative also retains the t^(-1/5) scale gain. -/
theorem jacobianFactor_derivative_bound {t z : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    |deriv (fun y => jacobianFactor y z) t| ≤ t ^ (-6 / 5 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hx := coordinate_pos ht0 hz.1
  have hb := jacobianFactor_bounds ht hz
  have hz0 := hz.1
  have hJ0 := hb.1.le
  rw [(jacobianFactor_hasDerivAt ht0 hz.1).deriv,
    abs_of_nonneg (by positivity)]
  have hpow := coordinate_neg_power ht hz (show (0 : ℝ) ≤ 6 / 5 by norm_num)
  have htwo : (2 : ℝ) ^ (6 / 5 : ℝ) ≤ 4 := by
    simpa only [Real.rpow_two, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show (6 / 5 : ℝ) ≤ 2 by norm_num)
  have hxbound : coordinate t z ^ (-6 / 5 : ℝ) ≤ 4 * t ^ (-6 / 5 : ℝ) :=
    by convert hpow.trans (mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg ht0.le _)) using 1 <;> norm_num
  have hcube : jacobianFactor t z ^ 3 ≤ 1 := pow_le_one₀ hb.1.le hb.2.1
  calc
    _ ≤ ((4 / 25 : ℝ) * z * (4 * t ^ (-6 / 5 : ℝ))) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hxbound (by positivity)) hcube
        (by positivity) (by positivity)
    _ ≤ _ := by nlinarith [Real.rpow_nonneg ht0.le (-6 / 5 : ℝ),
      mul_le_mul_of_nonneg_right hz.2 (Real.rpow_nonneg ht0.le (-6 / 5 : ℝ))]

end D5.S3.Arith.Robin.ForwardKernel.Remainder
