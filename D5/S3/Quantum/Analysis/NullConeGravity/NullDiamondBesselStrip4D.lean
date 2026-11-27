/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Holomorphic modular coordinates and uniform null-diamond strip decay. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondBesselSeries4D
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! The lifted logarithm on the modular strip gives a separately holomorphic
extension of the mixed boundary correction with uniform horizontal decay. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set

namespace NullConeGravity

def stripB : ℝ := 3/8

def modularU (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * z) / (1 + Complex.exp (2 * Real.pi * z))

def modularUprime (z : ℂ) : ℂ :=
  2 * Real.pi * Complex.exp (2 * Real.pi * z) /
    (1 + Complex.exp (2 * Real.pi * z))^2

def liftedLog (z : ℂ) : ℂ :=
  2 * Real.pi * z - Complex.log (1 + Complex.exp (2 * Real.pi * z))

def openStrip : Set ℂ := {z | |z.im| < 1/2}
def closedStrip : Set ℂ := {z | |z.im| ≤ stripB}

def stripG (M : ℝ) (z w : ℂ) (x : ℝ) : ℂ :=
  if x < 1 then
    let t := (M : ℂ)^2 * modularU z * modularU w * (1-(x : ℂ)) / 2
    let ell := (Real.log (M^2 * (1-x)/2) : ℂ) + liftedLog z + liftedLog w
    4 * modularUprime z * modularUprime w * correctionLog M t ell
  else 0

private theorem cos_strip_pos : 0 < Real.cos (Real.pi * stripB) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> unfold stripB <;> linarith [Real.pi_pos]

private theorem exp_modular_norm (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * z)‖ = Real.exp (2 * Real.pi * z.re) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

private theorem denom_slit (z : ℂ) (hz : z ∈ openStrip) :
    (1 + Complex.exp (2 * Real.pi * z)) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have htheta : |2 * Real.pi * z.im| < Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    have hh : |z.im| < 1/2 := hz
    nlinarith [mul_lt_mul_of_pos_left hh Real.pi_pos]
  have he : ((2 : ℂ) * Real.pi * z).im = 2 * Real.pi * z.im := by simp [Complex.mul_im]
  have hr : ((2 : ℂ) * Real.pi * z).re = 2 * Real.pi * z.re := by simp [Complex.mul_re]
  by_cases hi : (1 + Complex.exp (2 * Real.pi * z)).im = 0
  · left
    simp only [Complex.add_im, Complex.one_im, zero_add, Complex.exp_im, he, hr] at hi
    have hs := (mul_eq_zero.mp hi).resolve_left (Real.exp_ne_zero _)
    have ht := (Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.mp htheta).1
      (abs_lt.mp htheta).2).mp hs
    simp [Complex.add_re, Complex.exp_re, he, hr, ht]
    positivity
  · exact Or.inr hi

theorem strip_denom_lower (z : ℂ) (hz : z ∈ closedStrip) :
    Real.cos (Real.pi * stripB) * (1 + Real.exp (2*Real.pi*z.re)) ≤
      ‖(1 : ℂ) + Complex.exp (2*Real.pi*z)‖ := by
  let q : ℂ := ((Real.pi * z.im : ℝ) : ℂ) * Complex.I
  have hq : q.re = 0 := by simp [q, Complex.mul_re]
  have hqi : q.im = Real.pi * z.im := by simp [q, Complex.mul_im]
  have hrot : ‖Complex.exp (-q) * (1 + Complex.exp (2*Real.pi*z))‖ =
      ‖(1 : ℂ) + Complex.exp (2*Real.pi*z)‖ := by
    rw [norm_mul, Complex.norm_exp, Complex.neg_re, hq, neg_zero, Real.exp_zero, one_mul]
  have he : (Complex.exp (-q) * (1 + Complex.exp (2*Real.pi*z))).re =
      (1 + Real.exp (2*Real.pi*z.re)) * Real.cos (Real.pi*z.im) := by
    rw [mul_add, mul_one, ← Complex.exp_add, Complex.add_re, Complex.exp_re,
      Complex.exp_re, Complex.neg_re, Complex.neg_im, hq, hqi, neg_zero, Real.exp_zero,
      one_mul, Real.cos_neg]
    have hr : ((2 : ℂ) * Real.pi * z).re = 2 * Real.pi * z.re := by simp [Complex.mul_re]
    have hi : ((2 : ℂ) * Real.pi * z).im = 2 * Real.pi * z.im := by simp [Complex.mul_im]
    rw [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, hq, hqi, hr, hi]
    rw [show -(Real.pi * z.im) + 2 * Real.pi * z.im = Real.pi * z.im by ring]
    ring_nf
  have hc : Real.cos (Real.pi * stripB) ≤ Real.cos (Real.pi*z.im) := by
    rw [← Real.cos_abs (Real.pi*z.im), abs_mul, abs_of_pos Real.pi_pos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by unfold stripB; linarith [Real.pi_pos])
      (mul_le_mul_of_nonneg_left hz Real.pi_pos.le)
  calc
    _ ≤ (1 + Real.exp (2*Real.pi*z.re)) * Real.cos (Real.pi*z.im) := by
      rw [mul_comm (Real.cos _)]
      exact mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := he.symm
    _ ≤ _ := hrot ▸ Complex.re_le_norm _

theorem exp_liftedLog (z : ℂ) (hz : z ∈ openStrip) :
    Complex.exp (liftedLog z) = modularU z := by
  rw [liftedLog, Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero (denom_slit z hz)),
    modularU]

private theorem real_modular (r : ℝ) :
    modularU r = ((Real.exp (2*Real.pi*r) / (1+Real.exp (2*Real.pi*r)) : ℝ) : ℂ) := by
  have he : Complex.exp (2 * Real.pi * (r : ℂ)) =
      (Real.exp (2*Real.pi*r) : ℂ) := by rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [modularU, he]
  push_cast
  rfl

private theorem real_lifted (r : ℝ) :
    liftedLog r = (Real.log ((modularU r).re) : ℂ) := by
  have he : 0 < Real.exp (2*Real.pi*r) := Real.exp_pos _
  rw [real_modular, Complex.ofReal_re, Real.log_div he.ne' (by positivity), Real.log_exp]
  have he : (2 * Real.pi * (r : ℂ)) = ((2*Real.pi*r : ℝ) : ℂ) := by push_cast; ring
  unfold liftedLog
  rw [he, ← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_add,
    ← Complex.ofReal_log (by positivity)]
  push_cast
  rfl

theorem stripG_real (M r s x : ℝ) (hM : 0 < M) (hx : x < 1) :
    stripG M r s x =
      4 * modularUprime r * modularUprime s *
        correction M (modularU r).re (modularU s).re x := by
  have hu : 0 < (modularU r).re := by rw [real_modular, Complex.ofReal_re]; positivity
  have hv : 0 < (modularU s).re := by rw [real_modular, Complex.ofReal_re]; positivity
  have hur : ((modularU r).re : ℂ) = modularU r := by rw [real_modular, Complex.ofReal_re]
  have hvr : ((modularU s).re : ℂ) = modularU s := by rw [real_modular, Complex.ofReal_re]
  unfold stripG correction
  simp only [ite_eq_left hx, real_lifted]
  congr 1
  congr 1
  · push_cast
    rw [hur, hvr]
  · have he : M^2 * (modularU r).re * (modularU s).re * (1-x)/2 =
        M^2 * (1-x)/2 * (modularU r).re * (modularU s).re := by ring
    rw [he, Real.log_mul (by positivity) hv.ne', Real.log_mul (by positivity) hu.ne']
    push_cast
    ring

private theorem modular_diff (z : ℂ) (hz : z ∈ openStrip) :
    DifferentiableAt ℂ modularU z := by
  have he : DifferentiableAt ℂ (fun v : ℂ => Complex.exp (2 * Real.pi * v)) z := by
    fun_prop
  exact he.div ((differentiableAt_const (c := (1 : ℂ))).add he) (Complex.slitPlane_ne_zero (denom_slit z hz))

private theorem prime_diff (z : ℂ) (hz : z ∈ openStrip) :
    DifferentiableAt ℂ modularUprime z := by
  have he : DifferentiableAt ℂ (fun v : ℂ => Complex.exp (2 * Real.pi * v)) z := by
    fun_prop
  exact ((differentiableAt_const (c := (2 * Real.pi : ℂ))).mul he).div
    (((differentiableAt_const (c := (1 : ℂ))).add he).pow 2)
    (pow_ne_zero 2 (Complex.slitPlane_ne_zero (denom_slit z hz)))

private theorem lifted_diff (z : ℂ) (hz : z ∈ openStrip) :
    DifferentiableAt ℂ liftedLog z := by
  have he : DifferentiableAt ℂ (fun v : ℂ => 1 + Complex.exp (2 * Real.pi * v)) z := by
    fun_prop
  have hl : DifferentiableAt ℂ (fun v : ℂ => Complex.log (1 + Complex.exp (2 * Real.pi * v))) z :=
    he.clog (denom_slit z hz)
  exact ((differentiableAt_const (c := (2 * Real.pi : ℂ))).mul differentiableAt_id).sub hl

theorem stripG_diff_left (M : ℝ) (w : ℂ) (x : ℝ) :
    DifferentiableOn ℂ (fun z => stripG M z w x) openStrip := by
  intro z hz
  unfold stripG
  split_ifs
  · apply DifferentiableAt.differentiableWithinAt
    have hu := modular_diff z hz
    have hp := prime_diff z hz
    have hl := lifted_diff z hz
    unfold correctionLog
    have hP := besselP2_entire
    have hB := besselB2_entire
    fun_prop
  · exact differentiableWithinAt_const _

private theorem stripG_swap (M : ℝ) (z w : ℂ) (x : ℝ) :
    stripG M z w x = stripG M w z x := by
  unfold stripG
  split_ifs
  · unfold correctionLog
    ring_nf
  · rfl

theorem stripG_diff_right (M : ℝ) (z : ℂ) (x : ℝ) :
    DifferentiableOn ℂ (fun w => stripG M z w x) openStrip := by
  simpa only [stripG_swap M z] using stripG_diff_left M z x

private theorem denom_pos (z : ℂ) (hz : z ∈ closedStrip) :
    0 < ‖(1 : ℂ) + Complex.exp (2*Real.pi*z)‖ :=
  lt_of_lt_of_le (mul_pos cos_strip_pos (by positivity)) (strip_denom_lower z hz)

private theorem modular_norm (z : ℂ) (hz : z ∈ closedStrip) :
    ‖modularU z‖ ≤ (Real.cos (Real.pi * stripB))⁻¹ := by
  let c := Real.cos (Real.pi * stripB)
  have hc : 0 < c := cos_strip_pos
  rw [modularU, norm_div, exp_modular_norm, ← one_div, le_div_iff₀ hc]
  rw [div_mul_eq_mul_div, div_le_iff₀ (denom_pos z hz), one_mul]
  exact (by nlinarith : Real.exp (2*Real.pi*z.re) * c ≤
    c * (1 + Real.exp (2*Real.pi*z.re))).trans (strip_denom_lower z hz)

private theorem prime_norm (z : ℂ) (hz : z ∈ closedStrip) :
    ‖modularUprime z‖ ≤ (2*Real.pi / Real.cos (Real.pi*stripB)^2) *
      Real.exp (-2*Real.pi*|z.re|) := by
  let c := Real.cos (Real.pi * stripB)
  let q := Real.exp (2*Real.pi*z.re)
  have hc : 0 < c := cos_strip_pos
  have hq : 0 < q := Real.exp_pos _
  have hden : c * (1+q) ≤ ‖(1 : ℂ) + Complex.exp (2*Real.pi*z)‖ := strip_denom_lower z hz
  have hscalar : q / (1+q)^2 ≤ Real.exp (-2*Real.pi*|z.re|) := by
    rcases le_or_gt 0 z.re with h | h
    · rw [abs_of_nonneg h, show -2*Real.pi*z.re = -(2*Real.pi*z.re) by ring,
        Real.exp_neg]
      change q / (1+q)^2 ≤ q⁻¹
      rw [← one_div, le_div_iff₀ hq, div_mul_eq_mul_div, div_le_iff₀ (by positivity), one_mul]
      nlinarith
    · rw [abs_of_neg h, show -2*Real.pi*(-z.re) = 2*Real.pi*z.re by ring]
      change q / (1+q)^2 ≤ q
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hq.le (show 0 ≤ q^2 by positivity),
        mul_nonneg hq.le hq.le]
  rw [modularUprime, norm_div, norm_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, exp_modular_norm, norm_pow]
  change 2*Real.pi*q / ‖(1 : ℂ) + Complex.exp (2*Real.pi*z)‖^2 ≤
    (2*Real.pi / c^2) * _
  calc
    _ ≤ 2*Real.pi*q / (c*(1+q))^2 := by gcongr
    _ = (2*Real.pi/c^2) * (q/(1+q)^2) := by rw [mul_pow]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hscalar (by positivity)

private theorem lifted_norm :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ closedStrip, ‖liftedLog z‖ ≤ K * (1+|z.re|) := by
  let c := Real.cos (Real.pi*stripB)
  have hc : 0 < c := cos_strip_pos
  refine ⟨1 + |Real.log c| + |Real.log 2| + 6*Real.pi, by positivity, ?_⟩
  intro z hz
  let D := (1 : ℂ) + Complex.exp (2*Real.pi*z)
  have hd : 0 < ‖D‖ := denom_pos z hz
  have hlo : c ≤ ‖D‖ := by
    refine le_trans ?_ (strip_denom_lower z hz)
    exact le_mul_of_one_le_right hc.le (by linarith [Real.exp_pos (2*Real.pi*z.re)])
  have hexp : Real.exp (2*Real.pi*z.re) ≤ Real.exp (2*Real.pi*|z.re|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  have hone : 1 ≤ Real.exp (2*Real.pi*|z.re|) := Real.one_le_exp (by positivity)
  have hhi : ‖D‖ ≤ 2 * Real.exp (2*Real.pi*|z.re|) := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (2*Real.pi*z)‖ := norm_add_le _ _
      _ = 1 + Real.exp (2*Real.pi*z.re) := by rw [norm_one, exp_modular_norm]
      _ ≤ _ := by linarith
  have hlog : |Real.log ‖D‖| ≤ |Real.log c| + |Real.log 2| + 2*Real.pi*|z.re| := by
    have hl := Real.log_le_log hc hlo
    have hh := Real.log_le_log hd hhi
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hh
    apply abs_le.mpr
    have hnon : 0 ≤ 2*Real.pi*|z.re| := by positivity
    constructor
    · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log 2)]
    · linarith [le_abs_self (Real.log 2), abs_nonneg (Real.log c)]
  have him : |(Complex.log D).im| ≤ Real.pi :=
    abs_le.mpr ⟨(Complex.neg_pi_lt_log_im D).le, Complex.log_im_le_pi D⟩
  have hln : ‖Complex.log D‖ ≤ |Real.log c| + |Real.log 2| + 2*Real.pi*|z.re| + Real.pi := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re]
    linarith
  have hz' : ‖z‖ ≤ |z.re|+1 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h : |z.im| ≤ stripB := hz
    unfold stripB at h
    linarith
  calc
    ‖liftedLog z‖ ≤ ‖(2*Real.pi : ℂ)*z‖ + ‖Complex.log D‖ := norm_sub_le _ _
    _ ≤ (2*Real.pi) * (|z.re|+1) + (|Real.log c| + |Real.log 2| +
        2*Real.pi*|z.re| + Real.pi) := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      gcongr
    _ ≤ _ := by
      nlinarith [Real.pi_pos, abs_nonneg z.re, abs_nonneg (Real.log c), abs_nonneg (Real.log 2),
        mul_nonneg (abs_nonneg (Real.log c)) (abs_nonneg z.re),
        mul_nonneg (abs_nonneg (Real.log 2)) (abs_nonneg z.re),
        mul_nonneg Real.pi_pos.le (abs_nonneg z.re)]

theorem stripG_bound (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ z w : ℂ, z ∈ closedStrip → w ∈ closedStrip →
      ∀ x : ℝ, -1 ≤ x → x < 1 →
        ‖stripG M z w x‖ ≤
          C * Real.exp (-2*Real.pi*(|z.re|+|w.re|)) *
            (1+|z.re|+|w.re|+|Real.log (1-x)|) := by
  let c := Real.cos (Real.pi*stripB)
  let R := M^2/c^2
  let J := 2*Real.pi/c^2
  let F := ‖((M : ℂ)^2 / (16 * (Real.pi : ℂ)^2))‖
  have hc : 0 < c := cos_strip_pos
  obtain ⟨P, hP⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    besselP2_entire.continuous.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    besselB2_entire.continuous.continuousOn
  let A := 1 + |P| + |B|
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨K, hK, hL⟩ := lifted_norm
  let L := 1 + |Real.log (M^2/2)| + 2*K
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  refine ⟨1 + 4*J*J*F*A*(L+1), by positivity, ?_⟩
  intro z w hz hw x hx hx'
  let t := (M : ℂ)^2 * modularU z * modularU w * (1-(x : ℂ)) / 2
  let ell := (Real.log (M^2 * (1-x)/2) : ℂ) + liftedLog z + liftedLog w
  let S := 1+|z.re|+|w.re|+|Real.log (1-x)|
  have hS : 1 ≤ S := by dsimp [S]; linarith [abs_nonneg z.re, abs_nonneg w.re, abs_nonneg (Real.log (1-x))]
  have ht : t ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hxnorm : ‖(1 : ℂ) - (x : ℂ)‖ ≤ 2 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : 0 < 1-x)]
      linarith
    dsimp [t]
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hM, Complex.norm_ofNat]
    calc
      _ ≤ M^2*c⁻¹*c⁻¹*2/2 := by
        gcongr
        · exact modular_norm z hz
        · exact modular_norm w hw
      _ = R := by dsimp [R]; ring
  have hPn : ‖besselP2 t‖ ≤ A := (hP t ht).trans (by dsimp [A]; linarith [le_abs_self P, abs_nonneg B])
  have hBn : ‖besselB2 t‖ ≤ A := (hB t ht).trans (by dsimp [A]; linarith [le_abs_self B, abs_nonneg P])
  have hell : ‖ell‖ ≤ L*S := by
    calc
      _ ≤ ‖(Real.log (M^2 * (1-x)/2) : ℂ)‖ + ‖liftedLog z‖ + ‖liftedLog w‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ |Real.log (M^2/2)| + |Real.log (1-x)| + K*(1+|z.re|) + K*(1+|w.re|) := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          show M^2*(1-x)/2 = (M^2/2)*(1-x) by ring,
          Real.log_mul (by positivity) (by linarith : 1-x ≠ 0)]
        exact add_le_add (add_le_add (abs_add_le _ _) (hL z hz)) (hL w hw)
      _ ≤ _ := by
        dsimp [L, S]
        nlinarith [abs_nonneg z.re, abs_nonneg w.re, abs_nonneg (Real.log (1-x)),
          abs_nonneg (Real.log (M^2/2)),
          mul_nonneg hK.le (abs_nonneg z.re), mul_nonneg hK.le (abs_nonneg w.re),
          mul_nonneg hK.le (abs_nonneg (Real.log (1-x))),
          mul_nonneg (abs_nonneg (Real.log (M^2/2))) (abs_nonneg z.re),
          mul_nonneg (abs_nonneg (Real.log (M^2/2))) (abs_nonneg w.re),
          mul_nonneg (abs_nonneg (Real.log (M^2/2))) (abs_nonneg (Real.log (1-x)))]
  have hcorr : ‖correctionLog M t ell‖ ≤ F*A*(L+1)*S := by
    rw [correctionLog, norm_mul]
    change F * ‖ell * besselP2 t - besselB2 t‖ ≤ _
    calc
      _ ≤ F * (‖ell‖ * ‖besselP2 t‖ + ‖besselB2 t‖) := by
        gcongr
        simpa only [norm_mul] using norm_sub_le (ell * besselP2 t) (besselB2 t)
      _ ≤ F*(L*S*A + A) := by gcongr
      _ ≤ F*(L*S*A + A*S) := by
        gcongr
        exact le_mul_of_one_le_right hA.le hS
      _ = _ := by ring
  simp only [stripG, ite_eq_left hx']
  change ‖4 * modularUprime z * modularUprime w * correctionLog M t ell‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
  calc
    _ ≤ 4*(J*Real.exp (-2*Real.pi*|z.re|))*(J*Real.exp (-2*Real.pi*|w.re|))*
        (F*A*(L+1)*S) := by
      gcongr
      · exact prime_norm z hz
      · exact prime_norm w hw
    _ = 4*J*J*F*A*(L+1)*Real.exp (-2*Real.pi*(|z.re|+|w.re|))*S := by
      rw [show -2*Real.pi*(|z.re|+|w.re|) = -2*Real.pi*|z.re| + -2*Real.pi*|w.re| by ring,
        Real.exp_add]
      ring
    _ ≤ _ := by gcongr; linarith

end NullConeGravity
