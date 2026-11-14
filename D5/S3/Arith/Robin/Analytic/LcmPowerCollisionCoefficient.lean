/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict parameter comparison of the leading LCM power coefficients. -/

import D5.S3.Analytic.GauntBesselTail.Result
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The leading coefficients and their strictly increasing logarithmic ratios. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient

/-- The leading coefficient of the LCM power threshold. -/
def coefficient (κ x : ℝ) : ℝ :=
  (x - 1) * (x ^ (κ - 1) - 1) / ((x ^ κ - 1) * Real.log x)

/-- The leading coefficient is positive in its natural domain. -/
lemma coefficient_pos {κ x : ℝ} (hκ : 1 < κ) (hx : 1 < x) :
    0 < coefficient κ x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hpow (r : ℝ) (hr : 0 < r) : 0 < x ^ r - 1 :=
    sub_pos.mpr (Real.one_lt_rpow hx hr)
  exact div_pos (mul_pos (sub_pos.mpr hx) (hpow _ (by linarith)))
    (mul_pos (hpow _ (by linarith)) (Real.log_pos hx))

private lemma sinh_ratio_strictAnti :
    StrictAntiOn (fun z : ℝ => z / Real.sinh z) (Ioi 0) := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun z => z / Real.sinh z)
        ((Real.sinh x - x * Real.cosh x) / Real.sinh x ^ 2) x := by
    convert (hasDerivAt_id x).div (Real.hasDerivAt_sinh x)
      (Real.sinh_pos_iff.mpr hx).ne' using 1 <;> (first | rfl | (simp only [id_eq]; ring))
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
  intro x hx
  have hx : 0 < x := by simpa using hx
  rw [(hd x hx).deriv]
  exact div_neg_of_neg_of_pos
    (by linarith [D5.S3.Analytic.GauntBesselTail.Result.sinh_gap_pos hx])
    (sq_pos_of_pos (Real.sinh_pos_iff.mpr hx))

private lemma kernel_comparison {v s t : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hst : s < t) :
    (t / (2 * Real.sinh (v * t / 2))) ^ 2 <
      (s / (2 * Real.sinh (v * s / 2))) ^ 2 := by
  have ht := hs.trans hst
  have hvs : 0 < v * s / 2 := by positivity
  have hvt : 0 < v * t / 2 := by positivity
  have hlt := sinh_ratio_strictAnti hvs hvt (by nlinarith)
  have he (r : ℝ) :
      r / (2 * Real.sinh (v * r / 2)) =
        (1 / v) * ((v * r / 2) / Real.sinh (v * r / 2)) := by
    field_simp
  rw [he s, he t]
  have h := mul_lt_mul_of_pos_left hlt (one_div_pos.mpr hv)
  have hp : 0 < 1 / v * (v * t / 2 / Real.sinh (v * t / 2)) :=
    mul_pos (one_div_pos.mpr hv) (div_pos hvt (Real.sinh_pos_iff.mpr hvt))
  nlinarith

private lemma exp_kernel_identity {v s : ℝ} (hv : 0 < v) (hs : 0 < s) :
    s ^ 2 * Real.exp (v * s) / (Real.exp (v * s) - 1) ^ 2 =
      (s / (2 * Real.sinh (v * s / 2))) ^ 2 := by
  have he : Real.exp (v * s) = Real.exp (v * s / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hn : Real.exp (v * s / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hm : Real.exp (v * s) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hv hs))).ne'
  have hh : Real.sinh (v * s / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (show 0 < v * s / 2 by positivity)).ne'
  rw [Real.sinh_eq, Real.exp_neg, he]
  field_simp
  <;> ring

private lemma exp_quotient_derivative {s v : ℝ} (hs : 0 < s) (hv : 0 < v) :
    HasDerivAt (fun v => s / (Real.exp (v * s) - 1))
      (-(s / (2 * Real.sinh (v * s / 2))) ^ 2) v := by
  have hn : Real.exp (v * s) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hv hs))).ne'
  have hd := (hasDerivAt_const v s).div
    (((hasDerivAt_id v).mul_const s).exp.sub_const 1) hn
  convert hd using 1
  · rfl
  · dsimp
    rw [← exp_kernel_identity hv hs]
    ring

private lemma exp_quotient_difference_strictAnti {s t : ℝ}
    (hs : 0 < s) (hst : s < t) :
    StrictAntiOn (fun v => s / (Real.exp (v * s) - 1) -
      t / (Real.exp (v * t) - 1)) (Ioi 0) := by
  have hd (v : ℝ) (hv : 0 < v) :=
    (exp_quotient_derivative hs hv).sub (exp_quotient_derivative (hs.trans hst) hv)
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
  intro v hv
  have hv : 0 < v := by simpa using hv
  rw [(hd v hv).deriv]
  have h := kernel_comparison hv hs hst
  linarith

private lemma log_coefficient_derivative {κ x : ℝ} (hκ : 1 < κ) (hx : 1 < x) :
    HasDerivAt (fun κ => Real.log (coefficient κ x))
      (Real.log x / (Real.exp ((κ - 1) * Real.log x) - 1) -
        Real.log x / (Real.exp (κ * Real.log x) - 1)) κ := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have ha : 0 < x ^ (κ - 1) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow hx (by linarith))
  have hb : 0 < x ^ κ - 1 :=
    sub_pos.mpr (Real.one_lt_rpow hx (by linarith))
  have hdA := ((hasDerivAt_id κ).sub_const 1).const_rpow hx0
  have hdB := (hasDerivAt_id κ).const_rpow hx0
  have hd := (((hasDerivAt_const κ (x - 1)).mul (hdA.sub_const 1)).div
    ((hdB.sub_const 1).mul_const (Real.log x))
      (mul_pos hb (Real.log_pos hx)).ne').log (coefficient_pos hκ hx).ne'
  have hA : Real.exp ((κ - 1) * Real.log x) = x ^ (κ - 1) := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  have hB : Real.exp (κ * Real.log x) = x ^ κ := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  convert hd using 1
  · rfl
  · dsimp
    rw [hA, hB]
    field_simp [coefficient, ha.ne', hb.ne', (sub_pos.mpr hx).ne',
      (Real.log_pos hx).ne']
    <;> ring

/-- For increasing bases the ratio of leading coefficients increases in the parameter. -/
theorem log_coefficient_ratio_strictMono {p q : ℝ} (hp : 1 < p) (hpq : p < q) :
    StrictMonoOn (fun κ => Real.log (coefficient κ p / coefficient κ q)) (Ioi 1) := by
  have hq : 1 < q := hp.trans hpq
  have hs : 0 < Real.log p := Real.log_pos hp
  have hst : Real.log p < Real.log q :=
    Real.log_lt_log (zero_lt_one.trans hp) hpq
  have hd (κ : ℝ) (hκ : 1 < κ) :
      HasDerivAt (fun κ => Real.log (coefficient κ p / coefficient κ q))
        ((Real.log p / (Real.exp ((κ - 1) * Real.log p) - 1) -
          Real.log q / (Real.exp ((κ - 1) * Real.log q) - 1)) -
          (Real.log p / (Real.exp (κ * Real.log p) - 1) -
          Real.log q / (Real.exp (κ * Real.log q) - 1))) κ := by
    have hh := (log_coefficient_derivative hκ hp).sub (log_coefficient_derivative hκ hq)
    have he : (fun κ => Real.log (coefficient κ p / coefficient κ q)) =ᶠ[nhds κ]
        (fun κ => Real.log (coefficient κ p) - Real.log (coefficient κ q)) := by
      filter_upwards [Ioi_mem_nhds hκ] with t ht
      exact Real.log_div (coefficient_pos ht hp).ne' (coefficient_pos ht hq).ne'
    convert hh.congr_of_eventuallyEq he using 1 <;> ring
  apply strictMonoOn_of_deriv_pos (convex_Ioi 1)
    (fun κ hκ => (hd κ hκ).continuousAt.continuousWithinAt)
  intro κ hκ
  have hκ : 1 < κ := by simpa using hκ
  rw [(hd κ hκ).deriv]
  exact sub_pos.mpr (exp_quotient_difference_strictAnti hs hst
    (by change 0 < κ - 1; linarith) (by change 0 < κ; linarith) (by linarith))

end D5.S3.Arith.Robin.Analytic.LcmPowerCollisionCoefficient
