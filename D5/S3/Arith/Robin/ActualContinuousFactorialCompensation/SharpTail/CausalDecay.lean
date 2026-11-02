/- GID: D5/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualContinuousFactorialCompensation/SharpTail/CausalDecay
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The actual causal kernel has a centered decay rate and weighted L1 up to exponent 3/2. -/

import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.SharpTail
import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.CausalKernel

/-! The arithmetic sharp tail is consumed by the existing causal kernel.
Weighted integrability is a real analytic consequence; RH remains open. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.ActualContinuousFactorialCompensation

/-- The centered estimate concerns the literal causal pullback of the arithmetic G. -/
theorem r_centered_decay {t : ℝ} (ht : 0 ≤ t) :
    |r t - ell * Real.exp (-t / 2)| ≤
      (4 * gamma + 24) * (1 + t) * Real.exp (-3 * t / 2) := by
  have hb := G_sharp_tail_bound (Real.one_le_exp_iff.mpr ht)
  have he : Real.exp (-t / 2) / Real.exp t = Real.exp (-3 * t / 2) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [r, ite_eq_left ht, show Real.exp (-t / 2) * G (Real.exp t) -
    ell * Real.exp (-t / 2) = Real.exp (-t / 2) * (G (Real.exp t) - ell) by ring,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-t / 2) *
        ((4 * gamma + 24) * (1 + Real.log (Real.exp t)) / Real.exp t) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by rw [Real.log_exp, ← he]; ring

private lemma weighted_majorant_integrable {a : ℝ} (ha : a < 3 / 2) :
    IntegrableOn (fun t : ℝ =>
      (4 * gamma + 24) * (1 + t) * Real.exp ((a - 3 / 2) * t)) (Ioi 0) := by
  let b : ℝ := 3 / 2 - a
  have hb : 0 < b := by dsimp [b]; linarith
  have h0 : IntegrableOn (fun t : ℝ => Real.exp ((a - 3 / 2) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hΓ : IntegrableOn (fun u : ℝ => Real.exp (-u) * u) (Ioi 0) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
      (Real.GammaIntegral_convergent (s := 2) (by norm_num))
  have hscale : IntegrableOn (fun t : ℝ => Real.exp (-(b * t)) * (b * t)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp (-u) * u) 0 hb).mpr
    simpa using hΓ
  have h1 : IntegrableOn (fun t : ℝ => Real.exp ((a - 3 / 2) * t) * t) (Ioi 0) := by
    apply (hscale.div_const b).congr
    filter_upwards with t
    have he : -(b * t) = (a - 3 / 2) * t := by dsimp [b]; ring
    rw [he]
    field_simp
  apply ((h0.add h1).const_mul (4 * gamma + 24)).congr
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

/-- Each real weight exponent below 3/2 is integrable for the centered actual kernel. -/
theorem r_centered_weighted_integrable (a : ℝ) (ha : a < 3 / 2) :
    IntegrableOn (fun t : ℝ => Real.exp (a * t) *
      (r t - ell * Real.exp (-t / 2))) (Ioi 0) := by
  have hm : Measurable (fun t : ℝ => Real.exp (a * t) *
      (r t - ell * Real.exp (-t / 2))) := by
    have hr : Measurable r := causal_kernel.1.measurable
    fun_prop
  apply (weighted_majorant_integrable ha).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (a * t) *
        ((4 * gamma + 24) * (1 + t) * Real.exp (-3 * t / 2)) :=
      mul_le_mul_of_nonneg_left (r_centered_decay ht.le) (Real.exp_pos _).le
    _ = _ := by
      rw [show (a - 3 / 2) * t = a * t + (-3 * t / 2) by ring, Real.exp_add]
      ring

end D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
