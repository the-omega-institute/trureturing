/- GID: D5/S3/Analysis/HalfIntegerSchwingerIntegral
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary5-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An elementary Schwinger integral obtained by differentiating Gaussian subordination and applying reciprocal substitution. -/

import OmegaBuild.Commands
import D5.S3.Analysis.GaussianSubordination
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

An elementary Schwinger integral obtained by differentiating Gaussian subordination
and applying reciprocal substitution.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open scoped Topology

namespace Omega

private def moment (b a s : ℝ) : ℝ :=
  s ^ (-(1 / 2) : ℝ) * Real.exp (-a * s - b / s)

private theorem moment_integral {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ s in Ioi (0 : ℝ), moment b a s) =
      Real.sqrt Real.pi / Real.sqrt a * Real.exp (-(2 * Real.sqrt b) * Real.sqrt a) := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · have he (s : ℝ) : moment 0 a s = s ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(a * s)) := by
      rw [moment, zero_div, sub_zero, neg_mul]
      congr 2
      norm_num
    simp_rw [he]
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2) ha,
      Real.Gamma_one_half_eq,
      one_div, Real.inv_rpow ha.le, ← Real.sqrt_eq_rpow, div_eq_inv_mul]
    simp only [Real.sqrt_zero, mul_zero, neg_zero, zero_mul, Real.exp_zero, mul_one]
  · have hs := gaussian_subordination (Real.sqrt_pos.2 ha)
      (mul_pos two_pos (Real.sqrt_pos.2 hb))
    simp only [Real.sq_sqrt ha.le, show (2 * Real.sqrt b) ^ 2 = 4 * b by
      rw [mul_pow, Real.sq_sqrt hb.le]; ring] at hs
    have he (s : ℝ) : -(a * s) - 4 * b / (4 * s) = -a * s - b / s := by ring
    simp_rw [he] at hs
    unfold moment
    have hsa := (Real.sqrt_pos.2 ha).ne'
    have hsp := (Real.sqrt_pos.2 Real.pi_pos).ne'
    apply (mul_right_inj' (show (1 / (2 * Real.sqrt Real.pi) : ℝ) ≠ 0 by positivity)).mp
    rw [← hs]
    field_simp

private theorem moment_deriv (b : ℝ) (hb : 0 ≤ b) :
    HasDerivAt (fun a => ∫ s in Ioi (0 : ℝ), moment b a s)
      (-(∫ s in Ioi (0 : ℝ), s ^ (1 / 2 : ℝ) * Real.exp (-s - b / s))) 1 := by
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let F' (a s : ℝ) := -(s ^ (1 / 2 : ℝ) * Real.exp (-a * s - b / s))
  have hpow {s : ℝ} (hs : 0 < s) : s ^ (-(1 / 2) : ℝ) * s = s ^ (1 / 2 : ℝ) := by
    conv_lhs => arg 2; rw [← Real.rpow_one s]
    rw [← Real.rpow_add hs]
    congr 1 <;> norm_num
  have hm (a : ℝ) : AEStronglyMeasurable (moment b a) μ := by
    unfold moment
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have hfm : AEStronglyMeasurable (F' 1) μ := by
    dsimp [F']
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have hi : Integrable (moment b 1) μ := by
    apply (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
      (s := -(1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 1)).mono' (hm 1)
    filter_upwards [ae_restrict_mem measurableSet_Ioi (μ := volume)] with s hs
    change 0 < s at hs
    rw [moment, Real.norm_of_nonneg (by positivity : 0 ≤ s ^ (-(1 / 2) : ℝ) * _)]
    simp only [Real.rpow_one, neg_mul, one_mul]
    gcongr
    exact sub_le_self _ (div_nonneg hb hs.le)
  have hd : ∀ᵐ s ∂μ, ∀ a ∈ Ioi (1 / 2 : ℝ),
      HasDerivAt (fun x => moment b x s) (F' a s) a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi (μ := volume)] with s hs a _
    have h := (((hasDerivAt_id a).neg.mul_const s).sub_const (b / s)).exp.const_mul
      (s ^ (-(1 / 2) : ℝ))
    have he : (fun y => s ^ (-(1 / 2) : ℝ) * Real.exp ((-id) y * s - b / s)) =
        fun x => moment b x s := rfl
    rw [he] at h
    convert h using 1
    dsimp [F']
    simp only [neg_one_mul, Pi.neg_apply, id_eq]
    rw [show s ^ (-(1 / 2) : ℝ) * (Real.exp (-a * s - b / s) * -s) =
      -(s ^ (-(1 / 2) : ℝ) * s * Real.exp (-a * s - b / s)) by ring, hpow hs]
  have hB : ∀ᵐ s ∂μ, ∀ a ∈ Ioi (1 / 2 : ℝ),
      ‖F' a s‖ ≤ s ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2) * s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi (μ := volume)] with s hs a ha
    change 0 < s at hs
    change 1 / 2 < a at ha
    dsimp only [F']
    rw [norm_neg, Real.norm_of_nonneg (by positivity : 0 ≤ s ^ (1 / 2 : ℝ) * _)]
    gcongr
    nlinarith [div_nonneg hb hs.le, mul_le_mul_of_nonneg_right ha.le hs.le]
  have hBi : Integrable (fun s : ℝ => s ^ (1 / 2 : ℝ) * Real.exp (-(1 / 2) * s)) μ := by
    change IntegrableOn _ (Ioi 0) volume
    simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)
  simpa only [F', integral_neg, one_mul, neg_one_mul] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)) (.of_forall hm) hi hfm hB hBi hd).2

private theorem moment_half {b : ℝ} (hb : 0 ≤ b) :
    (∫ s in Ioi (0 : ℝ), s ^ (1 / 2 : ℝ) * Real.exp (-s - b / s)) =
      Real.sqrt Real.pi / 2 * Real.exp (-(2 * Real.sqrt b)) * (1 + 2 * Real.sqrt b) := by
  have he : (fun a => ∫ s in Ioi (0 : ℝ), moment b a s) =ᶠ[𝓝 1]
      (fun a => Real.sqrt Real.pi / Real.sqrt a * Real.exp (-(2 * Real.sqrt b) * Real.sqrt a)) := by
    filter_upwards [Ioi_mem_nhds zero_lt_one] with a ha using moment_integral ha hb
  have h := (moment_deriv b hb).congr_of_eventuallyEq he.symm
  have hs : HasDerivAt Real.sqrt (1 / 2) 1 := by
    simpa using (Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0))
  have hd := ((hasDerivAt_const (1 : ℝ) (Real.sqrt Real.pi)).div hs (by norm_num))
    |>.mul ((hs.const_mul (-(2 * Real.sqrt b))).exp)
  have hk := h.unique hd
  change _ = (0 * Real.sqrt 1 - Real.sqrt Real.pi * (1 / 2)) / Real.sqrt 1 ^ 2 *
    Real.exp (-(2 * Real.sqrt b) * Real.sqrt 1) + Real.sqrt Real.pi / Real.sqrt 1 * _ at hk
  simp only [Real.sqrt_one, mul_one, div_one, zero_sub, one_pow] at hk
  rw [← neg_inj, hk]
  ring

/-- The five-dimensional Schwinger integral for nonnegative mass and positive separation. -/
theorem integral_half_integer_schwinger {m q : ℝ} (hm : 0 ≤ m) (hq : 0 < q) :
    (∫ s in Ioi (0 : ℝ), s ^ (-(5 / 2) : ℝ) * Real.exp (-m ^ 2 * s - q / (4 * s))) =
      4 * Real.sqrt Real.pi / (q * Real.sqrt q) *
        Real.exp (-(m * Real.sqrt q)) * (1 + m * Real.sqrt q) := by
  let c := q / 4
  have hc : 0 < c := by positivity
  rw [integral_Ioi_const_div hc]
  have he : (∫ s in Ioi (0 : ℝ), (c / s ^ 2) •
      ((c / s) ^ (-(5 / 2) : ℝ) * Real.exp (-m ^ 2 * (c / s) - q / (4 * (c / s))))) =
      c ^ (-(3 / 2) : ℝ) * ∫ s in Ioi (0 : ℝ),
        s ^ (1 / 2 : ℝ) * Real.exp (-s - (m ^ 2 * c) / s) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi (μ := volume)] with s hs
    change 0 < s at hs
    have hrad : (c / s ^ 2) * (c / s) ^ (-(5 / 2) : ℝ) =
        c ^ (-(3 / 2) : ℝ) * s ^ (1 / 2 : ℝ) := by
      rw [Real.div_rpow hc.le hs.le, show c / s ^ 2 * (c ^ (-(5 / 2) : ℝ) /
        s ^ (-(5 / 2) : ℝ)) = (c ^ (-(5 / 2) : ℝ) * c) /
          (s ^ (2 : ℝ) * s ^ (-(5 / 2) : ℝ)) by rw [Real.rpow_two]; ring,
        ← Real.rpow_add hs, ← Real.rpow_add_one hc.ne',
        show (2 + -(5 / 2) : ℝ) = -(1 / 2) by norm_num,
        show (-(5 / 2) + 1 : ℝ) = -(3 / 2) by norm_num,
        Real.rpow_neg hs.le, div_inv_eq_mul]
    rw [smul_eq_mul, ← mul_assoc, hrad, mul_assoc]
    congr 3
    unfold c
    field_simp
    <;> ring
  rw [he, moment_half (by positivity : 0 ≤ m ^ 2 * c)]
  have hs : Real.sqrt (m ^ 2 * c) = m * Real.sqrt q / 2 := by
    rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq hm, show c = q / 4 from rfl,
      Real.sqrt_div hq.le, show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  have hp : c ^ (-(3 / 2) : ℝ) = 8 / (q * Real.sqrt q) := by
    rw [Real.rpow_neg hc.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hc, Real.rpow_one, ← Real.sqrt_eq_rpow, show c = q / 4 from rfl,
      Real.sqrt_div hq.le, show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    field_simp
    <;> norm_num
  rw [hs, hp, show 2 * (m * Real.sqrt q / 2) = m * Real.sqrt q by ring]
  ring

end Omega
