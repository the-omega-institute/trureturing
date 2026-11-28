/- GID: D5/S3/Weil/Analytic/NymanWeightedMomentEndpoint
   generality: I
   mirror-B: none(waiver:logarithmic-moment-support)
   mirror-E: none(waiver:logarithmic-moment-analysis)
   anchors: []
   utility: none
   digest: A logarithmic moment controls the endpoint difference quotient. -/

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! The right derivative of a weighted real Mellin integral at its endpoint. -/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace NymanWeightedMomentEndpoint

private def differenceKernel (t x : ℝ) : ℝ :=
  (1 - Real.exp (-(t * Real.log x))) / t

private theorem differenceKernel_measurable (t : ℝ) : Measurable (differenceKernel t) := by
  unfold differenceKernel
  exact (measurable_const.sub (Real.continuous_exp.measurable.comp
    (measurable_const.mul Real.measurable_log).neg)).div measurable_const

private theorem differenceKernel_tendsto (x : ℝ) :
    Tendsto (fun t : ℝ => differenceKernel t x) (𝓝[>] 0) (𝓝 (Real.log x)) := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(t * Real.log x))) (-(Real.log x)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (Real.log x)).neg.exp)
  have hdiff : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(t * Real.log x))) (Real.log x) 0 := by
    simpa only [sub_eq_add_neg, Pi.neg_apply, neg_neg] using hexp.neg.const_add (1 : ℝ)
  simpa [differenceKernel, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hdiff.tendsto_slope_zero_right

private theorem differenceKernel_bounds {t x : ℝ} (ht : 0 < t) (hx : 1 < x) :
    0 ≤ differenceKernel t x ∧ differenceKernel t x ≤ Real.log x := by
  have hprod := mul_nonneg ht.le (Real.log_nonneg hx.le)
  have hexp := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hprod)
  unfold differenceKernel
  refine ⟨div_nonneg (sub_nonneg.mpr hexp) ht.le, (div_le_iff₀ ht).mpr ?_⟩
  linarith [Real.add_one_le_exp (-(t * Real.log x))]

/-- A logarithmic first moment gives the endpoint right difference quotient on `(1, ∞)`. -/
theorem tendsto_integral_difference_quotient {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi (1 : ℝ)))
    (hlog : IntegrableOn (fun x => Real.log x * g x) (Ioi (1 : ℝ))) :
    Tendsto (fun t : ℝ =>
      ((∫ x in Ioi (1 : ℝ), g x) -
        (∫ x in Ioi (1 : ℝ), Real.exp (-(t * Real.log x)) * g x)) / t)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (1 : ℝ), Real.log x * g x)) := by
  have hbound : IntegrableOn (fun x => Real.log x * |g x|) (Ioi (1 : ℝ)) := by
    refine hlog.norm.congr ((ae_restrict_iff' measurableSet_Ioi).2 ?_)
    exact Eventually.of_forall fun x hx => by
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg hx.le)]
  have hlim : Tendsto (fun t : ℝ => ∫ x in Ioi (1 : ℝ), differenceKernel t x * g x)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (1 : ℝ), Real.log x * g x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Real.log x * |g x|) ?_ ?_ hbound ?_
    · exact Eventually.of_forall fun t =>
        (differenceKernel_measurable t).aestronglyMeasurable.mul hg.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      obtain ⟨hnonneg, hupper⟩ := differenceKernel_bounds (mem_Ioi.mp ht) hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_right hupper (abs_nonneg _)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x _ => ?_)
      exact (differenceKernel_tendsto x).mul tendsto_const_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht₀ : 0 < t := mem_Ioi.mp ht
  have hExpMeas : Measurable (fun x : ℝ => Real.exp (-(t * Real.log x))) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul Real.measurable_log).neg
  have hExp : IntegrableOn (fun x => Real.exp (-(t * Real.log x)) * g x) (Ioi (1 : ℝ)) := by
    refine Integrable.mono hg (hExpMeas.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) <| Real.exp_le_one_iff.mpr <|
      neg_nonpos.mpr (mul_nonneg ht₀.le (Real.log_nonneg hx.le))
  calc
    _ = ∫ x in Ioi (1 : ℝ), (g x - Real.exp (-(t * Real.log x)) * g x) / t := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [differenceKernel, div_eq_mul_inv]
        ring
    _ = ((∫ x in Ioi (1 : ℝ), g x) -
        (∫ x in Ioi (1 : ℝ), Real.exp (-(t * Real.log x)) * g x)) / t := by
      rw [integral_div]
      exact congrArg (fun z : ℝ => z / t) (integral_sub hg hExp)

/-- Real Mellin specialization for a signal whose ordinary and logarithmic moments converge. -/
theorem tendsto_weighted_moment_difference_quotient {C : ℝ → ℝ}
    (hC : IntegrableOn (fun x => C x / x ^ 2) (Ioi (1 : ℝ)))
    (hlog : IntegrableOn (fun x => C x * Real.log x / x ^ 2) (Ioi (1 : ℝ))) :
    Tendsto (fun t : ℝ =>
      ((∫ x in Ioi (1 : ℝ), C x / x ^ 2) -
        (∫ x in Ioi (1 : ℝ), x ^ (-t) * (C x / x ^ 2))) / t)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi (1 : ℝ), C x * Real.log x / x ^ 2)) := by
  have hlog' : IntegrableOn (fun x => Real.log x * (C x / x ^ 2)) (Ioi (1 : ℝ)) := by
    refine hlog.congr_fun (fun x _ => ?_) measurableSet_Ioi
    ring
  have h := tendsto_integral_difference_quotient hC hlog'
  have htarget : (∫ x in Ioi (1 : ℝ), Real.log x * (C x / x ^ 2)) =
      ∫ x in Ioi (1 : ℝ), C x * Real.log x / x ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [htarget] at h
  apply h.congr'
  refine Eventually.of_forall fun t => ?_
  have hkernel : (∫ x in Ioi (1 : ℝ), Real.exp (-(t * Real.log x)) * (C x / x ^ 2)) =
      ∫ x in Ioi (1 : ℝ), x ^ (-t) * (C x / x ^ 2) := by
    apply integral_congr_ae
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    dsimp only
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hx),
      show Real.log x * -t = -(t * Real.log x) by ring]
  simp only [hkernel]

end NymanWeightedMomentEndpoint
