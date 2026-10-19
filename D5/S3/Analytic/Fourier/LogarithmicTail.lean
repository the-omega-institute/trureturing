/- GID: D5/S3/Analytic/Fourier/LogarithmicTail
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/LogarithmicTail
   mirror-E: none(waiver:one-dimensional-improper-integral)
   anchors: []
   utility: none
   digest: Evaluate and bound the shifted-logarithmic Fourier tail on every positive half-line. -/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The logarithmic Fourier tail

The actual integrand `(1 + log (1 + t)) / t^2` is integrable on `t > R`
for every `R > 0`. Its tail is evaluated from an explicit antiderivative
whose limit at infinity is proved, then bounded without a numerical cutoff.

The unshifted logarithm in Robin.QuotientIntegralBudget is a different
integrand. This module does not import that arithmetic development.
All declarations are analytic statements over an unbounded real domain;
there is no finite computation or certified numerical instance.
-/

noncomputable section

namespace D5.S3.Analytic.Fourier.LogarithmicTail

open Filter MeasureTheory Set
open scoped Topology

private def tailPrimitive (t : ℝ) : ℝ :=
  -(1 + Real.log (1 + t)) / t - (Real.log (1 + t) - Real.log t)

private theorem hasDerivAt_tailPrimitive {t : ℝ} (ht : 0 < t) :
    HasDerivAt tailPrimitive ((1 + Real.log (1 + t)) / t ^ 2) t := by
  have hplus : 0 < 1 + t := by positivity
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t := by
    simpa only [id_eq] using ((hasDerivAt_id t).const_add 1).log hplus.ne'
  have h := ((hlog.const_add 1).neg.div (hasDerivAt_id t) ht.ne').sub
    (hlog.sub (Real.hasDerivAt_log ht.ne'))
  change HasDerivAt
    (fun x : ℝ => -(1 + Real.log (1 + x)) / x -
      (Real.log (1 + x) - Real.log x)) _ t
  apply h.congr_deriv
  simp only [Pi.neg_apply, id_eq]
  field_simp [ht.ne', hplus.ne']
  ring

private theorem tendsto_tailPrimitive :
    Tendsto tailPrimitive atTop (𝓝 0) := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hdiff : Tendsto (fun t : ℝ => Real.log (1 + t) - Real.log t)
      atTop (𝓝 0) := by
    simpa only [add_comm] using Real.tendsto_log_comp_add_sub_log 1
  have hdiffdiv : Tendsto
      (fun t : ℝ => (Real.log (1 + t) - Real.log t) / t) atTop (𝓝 0) :=
    hdiff.div_atTop tendsto_id
  have hquot : Tendsto (fun t : ℝ => (1 + Real.log (1 + t)) / t)
      atTop (𝓝 0) := by
    have heq : (fun t : ℝ => (1 + Real.log (1 + t)) / t) =
        fun t : ℝ => 1 / t + Real.log t / t + (Real.log (1 + t) - Real.log t) / t := by
      ext t
      ring
    rw [heq]
    simpa only [add_zero] using (hinv.add hlog).add hdiffdiv
  change Tendsto
    (fun t : ℝ => -(1 + Real.log (1 + t)) / t - (Real.log (1 + t) - Real.log t))
    atTop (𝓝 0)
  simpa only [neg_div, neg_zero, sub_zero] using hquot.neg.sub hdiff

/-- The actual shifted-logarithmic tail is integrable above every positive cutoff. -/
theorem integrableOn_logarithmic_tail {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => (1 + Real.log (1 + t)) / t ^ 2) (Ioi R) := by
  refine integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => hasDerivAt_tailPrimitive (hR.trans_le ht)) ?_
    tendsto_tailPrimitive
  intro t ht
  have htpos : 0 < t := hR.trans ht
  exact div_nonneg
    (add_nonneg zero_le_one (Real.log_nonneg (by linarith))) (sq_nonneg t)

/-- Exact improper integration retains the logarithmic endpoint correction. -/
theorem integral_logarithmic_tail {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in Ioi R, (1 + Real.log (1 + t)) / t ^ 2) =
      (1 + Real.log (1 + R)) / R + Real.log (1 + 1 / R) := by
  have hlogratio : Real.log (1 + 1 / R) = Real.log (1 + R) - Real.log R := by
    rw [show 1 + 1 / R = (1 + R) / R by field_simp; ring,
      Real.log_div (by positivity : (1 + R) ≠ 0) hR.ne']
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => hasDerivAt_tailPrimitive (hR.trans_le ht))
    (integrableOn_logarithmic_tail hR) tendsto_tailPrimitive
  rw [h, hlogratio]
  simp only [tailPrimitive]
  ring

/-- The usual logarithmic tail budget holds for every positive cutoff,
so in particular for all cutoffs at least one. -/
theorem integral_logarithmic_tail_le {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in Ioi R, (1 + Real.log (1 + t)) / t ^ 2) ≤
      (2 + Real.log (1 + R)) / R := by
  rw [integral_logarithmic_tail hR]
  have hlog : Real.log (1 + 1 / R) ≤ 1 / R := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / R)
    linarith
  calc
    (1 + Real.log (1 + R)) / R + Real.log (1 + 1 / R) ≤
        (1 + Real.log (1 + R)) / R + 1 / R := add_le_add le_rfl hlog
    _ = (2 + Real.log (1 + R)) / R := by ring

#print axioms integrableOn_logarithmic_tail
#print axioms integral_logarithmic_tail
#print axioms integral_logarithmic_tail_le

end D5.S3.Analytic.Fourier.LogarithmicTail
