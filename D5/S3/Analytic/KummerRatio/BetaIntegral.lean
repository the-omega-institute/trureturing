/- GID: D5/S3/Analytic/KummerRatio/BetaIntegral
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/BetaIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Beta, mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence]
   utility: none
   digest: Real beta moments and the beta integral representation of the Kummer series. -/

import D5.S3.Analytic.KummerRatio.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set MeasureTheory
open scoped Real
open D5.S3.Analytic.KummerRatio.Defs

namespace D5.S3.Analytic.KummerRatio.BetaIntegral

/-- The real beta integral is the quotient of the corresponding Gamma values. -/
theorem integral_beta {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ t in (0:ℝ)..1, t^(p-1) * (1-t)^(q-1)) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p+q) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hconv : (∫ t in (0:ℝ)..1, ((t^(p-1) * (1-t)^(q-1) : ℝ) : ℂ)) =
      Complex.betaIntegral p q := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro t ht
    dsimp only
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht.1),
      Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le)]
    push_cast
    rfl
  rw [hconv, Complex.betaIntegral_eq_Gamma_mul_div _ _ hp hq]
  push_cast
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_add,
      Complex.Gamma_ofReal]

end D5.S3.Analytic.KummerRatio.BetaIntegral
