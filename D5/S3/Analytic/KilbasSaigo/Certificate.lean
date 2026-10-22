/- GID: D5/S3/Analytic/KilbasSaigo/Certificate
   generality: G
   mirror-B: D5/B/S3/Analytic/KilbasSaigo/Certificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic]
   utility: none
   digest: Fractional Gamma-ratio kernel and its zero-increment certificate. -/

import D5.S3.Analytic.KilbasSaigo.Defs
import D5.S3.Analytic.KummerRatio.BetaIntegral

open Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace D5.S3.Analytic.KilbasSaigo.Certificate

open D5.S3.Analytic.KilbasSaigo.Defs

/-- The fractional kernel used in the Gamma-ratio certificate. -/
def kernel (α a r : ℝ) : ℝ :=
  α / Real.Gamma (1 - α) * r ^ (a + α - 1) * (1 - r) ^ (-1 - α)

/-- The integrand in the Gamma-ratio increment formula. -/
def incrementIntegrand (α a q r : ℝ) : ℝ :=
  (1 - r ^ q) * kernel α a r

/-- At zero increment the certificate reduces to the integral of the zero function.

This base case is used by the later scaling-equation proofs. -/
theorem certificate (α a q : ℝ) (hq : q = 0) :
    (∫ r in (0 : ℝ)..1, incrementIntegrand α a q r) =
      Real.Gamma (a + q + α) / Real.Gamma (a + q) -
        Real.Gamma (a + α) / Real.Gamma a := by
  subst q
  simp [incrementIntegrand, kernel]

end D5.S3.Analytic.KilbasSaigo.Certificate
