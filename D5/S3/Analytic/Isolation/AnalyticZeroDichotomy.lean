/- GID: D5/S3/Analytic/Isolation/AnalyticZeroDichotomy
   generality: G
   mirror-B: D5/B/S3/Analytic/Isolation/AnalyticZeroDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Analytic relations either vanish identically or have isolated zeros. -/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic

/- Provenance: thin wrapper over pinned mathlib's global isolated-zero dichotomy,
   `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`. -/

open Filter

namespace D5.S3.Analytic.Isolation.AnalyticZeroDichotomy

/-- A complex-analytic relation on a preconnected set either vanishes identically or has
codiscretely many nonzero points. -/
theorem analytic_zero_dichotomy
    {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) :
    Set.EqOn f 0 U ∨ ∀ᶠ z in codiscreteWithin U, f z ≠ 0 :=
  hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hU

end D5.S3.Analytic.Isolation.AnalyticZeroDichotomy
