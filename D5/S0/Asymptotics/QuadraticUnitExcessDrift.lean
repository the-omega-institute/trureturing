/- GID: D5/S0/Asymptotics/QuadraticUnitExcessDrift
   generality: G
   mirror-B: D5/B/S0/Asymptotics/QuadraticUnitExcessDrift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The reciprocal excess identity gives the closed drift slope, while reciprocal invariance and antisymmetry force zero drift. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace D5.S0.Asymptotics.QuadraticUnitExcessDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Let `V` be a reciprocal-pair value and `s` its drift. If the reciprocal
excess identity holds, a unit `epsilon > 1` has reciprocal trace `2 * t`, and
the pair value cancels there, then its drift is
`-pi * (2 * t - 3) / (6 * log epsilon)`. Moreover, reciprocal antisymmetry
forces the drift to vanish at every point where it is also reciprocal-invariant.

The positivity of `epsilon` is explicit because Lean defines `Real.log` on all
reals; `1 < epsilon` is what makes division by `log epsilon` legitimate. -/
theorem quadratic_unit_excess_drift
    (V s : Real -> Real) (epsilon : Real) (t : Int)
    (hepsilon : 1 < epsilon)
    (hreciprocal : forall x, 0 < x -> s x⁻¹ = -s x)
    (hexcess : forall x, 0 < x ->
      V x + V x⁻¹ = Real.pi / 6 * (x + x⁻¹) - Real.pi / 2 + s x * Real.log x)
    (htrace : epsilon + epsilon⁻¹ = 2 * (t : Real))
    (hcancel : V epsilon + V epsilon⁻¹ = 0) :
    s epsilon = -(Real.pi * (2 * (t : Real) - 3)) / (6 * Real.log epsilon) ∧
      forall x, 0 < x -> s x⁻¹ = s x -> s x = 0 := by
  have hepsilon_pos : 0 < epsilon := lt_trans (by norm_num) hepsilon
  have hlog_pos : 0 < Real.log epsilon := Real.log_pos hepsilon
  have heq := hexcess epsilon hepsilon_pos
  constructor
  · rw [htrace, hcancel] at heq
    apply (eq_div_iff (mul_ne_zero (by norm_num) hlog_pos.ne')).2
    linear_combination -6 * heq
  · intro x hx hinvariant
    have hanti := hreciprocal x hx
    linarith

#print axioms quadratic_unit_excess_drift

end D5.S0.Asymptotics.QuadraticUnitExcessDrift
