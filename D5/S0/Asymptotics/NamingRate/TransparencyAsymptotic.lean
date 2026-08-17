/- GID: D5/S0/Asymptotics/NamingRate/TransparencyAsymptotic
   generality: G
   mirror-B: D5/B/S0/Asymptotics/NamingRate/TransparencyAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The naming-rate transparency is asymptotic to the reciprocal sample count. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace D5.S0.Asymptotics.NamingRate.TransparencyAsymptotic

/-- For the naming rate `F(n) = (n + 1) / (n + 2)`, the scaled transparency
`n * (1 - F(n))` tends to one. -/
theorem naming_rate_transparency_asymptotic :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * (1 - ((n : ℝ) + 1) / ((n : ℝ) + 2)))
      Filter.atTop (nhds 1) := by
  apply (tendsto_natCast_div_add_atTop (2 : ℝ)).congr'
  filter_upwards with n
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

#print axioms naming_rate_transparency_asymptotic

end D5.S0.Asymptotics.NamingRate.TransparencyAsymptotic
