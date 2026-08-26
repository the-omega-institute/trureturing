/- GID: D5/S1/Deficit/Beatty/GoldenSubstStartAsymptoticSlope
   generality: I
   mirror-B: D5/B/S1/Deficit/Beatty/GoldenSubstStartAsymptoticSlope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden substitution-start ratio tends to the golden ratio. -/

import D5.S1.Words.GoldenDensity
import D5.S1.Words.GoldenSubstFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.Beatty.GoldenSubstStartAsymptoticSlope

open D5.S1.Words

/-- The substitution-start sequence has asymptotic slope equal to the golden ratio. -/
theorem golden_subst_start_asymptotic_slope :
    Filter.Tendsto (fun v : Nat => (goldenSubstStart v : Real) / (v : Real))
      Filter.atTop (nhds Real.goldenRatio) := by
  have hsum :
      Filter.Tendsto
        (fun v : Nat => (1 : Real) + (goldenWindowTrueCount 0 v : Real) / (v : Real))
        Filter.atTop (nhds ((1 : Real) + Real.goldenRatio⁻¹)) :=
    tendsto_const_nhds.add golden_word_true_density
  have hphi : (1 : Real) + Real.goldenRatio⁻¹ = Real.goldenRatio := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  rw [hphi] at hsum
  apply hsum.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : Nat)] with v hv
  have hv0 : (v : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hv))
  rw [goldenSubstStart]
  push_cast
  field_simp

end D5.S1.Deficit.Beatty.GoldenSubstStartAsymptoticSlope
