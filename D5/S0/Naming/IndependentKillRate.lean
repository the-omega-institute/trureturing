/- GID: D5/S0/Naming/IndependentKillRate
   generality: G
   mirror-B: D5/B/S0/Naming/IndependentKillRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent coverage and visibility make the kill rate their product. -/

import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

namespace D5.S0.Naming.IndependentKillRate

/-- If coverage and visibility are independent events with the named rates,
then their intersection has the product rate. -/
theorem independent_kill_rate {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) (covered visible : Set Outcome)
    (coverageRate visibilityRate : ENNReal)
    (independent : IndepSet covered visible measure)
    (coverage : measure covered = coverageRate)
    (visibility : measure visible = visibilityRate) :
    measure (covered ∩ visible) = coverageRate * visibilityRate := by
  rw [independent.measure_inter_eq_mul, coverage, visibility]

/-- The event and rate hypotheses are jointly satisfiable. -/
example : exists (measure : Measure PUnit) (covered visible : Set PUnit)
    (coverageRate visibilityRate : ENNReal),
    IndepSet covered visible measure /\
      measure covered = coverageRate /\ measure visible = visibilityRate := by
  refine ⟨0, ∅, ∅, 0, 0, ?_, by simp, by simp⟩
  exact indepSet_empty_left (μ := (0 : Measure PUnit)) ∅

end D5.S0.Naming.IndependentKillRate
