/- GID: D5/S3/ConceptDynamics/Communication/ExpressiveReportingCountermodel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/ExpressiveReportingCountermodel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A lossless direct report carrier permits an optimal nontruthful strategy. -/

import D5.S3.ConceptDynamics.Communication.TruthfulnessSufficiencyIndependence
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-24):
   * Exact family hit `ReportProfile` supplies the canonical true-report and
     sent-report primitives and is imported rather than redeclared.
   * `truthfulness_sufficiency_independence` contains an adjacent Boolean
     nontruthful sufficient profile, but its public witness neither states that
     the truthful direct report is `id` nor exposes mechanism utilities and
     strategic optimality, so it does not cover this atom's countermodel.
   * Repository searches for direct reporting, Boolean misreports, report-space
     capacity, and utility-maximizing nontruthful strategies found no exact
     theorem. `DominantStrategyDirectification` proves the converse direction
     under a dominant-strategy premise.
   * Pinned Mathlib supplies `Bool.false_ne_true` and ordered real numerals; it
     has no mechanism-design theorem for this countermodel. `loogle` and
     `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.ExpressiveReportingCountermodel

open D5.S3.ConceptDynamics.Communication.TruthfulnessSufficiencyIndependence

/-- There is a direct Boolean mechanism whose report and type carriers agree
and whose truthful encoding is lossless, yet both types strictly prefer the
outcome induced by report `false`. The constant-`false` sent strategy is
optimal, and type `true` therefore sends a nontruthful report. -/
theorem expressive_report_space_does_not_force_truthful_revelation :
    ∃ (profile : ReportProfile Bool Bool Bool)
      (mechanism : Bool -> Bool) (utility : Bool -> Bool -> Real),
      profile.trueReport = id ∧
        profile.sentReport true = false ∧
        profile.sentReport ≠ profile.trueReport ∧
        (∀ trueType,
          utility trueType (mechanism false) >
            utility trueType (mechanism true)) ∧
        ∀ trueType alternativeReport,
          utility trueType (mechanism (profile.sentReport trueType)) ≥
            utility trueType (mechanism alternativeReport) := by
  let profile : ReportProfile Bool Bool Bool :=
    { target := id
      trueReport := id
      sentReport := fun _ => false
      decode := id }
  let mechanism : Bool -> Bool := id
  let utility : Bool -> Bool -> Real := fun _ outcome => if outcome then 0 else 1
  refine ⟨profile, mechanism, utility, rfl, rfl, ?_, ?_, ?_⟩
  · intro truthful
    exact Bool.false_ne_true (congrFun truthful true)
  · intro trueType
    norm_num [utility, mechanism]
  · intro trueType alternativeReport
    cases alternativeReport <;> norm_num [profile, utility, mechanism]

#print axioms expressive_report_space_does_not_force_truthful_revelation

end D5.S3.ConceptDynamics.Communication.ExpressiveReportingCountermodel
