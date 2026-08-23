/- GID: D5/S3/ConceptDynamics/StrictSeparationImpossibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/StrictSeparationImpossibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Common outcome utilities and homogeneous report costs forbid opposite strict preferences. -/

import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-21):
   * Searches of D5, the active frozen ledger, and the source vocabulary for
     strict separation, mechanism reports, common utilities, and homogeneous
     costs found no exact theorem.
   * Pinned Mathlib exact hits `lt_asymm` and equality rewriting are applied
     directly: common utility transfers the first strict inequality between
     types, after which `lt_asymm` closes the contradiction.
   * Repository incentive and preference modules are adjacent but use distinct
     primitives and do not package this impossibility for an arbitrary result
     map and report-cost function.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.StrictSeparationImpossibility

/-- When two types assign the same utility to every mechanism outcome and
report costs are type-independent, opposite strict preferences for two reports
cannot arise from one mechanism result map. -/
theorem strict_separation_impossible
    {Theta Report Outcome : Type*}
    (theta theta' : Theta) (reportTheta reportTheta' : Report)
    (mechanismResult : Report -> Outcome)
    (utility : Theta -> Outcome -> Real)
    (reportCost : Report -> Real)
    (sameUtility : forall outcome : Outcome,
      utility theta outcome = utility theta' outcome) :
    ¬(
      (utility theta (mechanismResult reportTheta) - reportCost reportTheta >
        utility theta (mechanismResult reportTheta') - reportCost reportTheta') ∧
      (utility theta' (mechanismResult reportTheta') - reportCost reportTheta' >
        utility theta' (mechanismResult reportTheta) - reportCost reportTheta)) := by
  rintro ⟨thetaPrefers, theta'Prefers⟩
  have transferred :
      utility theta' (mechanismResult reportTheta) - reportCost reportTheta >
        utility theta' (mechanismResult reportTheta') - reportCost reportTheta' := by
    simpa only [sameUtility (mechanismResult reportTheta),
      sameUtility (mechanismResult reportTheta')] using thetaPrefers
  exact (lt_asymm transferred theta'Prefers)

/-- Boolean types provide an inhabited witness domain for the source mechanism
and report model, while the theorem remains fully parametric in its primitives. -/
example :
    ∃ (mechanismResult : Bool -> Bool) (utility : Bool -> Bool -> Real)
      (reportCost : Bool -> Real),
      mechanismResult = id ∧
        (forall outcome, utility false outcome = utility true outcome) ∧
        reportCost = fun _ => 0 := by
  refine ⟨id, fun _ outcome => if outcome then 1 else 0, fun _ => 0, rfl, ?_, rfl⟩
  intro outcome
  rfl

#print axioms strict_separation_impossible

end D5.S3.ConceptDynamics.StrictSeparationImpossibility
