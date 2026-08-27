/- GID: D5/S3/ConceptDynamics/Agency/PlanCylinderCommitmentTelescoping
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/PlanCylinderCommitmentTelescoping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Action-selected plan cylinders telescope their finite commitment depths. -/

import Mathlib.Analysis.SpecialFunctions.Log.Base

/- Library-search audit trail (2026-08-27):
   * Current-tree searches for commitment depth, action-selected plan cylinders,
     log-cardinality differences, and history telescoping found no exact declaration.
   * `CumulativeTax` supplies related additive accounting but does not construct
     finite plan cylinders from histories, action prescriptions, and chosen actions.
   * Exact pinned-Mathlib hit `Finset.sum_range_sub'` is applied directly after
     the public cylinder-transition premise identifies consecutive plan spaces.
   * No new definition or abbreviation is introduced: compatible plan sets,
     action cylinders, and their base-two log-cardinality losses are public. -/

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.PlanCylinderCommitmentTelescoping

/-- Along an actual finite history, suppose the compatible plans at every next
history are exactly the plans at the current history that prescribe the chosen
action. The sum of the resulting base-two log-cardinality losses is the loss
from the initial compatible-plan space to the terminal one. -/
theorem plan_cylinder_commitment_depth_telescopes
    {History Plan Action : Type*} [DecidableEq Action]
    (compatiblePlans : History -> { plans : Finset Plan // plans.Nonempty })
    (plannedAction : History -> Plan -> Action)
    (history : Nat -> History) (chosenAction : Nat -> Action) (n : Nat)
    (step : forall t, t < n ->
      (compatiblePlans (history (t + 1))).1 =
        (compatiblePlans (history t)).1.filter
          (fun plan => plannedAction (history t) plan = chosenAction t)) :
    (∑ t ∈ Finset.range n,
        (Real.logb 2 (compatiblePlans (history t)).1.card -
          Real.logb 2
            ((compatiblePlans (history t)).1.filter
              (fun plan => plannedAction (history t) plan = chosenAction t)).card)) =
      Real.logb 2 (compatiblePlans (history 0)).1.card -
        Real.logb 2 (compatiblePlans (history n)).1.card := by
  calc
    (∑ t ∈ Finset.range n,
        (Real.logb 2 (compatiblePlans (history t)).1.card -
          Real.logb 2
            ((compatiblePlans (history t)).1.filter
              (fun plan => plannedAction (history t) plan = chosenAction t)).card)) =
        ∑ t ∈ Finset.range n,
          (Real.logb 2 (compatiblePlans (history t)).1.card -
            Real.logb 2 (compatiblePlans (history (t + 1))).1.card) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [<- step t (Finset.mem_range.mp ht)]
    _ = Real.logb 2 (compatiblePlans (history 0)).1.card -
        Real.logb 2 (compatiblePlans (history n)).1.card := by
      simpa using
        (Finset.sum_range_sub'
          (fun t => Real.logb 2 (compatiblePlans (history t)).1.card) n)

#print axioms plan_cylinder_commitment_depth_telescopes

end D5.S3.ConceptDynamics.Agency.PlanCylinderCommitmentTelescoping
