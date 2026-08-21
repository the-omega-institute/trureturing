/- GID: D5/S3/ConceptDynamics/TargetRisk/RefinementTargetRiskMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/TargetRisk/RefinementTargetRiskMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor-map refinement monotonically shrinks target risk. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/- Library-search audit trail (2026-08-21):
   * Exact repository hit
     `RefinementRiskCostTradeoff.refinement_reduces_target_risk_and_raises_cost`
     has the required risk inclusion as its first conjunct and is applied
     directly below.
   * Exact repository hits `ConceptJoinUniversal.Refines`,
     `RefinementRiskCostTradeoff.defectRelation`, and
     `RefinementRiskCostTradeoff.targetRisk` are the frozen family primitives
     used in the public statement.
   * Searches of D5 and the active frozen ledger found no separate theorem
     whose public conclusion is only this boxed risk monotonicity statement.
   * `loogle` and `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.TargetRisk.RefinementTargetRiskMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- A factor-map refinement cannot introduce a target risk that was absent for
the coarser readout. -/
theorem refinement_monotone_target_risk
    {X C D Target : Type*} (q_C : Concept X C) (q_D : Concept X D)
    (targets : Set (Concept X Target)) (refinement : Refines q_C q_D) :
    targetRisk q_D targets ⊆ targetRisk q_C targets :=
  (refinement_reduces_target_risk_and_raises_cost
    q_C q_D targets refinement).1

/-- The refinement hypothesis is inhabited by a constant-to-identity readout
pair on a nonempty finite carrier. -/
example : Refines (fun _ : Bool => ()) (id : Concept Bool Bool) :=
  ⟨fun _ => (), rfl⟩

/-- The public inclusion is nontrivial: without refinement, the reverse
constant/identity pair has a target that is risky only for the coarse readout. -/
example :
    let coarse : Concept Bool Unit := fun _ => ()
    let fine : Concept Bool Bool := id
    let targets : Set (Concept Bool Bool) := {id}
    (id : Concept Bool Bool) ∈ targetRisk coarse targets ∧
      (id : Concept Bool Bool) ∉ targetRisk fine targets := by
  dsimp
  constructor
  · exact ⟨Set.mem_singleton _, ⟨(false, true), rfl, Bool.false_ne_true⟩⟩
  · rintro ⟨_, ⟨⟨left, right⟩, sameCoordinate, differentTarget⟩⟩
    exact differentTarget sameCoordinate

#print axioms refinement_monotone_target_risk

end D5.S3.ConceptDynamics.TargetRisk.RefinementTargetRiskMonotonicity
