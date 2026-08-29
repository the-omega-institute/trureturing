/- GID: D5/S3/ConceptDynamics/Governance/ConsumptionProductionInputSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/ConsumptionProductionInputSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A two-artifact witness separates runtime consumption from production input. -/

import Mathlib.Data.Set.Finite.Basic

/- Library-search audit trail (2026-08-29):
   * Exact searches for `prodInputs`, `ConsumptionProductionInputSeparation`,
     and runtime-consumer/production-input relations in `D5` found no declaration.
   * `CommitInterfaceSealPreservation` and `TargetLaunderingCriterion` were
     inspected directly; their commitment carriers do not encode either relation.
   * Pinned Mathlib v4.31.0 supplies `Bool`, `Set.mem_empty_iff_false`, and
     `Set.mem_singleton_iff`, but no domain theorem connecting these relations.
     The proof therefore uses those library facts in the concrete source witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.ConsumptionProductionInputSeparation

/-- On the finite two-element artifact type, an artifact can consume another at
runtime even though its production-input record is present and empty. -/
theorem consumption_not_inverse_to_production_input :
    exists (x y : Bool)
      (consumers : Bool -> Set Bool)
      (prodInputs : Bool -> Option (Set Bool)),
      x ≠ y /\
        consumers x = {y} /\
        y ∈ consumers x /\
        prodInputs y = some ∅ /\
        x ∉ (∅ : Set Bool) := by
  refine ⟨false, true,
    (fun artifact => if artifact = false then {true} else ∅),
    (fun artifact => if artifact = true then some ∅ else none), ?_⟩
  simp

#print axioms consumption_not_inverse_to_production_input

end D5.S3.ConceptDynamics.Governance.ConsumptionProductionInputSeparation
