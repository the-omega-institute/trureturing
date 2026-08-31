/- GID: D5/S3/ConceptDynamics/GovernanceFixedPoint/DualRuleDeadlockCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GovernanceFixedPoint/DualRuleDeadlockCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A repair class is deadlocked exactly when it has no jointly allowed repair. -/

import D5.S3.ConceptDynamics.GovernanceFixedPoint.Core

/- Library-search audit trail (2026-08-31):
   * Exact searches for `deadlocked_iff_empty_joint_allowance` and the full
     `Deadlocked`/intersection conclusion found no theorem in D5 or pinned Mathlib.
   * Shape searches found `Set.not_nonempty_iff_eq_empty`, which converts the
     independently frozen reachability predicate to the required empty-set equality.
   * No finiteness, inhabitance, or decidable-membership assumption is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.GovernanceFixedPoint

/-- Deadlock is exactly emptiness of the repair class's jointly allowed part. -/
theorem deadlocked_iff_empty_joint_allowance
    {Repair : Type u}
    (repairClass allow₁ allow₂ : Set Repair) :
    Deadlocked repairClass allow₁ allow₂ ↔
      repairClass ∩ JointAllowed allow₁ allow₂ = ∅ := by
  change
    (¬ (repairClass ∩ JointAllowed allow₁ allow₂).Nonempty) ↔
      repairClass ∩ JointAllowed allow₁ allow₂ = ∅
  exact Set.not_nonempty_iff_eq_empty

#print axioms deadlocked_iff_empty_joint_allowance

-- Elaboration witnesses for domain inhabitance and nontrivial deadlock behavior.
example : Unit := ()

example :
    Deadlocked (∅ : Set Unit) Set.univ Set.univ := by
  rw [deadlocked_iff_empty_joint_allowance]
  simp

example :
    ¬ Deadlocked (Set.univ : Set Unit) Set.univ Set.univ := by
  rw [deadlocked_iff_empty_joint_allowance]
  simp [JointAllowed]

end D5.S3.ConceptDynamics.GovernanceFixedPoint
