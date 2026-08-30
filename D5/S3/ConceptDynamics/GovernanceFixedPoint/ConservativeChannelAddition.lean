/- GID: D5/S3/ConceptDynamics/GovernanceFixedPoint/ConservativeChannelAddition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GovernanceFixedPoint/ConservativeChannelAddition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every deadlocked repair class can be added as an exact conservative channel. -/

import Mathlib.Order.BooleanAlgebra.Set
import D5.S3.ConceptDynamics.GovernanceFixedPoint.DualRuleDeadlockCriterion

/- Library-search audit trail (2026-08-31):
   * Exact searches for `conservative_channel_exists` and its existential
     `ConservativeChannel` conclusion found no declaration in tracked D5 sources.
   * Shape searches found `Set.union_sdiff_cancel_left`; its disjointness premise
     is supplied by the independently frozen G-G deadlock characterization.
   * The witness is exactly `repairClass`; neither original allowance is changed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.GovernanceFixedPoint

/-- A deadlocked repair class itself forms an exact conservative channel. -/
theorem conservative_channel_exists
    {Repair : Type u}
    (repairClass allow₁ allow₂ : Set Repair)
    (hdeadlocked : Deadlocked repairClass allow₁ allow₂) :
    ∃ channel : Set Repair,
      ConservativeChannel repairClass allow₁ allow₂ channel := by
  have hempty :=
    (deadlocked_iff_empty_joint_allowance
      repairClass allow₁ allow₂).mp hdeadlocked
  refine ⟨repairClass, ?_⟩
  constructor
  · exact Set.subset_union_left
  · change
      (JointAllowed allow₁ allow₂ ∪ repairClass) \
          JointAllowed allow₁ allow₂ = repairClass
    exact Set.union_sdiff_cancel_left (by
      rw [Set.inter_comm, hempty])

#print axioms conservative_channel_exists

-- Elaboration witnesses for domain inhabitance and a satisfiable deadlock premise.
example : Unit := ()

example :
    Deadlocked (∅ : Set Unit) Set.univ Set.univ := by
  rw [deadlocked_iff_empty_joint_allowance]
  simp

example :
    ∃ channel : Set Unit,
      ConservativeChannel (∅ : Set Unit) Set.univ Set.univ channel := by
  apply conservative_channel_exists
  rw [deadlocked_iff_empty_joint_allowance]
  simp

end D5.S3.ConceptDynamics.GovernanceFixedPoint
