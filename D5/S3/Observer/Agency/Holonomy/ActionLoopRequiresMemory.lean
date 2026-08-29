/- GID: D5/S3/Observer/Agency/Holonomy/ActionLoopRequiresMemory
   generality: G
   mirror-B: D5/B/S3/Observer/Agency/Holonomy/ActionLoopRequiresMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A policy-visible loop effect requires nontrivial memory transport. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-29):
   * The statement is formulated over arbitrary types and functions.
   * Pinned Mathlib supplies only the elementary logical and function facts
     used below.
   * No finiteness, decidable equality, topology, probability, or algebraic
     structure is assumed unless it occurs explicitly in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Agency.Holonomy.ActionLoopRequiresMemory

universe u v w

/-- If traversing a loop changes the action selected by a policy, then the
loop changes the memory state. -/
theorem policy_change_implies_memory_change
    {Question : Type u} {Memory : Type v} {Action : Type w}
    (policy : Question -> Memory -> Action)
    (question : Question) (holonomy : Memory -> Memory) (memory : Memory)
    (policyChanges :
      policy question (holonomy memory) ≠ policy question memory) :
    holonomy memory ≠ memory := by
  intro memoryFixed
  apply policyChanges
  rw [memoryFixed]

/-- An injective policy coordinate detects every nontrivial memory transport. -/
theorem injective_policy_detects_memory_change
    {Question : Type u} {Memory : Type v} {Action : Type w}
    (policy : Question -> Memory -> Action)
    (question : Question) (holonomy : Memory -> Memory) (memory : Memory)
    (policyInjective : Function.Injective (policy question))
    (memoryChanges : holonomy memory ≠ memory) :
    policy question (holonomy memory) ≠ policy question memory := by
  intro sameAction
  exact memoryChanges (policyInjective sameAction)

#print axioms policy_change_implies_memory_change
#print axioms injective_policy_detects_memory_change

end D5.S3.Observer.Agency.Holonomy.ActionLoopRequiresMemory
