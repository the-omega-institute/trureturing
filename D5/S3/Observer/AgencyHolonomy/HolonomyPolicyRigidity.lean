/- GID: D5/S3/Observer/Agency/Holonomy/HolonomyPolicyRigidity
   generality: G
   mirror-B: D5/B/S3/Observer/Agency/Holonomy/HolonomyPolicyRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An injective policy invariant under holonomy forces trivial holonomy. -/

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

namespace D5.S3.Observer.Agency.Holonomy.HolonomyPolicyRigidity

universe u v

/-- A memory holonomy invisible to an injective policy must be the identity. -/
theorem policy_invariant_holonomy_eq_identity
    {Memory : Type u} {Action : Type v}
    (policy : Memory -> Action) (holonomy : Memory -> Memory)
    (policyInjective : Function.Injective policy)
    (policyInvariant : forall memory,
      policy (holonomy memory) = policy memory) :
    holonomy = id := by
  funext memory
  simpa using policyInjective (policyInvariant memory)

/-- Pointwise policy faithfulness rules out a nontrivial invisible loop at
every memory state. -/
theorem no_nontrivial_invisible_loop
    {Memory : Type u} {Action : Type v}
    (policy : Memory -> Action) (holonomy : Memory -> Memory)
    (policyInjective : Function.Injective policy)
    (policyInvariant : forall memory,
      policy (holonomy memory) = policy memory)
    (memory : Memory) :
    holonomy memory = memory :=
  policyInjective (policyInvariant memory)

#print axioms policy_invariant_holonomy_eq_identity
#print axioms no_nontrivial_invisible_loop

end D5.S3.Observer.Agency.Holonomy.HolonomyPolicyRigidity
