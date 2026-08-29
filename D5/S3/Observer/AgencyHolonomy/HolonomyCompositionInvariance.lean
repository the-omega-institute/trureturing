/- GID: D5/S3/Observer/AgencyHolonomy/HolonomyCompositionInvariance
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/HolonomyCompositionInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Policy-invisible memory transports are closed under composition. -/

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

namespace D5.S3.Observer.AgencyHolonomy.HolonomyCompositionInvariance

universe u v

def PolicyInvisible {Memory : Type u} {Action : Type v}
    (policy : Memory -> Action) (transport : Memory -> Memory) : Prop :=
  forall memory, policy (transport memory) = policy memory

/-- The composite of two policy-invisible transports is policy-invisible. -/
theorem invisible_transports_compose
    {Memory : Type u} {Action : Type v}
    (policy : Memory -> Action) (first second : Memory -> Memory)
    (firstInvisible : PolicyInvisible policy first)
    (secondInvisible : PolicyInvisible policy second) :
    PolicyInvisible policy (second ∘ first) := by
  intro memory
  rw [Function.comp_apply, secondInvisible (first memory),
    firstInvisible memory]

/-- Identity transport is policy-invisible. -/
theorem identity_transport_invisible
    {Memory : Type u} {Action : Type v}
    (policy : Memory -> Action) :
    PolicyInvisible policy id := by
  intro memory
  rfl

#print axioms invisible_transports_compose
#print axioms identity_transport_invisible

end D5.S3.Observer.AgencyHolonomy.HolonomyCompositionInvariance
