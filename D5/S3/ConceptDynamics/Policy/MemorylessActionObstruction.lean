/- GID: D5/S3/ConceptDynamics/Policy/MemorylessActionObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Policy/MemorylessActionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Repeated public states with different actions rule out a memoryless policy. -/

import Mathlib

/- Library-search audit trail (2026-08-27):
   * Repository search for a theorem of the form `s (q t) = a t` found no exact hit;
     nearby policy-capability results use different source objects.
   * Pinned Mathlib has no source-specific memoryless-policy theorem; function congruence
     and equality transitivity are the only supporting primitives needed here.
   * Body-shape search for a named memoryless-policy predicate found no canonical primitive,
     so the public statement keeps the policy equation explicit rather than declaring one.
   * Loogle and LeanSearch are unavailable on PATH in this worktree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Policy.MemorylessActionObstruction

/-- If the same public state occurs with two different required actions, no action rule
depending only on the public state can realize both observations. -/
theorem no_memoryless_policy
    {Time PublicState Action : Type*}
    (publicState : Time -> PublicState) (action : Time -> Action)
    (t u : Time) (sameState : publicState t = publicState u)
    (differentAction : action t ≠ action u) :
    ¬ exists policy : PublicState -> Action,
      forall time, policy (publicState time) = action time := by
  rintro ⟨policy, hpolicy⟩
  apply differentAction
  calc
    action t = policy (publicState t) := (hpolicy t).symm
    _ = policy (publicState u) := congrArg policy sameState
    _ = action u := hpolicy u

#print axioms no_memoryless_policy

end D5.S3.ConceptDynamics.Policy.MemorylessActionObstruction
