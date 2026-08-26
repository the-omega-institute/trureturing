/- GID: D5/S3/ConceptDynamics/Identifiability/RoleProfileAdaptiveDepthOptimality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identifiability/RoleProfileAdaptiveDepthOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent binary profiles need and admit exactly one experiment per role. -/

import D5.S3.ConceptDynamics.Coding.BinaryProtocolDepthLowerBound
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-26):
   * Exact D5 clause hit `adaptive_binary_protocol_depth_lower_bound` supplies
     the canonical lower bound for `BinaryProtocol` and is applied directly.
   * Exact D5 primitive hits `BinaryProtocol`, `IdentifiesGiven`,
     `worstFiberDiversity`, and `jointReadout` supply the strategy, exactness,
     profile diversity, and nonadaptive joint-readout objects.
   * `BinaryCharacterBasisMinimality` constructs minimum character bases for
     finite abelian groups, but does not state the adaptive protocol clause on
     the full independent-profile carrier.
   * Exact pinned-Mathlib hits `Fintype.card_pi` and `Nat.clog_pow` compute the
     cardinality and binary logarithm. No exact whole-theorem hit was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identifiability.RoleProfileAdaptiveDepthOptimality

open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification
open D5.S3.ConceptDynamics.Coding.BinaryProtocolDepthLowerBound
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- On the carrier of all `r`-bit role profiles, every deterministic adaptive
binary protocol that identifies the profile has depth at least `r`. The
canonical coordinate role basis, queried jointly, identifies every profile
nonadaptively. -/
theorem independent_role_profile_adaptive_depth_optimality (r : Nat) :
    (forall {depth : Nat}
        (protocol : BinaryProtocol (Fin r -> Bool) depth),
      IdentifiesGiven (fun _ : Fin r -> Bool => ()) id protocol ->
        r <= depth) /\
      Function.Injective
        (jointReadout (fun i : Fin r =>
          fun profile : Fin r -> Bool => profile i)) := by
  constructor
  · intro depth protocol identifies
    have lowerBound :=
      adaptive_binary_protocol_depth_lower_bound
        (current := fun _ : Fin r -> Bool => ())
        (target := id) protocol identifies
    have diversity :
        worstFiberDiversity (fun _ : Fin r -> Bool => ()) id = 2 ^ r := by
      simp [worstFiberDiversity, fiberTargetDiversity, fiberTargetValues]
    simpa [diversity, Nat.clog_pow] using lowerBound
  · intro left right sameProfile
    funext i
    simpa [jointReadout] using congrFun sameProfile i

#print axioms independent_role_profile_adaptive_depth_optimality

end D5.S3.ConceptDynamics.Identifiability.RoleProfileAdaptiveDepthOptimality
