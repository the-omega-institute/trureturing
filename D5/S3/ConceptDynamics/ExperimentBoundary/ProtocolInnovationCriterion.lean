/- GID: D5/S3/ConceptDynamics/ExperimentBoundary/ProtocolInnovationCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentBoundary/ProtocolInnovationCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A protocol is innovative exactly when it separates a current observation fiber. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-28):
   * Body-shape searches found the canonical `Concept`, `conceptJoin`, and
     `Setoid.ker` primitives; they are imported rather than redeclared.
   * `LatentAdequacyCriterion.latent_join_strict_iff_inadequate` gives strict
     factorization refinement versus non-recoverability, but does not publicly
     expose the source's separating state pair.
   * Pinned Mathlib's `Set.ssubset_iff_exists` is the exact strict-containment
     witness characterization and is applied directly below. No exact theorem
     combining the canonical join with the explicit witness was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentBoundary.ProtocolInnovationCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- Adjoining a protocol law strictly shrinks the current observation kernel
exactly when the new law separates two states in one current observation fiber. -/
theorem protocol_innovation_iff_separates_current_fiber
    {X Current Law : Type*}
    (current : Concept X Current) (protocolLaw : Concept X Law) :
    {pair : X × X |
        Setoid.ker (conceptJoin current protocolLaw) pair.1 pair.2} ⊂
        {pair : X × X | Setoid.ker current pair.1 pair.2} ↔
      ∃ x y, current x = current y ∧ protocolLaw x ≠ protocolLaw y := by
  constructor
  · intro strict
    rcases (Set.ssubset_iff_exists.mp strict).2 with
      ⟨pair, sameCurrent, notSameJoin⟩
    refine ⟨pair.1, pair.2, sameCurrent, ?_⟩
    intro sameLaw
    exact notSameJoin (Prod.ext sameCurrent sameLaw)
  · rintro ⟨x, y, sameCurrent, differentLaw⟩
    apply Set.ssubset_iff_exists.mpr
    constructor
    · intro pair sameJoin
      exact congrArg Prod.fst sameJoin
    · refine ⟨(x, y), sameCurrent, ?_⟩
      intro sameJoin
      exact differentLaw (congrArg Prod.snd sameJoin)

example :
    {pair : Bool × Bool |
        Setoid.ker
          (conceptJoin (fun _ : Bool => ()) (id : Bool → Bool))
          pair.1 pair.2} ⊂
      {pair : Bool × Bool | Setoid.ker (fun _ : Bool => ()) pair.1 pair.2} := by
  apply (protocol_innovation_iff_separates_current_fiber
    (fun _ : Bool => ()) (id : Bool → Bool)).2
  exact ⟨false, true, rfl, Bool.false_ne_true⟩

#print axioms protocol_innovation_iff_separates_current_fiber

end D5.S3.ConceptDynamics.ExperimentBoundary.ProtocolInnovationCriterion
