/- GID: D5/S3/ConceptDynamics/Provenance/SourceCutsetInclusionMinimalHittingDuality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/SourceCutsetInclusionMinimalHittingDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Source cuts hit exactly every canonical inclusion-minimal proof support. -/

import D5.S3.ConceptDynamics.DagCompletion.MinimalDependencySupport
import D5.S3.ConceptDynamics.Provenance.SourceCutsetHittingDuality

/- Library-search audit trail (2026-08-27):
   * Repository name and body-shape searches found the frozen source-cutset
     theorem and the canonical `InclusionMinimalSupport` predicate, but no
     theorem already stated with that canonical predicate.
   * The frozen `IsMinimalProofSupport` body is alpha-equivalent to
     `InclusionMinimalSupport`; its hitting predicate and hitting minimum are
     therefore not reused here. The independent frozen `IsSourceCut` and
     `proofResilience` definitions have no other body-shape match in D5.
   * Pinned Mathlib searches for hitting sets, minimum hitting cardinality, and
     hypergraph transversals found no exact theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Provenance.SourceCutsetInclusionMinimalHittingDuality

open D5.S3.ConceptDynamics.DagCompletion.MinimalDependencySupport
open D5.S3.ConceptDynamics.Provenance.SourceCutsetHittingDuality

/-- For finite monotone provenance, source cuts are precisely the removals that
hit every canonical inclusion-minimal proof support. Their least cardinality is
the corresponding minimum hitting cardinality. -/
theorem source_cutset_inclusion_minimal_hitting_duality
    {Source : Type*} [Fintype Source] [DecidableEq Source]
    (provable : Finset Source -> Prop) (provableMonotone : Monotone provable) :
    let hitsEveryInclusionMinimalSupport : Finset Source -> Prop :=
      fun removed =>
        forall support : Finset Source,
          InclusionMinimalSupport provable support ->
            (removed ∩ support).Nonempty
    (forall removed : Finset Source,
      IsSourceCut provable removed <->
        hitsEveryInclusionMinimalSupport removed) ∧
      proofResilience provable =
        sInf {size : Nat | exists removed : Finset Source,
          hitsEveryInclusionMinimalSupport removed ∧ removed.card = size} := by
  simpa only [
    HitsEveryMinimalProofSupport,
    minimumHittingCardinality,
    IsMinimalProofSupport,
    InclusionMinimalSupport
  ] using
    SourceCutsetHittingDuality.source_cutset_hitting_duality
      provable provableMonotone

#print axioms source_cutset_inclusion_minimal_hitting_duality

end D5.S3.ConceptDynamics.Provenance.SourceCutsetInclusionMinimalHittingDuality
