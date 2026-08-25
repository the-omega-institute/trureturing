/- GID: D5/S3/ConceptDynamics/Disclosure/SensitiveLeakageMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Disclosure/SensitiveLeakageMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joining a fixed sensitive readout preserves concept refinement. -/

import D5.S3.ConceptDynamics.Dependency.BasicDependencyRules

/- Library-search audit trail (2026-08-25):
   * Repository search found the canonical `Concept`, `Refines`, and
     `conceptJoin` family primitives; they are imported rather than redeclared.
   * Exact repository hit `basic_dependency_rules` contains the required
     augmentation law as one clause of a larger seven-clause statement. That
     clause is applied directly below; no standalone exact theorem was found.
   * The pinned library's `Function.FactorsThrough` composition API is adjacent,
     but it has no exact theorem for the canonical concept join and refinement
     relation used by this family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Disclosure.SensitiveLeakageMonotonicity

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Dependency.BasicDependencyRules

/-- Refining a concept also refines its joint readout with a fixed sensitive concept. -/
theorem sensitive_leakage_monotone
    {X Current Refined Sensitive : Type*}
    (current : Concept X Current) (refined : Concept X Refined)
    (sensitive : Concept X Sensitive) (refinement : Refines current refined) :
    Refines (conceptJoin current sensitive) (conceptJoin refined sensitive) := by
  exact (basic_dependency_rules refined current sensitive sensitive).2.2.2.1 refinement

#print axioms sensitive_leakage_monotone

end D5.S3.ConceptDynamics.Disclosure.SensitiveLeakageMonotonicity
