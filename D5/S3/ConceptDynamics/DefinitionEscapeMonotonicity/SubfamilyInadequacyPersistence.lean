/- GID: D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/SubfamilyInadequacyPersistence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeMonotonicity/SubfamilyInadequacyPersistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full-family target inadequacy persists under every subfamily restriction. -/

import D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/- Library-search audit trail (2026-08-25):
   * Exact-shape searches for `TargetAdequate (jointReadout`, arbitrary
     subfamilies, and target factorization found no declaration with this
     implication.
   * `BlindKernelObstruction.blind_kernel_obstruction` assumes a stronger
     nonempty blind residual and packages finite-selection and compactification
     clauses. `RelativeSemanticDiagonal.complete_catalog_diagonal_obstructs_subfamily`
     is restricted to a complete-catalog diagonal target. Neither is an exact
     hit for an arbitrary target and family.
   * The canonical source primitives `jointReadout` and `TargetAdequate` are
     imported and instantiated directly. No second family readout or adequacy
     predicate is introduced.
   * Pinned Mathlib provides `Function.FactorsThrough` and
     `Function.factorsThrough_iff`, but no theorem about the repository's
     dependent joint readout and arbitrary subfamilies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.SubfamilyInadequacyPersistence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

/-- If a target cannot be decoded from the full dependent family readout, it
cannot be decoded from the readout of any subfamily, including finite,
countable, and full selections. -/
theorem full_family_inadequacy_persists_to_subfamilies
    {I X Target : Type*} {V : I -> Type*}
    (q : forall i, Concept X (V i)) (target : Concept X Target) :
    (Not (TargetAdequate (jointReadout q) target)) ->
      forall J : Set I,
        Not (TargetAdequate
          (jointReadout (fun member : J => q member.1)) target) := by
  intro fullFamilyInadequate J subfamilyAdequate
  apply fullFamilyInadequate
  rcases subfamilyAdequate with ⟨recover, targetFactors⟩
  refine ⟨recover ∘ (fun fullReadout member => fullReadout member.1), ?_⟩
  rw [targetFactors]
  rfl

#print axioms full_family_inadequacy_persists_to_subfamilies

end D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.SubfamilyInadequacyPersistence
