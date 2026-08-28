/- GID: D5/S3/ConceptDynamics/Identity/PluralIdentityTheoryJudgments
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identity/PluralIdentityTheoryJudgments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct identity concepts can issue opposite judgments under distinct relations. -/

import D5.S3.ConceptDynamics.Identity.ConceptRelativeIdentity

/- Library-search audit trail (2026-08-26):
   * Exact repository searches for plural identity theories, different identity
     conclusions, and direct contradiction found no frozen theorem with all
     clauses of the source proposition.
   * The family primitive `ConceptIdentity` already constructs compatibility as
     equality under a readout and is imported rather than redeclared.
   * Body-shape searches for a Boolean constant-versus-identity concept family
     and unequal `ConceptIdentity` relations returned no duplicate construction.
   * Pinned Mathlib supplies function congruence and Boolean distinctness, but
     no exact theorem packages the two indexed identity judgments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identity.PluralIdentityTheoryJudgments

open D5.S3.ConceptDynamics.Identity.ConceptRelativeIdentity

/-- Two identity theories can use different concepts and therefore different
compatibility relations. The same pair is identified by the first theory and
distinguished by the second, so the opposite judgments are indexed by different
relations rather than forming a contradiction inside one identity predicate. -/
theorem identity_theories_can_disagree_on_distinct_propositions :
    ∃ firstConcept secondConcept : Bool → Bool,
      firstConcept ≠ secondConcept ∧
      ConceptIdentity firstConcept ≠ ConceptIdentity secondConcept ∧
      ConceptIdentity firstConcept false true ∧
      ¬ConceptIdentity secondConcept false true := by
  let firstConcept : Bool → Bool := fun _ => false
  let secondConcept : Bool → Bool := id
  refine ⟨firstConcept, secondConcept, ?_, ?_, rfl, ?_⟩
  · intro sameConcept
    have sameAtTrue := congrFun sameConcept true
    exact Bool.false_ne_true sameAtTrue
  · intro sameCompatibility
    have sameJudgment := congrArg
      (fun relation : Bool → Bool → Prop => relation false true)
      sameCompatibility
    have firstJudgment : ConceptIdentity firstConcept false true := rfl
    exact Bool.false_ne_true (Eq.mp sameJudgment firstJudgment)
  · exact Bool.false_ne_true

#print axioms identity_theories_can_disagree_on_distinct_propositions

end D5.S3.ConceptDynamics.Identity.PluralIdentityTheoryJudgments
