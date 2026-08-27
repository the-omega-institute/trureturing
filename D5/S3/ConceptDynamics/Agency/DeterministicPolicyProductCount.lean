/- GID: D5/S3/ConceptDynamics/Agency/DeterministicPolicyProductCount
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/DeterministicPolicyProductCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Policy sections biject to fiber choices and obey the product count. -/

import D5.S3.ConceptDynamics.Agency.FinitePolicySectionCount

/- Library-search audit trail (2026-08-27):
   * Exact D5 hit `finite_policy_sections_card` proves the source's cardinality
     equation and is applied directly.
   * That frozen theorem keeps its section equivalence proof-local, so it does
     not publicly state the source's preceding canonical-product clause.
   * Repository body-shape searches found no public canonical map from the
     source-constructed projection sections to dependent legal-action choices.
     The map is therefore exposed as a lambda in this theorem, without adding
     a definition or abbreviation.
   * Pinned Mathlib hit `Equiv.bijective` supplies the bijectivity projection. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.DeterministicPolicyProductCount

open D5.S3.ConceptDynamics.Agency.FinitePolicySectionCount

/-- A section of the total legal-action projection canonically determines one
legal action in each state fiber, and this explicit map is bijective. On a
finite state carrier, the same section type has the product cardinality. -/
theorem deterministic_policy_product_and_count
    {Q A : Type*} [Fintype Q] (Legal : Q -> A -> Prop) :
    Function.Bijective
        (fun policy :
            {policy : Q -> {qa : Q × A // Legal qa.1 qa.2} //
              forall q, (policy q).1.1 = q} =>
          fun q : Q =>
            (⟨(policy.1 q).1.2,
              Eq.mp
                (congrArg (fun q' => Legal q' (policy.1 q).1.2) (policy.2 q))
                (policy.1 q).2⟩ : {action : A // Legal q action})) ∧
      Nat.card
          {policy : Q -> {qa : Q × A // Legal qa.1 qa.2} //
            forall q, (policy q).1.1 = q} =
        ∏ q, Nat.card {action : A // Legal q action} := by
  let sectionEquiv :
      {policy : Q -> {qa : Q × A // Legal qa.1 qa.2} //
          forall q, (policy q).1.1 = q} ≃
        forall q, {action : A // Legal q action} :=
    { toFun := fun policy q =>
        ⟨(policy.1 q).1.2,
          Eq.mp
            (congrArg (fun q' => Legal q' (policy.1 q).1.2) (policy.2 q))
            (policy.1 q).2⟩
      invFun := fun choice =>
        ⟨fun q => ⟨(q, (choice q).1), (choice q).2⟩, fun _ => rfl⟩
      left_inv := by
        intro policy
        apply Subtype.ext
        funext q
        apply Subtype.ext
        apply Prod.ext
        · exact (policy.2 q).symm
        · rfl
      right_inv := by
        intro choice
        funext q
        apply Subtype.ext
        rfl }
  constructor
  · exact sectionEquiv.bijective
  · exact finite_policy_sections_card Legal

#print axioms deterministic_policy_product_and_count

end D5.S3.ConceptDynamics.Agency.DeterministicPolicyProductCount
