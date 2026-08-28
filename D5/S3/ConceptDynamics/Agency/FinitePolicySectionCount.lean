/- GID: D5/S3/ConceptDynamics/Agency/FinitePolicySectionCount
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/FinitePolicySectionCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Count finite-state policy sections as the product of legal-action fiber sizes. -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

/- Library-search audit trail (2026-08-27):
   * Repository name searches for legal-action bundles, deterministic policy
     sections, and finite policy-section counts found no existing declaration.
   * Body-shape searches for subtypes built from `Legal`, right inverses of a
     sigma projection, and section-cardinality products found no canonical D5
     primitive. No new definition or abbreviation is introduced here.
   * Exact pinned-Mathlib hit `Nat.card_pi` counts a dependent function type.
     No Mathlib theorem was found that first identifies sections of the
     source's constructed legal-action projection with that dependent product. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Agency.FinitePolicySectionCount

/-- For a finite observation-state carrier, the deterministic sections of the
total legal-action projection are counted by the product of the legal-action
fiber cardinalities. The total space and the section equation are constructed
directly from `Legal`; they are not replaced by a definition of the target
dependent product. -/
theorem finite_policy_sections_card
    {Q A : Type*} [Fintype Q] (Legal : Q -> A -> Prop) :
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
  rw [Nat.card_congr sectionEquiv, Nat.card_pi]

#print axioms finite_policy_sections_card

end D5.S3.ConceptDynamics.Agency.FinitePolicySectionCount
