/- GID: D5/S3/ConceptDynamics/Deliberation/InformationCompleteNormativeDivergence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Deliberation/InformationCompleteNormativeDivergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete information allows divergence; incomplete information allows blind agreement. -/

import D5.S3.ConceptDynamics.Contracts.FutureObligationIncompleteness

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'complete_information_permits_normative_divergence' D5
     Golden/Frozen/accepted` found no hit.
   * Repository searches for `Function.Injective`, factorization, blindness, and
     `Doctrine` found adjacent results but no theorem combining both directions.
   * Exact repository hit `nonfaithful_interface_future_incomplete` supplies a
     separating Boolean target for every noninjective concept and is reused below.
   * `history_sensitive_evaluation_not_outcome_reducible` has the same abstract
     factorization obstruction, but its endpoint-history framing adds no needed
     witness beyond the stronger interface theorem imported here.
   * Pinned Mathlib's `Function.not_injective_iff` and
     `Function.factorsThrough_iff` are already used by the imported theorem.
     No library result packages normative divergence together with blind consensus. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Deliberation.InformationCompleteNormativeDivergence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Contracts.FutureObligationIncompleteness

/-- Two subjects reach normative consensus when their normative functions agree. -/
def NormativeConsensus {X U : Type*} (left right : Concept X U) : Prop :=
  left = right

/-- An injective concept cannot force normative consensus, while every noninjective
concept admits equal normative functions sharing a target they cannot answer through
that concept. -/
theorem complete_information_permits_normative_divergence :
    (∀ {X I U : Type*} [Nonempty X] (concept : Concept X I)
        (leftValue rightValue : U),
      leftValue ≠ rightValue → Function.Injective concept →
        ∃ leftNorm rightNorm : Concept X U,
          ∃ witness : X, leftNorm witness ≠ rightNorm witness) ∧
    (∀ {X I : Type*} (concept : Concept X I),
      (¬Function.Injective concept) →
        ∃ leftNorm rightNorm target : Concept X Bool,
          NormativeConsensus leftNorm rightNorm ∧
            ¬∃ answer : I → Bool, target = answer ∘ concept) := by
  constructor
  · intro X I U nonemptyX concept leftValue rightValue valuesDiffer _
    obtain ⟨state⟩ := nonemptyX
    let leftNorm : Concept X U := fun _ => leftValue
    let rightNorm : Concept X U := fun _ => rightValue
    exact ⟨leftNorm, rightNorm, state, valuesDiffer⟩
  · intro X I concept notInjective
    obtain ⟨state, _, _, _, _, targetDoesNotFactor⟩ :=
      (nonfaithful_interface_future_incomplete concept).1 notInjective
    let agreedNorm : Concept X Bool := fun _ => true
    exact ⟨agreedNorm, agreedNorm, collisionObligation state, rfl,
      targetDoesNotFactor⟩

example :
    ∃ (concept : Concept Unit Unit) (leftNorm rightNorm : Concept Unit Bool),
      Function.Injective concept ∧
        ∃ state : Unit, leftNorm state ≠ rightNorm state := by
  refine ⟨id, (fun _ => true), (fun _ => false), Function.injective_id, (), ?_⟩
  decide

example :
    ∃ (concept : Concept Bool Unit) (leftNorm rightNorm target : Concept Bool Bool),
      (¬Function.Injective concept) ∧
        NormativeConsensus leftNorm rightNorm ∧
          ¬∃ answer : Unit → Bool, target = answer ∘ concept := by
  let concept : Concept Bool Unit := fun _ => ()
  have notInjective : ¬Function.Injective concept := by
    intro injective
    exact Bool.false_ne_true (injective rfl)
  obtain ⟨state, _, _, _, _, blind⟩ :=
    (nonfaithful_interface_future_incomplete concept).1 notInjective
  let agreedNorm : Concept Bool Bool := fun _ => true
  exact ⟨concept, agreedNorm, agreedNorm, collisionObligation state,
    notInjective, rfl, blind⟩

#print axioms complete_information_permits_normative_divergence

end D5.S3.ConceptDynamics.Deliberation.InformationCompleteNormativeDivergence
