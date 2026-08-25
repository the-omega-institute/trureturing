/- GID: D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/LosslessEncodingCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Encoding is lossless exactly when it is injective on the sender image. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Set.Function

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'lossless_iff_injective_on_image' D5 Golden/Frozen/accepted`
     returned no matches.
   * `rg -in 'Set.InjOn|InjOn|Set.range|coarser|Refines'
     D5/S3/ConceptDynamics/` found `KnowledgePolicyThreshold`, which assumes
     injectivity on a secret image for recovery, but no lossless equivalence or
     strict-coarsening criterion. Broader structural searches found no duplicate.
   * Pinned Mathlib provides `Set.InjOn.eq_iff` for equality reflection on a set;
     it is applied to sender-image witnesses below. `Function.Injective.comp` and
     `Set.range_comp` are adjacent but do not package the required fiber equivalence.
   * The converse and strict-coarsening witness use only `Set.InjOn`, range
     witnesses, function composition, equality transport, and classical negation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.LosslessEncodingCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- The message concept is the sender's actual concept followed by its encoder. -/
def messageConcept {X S M : Type*}
    (sender : Concept X S) (encoder : S -> M) : Concept X M :=
  encoder ∘ sender

/-- An encoding preserves exactly the sender's distinctions if and only if its
encoder is injective on the coordinates the sender actually realizes. -/
theorem lossless_iff_injective_on_image {X S M : Type*}
    (sender : Concept X S) (encoder : S -> M) :
    Set.InjOn encoder (Set.range sender) ↔
      ∀ x y, messageConcept sender encoder x = messageConcept sender encoder y ↔
        sender x = sender y := by
  constructor
  · intro injective x y
    unfold messageConcept Function.comp
    exact injective.eq_iff
      (show sender x ∈ Set.range sender from ⟨x, rfl⟩)
      (show sender y ∈ Set.range sender from ⟨y, rfl⟩)
  · intro sameFibers source₁ source₁InRange source₂ source₂InRange sameMessage
    rcases source₁InRange with ⟨x, rfl⟩
    rcases source₂InRange with ⟨y, rfl⟩
    exact (sameFibers x y).mp sameMessage

/-- Failure of injectivity on the actual sender image is exactly the existence
of a sender distinction collapsed by the message. -/
theorem not_injective_on_image_iff_strictly_coarser {X S M : Type*}
    (sender : Concept X S) (encoder : S -> M) :
    ¬Set.InjOn encoder (Set.range sender) ↔
      ∃ x y, messageConcept sender encoder x = messageConcept sender encoder y ∧
        sender x ≠ sender y := by
  classical
  constructor
  · intro notInjective
    by_contra noCollapsedPair
    apply notInjective
    apply (lossless_iff_injective_on_image sender encoder).mpr
    intro x y
    constructor
    · intro sameMessage
      by_contra differentSender
      exact noCollapsedPair ⟨x, y, sameMessage, differentSender⟩
    · intro sameSender
      unfold messageConcept Function.comp
      exact congrArg encoder sameSender
  · rintro ⟨x, y, sameMessage, differentSender⟩ injective
    apply differentSender
    exact ((lossless_iff_injective_on_image sender encoder).mp injective x y).mp
      sameMessage

/-- Under one lossy encoder, the message itself remains a decidable target,
while the sender's full concept is not decidable from the message. -/
theorem lost_distinction_importance_depends_on_target {X S M : Type*}
    (sender : Concept X S) (encoder : S -> M)
    (lossy : ¬Set.InjOn encoder (Set.range sender)) :
    Refines (messageConcept sender encoder) (messageConcept sender encoder) ∧
      ¬Refines sender (messageConcept sender encoder) := by
  constructor
  · exact ⟨id, rfl⟩
  · rintro ⟨decode, senderFactors⟩
    obtain ⟨x, y, sameMessage, differentSender⟩ :=
      (not_injective_on_image_iff_strictly_coarser sender encoder).mp lossy
    apply differentSender
    rw [senderFactors]
    exact congrArg decode sameMessage

example :
    Refines
        (messageConcept (id : Concept Bool Bool) (fun _ => ()))
        (messageConcept (id : Concept Bool Bool) (fun _ => ())) ∧
      ¬Refines (id : Concept Bool Bool)
        (messageConcept (id : Concept Bool Bool) (fun _ => ())) := by
  apply lost_distinction_importance_depends_on_target
  intro injective
  exact Bool.false_ne_true
    (injective ⟨false, rfl⟩ ⟨true, rfl⟩ rfl)

#print axioms lossless_iff_injective_on_image

end D5.S3.ConceptDynamics.Coding.LosslessEncodingCriterion
