/- GID: D5/S3/ConceptDynamics/Coding/TargetRelevantOmission
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/TargetRelevantOmission
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target-relevant omission is witnessed by a collapsed target distinction. -/

import D5.S3.ConceptDynamics.Coding.LosslessEncodingCriterion

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'omission_iff_witness_exists' D5 Golden/Frozen/accepted`
     returned no matches.
   * Searches for `TargetRelevantOmission`, target-sensitive non-refinement,
     fiber witnesses, and factorization found no repository theorem with this
     sender/message/target characterization.
   * Exact family hit `messageConcept` and the adjacent theorem
     `not_injective_on_image_iff_strictly_coarser` occur in the imported 238.2
     module. The definition is reused; its theorem lacks the target clause and
     therefore does not cover the present result.
   * Pinned Mathlib's `Function.factorsThrough_iff` converts fiber constancy to
     whole-codomain factorization when the target is nonempty. The inhabited
     state-space hypothesis supplies such a target value; the remaining proof
     uses classical negation and equality transport. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Coding.LosslessEncodingCriterion

/-- A message has a target-relevant omission when the sender determines the
target but the encoded message does not. -/
def TargetRelevantOmission {X S M Target : Type*}
    (sender : Concept X S) (encoder : S -> M) (target : Concept X Target) : Prop :=
  Refines target sender ∧ ¬Refines target (messageConcept sender encoder)

namespace TargetRelevantOmission

/-- Assuming the sender determines the target, omission is exactly a pair
merged by the message but separated by both target and sender. The sender
inequality is logically redundant under the assumption, but records that the
sender possessed the distinction that the encoder deleted. -/
theorem omission_iff_witness_exists
    {X S M Target : Type*} [Nonempty X]
    (sender : Concept X S) (encoder : S -> M) (target : Concept X Target)
    (senderSufficient : Refines target sender) :
    TargetRelevantOmission sender encoder target ↔
      ∃ x y, messageConcept sender encoder x = messageConcept sender encoder y ∧
        target x ≠ target y ∧ sender x ≠ sender y := by
  letI : Nonempty Target := ⟨target (Classical.choice inferInstance)⟩
  have refinesMessageIffFibers :
      Refines target (messageConcept sender encoder) ↔
        Function.FactorsThrough target (messageConcept sender encoder) := by
    change (∃ factor : M -> Target,
      target = factor ∘ messageConcept sender encoder) ↔
        Function.FactorsThrough target (messageConcept sender encoder)
    exact (Function.factorsThrough_iff
      (f := messageConcept sender encoder) target).symm
  constructor
  · rintro ⟨_, messageInsufficient⟩
    have targetVariesOnMessageFiber :
        ∃ x y, messageConcept sender encoder x = messageConcept sender encoder y ∧
          target x ≠ target y := by
      classical
      by_contra noWitness
      apply messageInsufficient
      apply refinesMessageIffFibers.mpr
      intro x y sameMessage
      by_contra differentTarget
      exact noWitness ⟨x, y, sameMessage, differentTarget⟩
    obtain ⟨x, y, sameMessage, differentTarget⟩ := targetVariesOnMessageFiber
    refine ⟨x, y, sameMessage, differentTarget, ?_⟩
    rintro sameSender
    rcases senderSufficient with ⟨targetFromSender, targetFactors⟩
    apply differentTarget
    rw [targetFactors]
    exact congrArg targetFromSender sameSender
  · rintro ⟨x, y, sameMessage, differentTarget, _⟩
    refine ⟨senderSufficient, ?_⟩
    rintro ⟨targetFromMessage, targetFactors⟩
    apply differentTarget
    rw [targetFactors]
    exact congrArg targetFromMessage sameMessage

example :
    TargetRelevantOmission (id : Concept Bool Bool) (fun _ => ())
        (id : Concept Bool Bool) ∧
      ∃ x y, messageConcept (id : Concept Bool Bool) (fun _ => ()) x =
          messageConcept (id : Concept Bool Bool) (fun _ => ()) y ∧
        (id : Concept Bool Bool) x ≠ (id : Concept Bool Bool) y ∧
        (id : Concept Bool Bool) x ≠ (id : Concept Bool Bool) y := by
  have senderSufficient :
      Refines (id : Concept Bool Bool) (id : Concept Bool Bool) :=
    ⟨id, rfl⟩
  have witness :
      ∃ x y, messageConcept (id : Concept Bool Bool) (fun _ => ()) x =
          messageConcept (id : Concept Bool Bool) (fun _ => ()) y ∧
        (id : Concept Bool Bool) x ≠ (id : Concept Bool Bool) y ∧
        (id : Concept Bool Bool) x ≠ (id : Concept Bool Bool) y :=
    ⟨false, true, rfl, Bool.false_ne_true, Bool.false_ne_true⟩
  exact ⟨(omission_iff_witness_exists (id : Concept Bool Bool) (fun _ => ())
    (id : Concept Bool Bool) senderSufficient).mpr witness, witness⟩

#print axioms omission_iff_witness_exists

end TargetRelevantOmission

end D5.S3.ConceptDynamics.Coding
