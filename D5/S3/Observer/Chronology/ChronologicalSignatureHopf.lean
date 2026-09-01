/- GID: D5/S3/Observer/Chronology/ChronologicalSignatureHopf
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/ChronologicalSignatureHopf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Step-two chronological signatures satisfy the group-like coproduct and antipode laws, and the antipode reverses event order with negated values. -/

import D5.S3.Observer.Chronology.StepTwoChronologicalLogarithm
import Mathlib.Tactic

/-!
# Group-like Hopf laws for step-two chronological signatures

The finite step-two signature already carries Chen multiplication. This module
adds the group-like diagonal, its terminal counit, and the explicit antipode
from `StepTwoChronologicalLogarithm`. It proves the two convolution
cancellation identities, anti-multiplicativity, involutivity, and the concrete
chronological interpretation of the antipode: reverse the event word and
negate every observed event value.

These are the group-like Hopf identities available at the finite step-two
level. This module does not claim an instance of Mathlib's linear
`HopfAlgebra`, a tensor-algebra coproduct, shuffle multiplication, a completed
coalgebra, or convergence of an infinite signature.
-/

/- Library-search audit trail (2026-09-01):
   * `StepTwoChronologicalSignature` owns Chen multiplication and event-word
     signatures.
   * `StepTwoChronologicalLogarithm` owns the exact BCH equivalence and the
     explicit division-free antipode. This module only packages their
     group-like consequences and proves the event-word reversal theorem.
   * Repository search found no existing owner of reverse-and-negate as the
     antipode action on chronological event words.
   * Pinned Mathlib's full Hopf-algebra hierarchy is intentionally not
     instantiated because this finite coordinate object has not been equipped
     here with the required linear tensor coalgebra. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.ChronologicalSignatureHopf

open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.StepTwoChronologicalLogarithm

universe u v

/-- The group-like diagonal of a finite step-two signature. -/
def groupLikeCoproduct {A : Type u}
    (signature : StepTwoSignature A) :
    StepTwoSignature A × StepTwoSignature A :=
  (signature, signature)

/-- The terminal counit of the group-like finite skeleton. -/
def groupLikeCounit {A : Type u}
    (_signature : StepTwoSignature A) : PUnit :=
  PUnit.unit

/-- The group-like diagonal preserves chronological multiplication
componentwise. -/
theorem group_like_coproduct_mul {A : Type u} [Ring A]
    (left right : StepTwoSignature A) :
    groupLikeCoproduct (left * right) =
      ((groupLikeCoproduct left).1 * (groupLikeCoproduct right).1,
       (groupLikeCoproduct left).2 * (groupLikeCoproduct right).2) := by
  rfl

/-- Iterating the diagonal on its first leg gives three identical group-like
components. -/
theorem group_like_coproduct_left_iterated {A : Type u}
    (signature : StepTwoSignature A) :
    ((groupLikeCoproduct signature).1,
      (groupLikeCoproduct (groupLikeCoproduct signature).2).1,
      (groupLikeCoproduct (groupLikeCoproduct signature).2).2) =
      (signature, signature, signature) := by
  rfl

/-- Iterating the diagonal on its second leg gives the same three group-like
components. -/
theorem group_like_coproduct_right_iterated {A : Type u}
    (signature : StepTwoSignature A) :
    ((groupLikeCoproduct (groupLikeCoproduct signature).1).1,
      (groupLikeCoproduct (groupLikeCoproduct signature).1).2,
      (groupLikeCoproduct signature).2) =
      (signature, signature, signature) := by
  rfl

/-- The two iterated group-like diagonals agree. -/
theorem group_like_coproduct_coassociative {A : Type u}
    (signature : StepTwoSignature A) :
    ((groupLikeCoproduct signature).1,
      (groupLikeCoproduct (groupLikeCoproduct signature).2).1,
      (groupLikeCoproduct (groupLikeCoproduct signature).2).2) =
    ((groupLikeCoproduct (groupLikeCoproduct signature).1).1,
      (groupLikeCoproduct (groupLikeCoproduct signature).1).2,
      (groupLikeCoproduct signature).2) := by
  rfl

/-- The counit erases either leg of the group-like diagonal. -/
theorem group_like_counit {A : Type u}
    (signature : StepTwoSignature A) :
    (groupLikeCounit (groupLikeCoproduct signature).1,
      (groupLikeCoproduct signature).2) =
      (PUnit.unit, signature) := by
  rfl

/-- Left convolution of the antipode with the identity is the empty
signature. -/
theorem antipode_left_convolution {A : Type u} [Ring A]
    (signature : StepTwoSignature A) :
    signatureAntipode (groupLikeCoproduct signature).1 *
      (groupLikeCoproduct signature).2 = 1 := by
  exact signature_antipode_mul signature

/-- Right convolution of the identity with the antipode is the empty
signature. -/
theorem antipode_right_convolution {A : Type u} [Ring A]
    (signature : StepTwoSignature A) :
    (groupLikeCoproduct signature).1 *
      signatureAntipode (groupLikeCoproduct signature).2 = 1 := by
  exact mul_signature_antipode signature

/-- The antipode preserves the group-like diagonal componentwise. -/
theorem group_like_coproduct_antipode {A : Type u} [Ring A]
    (signature : StepTwoSignature A) :
    groupLikeCoproduct (signatureAntipode signature) =
      (signatureAntipode (groupLikeCoproduct signature).1,
       signatureAntipode (groupLikeCoproduct signature).2) := by
  rfl

/-- Reversing an event word and negating every observed value realizes the
step-two signature antipode. -/
theorem chronological_signature_reverse_neg
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    chronologicalSignature (fun event => -observe event) events.reverse =
      signatureAntipode (chronologicalSignature observe events) := by
  induction events with
  | nil =>
      simp [chronologicalSignature, signatureAntipode,
        StepTwoSignature.identity]
  | cons event events ih =>
      rw [List.reverse_cons, chronological_signature_append, ih]
      simp only [chronological_signature_cons,
        chronological_signature_nil, mul_one]
      rw [← signature_antipode_event]
      rw [signature_antipode_mul_rev]

/-- In logarithmic coordinates, reverse-and-negate is coordinatewise
negation. -/
theorem chronological_log_reverse_neg
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    chronologicalLog
        (chronologicalSignature (fun event => -observe event) events.reverse) =
      StepTwoLogarithm.inverse
        (chronologicalLog (chronologicalSignature observe events)) := by
  rw [chronological_signature_reverse_neg, chronological_log_antipode]

/-- Applying reverse-and-negate twice recovers the original step-two
signature. -/
theorem chronological_signature_reverse_neg_involutive
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (events : List Event) :
    signatureAntipode
        (chronologicalSignature (fun event => -observe event) events.reverse) =
      chronologicalSignature observe events := by
  rw [chronological_signature_reverse_neg,
    signature_antipode_involutive]

/-- Reverse-and-negate converts concatenation into the reversed product of
the two antipodes. -/
theorem chronological_signature_reverse_neg_append
    {Event : Type v} {A : Type u} [Ring A]
    (observe : Event → A) (earlierWord laterWord : List Event) :
    chronologicalSignature
        (fun event => -observe event) (earlierWord ++ laterWord).reverse =
      signatureAntipode (chronologicalSignature observe laterWord) *
        signatureAntipode (chronologicalSignature observe earlierWord) := by
  rw [chronological_signature_reverse_neg,
    chronological_signature_append, signature_antipode_mul_rev]

example :
    groupLikeCoproduct
        (eventSignature (1 : ℤ)) =
      (eventSignature 1, eventSignature 1) := by
  rfl

#print axioms group_like_coproduct_mul
#print axioms group_like_coproduct_coassociative
#print axioms antipode_left_convolution
#print axioms antipode_right_convolution
#print axioms group_like_coproduct_antipode
#print axioms chronological_signature_reverse_neg
#print axioms chronological_log_reverse_neg
#print axioms chronological_signature_reverse_neg_involutive
#print axioms chronological_signature_reverse_neg_append

end D5.S3.Observer.Chronology.ChronologicalSignatureHopf
