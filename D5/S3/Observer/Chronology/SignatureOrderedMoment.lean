/- GID: D5/S3/Observer/Chronology/SignatureOrderedMoment
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/SignatureOrderedMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite signatures store event squares and ordered pairs; Magnus is their antisymmetrization. -/

import D5.S3.Observer.Chronology.PrimeGoldenThirdOrderChronologyEscape

/-!
# All-word signature and ordered-moment semantics

This module supplies the paper's missing bridge from its compositional
step-two carrier to its existing ordered-pair moment, for arbitrary finite
words and semiring observations. A noncommutative square decomposition then
identifies the corrected Magnus coordinate with the difference between the
two orientations of the pair moment. No division or commutativity is used.

Library search: the imported module owns orderedPairMoment; the generic
append, square, and signature identities below were absent in D5 and pinned
Mathlib. List.sum_append and List.sum_reverse are reused from Mathlib.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.SignatureOrderedMoment

open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.PrimeGoldenThirdOrderChronologyEscape

universe u v

/-- Scattered pairs in an append are internal pairs plus the ordered cross product. -/
theorem ordered_pair_moment_append {A : Type u} [Semiring A] (xs ys : List A) :
    orderedPairMoment (xs ++ ys) =
      orderedPairMoment xs + xs.sum * ys.sum + orderedPairMoment ys := by
  induction xs with
  | nil => simp [orderedPairMoment]
  | cons x xs ih =>
    simp only [List.cons_append, orderedPairMoment, List.sum_append, List.sum_cons, ih]
    noncomm_ring

/-- The square of a word sum decomposes into diagonal and both ordered orientations. -/
theorem sum_mul_sum_eq_ordered_pair_moments {A : Type u} [Semiring A] (xs : List A) :
    xs.sum * xs.sum = (xs.map fun x => x * x).sum +
      orderedPairMoment xs + orderedPairMoment xs.reverse := by
  induction xs with
  | nil => simp [orderedPairMoment]
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons, List.reverse_cons,
      ordered_pair_moment_append, orderedPairMoment, List.sum_reverse,
      List.sum_nil, mul_zero, add_zero]
    noncomm_ring [ih]

/-- The stored doubled coordinate is the diagonal event-square sum plus twice M2. -/
theorem chronological_signature_doubledDegreeTwo_eq
    {A : Type u} {E : Type v} [Semiring A] (observe : E → A) (w : List E) :
    (chronologicalSignature observe w).doubledDegreeTwo =
      (w.map fun e => observe e * observe e).sum +
        2 * orderedPairMoment (w.map observe) := by
  induction w with
  | nil => simp [orderedPairMoment]
  | cons e w ih =>
    simp only [chronological_signature_cons, StepTwoSignature.doubledDegreeTwo_mul,
      eventSignature, chronological_signature_degree_one, List.map_cons,
      List.sum_cons, orderedPairMoment, ih]
    noncomm_ring

/-- The corrected degree-two coordinate is the antisymmetrized ordered-pair moment. -/
theorem doubledMagnusDegreeTwo_eq_orderedPairMoment_sub_reverse
    {A : Type u} {E : Type v} [Ring A] (observe : E → A) (w : List E) :
    doubledMagnusDegreeTwo (chronologicalSignature observe w) =
      orderedPairMoment (w.map observe) - orderedPairMoment (w.map observe).reverse := by
  rw [doubledMagnusDegreeTwo, chronological_signature_doubledDegreeTwo_eq,
    chronological_signature_degree_one, sum_mul_sum_eq_ordered_pair_moments]
  simp only [List.map_map, Function.comp_def]
  noncomm_ring

end D5.S3.Observer.Chronology.SignatureOrderedMoment
