/- GID: D5/S3/Observer/Chronology/PrimeGoldenThirdOrderChronologyEscape
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two prime-golden words can share bidegree, complete scalar trajectory, and the full step-two signature while a cubic ordered moment still separates their chronology. -/

import D5.S3.Observer.Chronology.PrimeGoldenChronologyFiberSeparation
import Mathlib.Tactic

/-!
# A third-order escape from step-two chronology fibers

The two words `ABBA` and `BAAB` contain the same multiset of events. They have
the same prime-golden bidegree and the same complete scalar Euler trajectory.
More strongly, their full step-two chronological signatures agree in every
associative ring representation.

A cubic ordered moment can nevertheless distinguish them. This supplies a
finite, explicit certificate that bidegree data, scalar Fourier trajectories,
and degree-two Magnus data do not exhaust chronology. A step-three signature
or another third-order ordered observer is required whenever the displayed
cubic difference is nonzero.

This file defines only the finite ordered moments needed for the witness. It
does not construct a complete step-three Hopf algebra, prove a PBW theorem, or
assert that every step-two fiber is separated at degree three.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeGoldenThirdOrderChronologyEscape

open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge
open D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature
open D5.S3.Observer.Chronology.PrimeGoldenChronologyFiberSeparation

noncomputable section

universe u

/-- Sum of all ordered degree-two subwords of a finite value word. -/
def orderedPairMoment {A : Type u} [Semiring A] : List A → A
  | [] => 0
  | value :: values => value * values.sum + orderedPairMoment values

/-- Sum of all ordered degree-three subwords of a finite value word. -/
def orderedTripleMoment {A : Type u} [Semiring A] : List A → A
  | [] => 0
  | value :: values =>
      value * orderedPairMoment values + orderedTripleMoment values

/-- Third-order chronological readout after applying an associative-algebra
observation to each event. -/
def thirdOrderReadout
    {A : Type u} [Semiring A]
    (observe : PrimeGoldenStepEvent → A)
    (events : List PrimeGoldenStepEvent) : A :=
  orderedTripleMoment (events.map observe)

/-- The words `ABBA` and `BAAB` have the same ordered degree-two moment. -/
theorem ordered_pair_moment_abba_eq_baab
    {A : Type u} [Ring A] (a b : A) :
    orderedPairMoment [a, b, b, a] =
      orderedPairMoment [b, a, a, b] := by
  simp [orderedPairMoment]
  noncomm_ring

/-- Their first cubic ordered moment has this explicit normal form. -/
theorem ordered_triple_moment_abba
    {A : Type u} [Ring A] (a b : A) :
    orderedTripleMoment [a, b, b, a] =
      a * b * b + 2 * (a * b * a) + b * b * a := by
  simp [orderedTripleMoment, orderedPairMoment]
  noncomm_ring

/-- Their second cubic ordered moment has the complementary normal form. -/
theorem ordered_triple_moment_baab
    {A : Type u} [Ring A] (a b : A) :
    orderedTripleMoment [b, a, a, b] =
      b * a * a + 2 * (b * a * b) + a * a * b := by
  simp [orderedTripleMoment, orderedPairMoment]
  noncomm_ring

/-- The complete step-two signatures of `ABBA` and `BAAB` agree in every ring.
Thus even the degree-two chronology ledger can have nontrivial fibers. -/
theorem step_two_signature_abba_eq_baab
    {A : Type u} [Ring A] (a b : A) :
    chronologicalSignature (fun value : A => value) [a, b, b, a] =
      chronologicalSignature (fun value : A => value) [b, a, a, b] := by
  ext <;>
    simp [chronologicalSignature, eventSignature,
      StepTwoSignature.compose] <;>
    noncomm_ring

/-- The corresponding prime-golden event words have equal bidegree. -/
theorem prime_golden_bidegree_abba_eq_baab
    (first second : PrimeGoldenStepEvent) :
    primeGoldenBidegree [first, second, second, first] =
      primeGoldenBidegree [second, first, first, second] := by
  ext <;>
    simp [primeGoldenBidegree, shortStepCount,
      add_comm, add_left_comm, add_assoc]

/-- Their complete scalar Euler trajectories also agree. -/
theorem prime_golden_scalar_trajectory_abba_eq_baab
    (first second : PrimeGoldenStepEvent) :
    SameScalarTrajectory
      [first, second, second, first]
      [second, first, first, second] := by
  intro time
  simp [scalarStepEndpoint, mul_comm, mul_left_comm, mul_assoc]

/-- Every associative observation gives the two event words the same full
step-two chronological signature. -/
theorem prime_golden_step_two_signature_abba_eq_baab
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (first second : PrimeGoldenStepEvent) :
    chronologicalSignature observe [first, second, second, first] =
      chronologicalSignature observe [second, first, first, second] := by
  simpa using
    step_two_signature_abba_eq_baab (observe first) (observe second)

/-- A nonzero cubic difference separates the two words after all count,
scalar-trajectory, and step-two observations have identified them. -/
theorem prime_golden_third_order_chronology_escape
    {A : Type u} [Ring A]
    (observe : PrimeGoldenStepEvent → A)
    (first second : PrimeGoldenStepEvent)
    (hCubic :
      observe first * observe second * observe second +
          2 * (observe first * observe second * observe first) +
          observe second * observe second * observe first ≠
        observe second * observe first * observe first +
          2 * (observe second * observe first * observe second) +
          observe first * observe first * observe second) :
    primeGoldenBidegree [first, second, second, first] =
        primeGoldenBidegree [second, first, first, second] ∧
      SameScalarTrajectory
        [first, second, second, first]
        [second, first, first, second] ∧
      chronologicalSignature observe [first, second, second, first] =
        chronologicalSignature observe [second, first, first, second] ∧
      thirdOrderReadout observe [first, second, second, first] ≠
        thirdOrderReadout observe [second, first, first, second] := by
  refine
    ⟨prime_golden_bidegree_abba_eq_baab first second,
      prime_golden_scalar_trajectory_abba_eq_baab first second,
      prime_golden_step_two_signature_abba_eq_baab observe first second,
      ?_⟩
  simpa [thirdOrderReadout, ordered_triple_moment_abba,
    ordered_triple_moment_baab] using hCubic

#print axioms ordered_pair_moment_abba_eq_baab
#print axioms ordered_triple_moment_abba
#print axioms ordered_triple_moment_baab
#print axioms step_two_signature_abba_eq_baab
#print axioms prime_golden_bidegree_abba_eq_baab
#print axioms prime_golden_scalar_trajectory_abba_eq_baab
#print axioms prime_golden_step_two_signature_abba_eq_baab
#print axioms prime_golden_third_order_chronology_escape

end

end D5.S3.Observer.Chronology.PrimeGoldenThirdOrderChronologyEscape
