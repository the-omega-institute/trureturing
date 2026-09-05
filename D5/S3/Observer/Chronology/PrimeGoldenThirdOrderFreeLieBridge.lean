/- GID: D5/S3/Observer/Chronology/PrimeGoldenThirdOrderFreeLieBridge
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/Mathlib.Algebra.Lie.Free]
   digest: The residual ABBA/BAAB step-two fiber is separated by a nonzero degree-three free-Lie primitive with an explicit integer-matrix witness. -/

import D5.S3.Observer.Chronology.PrimeGoldenThirdOrderChronologyEscape
import D5.S3.Observer.Chronology.StepTwoFreeLieBridge
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# A strict third-order free-Lie chronology refinement

The existing `ABBA`/`BAAB` witness proves that prime-golden bidegree, complete
scalar phase trajectory, and the full step-two signature can agree while a
cubic ordered moment differs. This module identifies that cubic defect with
the standard degree-three Lie primitive

`-[a + b, [a, b]]`.

The identification is representation-theoretic rather than a naming device:
Mathlib's free-Lie universal map sends the corresponding free word to the
cubic chronology defect in every associative-algebra representation.

An explicit representation by the integer matrices `E12` and `E21` evaluates
the primitive to the nonzero matrix

`!![0, 2; -2, 0]`.

Consequently the degree-three word is nonzero in the free Lie algebra, and a
concrete pair of prime-golden histories has equal count, scalar, and step-two
readouts but unequal third-order readouts. This proves a strict refinement of
one genuine step-two observation fiber. It does not claim that degree three
separates every chronology fiber or construct the complete step-three Hopf
signature.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeGoldenThirdOrderFreeLieBridge

open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.StepTwoFreeLieBridge
open D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge
open D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature
open D5.S3.Observer.Chronology.PrimeGoldenChronologyFiberSeparation
open D5.S3.Observer.Chronology.PrimeGoldenThirdOrderChronologyEscape

local notation "ringCommutator" =>
  D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator

-- Use the same associative-algebra Lie structure as the generic evaluation
-- owner, including when the scalar ring is specialized to the integers.
attribute [local instance 2000] LieRing.ofAssociativeRing
attribute [local instance 2000] LieAlgebra.ofAssociativeAlgebra

noncomputable section

universe u v

/-- Difference of the cubic ordered moments of `ABBA` and `BAAB`. -/
def cubicChronologyDefect
    {A : Type u} [Ring A] (a b : A) : A :=
  orderedTripleMoment [a, b, b, a] -
    orderedTripleMoment [b, a, a, b]

/-- The residual cubic chronology defect is exactly a degree-three nested
commutator. -/
theorem cubic_chronology_defect_eq_neg_nested_commutator
    {A : Type u} [Ring A] (a b : A) :
    cubicChronologyDefect a b =
      -ringCommutator (a + b) (ringCommutator a b) := by
  unfold cubicChronologyDefect
  rw [ordered_triple_moment_abba, ordered_triple_moment_baab]
  unfold D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator
  noncomm_ring

/-- Swapping the two event values reverses the orientation of the cubic
chronology defect. -/
theorem cubic_chronology_defect_swap
    {A : Type u} [Ring A] (a b : A) :
    cubicChronologyDefect b a = -cubicChronologyDefect a b := by
  rw [cubic_chronology_defect_eq_neg_nested_commutator,
    cubic_chronology_defect_eq_neg_nested_commutator]
  unfold D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator
  noncomm_ring

/-- The universal degree-three free-Lie word underlying the residual
chronology defect. -/
noncomputable def thirdOrderFreeLieWord
    {Event : Type v} (left right : Event) : FreeLieAlgebra ℤ Event :=
  -⁅FreeLieAlgebra.of ℤ left + FreeLieAlgebra.of ℤ right,
      ⁅FreeLieAlgebra.of ℤ left, FreeLieAlgebra.of ℤ right⁆⁆

/-- Every associative-algebra representation evaluates the universal
free-Lie word to the cubic chronology defect. -/
theorem free_lie_evaluation_third_order
    {Event : Type v} {A : Type u}
    [Ring A] [Algebra ℤ A]
    (observe : Event → A) (left right : Event) :
    freeLieEvaluation ℤ A observe (thirdOrderFreeLieWord left right) =
      cubicChronologyDefect (observe left) (observe right) := by
  unfold thirdOrderFreeLieWord
  rw [map_neg, LieHom.map_lie, map_add,
    free_lie_evaluation_generator,
    free_lie_evaluation_generator,
    free_lie_evaluation_bracket]
  change
    -ringCommutator (observe left + observe right)
        (ringCommutator (observe left) (observe right)) =
      cubicChronologyDefect (observe left) (observe right)
  exact
    (cubic_chronology_defect_eq_neg_nested_commutator
      (observe left) (observe right)).symm

/-- The explicit associative-algebra representation used to certify that the
universal degree-three word is nonzero. -/
abbrev IntegerMatrix2 := Matrix (Fin 2) (Fin 2) ℤ

/-- The matrix unit `E12`. -/
def e12 : IntegerMatrix2 := !![0, 1; 0, 0]

/-- The matrix unit `E21`. -/
def e21 : IntegerMatrix2 := !![0, 0; 1, 0]

/-- The explicit value of the cubic chronology defect on the two matrix
units. -/
def cubicWitnessMatrix : IntegerMatrix2 := !![0, 2; -2, 0]

/-- The nested commutator evaluates to a concrete nonzero integer matrix. -/
theorem cubic_chronology_defect_e12_e21 :
    cubicChronologyDefect e12 e21 = cubicWitnessMatrix := by
  rw [cubic_chronology_defect_eq_neg_nested_commutator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e12, e21, cubicWitnessMatrix,
      D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity.commutator,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix certificate is nonzero. -/
theorem cubic_witness_matrix_ne_zero : cubicWitnessMatrix ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrFun hzero (0 : Fin 2)) (1 : Fin 2)
  norm_num [cubicWitnessMatrix] at hentry

/-- Hence the represented cubic chronology defect is nonzero. -/
theorem cubic_chronology_defect_e12_e21_ne_zero :
    cubicChronologyDefect e12 e21 ≠ 0 := by
  rw [cubic_chronology_defect_e12_e21]
  exact cubic_witness_matrix_ne_zero

/-- Two labels for the universal free-Lie nonvanishing certificate. -/
inductive TwoEvent
  | left
  | right
  deriving DecidableEq

/-- Matrix representation of the two universal event labels. -/
def twoEventObservation : TwoEvent → IntegerMatrix2
  | .left => e12
  | .right => e21

/-- The universal degree-three free-Lie word is genuinely nonzero. -/
theorem third_order_free_lie_word_nonzero :
    thirdOrderFreeLieWord TwoEvent.left TwoEvent.right ≠ 0 := by
  intro hzero
  have hevaluation : cubicChronologyDefect e12 e21 = 0 := by
    calc
      cubicChronologyDefect e12 e21 =
          freeLieEvaluation ℤ IntegerMatrix2 twoEventObservation
            (thirdOrderFreeLieWord TwoEvent.left TwoEvent.right) := by
        symm
        simpa [twoEventObservation] using
          free_lie_evaluation_third_order
            twoEventObservation TwoEvent.left TwoEvent.right
      _ = freeLieEvaluation ℤ IntegerMatrix2 twoEventObservation 0 := by
        rw [hzero]
      _ = 0 := by simp
  exact cubic_chronology_defect_e12_e21_ne_zero hevaluation

/-- The fixed prime channel used in the concrete chronology witness. -/
def primeTwo : Nat.Primes := ⟨2, by norm_num⟩

/-- First prime-golden event of the strict-refinement witness. -/
def eventA : PrimeGoldenStepEvent where
  prime := primeTwo
  layer := 0

/-- Second prime-golden event of the strict-refinement witness. -/
def eventB : PrimeGoldenStepEvent where
  prime := primeTwo
  layer := 1

/-- Matrix observation distinguishing the two concrete event labels. -/
def explicitMatrixObservation
    (event : PrimeGoldenStepEvent) : IntegerMatrix2 :=
  if event.layer = 0 then e12 else e21

/-- The concrete event observations are the two matrix units. -/
@[simp] theorem explicit_matrix_observation_eventA :
    explicitMatrixObservation eventA = e12 := by
  simp [explicitMatrixObservation, eventA]

@[simp] theorem explicit_matrix_observation_eventB :
    explicitMatrixObservation eventB = e21 := by
  simp [explicitMatrixObservation, eventB]

/-- Explicit strictness certificate: `ABBA` and `BAAB` agree under bidegree,
all scalar phase times, and the complete step-two signature, yet the
third-order readout separates them. -/
theorem explicit_degree_three_strict_refinement :
    primeGoldenBidegree [eventA, eventB, eventB, eventA] =
        primeGoldenBidegree [eventB, eventA, eventA, eventB] ∧
      SameScalarTrajectory
        [eventA, eventB, eventB, eventA]
        [eventB, eventA, eventA, eventB] ∧
      chronologicalSignature explicitMatrixObservation
          [eventA, eventB, eventB, eventA] =
        chronologicalSignature explicitMatrixObservation
          [eventB, eventA, eventA, eventB] ∧
      thirdOrderReadout explicitMatrixObservation
          [eventA, eventB, eventB, eventA] ≠
        thirdOrderReadout explicitMatrixObservation
          [eventB, eventA, eventA, eventB] := by
  apply prime_golden_third_order_chronology_escape
    explicitMatrixObservation eventA eventB
  intro hcubic
  apply cubic_chronology_defect_e12_e21_ne_zero
  unfold cubicChronologyDefect
  rw [ordered_triple_moment_abba, ordered_triple_moment_baab]
  apply sub_eq_zero.mpr
  simpa using hcubic

#print axioms cubic_chronology_defect_eq_neg_nested_commutator
#print axioms cubic_chronology_defect_swap
#print axioms free_lie_evaluation_third_order
#print axioms cubic_chronology_defect_e12_e21
#print axioms cubic_chronology_defect_e12_e21_ne_zero
#print axioms third_order_free_lie_word_nonzero
#print axioms explicit_degree_three_strict_refinement

end

end D5.S3.Observer.Chronology.PrimeGoldenThirdOrderFreeLieBridge
