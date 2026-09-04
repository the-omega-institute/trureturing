/- GID: D5/S3/Observer/Chronology/PrimeGoldenThirdMagnusStrictness
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two prime-golden histories with equal second Magnus data are separated by an explicit nonzero third Magnus primitive. -/

import D5.S3.Observer.Chronology.StepThreePrimitiveMagnus
import D5.S3.Observer.Chronology.PrimeGoldenStepThreeStrictness
import Mathlib.Tactic

/-!
# Strictness of the third Magnus primitive

The step-three Chen coordinate already separates the explicit `ABBA/BAAB`
residual fiber. This module proves that the separation survives logarithmic
projection to the genuine third Magnus primitive.

The two words have equal degree-one and degree-two signatures. Therefore every
lower-order correction in `12 Ω₃` cancels, and the primitive difference is
exactly twelve times the cubic free-Lie defect. Under the `E12/E21`
representation this is the nonzero matrix `!![0, 24; -24, 0]`.

Hence the new information is primitive Lie chronology rather than a purely
tensor-coordinate artifact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeGoldenThirdMagnusStrictness

open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.StepThreeChronologicalSignature
open D5.S3.Observer.Chronology.StepThreePrimitiveMagnus
open D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge
open D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature
open D5.S3.Observer.Chronology.PrimeGoldenChronologyFiberSeparation
open D5.S3.Observer.Chronology.PrimeGoldenThirdOrderChronologyEscape
open D5.S3.Observer.Chronology.PrimeGoldenThirdOrderFreeLieBridge
open D5.S3.Observer.Chronology.PrimeGoldenStepThreeStrictness

noncomputable section

universe u

/-- The primitive third-coordinate difference is twelve times the cubic
chronology defect. -/
theorem duodecupled_magnus_abba_sub_baab
    {A : Type u} [Ring A] (a b : A) :
    duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature (fun value : A => value)
          [a, b, b, a]) -
      duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature (fun value : A => value)
          [b, a, a, b]) =
      12 * cubicChronologyDefect a b := by
  simp [duodecupledMagnusDegreeThree,
    chronologicalStepThreeSignature, eventStepThreeSignature,
    StepThreeSignature.compose, cubicChronologyDefect,
    orderedTripleMoment, orderedPairMoment]
  noncomm_ring

/-- Explicit value of the third Magnus difference. -/
def thirdMagnusWitnessMatrix : IntegerMatrix2 := !![0, 24; -24, 0]

/-- The `E12/E21` representation evaluates the third Magnus difference to its
explicit nonzero witness. -/
theorem duodecupled_magnus_e12_e21_difference :
    duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature
          (fun value : IntegerMatrix2 => value) [e12, e21, e21, e12]) -
      duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature
          (fun value : IntegerMatrix2 => value) [e21, e12, e12, e21]) =
      thirdMagnusWitnessMatrix := by
  rw [duodecupled_magnus_abba_sub_baab,
    cubic_chronology_defect_e12_e21]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicWitnessMatrix, thirdMagnusWitnessMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The third Magnus matrix witness is nonzero. -/
theorem third_magnus_witness_matrix_ne_zero :
    thirdMagnusWitnessMatrix ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrFun hzero (0 : Fin 2)) (1 : Fin 2)
  norm_num [thirdMagnusWitnessMatrix] at hentry

/-- Equal step-two data does not force equal third Magnus primitives. -/
theorem explicit_third_magnus_abba_ne_baab :
    duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature
          (fun value : IntegerMatrix2 => value) [e12, e21, e21, e12]) ≠
      duodecupledMagnusDegreeThree
        (chronologicalStepThreeSignature
          (fun value : IntegerMatrix2 => value) [e21, e12, e12, e21]) := by
  intro hequal
  have hzero :
      duodecupledMagnusDegreeThree
          (chronologicalStepThreeSignature
            (fun value : IntegerMatrix2 => value) [e12, e21, e21, e12]) -
        duodecupledMagnusDegreeThree
          (chronologicalStepThreeSignature
            (fun value : IntegerMatrix2 => value) [e21, e12, e12, e21]) = 0 :=
    sub_eq_zero.mpr hequal
  rw [duodecupled_magnus_e12_e21_difference] at hzero
  exact third_magnus_witness_matrix_ne_zero hzero

/-- The explicit prime-golden pair has equal count, scalar, and second-Magnus
readouts, yet distinct third-Magnus primitives. -/
theorem explicit_prime_golden_third_magnus_strictness :
    primeGoldenBidegree [eventA, eventB, eventB, eventA] =
        primeGoldenBidegree [eventB, eventA, eventA, eventB] ∧
      SameScalarTrajectory
        [eventA, eventB, eventB, eventA]
        [eventB, eventA, eventA, eventB] ∧
      doubledMagnusDegreeTwoOfStepThree
          (chronologicalStepThreeSignature explicitMatrixObservation
            [eventA, eventB, eventB, eventA]) =
        doubledMagnusDegreeTwoOfStepThree
          (chronologicalStepThreeSignature explicitMatrixObservation
            [eventB, eventA, eventA, eventB]) ∧
      duodecupledMagnusDegreeThree
          (chronologicalStepThreeSignature explicitMatrixObservation
            [eventA, eventB, eventB, eventA]) ≠
        duodecupledMagnusDegreeThree
          (chronologicalStepThreeSignature explicitMatrixObservation
            [eventB, eventA, eventA, eventB]) := by
  refine
    ⟨prime_golden_bidegree_abba_eq_baab eventA eventB,
      prime_golden_scalar_trajectory_abba_eq_baab eventA eventB,
      ?_, ?_⟩
  · unfold doubledMagnusDegreeTwoOfStepThree
    rw [truncate_chronological_step_three_signature,
      truncate_chronological_step_three_signature,
      prime_golden_step_two_signature_abba_eq_baab]
  · simpa [chronologicalStepThreeSignature] using
      explicit_third_magnus_abba_ne_baab

#print axioms duodecupled_magnus_abba_sub_baab
#print axioms duodecupled_magnus_e12_e21_difference
#print axioms explicit_third_magnus_abba_ne_baab
#print axioms explicit_prime_golden_third_magnus_strictness

end

end D5.S3.Observer.Chronology.PrimeGoldenThirdMagnusStrictness
