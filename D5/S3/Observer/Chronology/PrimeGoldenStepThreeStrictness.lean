/- GID: D5/S3/Observer/Chronology/PrimeGoldenStepThreeStrictness
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A concrete prime-golden chronology has equal complete step-two truncations but unequal step-three Chen signatures, certified by a nonzero nested-commutator matrix. -/

import D5.S3.Observer.Chronology.StepThreeChronologicalSignature
import D5.S3.Observer.Chronology.PrimeGoldenThirdOrderFreeLieBridge
import Mathlib.Tactic

/-!
# Strict step-three refinement of a prime-golden chronology fiber

The words `ABBA` and `BAAB` already form a residual fiber after prime-golden
bidegree, complete scalar phase trajectory, and the full step-two signature.
This module places that witness inside a genuine step-three Chen signature.

The difference of their factorially normalized degree-three coordinates is
six times the cubic chronology defect, hence

`-6 * [a + b, [a, b]]`.

For the explicit integer matrices `E12` and `E21`, this difference is
`!![0, 12; -12, 0]`, so it is nonzero. Consequently truncation from the
step-three signature monoid to the step-two signature monoid is not injective.
The result proves a strict observation-fiber refinement rather than merely
renaming the previously defined cubic statistic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeGoldenStepThreeStrictness

open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.StepThreeChronologicalSignature
open D5.S3.Observer.Chronology.PrimeWordAntipodeParityStepBridge
open D5.S3.Observer.Chronology.PrimeGoldenBigradedChronologicalSignature
open D5.S3.Observer.Chronology.PrimeGoldenChronologyFiberSeparation
open D5.S3.Observer.Chronology.PrimeGoldenThirdOrderChronologyEscape
open D5.S3.Observer.Chronology.PrimeGoldenThirdOrderFreeLieBridge

noncomputable section

universe u

/-- The degree-three difference between `ABBA` and `BAAB` is six times the
ordered cubic chronology defect. -/
theorem sextupled_degree_three_abba_sub_baab
    {A : Type u} [Ring A] (a b : A) :
    (chronologicalStepThreeSignature (fun value : A => value)
        [a, b, b, a]).sextupledDegreeThree -
      (chronologicalStepThreeSignature (fun value : A => value)
        [b, a, a, b]).sextupledDegreeThree =
      6 * cubicChronologyDefect a b := by
  simp [chronologicalStepThreeSignature, eventStepThreeSignature,
    StepThreeSignature.compose, cubicChronologyDefect,
    orderedTripleMoment, orderedPairMoment]
  noncomm_ring

/-- The two words have exactly the same complete step-two truncation in every
associative ring representation. -/
theorem truncate_step_three_abba_eq_baab
    {A : Type u} [Ring A] (a b : A) :
    truncateStepTwo
        (chronologicalStepThreeSignature (fun value : A => value)
          [a, b, b, a]) =
      truncateStepTwo
        (chronologicalStepThreeSignature (fun value : A => value)
          [b, a, a, b]) := by
  rw [truncate_chronological_step_three_signature,
    truncate_chronological_step_three_signature]
  exact step_two_signature_abba_eq_baab a b

/-- Six times the explicit cubic witness. -/
def sextupledCubicWitnessMatrix : IntegerMatrix2 := !![0, 12; -12, 0]

/-- The step-three coordinate difference evaluates to a concrete matrix. -/
theorem sextupled_degree_three_e12_e21_difference :
    (chronologicalStepThreeSignature (fun value : IntegerMatrix2 => value)
        [e12, e21, e21, e12]).sextupledDegreeThree -
      (chronologicalStepThreeSignature (fun value : IntegerMatrix2 => value)
        [e21, e12, e12, e21]).sextupledDegreeThree =
      sextupledCubicWitnessMatrix := by
  rw [sextupled_degree_three_abba_sub_baab,
    cubic_chronology_defect_e12_e21]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicWitnessMatrix, sextupledCubicWitnessMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The explicit degree-three difference is nonzero. -/
theorem sextupled_cubic_witness_matrix_ne_zero :
    sextupledCubicWitnessMatrix ≠ 0 := by
  intro hzero
  have hentry := congrFun (congrFun hzero (0 : Fin 2)) (1 : Fin 2)
  norm_num [sextupledCubicWitnessMatrix] at hentry

/-- The two explicit histories are identified by step two and separated by the
complete step-three signature. -/
theorem explicit_step_three_abba_ne_baab :
    chronologicalStepThreeSignature (fun value : IntegerMatrix2 => value)
        [e12, e21, e21, e12] ≠
      chronologicalStepThreeSignature (fun value : IntegerMatrix2 => value)
        [e21, e12, e12, e21] := by
  intro hequal
  have hthird := congrArg StepThreeSignature.sextupledDegreeThree hequal
  have hzero :
      (chronologicalStepThreeSignature (fun value : IntegerMatrix2 => value)
          [e12, e21, e21, e12]).sextupledDegreeThree -
        (chronologicalStepThreeSignature (fun value : IntegerMatrix2 => value)
          [e21, e12, e12, e21]).sextupledDegreeThree = 0 :=
    sub_eq_zero.mpr hthird
  rw [sextupled_degree_three_e12_e21_difference] at hzero
  exact sextupled_cubic_witness_matrix_ne_zero hzero

/-- The degree-three-to-degree-two monoid homomorphism has a genuine nontrivial
fiber. -/
theorem truncate_step_two_not_injective :
    ¬Function.Injective
      (truncateStepTwo :
        StepThreeSignature IntegerMatrix2 → StepTwoSignature IntegerMatrix2) := by
  intro hinjective
  apply explicit_step_three_abba_ne_baab
  apply hinjective
  exact truncate_step_three_abba_eq_baab e12 e21

/-- The concrete prime-golden histories agree in the count ledger, complete
scalar trajectory, and full step-two truncation, while their complete
step-three signatures differ. -/
theorem explicit_prime_golden_step_three_strict_refinement :
    primeGoldenBidegree [eventA, eventB, eventB, eventA] =
        primeGoldenBidegree [eventB, eventA, eventA, eventB] ∧
      SameScalarTrajectory
        [eventA, eventB, eventB, eventA]
        [eventB, eventA, eventA, eventB] ∧
      truncateStepTwo
          (chronologicalStepThreeSignature explicitMatrixObservation
            [eventA, eventB, eventB, eventA]) =
        truncateStepTwo
          (chronologicalStepThreeSignature explicitMatrixObservation
            [eventB, eventA, eventA, eventB]) ∧
      chronologicalStepThreeSignature explicitMatrixObservation
          [eventA, eventB, eventB, eventA] ≠
        chronologicalStepThreeSignature explicitMatrixObservation
          [eventB, eventA, eventA, eventB] := by
  refine
    ⟨prime_golden_bidegree_abba_eq_baab eventA eventB,
      prime_golden_scalar_trajectory_abba_eq_baab eventA eventB,
      ?_, ?_⟩
  · rw [truncate_chronological_step_three_signature,
      truncate_chronological_step_three_signature]
    exact prime_golden_step_two_signature_abba_eq_baab
      explicitMatrixObservation eventA eventB
  · simpa [chronologicalStepThreeSignature] using
      explicit_step_three_abba_ne_baab

#print axioms sextupled_degree_three_abba_sub_baab
#print axioms truncate_step_three_abba_eq_baab
#print axioms sextupled_degree_three_e12_e21_difference
#print axioms explicit_step_three_abba_ne_baab
#print axioms truncate_step_two_not_injective
#print axioms explicit_prime_golden_step_three_strict_refinement

end

end D5.S3.Observer.Chronology.PrimeGoldenStepThreeStrictness
