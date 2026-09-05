/- GID: D5/S3/Observer/GoldenChronology/GoldenFactorParikhMagnusBridge
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed Parikh matrix and its Chen coordinates recover legal golden factors. -/

import D5.S1.Words.GoldenRecovery.GoldenFactorSecondOrderBinomialRigidity
import D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge

/-!
# Golden-language faithfulness of the fixed Parikh observer

This recovers the unmerged #5014 adapter, reusing the unique binary observer.
The companion uploaded GoldenFactorHeisenbergReadout candidate is not copied:
it defines the same matrix readout again. The first two entries recover length
and counts, and the central entry recovers the scattered-pair statistic.
The conclusion concerns word content, not absolute starts or prime labels.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenChronology.GoldenFactorParikhMagnusBridge

open D5.S1.Words
open D5.S1.Words.GoldenRecovery.GoldenFactorSecondOrderBinomialRigidity
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open scoped BigOperators

private theorem golden_factor_append_letter (n i : ℕ) :
    goldenFactor (n + 1) i = goldenFactor n i ++ [goldenWord (i + n)] := by
  simp [goldenFactor, List.ofFn_succ', List.concat_eq_append]

private theorem golden_count_succ (i n : ℕ) :
    goldenWindowTrueCount i (n + 1) = goldenWindowTrueCount i n +
      if goldenWord (i + n) = true then 1 else 0 := by
  classical
  by_cases h : goldenWord (i + n) = true <;>
    simp [goldenWindowTrueCount, Finset.range_add_one, Finset.filter_insert, h]

/-- The actual word count is the canonical Beatty-window count. -/
theorem golden_factor_true_count (n i : ℕ) :
    (goldenFactor n i).count true = goldenWindowTrueCount i n := by
  induction n with
  | zero => simp [goldenFactor, goldenWindowTrueCount]
  | succ n ih =>
      rw [golden_factor_append_letter, List.count_append, golden_count_succ, ih]
      cases h : goldenWord (i + n) <;> simp [h]

/-- The actual pair counter is the canonical golden binomial statistic. -/
theorem golden_factor_scattered_count (n i : ℕ) :
    scatteredTrueFalseCount (goldenFactor n i) = goldenTrueFalseCount i n := by
  induction n with
  | zero => simp [goldenFactor, scatteredTrueFalseCount, goldenTrueFalseCount]
  | succ n ih =>
      rw [golden_factor_append_letter, scattered_true_false_count_append_letter,
        ih, golden_factor_true_count]
      simp only [goldenTrueFalseCount, Finset.sum_range_succ]

/-- Explicit division-free central Lie coordinate on a golden factor. -/
theorem golden_factor_doubled_magnus_center (n i : ℕ) :
    doubledMagnusDegreeTwo
        (chronologicalSignature binaryLetterObservation (goldenFactor n i)) 0 2 =
      2 * (goldenTrueFalseCount i n : ℤ) -
        (goldenWindowTrueCount i n : ℤ) *
          ((n : ℤ) - (goldenWindowTrueCount i n : ℤ)) := by
  have hlength := binary_letter_counts_length (goldenFactor n i)
  rw [golden_factor_true_count] at hlength
  have hfactorLength : (goldenFactor n i).length = n := by simp [goldenFactor]
  rw [hfactorLength] at hlength
  have hfalse : ((goldenFactor n i).count false : ℤ) =
      (n : ℤ) - (goldenWindowTrueCount i n : ℤ) := by omega
  rw [binary_doubled_magnus_center, golden_factor_scattered_count,
    golden_factor_true_count, hfalse]

/-- Equality of actual Parikh endpoints is exactly equality of legal factors. -/
theorem golden_factor_eq_iff_parikh_matrix_eq (n m i j : ℕ) :
    goldenFactor n i = goldenFactor m j ↔
      binaryParikhMatrix (goldenFactor n i) = binaryParikhMatrix (goldenFactor m j) := by
  constructor
  · intro h
    rw [h]
  · intro hmatrix
    have htrue := congrArg (fun matrix : IntegerMatrix3 => matrix 0 1) hmatrix
    have hfalse := congrArg (fun matrix : IntegerMatrix3 => matrix 1 2) hmatrix
    have hpairs := congrArg (fun matrix : IntegerMatrix3 => matrix 0 2) hmatrix
    rw [(binary_parikh_matrix_entries (goldenFactor n i)).1,
      (binary_parikh_matrix_entries (goldenFactor m j)).1] at htrue
    rw [(binary_parikh_matrix_entries (goldenFactor n i)).2.1,
      (binary_parikh_matrix_entries (goldenFactor m j)).2.1] at hfalse
    rw [(binary_parikh_matrix_entries (goldenFactor n i)).2.2,
      (binary_parikh_matrix_entries (goldenFactor m j)).2.2] at hpairs
    have htrueNat : (goldenFactor n i).count true = (goldenFactor m j).count true := by
      exact_mod_cast htrue
    have hfalseNat : (goldenFactor n i).count false = (goldenFactor m j).count false := by
      exact_mod_cast hfalse
    have hpairNat : scatteredTrueFalseCount (goldenFactor n i) =
        scatteredTrueFalseCount (goldenFactor m j) := by exact_mod_cast hpairs
    have hleftLength := binary_letter_counts_length (goldenFactor n i)
    have hrightLength := binary_letter_counts_length (goldenFactor m j)
    have hnLength : (goldenFactor n i).length = n := by simp [goldenFactor]
    have hmLength : (goldenFactor m j).length = m := by simp [goldenFactor]
    rw [hnLength] at hleftLength
    rw [hmLength] at hrightLength
    have hnm : n = m := by omega
    subst m
    apply golden_factor_eq_of_second_order_counts n i j
    · simpa only [golden_factor_true_count] using htrueNat
    · simpa only [golden_factor_scattered_count] using hpairNat

/-- First degree and the Magnus center recover the full legal word. -/
theorem golden_factor_eq_of_first_degree_and_magnus (n m i j : ℕ)
    (hfirst :
      (chronologicalSignature binaryLetterObservation (goldenFactor n i)).degreeOne =
        (chronologicalSignature binaryLetterObservation (goldenFactor m j)).degreeOne)
    (hmagnus :
      doubledMagnusDegreeTwo
          (chronologicalSignature binaryLetterObservation (goldenFactor n i)) 0 2 =
        doubledMagnusDegreeTwo
          (chronologicalSignature binaryLetterObservation (goldenFactor m j)) 0 2) :
    goldenFactor n i = goldenFactor m j := by
  apply (golden_factor_eq_iff_parikh_matrix_eq n m i j).mpr
  apply binary_parikh_eq_of_counts_and_magnus
  · have h := congrArg (fun matrix : IntegerMatrix3 => matrix 0 1) hfirst
    rw [(binary_step_two_signature_entries (goldenFactor n i)).1,
      (binary_step_two_signature_entries (goldenFactor m j)).1] at h
    exact_mod_cast h
  · have h := congrArg (fun matrix : IntegerMatrix3 => matrix 1 2) hfirst
    rw [(binary_step_two_signature_entries (goldenFactor n i)).2.1,
      (binary_step_two_signature_entries (goldenFactor m j)).2.1] at h
    exact_mod_cast h
  · exact hmagnus

/-- The represented Chen signature has the same kernel as the complete factor. -/
theorem golden_factor_eq_iff_step_two_signature_eq (n m i j : ℕ) :
    goldenFactor n i = goldenFactor m j ↔
      chronologicalSignature binaryLetterObservation (goldenFactor n i) =
        chronologicalSignature binaryLetterObservation (goldenFactor m j) := by
  constructor
  · intro h
    rw [h]
  · intro h
    apply golden_factor_eq_of_first_degree_and_magnus n m i j
    · exact congrArg StepTwoSignature.degreeOne h
    · exact congrArg
        (fun signature : StepTwoSignature IntegerMatrix3 =>
          doubledMagnusDegreeTwo signature 0 2) h

#print axioms golden_factor_eq_iff_parikh_matrix_eq
#print axioms golden_factor_eq_of_first_degree_and_magnus
#print axioms golden_factor_eq_iff_step_two_signature_eq

end D5.S3.Observer.GoldenChronology.GoldenFactorParikhMagnusBridge
