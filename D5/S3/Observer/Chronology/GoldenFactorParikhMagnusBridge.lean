/- GID: D5/S3/Observer/Chronology/GoldenFactorParikhMagnusBridge
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One fixed binary Parikh and step-two Magnus observer is faithful on legal golden factors. -/

import D5.S1.Words.GoldenFactorSecondOrderBinomialRigidity
import D5.S3.Observer.Chronology.BinaryParikhStepTwoBridge

/-!
# A fixed nilpotent observer reconstructs legal golden factors

The preceding word-theoretic owner reconstructs a fixed-length golden factor
from the true-letter count and scattered true-false count. The matrix owner
realizes these statistics as a standard binary Parikh matrix and as exact
coordinates of the existing Chen signature.

This adapter proves faithfulness of that actual matrix observer on consecutive
golden factors, including factors whose lengths were not supplied in advance.
Its two first-order entries recover the length; its center recovers the
ordered-pair count. First-degree matrix data together with one doubled Magnus
entry are equally sufficient. The legal LS/SL pair certifies that first degree
alone loses order.

This does not recover an absolute occurrence index, physical time, prime
labels, or arbitrary event words. The unrestricted ABBA/BAAB collision in the
matrix owner is retained. The significance is grammar-dependent sufficiency
of a fixed two-step nilpotent representation, not a general injectivity theorem
for Parikh matrices or an originality claim for Sturmian binomial rigidity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.GoldenFactorParikhMagnusBridge

open D5.S1.Words
open D5.S1.Words.GoldenFactorSecondOrderBinomialRigidity
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.BinaryParikhStepTwoBridge
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

/-- The list count in the actual matrix representation equals the existing
Beatty-window count. -/
theorem golden_factor_true_count (n i : ℕ) :
    (goldenFactor n i).count true = goldenWindowTrueCount i n := by
  induction n with
  | zero => simp [goldenFactor, goldenWindowTrueCount]
  | succ n ih =>
      rw [golden_factor_append_letter, List.count_append, golden_count_succ, ih]
      cases h : goldenWord (i + n) <;> simp [h]

/-- The matrix pair counter agrees with the existing golden binomial statistic. -/
theorem golden_factor_scattered_count (n i : ℕ) :
    scatteredTrueFalseCount (goldenFactor n i) = goldenTrueFalseCount i n := by
  induction n with
  | zero => simp [goldenFactor, scatteredTrueFalseCount, goldenTrueFalseCount]
  | succ n ih =>
      rw [golden_factor_append_letter, scattered_true_false_count_append_letter,
        ih, golden_factor_true_count]
      simp only [goldenTrueFalseCount, Finset.sum_range_succ]

/-- The doubled Magnus center on a legal factor is an explicit integer
statistic with no division. -/
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

/-- One fixed three-by-three Parikh observer is faithful on all legal golden
factors. Its first entries also recover length, which need not be fixed a priori. -/
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

/-- The first-degree matrix and one central Magnus coordinate suffice for
word recovery on the legal language. No higher-order coordinate is required. -/
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

/-- Existing represented Chen signatures have exactly the full-word fibers
on the legal golden language under this explicit fixed observation. -/
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

/-- A legal two-letter witness proves first-order insufficiency and gives
opposite, nonzero central Magnus entries at the sufficient second order. -/
theorem legal_golden_first_to_second_order_strictness :
    (chronologicalSignature binaryLetterObservation (goldenFactor 2 0)).degreeOne =
        (chronologicalSignature binaryLetterObservation (goldenFactor 2 1)).degreeOne ∧
      goldenFactor 2 0 ≠ goldenFactor 2 1 ∧
      doubledMagnusDegreeTwo
        (chronologicalSignature binaryLetterObservation (goldenFactor 2 0)) 0 2 = 1 ∧
      doubledMagnusDegreeTwo
        (chronologicalSignature binaryLetterObservation (goldenFactor 2 1)) 0 2 = -1 := by
  have hleft : goldenFactor 2 0 = [true, false] := by decide
  have hright : goldenFactor 2 1 = [false, true] := by decide
  rw [hleft, hright]
  decide

#print axioms golden_factor_true_count
#print axioms golden_factor_scattered_count
#print axioms golden_factor_doubled_magnus_center
#print axioms golden_factor_eq_iff_parikh_matrix_eq
#print axioms golden_factor_eq_of_first_degree_and_magnus
#print axioms golden_factor_eq_iff_step_two_signature_eq
#print axioms legal_golden_first_to_second_order_strictness

end D5.S3.Observer.Chronology.GoldenFactorParikhMagnusBridge
