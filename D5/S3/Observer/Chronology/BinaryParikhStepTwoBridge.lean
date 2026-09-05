/- GID: D5/S3/Observer/Chronology/BinaryParikhStepTwoBridge
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary Parikh matrices realize the count and ordered-pair coordinates of Chen signatures. -/

import D5.S3.Observer.Chronology.StepTwoChronologicalSignature
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Binary Parikh matrices as a step-two chronological observer

The standard binary Parikh matrix sends the first letter to `I + E01` and
its successor to `I + E12`. Its three upper entries count the two letters
and scattered first-before-second pairs. This module connects that classical
matrix mapping to the existing factorial Chen signature and doubled Magnus
coordinate. No second signature composition operation is introduced.

Here `true` is the first letter. The matrix generators are strictly upper
triangular, their squares vanish, and every product of three generators is
zero. The center of doubled Magnus is `2 * pairs - trueCount * falseCount`.
The mapping remains non-injective on arbitrary binary words.

Classical anchor: A. Mateescu, A. Salomaa, K. Salomaa and S. Yu,
A sharpening of the Parikh mapping, RAIRO ITA 35(6) (2001), 551-564,
DOI 10.1051/ita:2001131. Bibliography verified against the Numdam journal record.
Library search found prime-event Parikh *vectors* and Mathlib's abstract
Heisenberg Lie algebra, but neither supplies this binary word-to-matrix and
Chen-coordinate adapter. This is a formal integration, not a novelty claim
for Parikh matrices or Heisenberg algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.BinaryParikhStepTwoBridge

open D5.S3.Observer.Chronology.StepTwoChronologicalSignature

/-- Integer three-by-three matrices for the binary Parikh representation. -/
abbrev IntegerMatrix3 := Matrix (Fin 3) (Fin 3) ℤ

private def upper (r f c : ℤ) : IntegerMatrix3 :=
  !![0, r, c; 0, 0, f; 0, 0, 0]

private theorem upper_zero : upper 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem upper_add (r f c r' f' c' : ℤ) :
    upper r f c + upper r' f' c' = upper (r + r') (f + f') (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper]

private theorem upper_mul (r f c r' f' c' : ℤ) :
    upper r f c * upper r' f' c' = upper 0 0 (r * f') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Nilpotent letter observations: true maps to E01 and false to E12. -/
def binaryLetterObservation : Bool → IntegerMatrix3
  | true => upper 1 0 0
  | false => upper 0 1 0

/-- Scattered true-false pairs, allowing arbitrary intervening letters. -/
def scatteredTrueFalseCount : List Bool → ℕ
  | [] => 0
  | true :: tail => tail.count false + scatteredTrueFalseCount tail
  | false :: tail => scatteredTrueFalseCount tail

/-- Appending a false letter contributes one pair for each preceding true. -/
theorem scattered_true_false_count_append_letter (word : List Bool) (letter : Bool) :
    scatteredTrueFalseCount (word ++ [letter]) =
      scatteredTrueFalseCount word + if letter = true then 0 else word.count true := by
  induction word with
  | nil => cases letter <;> simp [scatteredTrueFalseCount]
  | cons head tail ih =>
      cases head <;> cases letter <;>
        simp [scatteredTrueFalseCount, ih, List.count_append] <;> omega

/-- The two binary letter counts exhaust the word length. -/
theorem binary_letter_counts_length (word : List Bool) :
    word.count true + word.count false = word.length := by
  induction word with
  | nil => rfl
  | cons head tail ih => cases head <;> simp_all <;> omega

/-- The usual binary Parikh matrix is a literal ordered product of unipotent
integer matrices. -/
def binaryParikhMatrix (word : List Bool) : IntegerMatrix3 :=
  (word.map fun letter => 1 + binaryLetterObservation letter).prod

private def matrixOfCounts (r f c : ℤ) : IntegerMatrix3 := 1 + upper r f c

private theorem matrix_of_counts_mul (r f c r' f' c' : ℤ) :
    matrixOfCounts r f c * matrixOfCounts r' f' c' =
      matrixOfCounts (r + r') (f + f') (c + c' + r * f') := by
  unfold matrixOfCounts
  calc
    (1 + upper r f c) * (1 + upper r' f' c') =
        1 + (upper r f c + upper r' f' c' + upper r f c * upper r' f' c') := by
      noncomm_ring
    _ = 1 + upper (r + r') (f + f') (c + c' + r * f') := by
      rw [upper_mul, upper_add, upper_add]
      simp

private theorem parikh_normal_form (word : List Bool) :
    binaryParikhMatrix word =
      matrixOfCounts (word.count true) (word.count false) (scatteredTrueFalseCount word) := by
  induction word with
  | nil => simp [binaryParikhMatrix, scatteredTrueFalseCount, matrixOfCounts, upper_zero]
  | cons letter tail ih =>
      change (1 + binaryLetterObservation letter) * binaryParikhMatrix tail = _
      rw [ih]
      cases letter
      · change matrixOfCounts 0 1 0 * _ = _
        rw [matrix_of_counts_mul]
        simp [scatteredTrueFalseCount, add_comm]
      · change matrixOfCounts 1 0 0 * _ = _
        rw [matrix_of_counts_mul]
        simp [scatteredTrueFalseCount, add_comm]

private def signatureOfCounts (r f c : ℤ) : StepTwoSignature IntegerMatrix3 where
  degreeOne := upper r f 0
  doubledDegreeTwo := upper 0 0 (2 * c)

private theorem signature_of_counts_mul (r f c r' f' c' : ℤ) :
    signatureOfCounts r f c * signatureOfCounts r' f' c' =
      signatureOfCounts (r + r') (f + f') (c + c' + r * f') := by
  apply StepTwoSignature.ext
  · change upper r f 0 + upper r' f' 0 = upper (r + r') (f + f') 0
    rw [upper_add]
    rfl
  · change upper 0 0 (2 * c) + 2 * (upper r f 0 * upper r' f' 0) +
        upper 0 0 (2 * c') = upper 0 0 (2 * (c + c' + r * f'))
    simp only [upper_mul, two_mul, upper_add, add_zero, zero_add]
    congr 1 <;> ring

private theorem event_signature_letter (letter : Bool) :
    eventSignature (binaryLetterObservation letter) =
      signatureOfCounts (if letter = true then 1 else 0)
        (if letter = true then 0 else 1) 0 := by
  cases letter <;> apply StepTwoSignature.ext <;>
    simp [binaryLetterObservation, eventSignature, signatureOfCounts, upper_mul]

private theorem signature_normal_form (word : List Bool) :
    chronologicalSignature binaryLetterObservation word =
      signatureOfCounts (word.count true) (word.count false) (scatteredTrueFalseCount word) := by
  induction word with
  | nil =>
      apply StepTwoSignature.ext <;>
        simp [signatureOfCounts, scatteredTrueFalseCount, upper_zero]
  | cons letter tail ih =>
      rw [chronological_signature_cons, event_signature_letter, ih, signature_of_counts_mul]
      cases letter <;> simp [scatteredTrueFalseCount, add_comm]

/-- The standard Parikh entries are exactly the two counts and ordered pairs. -/
theorem binary_parikh_matrix_entries (word : List Bool) :
    binaryParikhMatrix word 0 1 = (word.count true : ℤ) ∧
      binaryParikhMatrix word 1 2 = (word.count false : ℤ) ∧
      binaryParikhMatrix word 0 2 = (scatteredTrueFalseCount word : ℤ) := by
  rw [parikh_normal_form]
  simp [matrixOfCounts, upper, Matrix.one_apply]

/-- The same ordered-pair count is the central factorial Chen coordinate. -/
theorem binary_step_two_signature_entries (word : List Bool) :
    (chronologicalSignature binaryLetterObservation word).degreeOne 0 1 =
        (word.count true : ℤ) ∧
      (chronologicalSignature binaryLetterObservation word).degreeOne 1 2 =
        (word.count false : ℤ) ∧
      (chronologicalSignature binaryLetterObservation word).doubledDegreeTwo 0 2 =
        2 * (scatteredTrueFalseCount word : ℤ) := by
  rw [signature_normal_form]
  simp [signatureOfCounts, upper]

/-- The central doubled Magnus coordinate centers the ordered-pair count. -/
theorem binary_doubled_magnus_center (word : List Bool) :
    doubledMagnusDegreeTwo (chronologicalSignature binaryLetterObservation word) 0 2 =
      2 * (scatteredTrueFalseCount word : ℤ) -
        (word.count true : ℤ) * (word.count false : ℤ) := by
  rw [signature_normal_form]
  change (upper 0 0 (2 * (scatteredTrueFalseCount word : ℤ)) -
    upper (word.count true) (word.count false) 0 *
      upper (word.count true) (word.count false) 0) 0 2 = _
  rw [upper_mul]
  simp [upper]

/-- Counts and one central Magnus entry recover all three Parikh entries. -/
theorem binary_parikh_eq_of_counts_and_magnus (left right : List Bool)
    (htrue : left.count true = right.count true)
    (hfalse : left.count false = right.count false)
    (hmagnus :
      doubledMagnusDegreeTwo (chronologicalSignature binaryLetterObservation left) 0 2 =
        doubledMagnusDegreeTwo (chronologicalSignature binaryLetterObservation right) 0 2) :
    binaryParikhMatrix left = binaryParikhMatrix right := by
  rw [binary_doubled_magnus_center, binary_doubled_magnus_center, htrue, hfalse] at hmagnus
  have hpairs : scatteredTrueFalseCount left = scatteredTrueFalseCount right := by omega
  rw [parikh_normal_form, parikh_normal_form, htrue, hfalse, hpairs]

/-- This representation is two-step nilpotent: all triple generator products vanish. -/
theorem binary_letter_triple_product_zero (a b c : Bool) :
    binaryLetterObservation a * binaryLetterObservation b * binaryLetterObservation c = 0 := by
  cases a <;> cases b <;> cases c <;>
    simp [binaryLetterObservation, upper_mul, upper_zero]

/-- The language restriction in a recovery theorem cannot be dropped. -/
theorem binary_parikh_arbitrary_word_collision :
    binaryParikhMatrix [true, false, false, true] =
      binaryParikhMatrix [false, true, true, false] ∧
      ([true, false, false, true] : List Bool) ≠ [false, true, true, false] := by
  constructor
  · rw [parikh_normal_form, parikh_normal_form]
    rfl
  · decide

#print axioms scattered_true_false_count_append_letter
#print axioms binary_parikh_matrix_entries
#print axioms binary_step_two_signature_entries
#print axioms binary_doubled_magnus_center
#print axioms binary_parikh_eq_of_counts_and_magnus
#print axioms binary_letter_triple_product_zero
#print axioms binary_parikh_arbitrary_word_collision

end D5.S3.Observer.Chronology.BinaryParikhStepTwoBridge
