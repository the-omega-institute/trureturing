/- GID: D5/S3/Observer/Chronology/GoldenFactorHeisenbergReadout
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concrete Heisenberg transport and a central Magnus coordinate recover legal golden factors. -/

import D5.S1.Words.GoldenFactorSecondOrderBinomialRigidity
import D5.S3.Observer.Chronology.StepTwoChronologicalSignature
import Mathlib.Data.Matrix.Mul

/-!
# Concrete second-order recovery on the legal golden language

True and false are observed by E01 and E12 in three-by-three integer matrices.
The chronological product of their unitriangular pulses is H(r,z,P), where r
and z count the two letters and P counts scattered true-before-false pairs.
The existing represented step-two signature reads (r E01 + z E12, 2 P E02).
Its doubled Magnus central coordinate is 2 P - r z.

The recovery theorem applies to consecutive golden factors of known length.
It recovers the factor value, not its absolute occurrence index, and does not
assert faithfulness on arbitrary binary words or arbitrary representations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.GoldenFactorHeisenbergReadout

open D5.S1.Words
open D5.S1.Words.GoldenFactorSecondOrderBinomialRigidity
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature

abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℤ

/-- The three strictly upper-triangular coordinates. -/
def upper (r z p : ℤ) : Matrix3 := fun i j =>
  if i = 0 ∧ j = 1 then r else
  if i = 1 ∧ j = 2 then z else
  if i = 0 ∧ j = 2 then p else 0

/-- Unitriangular Heisenberg coordinates. -/
def heisenberg (r z p : ℤ) : Matrix3 := 1 + upper r z p

/-- The two observed matrix units. -/
def binaryGenerator (letter : Bool) : Matrix3 :=
  if letter = true then upper 1 0 0 else upper 0 1 0

/-- Exact pulse of one square-zero generator. -/
def binaryPulse (letter : Bool) : Matrix3 := 1 + binaryGenerator letter

/-- Count coordinates in the existing represented signature. -/
def countSignature (r z p : ℤ) : StepTwoSignature Matrix3 where
  degreeOne := upper r z 0
  doubledDegreeTwo := upper 0 0 (2 * p)

private theorem upper_zero : upper 0 0 0 = 0 := by
  ext i j
  simp [upper]

/-- The cross term counts true events before later false events. -/
theorem heisenberg_mul (r z p r' z' p' : ℤ) :
    heisenberg r z p * heisenberg r' z' p' =
      heisenberg (r + r') (z + z') (p + p' + r * z') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heisenberg, upper, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem pulse_true : binaryPulse true = heisenberg 1 0 0 := rfl
private theorem pulse_false : binaryPulse false = heisenberg 0 1 0 := rfl

private theorem count_signature_one : countSignature 0 0 0 = 1 := by
  apply StepTwoSignature.ext
  · exact upper_zero
  · simpa [countSignature] using upper_zero

private theorem count_signature_true (r z p : ℤ) :
    countSignature r z p * eventSignature (binaryGenerator true) =
      countSignature (r + 1) z p := by
  apply StepTwoSignature.ext
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [countSignature, eventSignature, binaryGenerator, upper] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [countSignature, eventSignature, binaryGenerator, upper,
        Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem count_signature_false (r z p : ℤ) :
    countSignature r z p * eventSignature (binaryGenerator false) =
      countSignature r (z + 1) (p + r) := by
  apply StepTwoSignature.ext
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [countSignature, eventSignature, binaryGenerator, upper] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [countSignature, eventSignature, binaryGenerator, upper,
        Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- Consecutive golden samples in chronological range order. -/
def goldenSamples (i n : ℕ) : List Bool :=
  (List.range n).map (fun k => goldenWord (i + k))

/-- Actual ordered multiplication of the pulses. -/
def goldenTransport (i n : ℕ) : Matrix3 :=
  ((goldenSamples i n).map binaryPulse).prod

/-- Existing step-two signature of the same samples. -/
def goldenMatrixSignature (i n : ℕ) : StepTwoSignature Matrix3 :=
  chronologicalSignature binaryGenerator (goldenSamples i n)

private theorem samples_succ (i n : ℕ) :
    goldenSamples i (n + 1) = goldenSamples i n ++ [goldenWord (i + n)] := by
  simp [goldenSamples, List.range_succ]

private theorem transport_succ (i n : ℕ) :
    goldenTransport i (n + 1) =
      goldenTransport i n * binaryPulse (goldenWord (i + n)) := by
  simp [goldenTransport, samples_succ]

private theorem signature_succ (i n : ℕ) :
    goldenMatrixSignature i (n + 1) =
      goldenMatrixSignature i n *
        eventSignature (binaryGenerator (goldenWord (i + n))) := by
  rw [goldenMatrixSignature, samples_succ, chronological_signature_append]
  simp [goldenMatrixSignature, chronologicalSignature]

private theorem count_succ (i n : ℕ) :
    goldenWindowTrueCount i (n + 1) = goldenWindowTrueCount i n +
      if goldenWord (i + n) = true then 1 else 0 := by
  classical
  by_cases h : goldenWord (i + n) = true <;>
    simp [goldenWindowTrueCount, Finset.range_add_one, Finset.filter_insert, h]

private theorem pair_count_succ (i n : ℕ) :
    goldenTrueFalseCount i (n + 1) = goldenTrueFalseCount i n +
      if goldenWord (i + n) = true then 0 else goldenWindowTrueCount i n := by
  unfold goldenTrueFalseCount
  rw [Finset.sum_range_succ]

/-- Closed form of the actual chronological matrix product. -/
theorem golden_transport_closed_form (i n : ℕ) :
    goldenTransport i n =
      heisenberg (goldenWindowTrueCount i n)
        ((n : ℤ) - goldenWindowTrueCount i n) (goldenTrueFalseCount i n) := by
  induction n with
  | zero =>
      simp [goldenTransport, goldenSamples, goldenWindowTrueCount,
        goldenTrueFalseCount, heisenberg, upper_zero]
  | succ n ih =>
      rw [transport_succ, ih, count_succ, pair_count_succ]
      cases h : goldenWord (i + n) with
      | false =>
          simp only [h, Bool.false_eq_true, if_false, Nat.add_zero]
          rw [pulse_false, heisenberg_mul]
          push_cast
          congr 1 <;> ring
      | true =>
          simp only [h, if_true, Nat.add_zero]
          rw [pulse_true, heisenberg_mul]
          push_cast
          congr 1 <;> ring

/-- The represented second coordinate reads twice the scattered pair count. -/
theorem golden_matrix_signature_closed_form (i n : ℕ) :
    goldenMatrixSignature i n =
      countSignature (goldenWindowTrueCount i n)
        ((n : ℤ) - goldenWindowTrueCount i n) (goldenTrueFalseCount i n) := by
  induction n with
  | zero =>
      simp [goldenMatrixSignature, goldenSamples, goldenWindowTrueCount,
        goldenTrueFalseCount, count_signature_one]
  | succ n ih =>
      rw [signature_succ, ih, count_succ, pair_count_succ]
      cases h : goldenWord (i + n) with
      | false =>
          simp only [h, Bool.false_eq_true, if_false, Nat.add_zero]
          rw [count_signature_false]
          push_cast
          congr 1 <;> ring
      | true =>
          simp only [h, if_true, Nat.add_zero]
          rw [count_signature_true]
          push_cast
          congr 1 <;> ring

/-- One central coordinate of the existing doubled Magnus observer. -/
def goldenMagnusCenter (i n : ℕ) : ℤ :=
  (doubledMagnusDegreeTwo (goldenMatrixSignature i n)) 0 2

/-- This Lie coordinate is the signed difference of the two pair orientations. -/
theorem golden_magnus_center_formula (i n : ℕ) :
    goldenMagnusCenter i n =
      2 * (goldenTrueFalseCount i n : ℤ) -
        (goldenWindowTrueCount i n : ℤ) *
          ((n : ℤ) - goldenWindowTrueCount i n) := by
  rw [goldenMagnusCenter, golden_matrix_signature_closed_form]
  norm_num [doubledMagnusDegreeTwo, countSignature, upper,
    Matrix.mul_apply, Fin.sum_univ_succ]

/-- A concrete matrix endpoint recovers a legal golden factor of known length. -/
theorem heisenberg_transport_recovers_golden_factor (n i j : ℕ)
    (h : goldenTransport i n = goldenTransport j n) :
    goldenFactor n i = goldenFactor n j := by
  rw [golden_transport_closed_form, golden_transport_closed_form] at h
  have hr := congrArg (fun m : Matrix3 => m 0 1) h
  have hp := congrArg (fun m : Matrix3 => m 0 2) h
  simp only [heisenberg, Matrix.add_apply, Matrix.one_apply, upper] at hr hp
  norm_num at hr hp
  apply golden_factor_eq_of_second_order_counts n i j
  · exact_mod_cast hr
  · exact_mod_cast hp

/-- The selected represented step-two signature is faithful on legal factors. -/
theorem step_two_matrix_signature_recovers_golden_factor (n i j : ℕ)
    (h : goldenMatrixSignature i n = goldenMatrixSignature j n) :
    goldenFactor n i = goldenFactor n j := by
  rw [golden_matrix_signature_closed_form, golden_matrix_signature_closed_form] at h
  have hr := congrArg (fun s : StepTwoSignature Matrix3 => s.degreeOne 0 1) h
  have hp := congrArg (fun s : StepTwoSignature Matrix3 => s.doubledDegreeTwo 0 2) h
  norm_num [countSignature, upper] at hr hp
  apply golden_factor_eq_of_second_order_counts n i j
  · exact_mod_cast hr
  · omega

/-- A count and one antisymmetric Magnus entry reconstruct the legal factor. -/
theorem count_and_magnus_recovers_golden_factor (n i j : ℕ)
    (hr : goldenWindowTrueCount i n = goldenWindowTrueCount j n)
    (hm : goldenMagnusCenter i n = goldenMagnusCenter j n) :
    goldenFactor n i = goldenFactor n j := by
  rw [golden_magnus_center_formula, golden_magnus_center_formula, hr] at hm
  apply golden_factor_eq_of_second_order_counts n i j hr
  omega

/-- A first-order collision in the legal language is separated by this transport. -/
theorem legal_first_order_collision_separated :
    (goldenMatrixSignature 0 2).degreeOne = (goldenMatrixSignature 1 2).degreeOne ∧
      goldenTransport 0 2 ≠ goldenTransport 1 2 := by
  obtain ⟨hr, hword, _, _⟩ := legal_golden_first_order_collision
  constructor
  · rw [golden_matrix_signature_closed_form, golden_matrix_signature_closed_form]
    simp only [countSignature, hr]
  · intro h
    exact hword (heisenberg_transport_recovers_golden_factor 2 0 1 h)

#print axioms heisenberg_mul
#print axioms golden_transport_closed_form
#print axioms golden_matrix_signature_closed_form
#print axioms golden_magnus_center_formula
#print axioms heisenberg_transport_recovers_golden_factor
#print axioms step_two_matrix_signature_recovers_golden_factor
#print axioms count_and_magnus_recovers_golden_factor
#print axioms legal_first_order_collision_separated

end D5.S3.Observer.Chronology.GoldenFactorHeisenbergReadout
