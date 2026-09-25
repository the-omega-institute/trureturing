/- GID: D5/S3/Observer/Linear/OscillatorSensorJets
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/OscillatorSensorJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact derivative tables and leading polynomial Gramians for the two equal-gain oscillator sensors. -/

import Mathlib

/-!
All matrices below are explicit rational matrices. Derivative rows are actually
computed as C B^k/k!, rather than supplied as an observability certificate.
The leading polynomial Gramians use integral_0^1 s^(i+j) ds = 1/(i+j+1).
The rational identities below do NOT establish that the exponential-trajectory
Gramian has this asymptotic, nor do they establish a Gaussian Bayes-risk limit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.OscillatorSensorJets

open scoped Matrix BigOperators

/-- Frequencies one and two, in energy-normalized position/momentum coordinates. -/
def generator : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 2; 0, 0, -2, 0]

def sumSensor : Matrix (Fin 1) (Fin 4) ℚ := !![1, 0, 1, 0]
def separateSensor : Matrix (Fin 2) (Fin 4) ℚ := !![1, 0, 0, 0; 0, 0, 1, 0]

def sumJets : Matrix (Fin 4) (Fin 4) ℚ := fun k j =>
  (sumSensor * generator ^ k.val) 0 j / (Nat.factorial k.val : ℚ)

def sumJetTable : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 1, 0; 0, 1, 0, 2; -1/2, 0, -2, 0; 0, -1/6, 0, -4/3]

/-- The full derivative table is obtained from the actual system and sensor. -/
theorem sum_jet_table : sumJets = sumJetTable := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sumJets, sumJetTable, sumSensor, generator, pow_succ,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

/-- Independent position sensors see both momentum coordinates at the next order. -/
theorem separate_first_derivative :
    separateSensor * generator = !![0, 1, 0, 0; 0, 0, 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [separateSensor, generator, Matrix.mul_apply, Fin.sum_univ_succ]

theorem equal_initial_gain :
    (sumSensor.transpose * sumSensor).trace = 2 ∧
      (separateSensor.transpose * separateSensor).trace = 2 := by
  constructor <;> norm_num [sumSensor, separateSensor, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]

/-- Explicit algebraic reconstruction from the four normalized sum-sensor jets. -/
def inverseSumJets : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4/3, 0, 2/3, 0; 0, 4/3, 0, 2;
     -1/3, 0, -2/3, 0; 0, -1/6, 0, -1]

theorem sum_jets_inverse : inverseSumJets * sumJets = 1 := by
  rw [sum_jet_table]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [inverseSumJets, sumJetTable, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ]

/-- No direction escapes all four derivative orders of the sum sensor. -/
theorem sum_jets_observable (x : Fin 4 → ℚ) : sumJets.mulVec x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun v => inverseSumJets.mulVec v) h
    simpa only [Matrix.mulVec_mulVec, sum_jets_inverse, Matrix.one_mulVec,
      Matrix.mulVec_zero] using hh
  · intro h
    rw [h, Matrix.mulVec_zero]

/-- The scalar monomial moment matrix of degrees zero through three. -/
def hilbertFour : Matrix (Fin 4) (Fin 4) ℚ := fun i j =>
  1 / ((i.val + j.val + 1 : ℕ) : ℚ)

def hilbertFourTable : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 1/2, 1/3, 1/4; 1/2, 1/3, 1/4, 1/5;
     1/3, 1/4, 1/5, 1/6; 1/4, 1/5, 1/6, 1/7]

theorem hilbert_four_table : hilbertFour = hilbertFourTable := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hilbertFour, hilbertFourTable]

/-- The exact leading polynomial Gramian before small-time scaling. -/
def sumPolynomialGram : Matrix (Fin 4) (Fin 4) ℚ :=
  sumJets.transpose * hilbertFour * sumJets

/-- Polynomial integral Gramian for the independent frequency-one/two modes. -/
def separatePolynomialGram : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 1/2, 0, 0; 1/2, 1/3, 0, 0;
     0, 0, 1, 1; 0, 0, 1, 4/3]

/-- All constant determinant identities are exact rational arithmetic. -/
theorem sum_jet_determinant : sumJets.det = 3 / 2 := by
  rw [sum_jet_table]
  norm_num [sumJetTable, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Matrix.det_fin_two]

theorem hilbert_four_determinant : hilbertFour.det = 1 / 6048000 := by
  rw [hilbert_four_table]
  norm_num [hilbertFourTable, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Matrix.det_fin_two]

theorem sum_polynomial_gram_determinant : sumPolynomialGram.det = 1 / 2688000 := by
  rw [sumPolynomialGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    sum_jet_determinant, hilbert_four_determinant]
  norm_num

theorem separate_polynomial_gram_determinant :
    separatePolynomialGram.det = 1 / 36 := by
  norm_num [separatePolynomialGram, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix, Matrix.det_fin_two]

/-- The determinant scaling is proved for the polynomial model itself.
It is not an assertion about the exponential trajectory without a remainder proof. -/
def sumScaling (T : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.diagonal ![1, T, T^2, T^3]

def scaledSumPolynomialGram (T : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  T • (sumJets.transpose * sumScaling T * hilbertFour * sumScaling T * sumJets)

theorem scaled_sum_polynomial_determinant (T : ℚ) :
    (scaledSumPolynomialGram T).det = T ^ 16 / 2688000 := by
  have hd : (sumScaling T).det = T^6 := by
    simp [sumScaling, Matrix.det_diagonal, Fin.prod_univ_succ]
    ring
  rw [scaledSumPolynomialGram, Matrix.det_smul]
  simp only [Fintype.card_fin, Matrix.det_mul, Matrix.det_transpose,
    sum_jet_determinant, hilbert_four_determinant, hd]
  ring

#print axioms sum_jet_table
#print axioms equal_initial_gain
#print axioms sum_jets_observable
#print axioms sum_polynomial_gram_determinant
#print axioms separate_polynomial_gram_determinant
#print axioms scaled_sum_polynomial_determinant

end D5.S3.Observer.Linear.OscillatorSensorJets
