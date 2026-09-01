/- GID: D5/S3/Quantum/Matrix/GoldenModularStandardPair
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/GoldenModularStandardPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify the finite golden modular standard pair and its two-point spectra. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Real.GoldenRatio

/- Library-search audit trail (2026-09-01):
   * No D5 declaration states the displayed golden matrix spectrum together with
     the conjugate-swap modular relation and Tomita involution.
   * Pinned Mathlib supplies `Real.goldenRatio_sq`, `Real.goldenConj_sq`,
     `Real.inv_goldenRatio`, `Real.log_pow`, and `Real.log_inv`; they are reused below.
   * `Mathlib.Analysis.InnerProductSpace.StandardSubspace` defines standard real
     subspaces, but its TODO explicitly leaves the Tomita conjugation and theorem open.
   * Searches of the other pinned Lean packages found no finite golden modular pair.
-/

namespace D5.S3.Quantum.Matrix.GoldenModularStandardPair

noncomputable section

/-- The displayed Fibonacci matrix. -/
def goldenF : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1]

/-- The positive matrix obtained by squaring `goldenF`. -/
def goldenDeltaMatrix : Matrix (Fin 2) (Fin 2) ℝ := goldenF * goldenF

/-- Point spectrum, which agrees with the ordinary spectrum for the explicit
finite-dimensional real symmetric matrices used below. -/
def matrixPointSpectrum (A : Matrix (Fin 2) (Fin 2) ℝ) : Set ℝ :=
  {lambda | ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ Matrix.mulVec A v = lambda • v}

/-- The expanding eigenvector of the golden matrix and its square. -/
def expandingVector : Fin 2 → ℝ := ![1, Real.goldenRatio]

/-- The contracting eigenvector, written with the golden conjugate. -/
def contractingVector : Fin 2 → ℝ := ![1, Real.goldenConj]

theorem golden_delta_matrix_value :
    goldenDeltaMatrix = !![1, 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [goldenDeltaMatrix, goldenF, Matrix.mul_apply, Fin.sum_univ_two]

private theorem expandingVector_ne_zero : expandingVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [expandingVector] at h0

private theorem contractingVector_ne_zero : contractingVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [contractingVector] at h0

theorem expandingVector_eigen :
    Matrix.mulVec goldenDeltaMatrix expandingVector =
      Real.goldenRatio ^ 2 • expandingVector := by
  rw [golden_delta_matrix_value]
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, expandingVector,
      Real.goldenRatio_sq] <;> ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, expandingVector]
    nlinarith [Real.goldenRatio_sq]

theorem contractingVector_eigen :
    Matrix.mulVec goldenDeltaMatrix contractingVector =
      Real.goldenConj ^ 2 • contractingVector := by
  rw [golden_delta_matrix_value]
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, contractingVector,
      Real.goldenConj_sq] <;> ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, contractingVector]
    nlinarith [Real.goldenConj_sq]

private theorem golden_delta_point_spectrum_conjugate :
    matrixPointSpectrum goldenDeltaMatrix =
      {Real.goldenRatio ^ 2, Real.goldenConj ^ 2} := by
  ext lambda
  constructor
  · rintro ⟨v, hv, heigen⟩
    rw [golden_delta_matrix_value] at heigen
    have h0 := congrFun heigen 0
    have h1 := congrFun heigen 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    have hv0 : v 0 ≠ 0 := by
      intro hv0
      have hv1 : v 1 = 0 := by nlinarith [h0]
      apply hv
      funext i
      fin_cases i
      · exact hv0
      · exact hv1
    have hcharacteristicTimes :
        (-lambda ^ 2 + 3 * lambda - 1) * v 0 = 0 := by
      linear_combination (lambda - 2) * h0 + h1
    have hcharacteristic : lambda ^ 2 - 3 * lambda + 1 = 0 := by
      have hpoly := (mul_eq_zero.mp hcharacteristicTimes).resolve_right hv0
      nlinarith
    have hsum : Real.goldenRatio ^ 2 + Real.goldenConj ^ 2 = 3 := by
      nlinarith [Real.goldenRatio_sq, Real.goldenConj_sq,
        Real.goldenRatio_add_goldenConj]
    have hproduct : Real.goldenRatio ^ 2 * Real.goldenConj ^ 2 = 1 := by
      calc
        Real.goldenRatio ^ 2 * Real.goldenConj ^ 2 =
            (Real.goldenRatio * Real.goldenConj) ^ 2 := by ring
        _ = (-1 : ℝ) ^ 2 := by rw [Real.goldenRatio_mul_goldenConj]
        _ = 1 := by norm_num
    have hfactor :
        (lambda - Real.goldenRatio ^ 2) *
            (lambda - Real.goldenConj ^ 2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hExpanding | hContracting
    · exact Set.mem_insert_iff.mpr (Or.inl (sub_eq_zero.mp hExpanding))
    · exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr (sub_eq_zero.mp hContracting)))
  · intro hlambda
    rcases Set.mem_insert_iff.mp hlambda with rfl | hlambda
    · exact ⟨expandingVector, expandingVector_ne_zero, expandingVector_eigen⟩
    · rw [Set.mem_singleton_iff] at hlambda
      subst lambda
      exact ⟨contractingVector, contractingVector_ne_zero, contractingVector_eigen⟩

theorem golden_delta_point_spectrum :
    matrixPointSpectrum goldenDeltaMatrix =
      {Real.goldenRatio ^ 2, Real.goldenRatio⁻¹ ^ 2} := by
  rw [golden_delta_point_spectrum_conjugate]
  have hinvSquare : Real.goldenRatio⁻¹ ^ 2 = Real.goldenConj ^ 2 := by
    rw [Real.inv_goldenRatio]
    ring
  rw [hinvSquare]

/-- Complex coordinates in the eigenbasis. -/
abbrev GoldenEigenState := Fin 2 → ℂ

/-- The modular operator in its eigenbasis. -/
def goldenDelta (psi : GoldenEigenState) : GoldenEigenState :=
  ![((Real.goldenRatio ^ 2 : ℝ) : ℂ) * psi 0,
    ((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) * psi 1]

/-- The inverse modular operator in the same eigenbasis. -/
def goldenDeltaInv (psi : GoldenEigenState) : GoldenEigenState :=
  ![((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) * psi 0,
    ((Real.goldenRatio ^ 2 : ℝ) : ℂ) * psi 1]

/-- The positive square root of the modular operator. -/
def goldenDeltaSqrt (psi : GoldenEigenState) : GoldenEigenState :=
  ![((Real.goldenRatio : ℝ) : ℂ) * psi 0,
    ((Real.goldenRatio⁻¹ : ℝ) : ℂ) * psi 1]

/-- Swap the two eigendirections and complex-conjugate their coordinates. -/
def goldenJ (psi : GoldenEigenState) : GoldenEigenState :=
  ![starRingEnd ℂ (psi 1), starRingEnd ℂ (psi 0)]

@[simp] theorem goldenJ_apply_zero (psi : GoldenEigenState) :
    goldenJ psi 0 = starRingEnd ℂ (psi 1) := rfl

@[simp] theorem goldenJ_apply_one (psi : GoldenEigenState) :
    goldenJ psi 1 = starRingEnd ℂ (psi 0) := rfl

@[simp] theorem goldenDelta_apply_zero (psi : GoldenEigenState) :
    goldenDelta psi 0 = ((Real.goldenRatio ^ 2 : ℝ) : ℂ) * psi 0 := rfl

@[simp] theorem goldenDelta_apply_one (psi : GoldenEigenState) :
    goldenDelta psi 1 = ((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) * psi 1 := rfl

/-- The squared Euclidean coordinate norm used to state the isometry property. -/
def coordinateEnergy (psi : GoldenEigenState) : ℝ :=
  Complex.normSq (psi 0) + Complex.normSq (psi 1)

/-- The Tomita operator `S = J Delta^(1/2)`. -/
def goldenS (psi : GoldenEigenState) : GoldenEigenState :=
  goldenJ (goldenDeltaSqrt psi)

@[simp] theorem goldenS_apply_zero (psi : GoldenEigenState) :
    goldenS psi 0 = starRingEnd ℂ
      (((Real.goldenRatio⁻¹ : ℝ) : ℂ) * psi 1) := rfl

@[simp] theorem goldenS_apply_one (psi : GoldenEigenState) :
    goldenS psi 1 = starRingEnd ℂ
      (((Real.goldenRatio : ℝ) : ℂ) * psi 0) := rfl

/-- The fixed real subspace, represented exactly as the fixed set of `S`. -/
def goldenFixedRealSpace : Set GoldenEigenState := {psi | goldenS psi = psi}

theorem goldenJ_antilinear_isometry :
    (∀ psi, goldenJ (goldenJ psi) = psi) ∧
      (∀ a psi, goldenJ (a • psi) = (starRingEnd ℂ a) • goldenJ psi) ∧
      (∀ psi, coordinateEnergy (goldenJ psi) = coordinateEnergy psi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro psi
    ext i
    fin_cases i <;> simp [goldenJ]
  · intro a psi
    ext i
    fin_cases i <;> simp [goldenJ, map_mul]
  · intro psi
    simp [coordinateEnergy, goldenJ, Complex.normSq_conj, add_comm]

theorem golden_delta_positive_weights :
    0 < Real.goldenRatio ^ 2 ∧ 0 < Real.goldenRatio⁻¹ ^ 2 := by
  exact ⟨sq_pos_of_pos Real.goldenRatio_pos,
    sq_pos_of_pos (inv_pos.mpr Real.goldenRatio_pos)⟩

private theorem golden_mul_inv :
    Real.goldenRatio * Real.goldenRatio⁻¹ = 1 := by
  exact mul_inv_cancel₀ Real.goldenRatio_ne_zero

private theorem golden_inv_mul :
    Real.goldenRatio⁻¹ * Real.goldenRatio = 1 := by
  rw [mul_comm, golden_mul_inv]

private theorem golden_sq_mul_inv_sq :
    Real.goldenRatio ^ 2 * Real.goldenRatio⁻¹ ^ 2 = 1 := by
  rw [← mul_pow, golden_mul_inv]
  norm_num

private theorem golden_inv_sq_mul_sq :
    Real.goldenRatio⁻¹ ^ 2 * Real.goldenRatio ^ 2 = 1 := by
  rw [mul_comm, golden_sq_mul_inv_sq]

theorem golden_delta_inverse_certificate (psi : GoldenEigenState) :
    goldenDelta (goldenDeltaInv psi) = psi ∧
      goldenDeltaInv (goldenDelta psi) = psi := by
  constructor <;> ext i <;> fin_cases i
  · change ((Real.goldenRatio ^ 2 : ℝ) : ℂ) *
      (((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) * psi 0) = psi 0
    rw [← mul_assoc, ← Complex.ofReal_mul, golden_sq_mul_inv_sq]
    simp
  · change ((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) *
      (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * psi 1) = psi 1
    rw [← mul_assoc, ← Complex.ofReal_mul, golden_inv_sq_mul_sq]
    simp
  · change ((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) *
      (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * psi 0) = psi 0
    rw [← mul_assoc, ← Complex.ofReal_mul, golden_inv_sq_mul_sq]
    simp
  · change ((Real.goldenRatio ^ 2 : ℝ) : ℂ) *
      (((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) * psi 1) = psi 1
    rw [← mul_assoc, ← Complex.ofReal_mul, golden_sq_mul_inv_sq]
    simp

theorem golden_delta_sqrt_certificate (psi : GoldenEigenState) :
    goldenDeltaSqrt (goldenDeltaSqrt psi) = goldenDelta psi := by
  ext i
  fin_cases i
  · change ((Real.goldenRatio : ℝ) : ℂ) *
      (((Real.goldenRatio : ℝ) : ℂ) * psi 0) =
        ((Real.goldenRatio ^ 2 : ℝ) : ℂ) * psi 0
    push_cast
    ring
  · change ((Real.goldenRatio⁻¹ : ℝ) : ℂ) *
      (((Real.goldenRatio⁻¹ : ℝ) : ℂ) * psi 1) =
        ((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) * psi 1
    push_cast
    ring

theorem goldenJ_delta_goldenJ (psi : GoldenEigenState) :
    goldenJ (goldenDelta (goldenJ psi)) = goldenDeltaInv psi := by
  ext i
  fin_cases i
  · change starRingEnd ℂ
      (((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (psi 0)) =
        ((Real.goldenRatio⁻¹ ^ 2 : ℝ) : ℂ) * psi 0
    rw [map_mul, Complex.conj_ofReal]
    simp
  · change starRingEnd ℂ
      (((Real.goldenRatio ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (psi 1)) =
        ((Real.goldenRatio ^ 2 : ℝ) : ℂ) * psi 1
    rw [map_mul, Complex.conj_ofReal]
    simp

theorem goldenS_involution (psi : GoldenEigenState) :
    goldenS (goldenS psi) = psi := by
  have h0 : goldenS (goldenS psi) 0 = psi 0 := by
    rw [goldenS_apply_zero, goldenS_apply_one, map_mul, Complex.conj_ofReal,
      Complex.conj_conj]
    rw [← mul_assoc, ← Complex.ofReal_mul, golden_inv_mul]
    simp
  have h1 : goldenS (goldenS psi) 1 = psi 1 := by
    rw [goldenS_apply_one, goldenS_apply_zero, map_mul, Complex.conj_ofReal,
      Complex.conj_conj]
    rw [← mul_assoc, ← Complex.ofReal_mul, golden_mul_inv]
    simp
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem golden_fixed_real_space_parameterization (psi : GoldenEigenState) :
    psi ∈ goldenFixedRealSpace ↔
      psi 1 = ((Real.goldenRatio : ℝ) : ℂ) * starRingEnd ℂ (psi 0) := by
  constructor
  · intro hpsi
    have h1 := congrFun hpsi 1
    rw [goldenS_apply_one, map_mul, Complex.conj_ofReal] at h1
    exact h1.symm
  · intro hpsi
    change goldenS psi = psi
    have hconj := congrArg (starRingEnd ℂ) hpsi
    rw [map_mul, Complex.conj_ofReal, Complex.conj_conj] at hconj
    have h0 : goldenS psi 0 = psi 0 := by
      rw [goldenS_apply_zero, map_mul, Complex.conj_ofReal, hconj,
        ← mul_assoc, ← Complex.ofReal_mul, golden_inv_mul]
      simp
    have h1 : goldenS psi 1 = psi 1 := by
      rw [goldenS_apply_one, map_mul, Complex.conj_ofReal]
      exact hpsi.symm
    ext i
    fin_cases i
    · exact h0
    · exact h1

/-- The coordinatewise logarithm of the positive diagonal modular operator. -/
def goldenDeltaLogMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.log (Real.goldenRatio ^ 2), 0;
    0, Real.log (Real.goldenRatio⁻¹ ^ 2)]

/-- The modular Hamiltonian displayed in its eigenbasis. -/
def goldenHamiltonianMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * Real.log Real.goldenRatio, 0;
    0, -2 * Real.log Real.goldenRatio]

theorem golden_delta_log_eq_hamiltonian :
    goldenDeltaLogMatrix = goldenHamiltonianMatrix := by
  have hlogSquare :
      Real.log (Real.goldenRatio ^ 2) = 2 * Real.log Real.goldenRatio := by
    rw [Real.log_pow]
    norm_num
  have hlogInvSquare :
      Real.log (Real.goldenRatio⁻¹ ^ 2) = -2 * Real.log Real.goldenRatio := by
    rw [Real.log_pow, Real.log_inv]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · exact hlogSquare
  · rfl
  · rfl
  · exact hlogInvSquare

private theorem diagonal_point_spectrum (a b : ℝ) :
    matrixPointSpectrum !![a, 0; 0, b] = {a, b} := by
  ext lambda
  constructor
  · rintro ⟨v, hv, heigen⟩
    have h0 := congrFun heigen 0
    have h1 := congrFun heigen 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1
        apply hv
        funext i
        fin_cases i
        · exact hv0
        · exact hv1
      have hb : b = lambda := h1.resolve_right hv1
      exact Set.mem_insert_iff.mpr
        (Or.inr (Set.mem_singleton_iff.mpr hb.symm))
    · have ha : a = lambda := h0.resolve_right hv0
      exact Set.mem_insert_iff.mpr (Or.inl ha.symm)
  · intro hlambda
    rcases Set.mem_insert_iff.mp hlambda with rfl | hlambda
    · refine ⟨![1, 0], ?_, ?_⟩
      · intro h
        have h0 := congrFun h 0
        norm_num at h0
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · rw [Set.mem_singleton_iff] at hlambda
      subst lambda
      refine ⟨![0, 1], ?_, ?_⟩
      · intro h
        have h1 := congrFun h 1
        norm_num at h1
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem golden_hamiltonian_point_spectrum :
    matrixPointSpectrum goldenHamiltonianMatrix =
      {2 * Real.log Real.goldenRatio, -2 * Real.log Real.goldenRatio} := by
  exact diagonal_point_spectrum _ _

/-- The complete finite-dimensional Tomita certificate attached to the displayed
golden matrix. All inverse, square-root, and logarithm inputs are positive. -/
theorem golden_modular_standard_pair :
    goldenDeltaMatrix = !![1, 1; 1, 2] ∧
      matrixPointSpectrum goldenDeltaMatrix =
        {Real.goldenRatio ^ 2, Real.goldenRatio⁻¹ ^ 2} ∧
      (∀ psi, goldenJ (goldenJ psi) = psi) ∧
      (∀ a psi, goldenJ (a • psi) = (starRingEnd ℂ a) • goldenJ psi) ∧
      (∀ psi, coordinateEnergy (goldenJ psi) = coordinateEnergy psi) ∧
      (0 < Real.goldenRatio ^ 2 ∧ 0 < Real.goldenRatio⁻¹ ^ 2) ∧
      (∀ psi, goldenJ (goldenDelta (goldenJ psi)) = goldenDeltaInv psi) ∧
      (∀ psi, goldenDelta (goldenDeltaInv psi) = psi ∧
        goldenDeltaInv (goldenDelta psi) = psi) ∧
      (∀ psi, goldenDeltaSqrt (goldenDeltaSqrt psi) = goldenDelta psi) ∧
      (∀ psi, goldenS (goldenS psi) = psi) ∧
      (∀ psi, psi ∈ goldenFixedRealSpace ↔
        psi 1 = ((Real.goldenRatio : ℝ) : ℂ) * starRingEnd ℂ (psi 0)) ∧
      goldenDeltaLogMatrix = goldenHamiltonianMatrix ∧
      matrixPointSpectrum goldenHamiltonianMatrix =
        {2 * Real.log Real.goldenRatio, -2 * Real.log Real.goldenRatio} := by
  exact ⟨golden_delta_matrix_value, golden_delta_point_spectrum,
    goldenJ_antilinear_isometry.1, goldenJ_antilinear_isometry.2.1,
    goldenJ_antilinear_isometry.2.2, golden_delta_positive_weights,
    goldenJ_delta_goldenJ, golden_delta_inverse_certificate,
    golden_delta_sqrt_certificate, goldenS_involution,
    golden_fixed_real_space_parameterization, golden_delta_log_eq_hamiltonian,
    golden_hamiltonian_point_spectrum⟩

/-- Positive-side numerical witness: the displayed seed has the displayed square,
and the real vector `(1, phi)` is fixed by `S`. -/
example :
    goldenF * goldenF = !![1, 1; 1, 2] ∧
      goldenS ![(1 : ℂ), ((Real.goldenRatio : ℝ) : ℂ)] =
        ![(1 : ℂ), ((Real.goldenRatio : ℝ) : ℂ)] := by
  constructor
  · exact golden_delta_matrix_value
  · change ![(1 : ℂ), ((Real.goldenRatio : ℝ) : ℂ)] ∈
      goldenFixedRealSpace
    apply (golden_fixed_real_space_parameterization _).2
    simp

/-- Negative-side numerical witness: the zero seed is not the displayed Fibonacci
matrix and its square is not the displayed positive matrix. -/
example :
    (0 : Matrix (Fin 2) (Fin 2) ℝ) ≠ goldenF ∧
      (0 : Matrix (Fin 2) (Fin 2) ℝ) * 0 ≠ !![1, 1; 1, 2] := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    norm_num [goldenF] at h01
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    norm_num at h00

#print axioms golden_modular_standard_pair

end

end D5.S3.Quantum.Matrix.GoldenModularStandardPair
