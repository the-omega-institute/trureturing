/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim; result=D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.result; claim=D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim
   digest: A separable qubit-ququart state violates the correlation-minor bound without FNF. -/

import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.CotfasDVGS
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

/-! The operator-norm conjecture following Theorem 3 of Peled, Te'eni, Carmi
and Cohen, arXiv:2005.12079v2. Hermitian bases have trace-product normalization one. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (pauliMatrix)

namespace D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation

/-- A complete Hilbert–Schmidt orthonormal family of Hermitian matrices. -/
def IsHermBasis {n m : ℕ} (a : Fin m → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i, (a i).IsHermitian) ∧ m = n ^ 2 ∧
    ∀ i j, (a i * a j).trace = if i = j then 1 else 0

/-- Real correlation coefficients in local Hermitian bases. -/
def corr {da db ma mb : ℕ}
    (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin ma → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin mb → Matrix (Fin db) (Fin db) ℂ) : Matrix (Fin ma) (Fin mb) ℝ :=
  fun i j => (ρ * (a i ⊗ₖ b j)).trace.re

/-- The compound matrix, with each minor in increasing row and column order. -/
def compound {m n : ℕ} (h : ℕ) (c : Matrix (Fin m) (Fin n) ℝ) :
    Matrix {r : Finset (Fin m) // r.card = h} {s : Finset (Fin n) // s.card = h} ℝ :=
  fun r s => (c.submatrix (r.val.orderEmbOfFin r.property)
    (s.val.orderEmbOfFin s.property)).det

/-- The Schatten infinity norm of the compound matrix. -/
def cmnInf {m n : ℕ} (h : ℕ) (c : Matrix (Fin m) (Fin n) ℝ) : ℝ := by
  classical
  exact ‖compound h c‖

/-- The right hand side of Theorem 3, with real exponent `(h-1)/2`. -/
def bound (da db h : ℕ) : ℝ :=
  1 / Real.sqrt ((max da db : ℝ) * (min da db : ℝ)) *
    (((max da db : ℝ) - 1) / ((max da db : ℝ) * ((h : ℝ) - 1)) *
      (((min da db : ℝ) - 1) / ((min da db : ℝ) * ((h : ℝ) - 1)))) ^
      (((h : ℝ) - 1) / 2)

/-- The proposed bound for all separable states, without filter normal form. -/
def claim : Prop := ∀ da db h : ℕ, 2 ≤ da → 2 ≤ db →
  max da db * min da db ≤ h ^ 2 → h ≤ (min da db) ^ 2 →
  ∀ (ρ : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ), IsSeparable ρ →
  ∀ (a : Fin (da ^ 2) → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin (db ^ 2) → Matrix (Fin db) (Fin db) ℂ),
    IsHermBasis a → IsHermBasis b → cmnInf h (corr ρ a b) ≤ bound da db h

private def projectors : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 0], !![1/5, 2/5; 2/5, 4/5], !![1/5, -2/5; -2/5, 4/5]]

private def rho : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  (333/1000 : ℂ) • (∑ j : Fin 3, projectors j ⊗ₖ single j.castSucc j.castSucc 1) +
    (1/8000 : ℂ) • 1

private def alice : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => ((Real.sqrt 2 : ℂ)⁻¹) •
    (![pauliMatrix .I, pauliMatrix .Z, pauliMatrix .X, pauliMatrix .Y] i)

private def symUnit (a b : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (single a b 1 + single b a 1)

private def skewUnit (a b : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (-Complex.I • single a b 1 + Complex.I • single b a 1)

private def bob : Fin 16 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![single 0 0 1, single 1 1 1, single 2 2 1, single 3 3 1,
    symUnit 0 1, symUnit 0 2, symUnit 0 3, symUnit 1 2, symUnit 1 3, symUnit 2 3,
    skewUnit 0 1, skewUnit 0 2, skewUnit 0 3, skewUnit 1 2, skewUnit 1 3, skewUnit 2 3]

private def coefficients : Matrix (Fin 4) (Fin 16) ℝ := fun i j =>
  if hj : j.val < 4 then
    (!![1333/4000, 1333/4000, 1333/4000, 1/4000;
        333/1000, -999/5000, -999/5000, 0;
        0, 333/1250, -333/1250, 0;
        0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℝ) i ⟨j.val, hj⟩ /
      Real.sqrt 2
  else 0

private def selectedRow : {r : Finset (Fin 4) // r.card = 3} :=
  ⟨{0, 1, 2}, by decide⟩

private def selectedCols (k : Fin 4) : {s : Finset (Fin 16) // s.card = 3} :=
  ⟨![{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}] k, by fin_cases k <;> decide⟩

private lemma projectors_density (j : Fin 3) : IsDensity (projectors j) := by
  rw [projectors]
  fin_cases j
  · convert D5.S3.Quantum.CotfasDVGS.normalization_isDensity
      (vecMulVec ![(1 : ℂ), 0] (star ![(1 : ℂ), 0]))
      (posSemidef_vecMulVec_self_star _) (by
        norm_num [Matrix.trace, Matrix.vecMulVec, Fin.sum_univ_two,
          Pi.star_apply, Complex.star_def, map_ofNat]) using 1
    ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [Matrix.vecMulVec, Matrix.trace, Fin.sum_univ_two,
        Pi.star_apply, Complex.real_smul, Complex.star_def, map_ofNat]
  · convert D5.S3.Quantum.CotfasDVGS.normalization_isDensity
      (vecMulVec ![(1 : ℂ), 2] (star ![(1 : ℂ), 2]))
      (posSemidef_vecMulVec_self_star _) (by
        norm_num [Matrix.trace, Matrix.vecMulVec, Fin.sum_univ_two,
          Pi.star_apply, Complex.star_def, map_ofNat]) using 1
    ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [Matrix.vecMulVec, Matrix.trace, Fin.sum_univ_two,
        Pi.star_apply, Complex.real_smul, Complex.star_def, map_ofNat]
  · convert D5.S3.Quantum.CotfasDVGS.normalization_isDensity
      (vecMulVec ![(1 : ℂ), -2] (star ![(1 : ℂ), -2]))
      (posSemidef_vecMulVec_self_star _) (by
        norm_num [Matrix.trace, Matrix.vecMulVec, Fin.sum_univ_two,
          Pi.star_apply, Complex.star_def, map_ofNat]) using 1
    ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [Matrix.vecMulVec, Matrix.trace, Fin.sum_univ_two,
        Pi.star_apply, Complex.real_smul, Complex.star_def, map_ofNat]

private lemma rho_separable : IsSeparable rho := by
  classical
  have hflag (j : Fin 4) : IsDensity (single j j (1 : ℂ)) := by
    simpa only [Matrix.trace_single_eq_same, inv_one, one_smul] using
      D5.S3.Quantum.CotfasDVGS.normalization_isDensity (single j j (1 : ℂ))
        (by simpa only [← Pi.single_star, star_one,
            ← Matrix.single_eq_single_vecMulVec_single] using
            posSemidef_vecMulVec_self_star (Pi.single j (1 : ℂ))) (by simp)
  have hmixed (n : ℕ) [NeZero n] : IsDensity ((1 / n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    simpa [Matrix.trace_one] using D5.S3.Quantum.CotfasDVGS.normalization_isDensity
      (1 : Matrix (Fin n) (Fin n) ℂ) PosSemidef.one (by simp [NeZero.ne n])
  refine ⟨4, ![333/1000, 333/1000, 333/1000, 1/1000],
    ![projectors 0, projectors 1, projectors 2, (1/2 : ℂ) • 1],
    ![single 0 0 1, single 1 1 1, single 2 2 1, (1/4 : ℂ) • 1], ?_, ?_, ?_, ?_⟩
  · intro t; fin_cases t <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · intro t
    fin_cases t
    · exact ⟨projectors_density 0, hflag 0⟩
    · exact ⟨projectors_density 1, hflag 1⟩
    · exact ⟨projectors_density 2, hflag 2⟩
    · exact ⟨hmixed 2, hmixed 4⟩
  · norm_num [rho, Fin.sum_univ_succ, smul_kronecker, kronecker_smul,
      one_kronecker_one, smul_smul, smul_add]
    module

private lemma alice_basis : IsHermBasis alice := by
  refine ⟨?_, by decide, ?_⟩
  · intro i
    rw [alice]
    change (alice i)ᴴ = alice i
    fin_cases i <;>
      simp [alice, Matrix.conjTranspose_smul,
        D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [alice, Matrix.trace_smul,
        D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_trace_pair] <;>
      ring_nf <;>
      norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_0 (j : Fin 16) :
    (bob 0 * bob j).trace = if (0 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.mul_add]

private lemma bob_pairing_1 (j : Fin 16) :
    (bob 1 * bob j).trace = if (1 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.mul_add]

private lemma bob_pairing_2 (j : Fin 16) :
    (bob 2 * bob j).trace = if (2 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.mul_add]

private lemma bob_pairing_3 (j : Fin 16) :
    (bob 3 * bob j).trace = if (3 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.mul_add]

private lemma bob_pairing_4 (j : Fin 16) :
    (bob 4 * bob j).trace = if (4 : Fin 16) = j then 1 else 0 := by
  rw [bob, symUnit]
  fin_cases j <;>
    simp [symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_5 (j : Fin 16) :
    (bob 5 * bob j).trace = if (5 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_6 (j : Fin 16) :
    (bob 6 * bob j).trace = if (6 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_7 (j : Fin 16) :
    (bob 7 * bob j).trace = if (7 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_8 (j : Fin 16) :
    (bob 8 * bob j).trace = if (8 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_9 (j : Fin 16) :
    (bob 9 * bob j).trace = if (9 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_10 (j : Fin 16) :
    (bob 10 * bob j).trace = if (10 : Fin 16) = j then 1 else 0 := by
  rw [bob, skewUnit]
  fin_cases j <;>
    simp [symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_11 (j : Fin 16) :
    (bob 11 * bob j).trace = if (11 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_12 (j : Fin 16) :
    (bob 12 * bob j).trace = if (12 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_13 (j : Fin 16) :
    (bob 13 * bob j).trace = if (13 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_14 (j : Fin 16) :
    (bob 14 * bob j).trace = if (14 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_pairing_15 (j : Fin 16) :
    (bob 15 * bob j).trace = if (15 : Fin 16) = j then 1 else 0 := by
  fin_cases j <;>
    simp [bob, symUnit, skewUnit, Matrix.add_mul, Matrix.mul_add,
      Matrix.trace_add]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma bob_basis : IsHermBasis bob := by
  rw [bob]
  refine ⟨?_, by decide, ?_⟩
  · intro i
    change (bob i)ᴴ = bob i
    fin_cases i <;> simp [bob, symUnit, skewUnit,
      Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.single_neg, add_comm]
  · intro i j
    fin_cases i
    · exact bob_pairing_0 j
    · exact bob_pairing_1 j
    · exact bob_pairing_2 j
    · exact bob_pairing_3 j
    · exact bob_pairing_4 j
    · exact bob_pairing_5 j
    · exact bob_pairing_6 j
    · exact bob_pairing_7 j
    · exact bob_pairing_8 j
    · exact bob_pairing_9 j
    · exact bob_pairing_10 j
    · exact bob_pairing_11 j
    · exact bob_pairing_12 j
    · exact bob_pairing_13 j
    · exact bob_pairing_14 j
    · exact bob_pairing_15 j

private lemma correlation_row_0 (j : Fin 16) :
    corr rho alice bob 0 j = coefficients 0 j := by
  rw [corr, rho]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_kronecker, Matrix.one_mul]
  fin_cases j <;>
    norm_num [alice, bob, projectors, symUnit, skewUnit, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, coefficients,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul,
      Matrix.trace_single_eq_same, Matrix.trace_single_eq_of_ne, Matrix.single_apply,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, ← Complex.ofReal_inv] <;> ring

private lemma correlation_row_1 (j : Fin 16) :
    corr rho alice bob 1 j = coefficients 1 j := by
  rw [corr, rho]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_kronecker, Matrix.one_mul]
  fin_cases j <;>
    norm_num [alice, bob, projectors, symUnit, skewUnit, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, coefficients,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul,
      Matrix.trace_single_eq_same, Matrix.trace_single_eq_of_ne, Matrix.single_apply,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, ← Complex.ofReal_inv] <;> ring

private lemma correlation_row_2 (j : Fin 16) :
    corr rho alice bob 2 j = coefficients 2 j := by
  rw [corr, rho]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_kronecker, Matrix.one_mul]
  fin_cases j <;>
    norm_num [alice, bob, projectors, symUnit, skewUnit, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, coefficients,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul,
      Matrix.trace_single_eq_same, Matrix.trace_single_eq_of_ne, Matrix.single_apply,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, ← Complex.ofReal_inv] <;> ring

private lemma correlation_row_3 (j : Fin 16) :
    corr rho alice bob 3 j = coefficients 3 j := by
  rw [corr, rho]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_kronecker, Matrix.one_mul]
  fin_cases j <;>
    norm_num [alice, bob, projectors, symUnit, skewUnit, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, coefficients,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul,
      Matrix.trace_single_eq_same, Matrix.trace_single_eq_of_ne, Matrix.single_apply,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, ← Complex.ofReal_inv]

private lemma correlation_eq : corr rho alice bob = coefficients := by
  ext i j
  rw [coefficients]
  fin_cases i
  · exact correlation_row_0 j
  · exact correlation_row_1 j
  · exact correlation_row_2 j
  · exact correlation_row_3 j

private lemma selectedCols_injective : Function.Injective selectedCols := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert hij; decide)

private lemma minor_value (k : Fin 4) :
    compound 3 coefficients selectedRow (selectedCols k) =
      (![147815037/1562500000, 110889/5000000000, -110889/5000000000,
        332667/12500000000] : Fin 4 → ℝ) k / Real.sqrt 2 ^ 3 := by
  have hr (i : Fin 3) : selectedRow.val.orderEmbOfFin selectedRow.property i =
      (![0, 1, 2] : Fin 3 → Fin 4) i := by
    exact congrFun (Finset.orderEmbOfFin_unique selectedRow.property
      (f := (![0, 1, 2] : Fin 3 → Fin 4)) (by decide) (by decide)).symm i
  have hc (k : Fin 4) (i : Fin 3) :
      (selectedCols k).val.orderEmbOfFin (selectedCols k).property i =
      (!![0, 1, 2; 0, 1, 3; 0, 2, 3; 1, 2, 3] : Matrix (Fin 4) (Fin 3) (Fin 16)) k i := by
    exact congrFun (Finset.orderEmbOfFin_unique (selectedCols k).property
      (f := (!![0, 1, 2; 0, 1, 3; 0, 2, 3; 1, 2, 3] : Matrix (Fin 4) (Fin 3) (Fin 16)) k)
      (by fin_cases k <;> decide) (by fin_cases k <;> decide)).symm i
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [compound]
  fin_cases k <;>
    simp only [Matrix.det_fin_three, Matrix.submatrix_apply, hr, hc] <;>
    norm_num [coefficients] <;> field_simp <;> ring

private lemma minor_energy :
    (∑ k : Fin 4, (compound 3 coefficients selectedRow (selectedCols k)) ^ 2) =
      559341805929555807 / 500000000000000000000 := by
  have h6 : Real.sqrt 2 ^ 6 = 8 := by
    calc
      Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := pow_mul _ 2 3
      _ = 8 := by norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [minor_value, div_pow, ← pow_mul]
  norm_num [Fin.sum_univ_succ, h6]

private lemma row_lower {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    [DecidableEq n] (c : Matrix m n ℝ) (r : m) (s : t → n)
    (hs : Function.Injective s) : (∑ k, c r (s k) ^ 2) ≤ ‖c‖ ^ 2 := by
  classical
  let x : EuclideanSpace ℝ m := EuclideanSpace.single r 1
  let y : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm (cᴴ *ᵥ x)
  have hx : ‖x‖ = 1 := by simp [x, EuclideanSpace.single, PiLp.norm_single]
  have hy : ‖y‖ ^ 2 = ∑ j, c r j ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [y, x, EuclideanSpace.single]
  have he := Matrix.l2_opNorm_mulVec cᴴ x
  rw [Matrix.l2_opNorm_conjTranspose, hx, mul_one] at he
  have hsquare : (∑ j, c r j ^ 2) ≤ ‖c‖ ^ 2 := by
    rw [← hy]
    exact (sq_le_sq₀ (norm_nonneg y) (norm_nonneg c)).mpr he
  refine le_trans ?_ hsquare
  calc
    (∑ k, c r (s k) ^ 2) = ∑ j ∈ Finset.univ.image s, c r j ^ 2 := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hs hab
    _ ≤ ∑ j, c r j ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

private lemma witness_lower :
    559341805929555807 / 500000000000000000000 ≤ cmnInf 3 (corr rho alice bob) ^ 2 := by
  classical
  rw [correlation_eq, cmnInf, ← minor_energy]
  exact row_lower (compound 3 coefficients) selectedRow selectedCols selectedCols_injective

private lemma bound_value : bound 2 4 3 = 3 / (64 * Real.sqrt 2) := by
  rw [bound]
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  norm_num [h8]
  ring

private lemma numerical_gap :
    (3 / (64 * Real.sqrt 2)) ^ 2 <
      (559341805929555807 / 500000000000000000000 : ℝ) := by
  norm_num [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The separable qubit-ququart example refutes the conjecture without FNF. -/
theorem result : ¬ claim := by
  intro hc
  have hu := hc 2 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rho rho_separable alice bob alice_basis bob_basis
  rw [bound_value] at hu
  have hn : 0 ≤ cmnInf 3 (corr rho alice bob) := by unfold cmnInf; positivity
  have hb : 0 ≤ 3 / (64 * Real.sqrt 2) := by positivity
  have hsq := (sq_le_sq₀ hn hb).mpr hu
  linarith [witness_lower, numerical_gap]

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
