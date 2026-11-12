/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim; result=D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.result; claim=D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim
   digest: A separable qubit-ququart state violates the correlation-minor bound without FNF. -/

import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Schatten.Partition
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.CotfasDVGS
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation

/-! The operator-norm conjecture following Theorem 3 of Peled, Te'eni, Carmi
and Cohen, arXiv:2005.12079v2. Hermitian bases have trace-product normalization one. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft partialTraceRight)
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

/-- The finite-p norm uses the existing actual rectangular complex Schatten functional.
The increasing real compound is complexified entrywise; infinity remains `cmnInf`. -/
def cmnP {m n : ℕ} (p : ℝ) (h : ℕ) (c : Matrix (Fin m) (Fin n) ℝ) : ℝ := by
  classical
  exact D5.S3.Quantum.Schatten.Partition.rectangularNorm
    ((compound h c).map Complex.ofReal) p

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

/-- The actual rational qubit--ququart family, including its white-noise term. -/
def noisyRho (t : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ :=
  (((1 - t) / 3 : ℝ) : ℂ) •
    (∑ j : Fin 3, projectors j ⊗ₖ single j.castSucc j.castSucc 1) +
    ((t / 8 : ℝ) : ℂ) • 1

private def rho : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ := noisyRho (1 / 1000)

def alice : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => ((Real.sqrt 2 : ℂ)⁻¹) •
    (![pauliMatrix .I, pauliMatrix .Z, pauliMatrix .X, pauliMatrix .Y] i)

private def symUnit (a b : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (single a b 1 + single b a 1)

private def skewUnit (a b : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (-Complex.I • single a b 1 + Complex.I • single b a 1)

def bob : Fin 16 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![single 0 0 1, single 1 1 1, single 2 2 1, single 3 3 1,
    symUnit 0 1, symUnit 0 2, symUnit 0 3, symUnit 1 2, symUnit 1 3, symUnit 2 3,
    skewUnit 0 1, skewUnit 0 2, skewUnit 0 3, skewUnit 1 2, skewUnit 1 3, skewUnit 2 3]

/-- The exact correlation coefficients in the normalized IZX Y / flag bases. -/
def noisyCoefficients (t : ℝ) : Matrix (Fin 4) (Fin 16) ℝ := fun i j =>
  if hj : j.val < 4 then
    (!![(4-t)/12, (4-t)/12, (4-t)/12, t/4;
        (1-t)/3, -(1-t)/5, -(1-t)/5, 0;
        0, 4*(1-t)/15, -4*(1-t)/15, 0;
        0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℝ) i ⟨j.val, hj⟩ /
      Real.sqrt 2
  else 0

private def coefficients : Matrix (Fin 4) (Fin 16) ℝ := noisyCoefficients (1 / 1000)

def selectedRow : {r : Finset (Fin 4) // r.card = 3} :=
  ⟨{0, 1, 2}, by decide⟩

def selectedCols (k : Fin 4) : {s : Finset (Fin 16) // s.card = 3} :=
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

private lemma noisy_separable (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsSeparable (noisyRho t) := by
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
  refine ⟨4, ![(1-t)/3, (1-t)/3, (1-t)/3, t],
    ![projectors 0, projectors 1, projectors 2, (1/2 : ℂ) • 1],
    ![single 0 0 1, single 1 1 1, single 2 2 1, (1/4 : ℂ) • 1], ?_, ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> dsimp <;> positivity
  · simp only [Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]; ring
  · intro t
    fin_cases t
    · exact ⟨projectors_density 0, hflag 0⟩
    · exact ⟨projectors_density 1, hflag 1⟩
    · exact ⟨projectors_density 2, hflag 2⟩
    · exact ⟨hmixed 2, hmixed 4⟩
  · simp only [noisyRho, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, smul_kronecker, kronecker_smul,
      one_kronecker_one, smul_smul, smul_add]
    push_cast
    module

private lemma rho_separable : IsSeparable rho :=
  noisy_separable (1 / 1000) (by norm_num) (by norm_num)

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

private lemma correlation_row_0 (t : ℝ) (j : Fin 16) :
    corr (noisyRho t) alice bob 0 j = noisyCoefficients t 0 j := by
  rw [corr, noisyRho]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_kronecker, Matrix.one_mul]
  fin_cases j <;>
    norm_num [alice, bob, projectors, symUnit, skewUnit, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, noisyCoefficients,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul,
      Matrix.trace_single_eq_same, Matrix.trace_single_eq_of_ne, Matrix.single_apply,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, ← Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul] <;> ring

private lemma correlation_row_1 (t : ℝ) (j : Fin 16) :
    corr (noisyRho t) alice bob 1 j = noisyCoefficients t 1 j := by
  rw [corr, noisyRho]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_kronecker, Matrix.one_mul]
  fin_cases j <;>
    norm_num [alice, bob, projectors, symUnit, skewUnit, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, noisyCoefficients,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul,
      Matrix.trace_single_eq_same, Matrix.trace_single_eq_of_ne, Matrix.single_apply,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, ← Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul] <;> ring

private lemma correlation_row_2 (t : ℝ) (j : Fin 16) :
    corr (noisyRho t) alice bob 2 j = noisyCoefficients t 2 j := by
  rw [corr, noisyRho]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_kronecker, Matrix.one_mul]
  fin_cases j <;>
    norm_num [alice, bob, projectors, symUnit, skewUnit, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, noisyCoefficients,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul,
      Matrix.trace_single_eq_same, Matrix.trace_single_eq_of_ne, Matrix.single_apply,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, ← Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul] <;> ring

private lemma correlation_row_3 (t : ℝ) (j : Fin 16) :
    corr (noisyRho t) alice bob 3 j = noisyCoefficients t 3 j := by
  rw [corr, noisyRho]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.sum_mul,
    ← Matrix.mul_kronecker_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_kronecker, Matrix.one_mul]
  fin_cases j <;>
    norm_num [alice, bob, projectors, symUnit, skewUnit, pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ, noisyCoefficients,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_single_mul,
      Matrix.trace_single_eq_same, Matrix.trace_single_eq_of_ne, Matrix.single_apply,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im, ← Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul]

private lemma correlation_eq (t : ℝ) : corr (noisyRho t) alice bob = noisyCoefficients t := by
  ext i j
  rw [noisyCoefficients]
  fin_cases i
  · exact correlation_row_0 t j
  · exact correlation_row_1 t j
  · exact correlation_row_2 t j
  · exact correlation_row_3 t j

private lemma selectedCols_injective : Function.Injective selectedCols := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert hij; decide)

private lemma minor_value (t : ℝ) (k : Fin 4) :
    compound 3 (noisyCoefficients t) selectedRow (selectedCols k) =
      (![64 * ((4-t)/12) * ((1-t)/3)^2 / 25,
        4 * (t/4) * ((1-t)/3)^2 / 5,
        -4 * (t/4) * ((1-t)/3)^2 / 5,
        24 * (t/4) * ((1-t)/3)^2 / 25] : Fin 4 → ℝ) k / Real.sqrt 2 ^ 3 := by
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
    norm_num [noisyCoefficients] <;> field_simp <;> ring

private lemma minor_energy :
    (∑ k : Fin 4, (compound 3 coefficients selectedRow (selectedCols k)) ^ 2) =
      559341805929555807 / 500000000000000000000 := by
  have h6 : Real.sqrt 2 ^ 6 = 8 := by
    calc
      Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := pow_mul _ 2 3
      _ = 8 := by norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [coefficients, minor_value, div_pow, ← pow_mul]
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
  rw [rho, correlation_eq]
  change _ ≤ cmnInf 3 coefficients ^ 2
  rw [cmnInf, ← minor_energy]
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

private lemma noisy_density (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsDensity (noisyRho t) := by
  obtain ⟨n, w, a, b, hw, hsum, hab, heq⟩ := noisy_separable t ht0 ht1
  rw [heq]
  constructor
  · exact Matrix.posSemidef_sum _ (fun j _ =>
      ((hab j).1.1.kronecker (hab j).2.1).smul (Complex.zero_le_real.mpr (hw j)))
  · simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_kronecker,
      (hab _).1.2, (hab _).2.2, mul_one]
    simpa [Complex.real_smul] using congrArg (fun x : ℝ => (x : ℂ)) hsum

private lemma noisy_noise_lower (t : ℝ) (ht1 : t ≤ 1) :
    (noisyRho t - ((t / 8 : ℝ) : ℂ) • 1).PosSemidef := by
  have heq : noisyRho t - ((t / 8 : ℝ) : ℂ) • 1 =
      ((1-t : ℝ) : ℂ) • noisyRho 0 := by
    simp [noisyRho, smul_smul]
    module
  rw [heq]
  exact (noisy_density 0 (by norm_num) (by norm_num)).1.smul
    (Complex.zero_le_real.mpr (sub_nonneg.mpr ht1))

private lemma noisy_positive (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (noisyRho t).PosDef := by
  have hn : (((t / 8 : ℝ) : ℂ) •
      (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr (by positivity))
  convert hn.posSemidef_add (noisy_noise_lower t ht1) using 1 <;> abel

private lemma noisy_bob_marginal (t : ℝ) :
    partialTraceLeft (noisyRho t) = Matrix.diagonal
      (![(((4-t)/12 : ℝ) : ℂ), (((4-t)/12 : ℝ) : ℂ),
        (((4-t)/12 : ℝ) : ℂ), ((t/4 : ℝ) : ℂ)] : Fin 4 → ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceLeft, noisyRho, projectors, Matrix.diagonal,
      Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single_apply,
      Matrix.one_apply, Fin.sum_univ_succ, Matrix.smul_apply] <;> ring

private lemma noisy_not_bob_mixed (t : ℝ) (ht : t ≤ 1 / 200) :
    partialTraceLeft (noisyRho t) ≠ (1 / 4 : ℂ) • 1 := by
  intro he
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M 3 3).re) he
  rw [noisy_bob_marginal] at h
  norm_num [Matrix.diagonal, Matrix.smul_apply] at h
  linarith

private lemma noisy_violation (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 200) :
    bound 2 4 3 < cmnInf 3 (corr (noisyRho t) alice bob) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    calc
      _ = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hu : (199 / 200 : ℝ)^2 ≤ (1-t)^2 := by nlinarith
  have hv : (799 / 200 : ℝ) ≤ 4-t := by linarith
  have hp := mul_le_mul hv hu (by norm_num : (0 : ℝ) ≤ (199/200)^2)
    (by linarith : (0 : ℝ) ≤ 4-t)
  have hpoly : 2025 < 512 * (4-t) * (1-t)^2 := by nlinarith
  have hm : compound 3 (noisyCoefficients t) selectedRow (selectedCols 0) =
      16 * (4-t) * (1-t)^2 / (1350 * Real.sqrt 2) := by
    rw [minor_value, hs3]
    norm_num
    ring
  have hstrict : 3 / (64 * Real.sqrt 2) <
      16 * (4-t) * (1-t)^2 / (1350 * Real.sqrt 2) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 64 * Real.sqrt 2)
      (by positivity : 0 < 1350 * Real.sqrt 2)).mpr
    nlinarith
  have hl := row_lower (compound 3 (noisyCoefficients t)) selectedRow
    (fun _ : Fin 1 => selectedCols 0) (fun _ _ _ => Subsingleton.elim _ _)
  simp only [Fin.sum_univ_one, hm] at hl
  rw [bound_value, correlation_eq]
  unfold cmnInf
  have hn : 0 ≤ ‖compound 3 (noisyCoefficients t)‖ := norm_nonneg _
  have hb : 0 ≤ 3 / (64 * Real.sqrt 2) := by positivity
  nlinarith

private lemma noisy_last_row_zero (t : ℝ) (j : Fin 16) :
    noisyCoefficients t 3 j = 0 := by
  fin_cases j <;> simp [noisyCoefficients]

private lemma noisy_compound_other_row (t : ℝ)
    (r : {r : Finset (Fin 4) // r.card = 3}) (hr : r ≠ selectedRow)
    (s : {s : Finset (Fin 16) // s.card = 3}) :
    compound 3 (noisyCoefficients t) r s = 0 := by
  have hmem : (3 : Fin 4) ∈ r.val := by
    by_contra hn
    have hsub : r.val ⊆ selectedRow.val := by
      intro x hx
      fin_cases x <;> simp_all [selectedRow]
    have heq : r.val = selectedRow.val := Finset.eq_of_subset_of_card_le hsub
      (by rw [r.property]; decide)
    exact hr (Subtype.ext heq)
  have hi : (3 : Fin 4) ∈ Set.range (r.val.orderEmbOfFin r.property) := by
    rw [Finset.range_orderEmbOfFin]
    exact hmem
  obtain ⟨i, hi⟩ := hi
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  change noisyCoefficients t (r.val.orderEmbOfFin r.property i)
    (s.val.orderEmbOfFin s.property j) = 0
  rw [hi]
  exact noisy_last_row_zero t _

private lemma noisy_compound_four_zero (t : ℝ) : compound 4 (noisyCoefficients t) = 0 := by
  ext r s
  have heq : r.val = Finset.univ := Finset.eq_univ_of_card r.val (by simpa using r.property)
  have hi : (3 : Fin 4) ∈ Set.range (r.val.orderEmbOfFin r.property) := by
    rw [Finset.range_orderEmbOfFin, heq]
    exact Finset.mem_univ _
  obtain ⟨i, hi⟩ := hi
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  change noisyCoefficients t (r.val.orderEmbOfFin r.property i)
    (s.val.orderEmbOfFin s.property j) = 0
  rw [hi]
  exact noisy_last_row_zero t _

private lemma noisy_compound_outer (t : ℝ) :
    compound 3 (noisyCoefficients t) = Matrix.vecMulVec
      (Pi.single selectedRow (1 : ℝ))
      (fun s => compound 3 (noisyCoefficients t) selectedRow s) := by
  ext r s
  by_cases hr : r = selectedRow
  · subst r
    change _ = (Pi.single selectedRow (1 : ℝ) : {r : Finset (Fin 4) // r.card = 3} → ℝ) selectedRow * _
    rw [Pi.single_eq_same, one_mul]
  · simp [Matrix.vecMulVec, Pi.single_apply, hr, noisy_compound_other_row t r hr s]

private lemma noisy_compound_other_col (t : ℝ)
    (s : {s : Finset (Fin 16) // s.card = 3})
    (hs : ∀ k, s ≠ selectedCols k) :
    compound 3 (noisyCoefficients t) selectedRow s = 0 := by
  by_cases hsub : s.val ⊆ ({0, 1, 2, 3} : Finset (Fin 16))
  · have hm : s.val ∈ ({0, 1, 2, 3} : Finset (Fin 16)).powersetCard 3 :=
      Finset.mem_powersetCard.mpr ⟨hsub, s.property⟩
    have he : ({0, 1, 2, 3} : Finset (Fin 16)).powersetCard 3 =
        {(selectedCols 0).val, (selectedCols 1).val, (selectedCols 2).val,
          (selectedCols 3).val} := by decide
    rw [he] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h
    · exact False.elim (hs 0 (Subtype.ext h))
    · exact False.elim (hs 1 (Subtype.ext h))
    · exact False.elim (hs 2 (Subtype.ext h))
    · exact False.elim (hs 3 (Subtype.ext h))
  · obtain ⟨x, hx, hout⟩ := Finset.not_subset.mp hsub
    have hx4 : ¬ x.val < 4 := by
      fin_cases x <;> simp_all
    have hi : x ∈ Set.range (s.val.orderEmbOfFin s.property) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    obtain ⟨j, hj⟩ := hi
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    simp [compound, Matrix.submatrix_apply, hj, noisyCoefficients, hx4]

private lemma noisy_row_energy (t : ℝ) :
    (∑ s, compound 3 (noisyCoefficients t) selectedRow s ^ 2) =
      ∑ k : Fin 4, compound 3 (noisyCoefficients t) selectedRow (selectedCols k) ^ 2 := by
  classical
  symm
  apply Fintype.sum_of_injective selectedCols selectedCols_injective
  · intro s hs
    rw [noisy_compound_other_col t s]
    · simp
    · intro k hk
      exact hs ⟨k, hk.symm⟩
  · intro i; rfl

private lemma single_row_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (r : m) (v : n → ℝ) :
    (Matrix.vecMulVec (Pi.single r (1 : ℝ)) v) *
      (Matrix.vecMulVec (Pi.single r (1 : ℝ)) v)ᴴ =
      Matrix.diagonal (Pi.single r (∑ j, v j ^ 2) : m → ℝ) := by
  ext i k
  by_cases hi : i = r <;> by_cases hk : k = r <;>
    simp_all [Matrix.mul_apply, Matrix.vecMulVec, Matrix.conjTranspose_apply,
      Pi.single_apply, Matrix.diagonal_apply, pow_two]
  all_goals aesop

lemma single_row_opnorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (r : m) (v : n → ℝ) :
    ‖Matrix.vecMulVec (Pi.single r (1 : ℝ)) v‖ = Real.sqrt (∑ j, v j ^ 2) := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self
    (Matrix.vecMulVec (Pi.single r (1 : ℝ)) v)ᴴ
  rw [Matrix.conjTranspose_conjTranspose, single_row_gram,
    Matrix.l2_opNorm_diagonal, Pi.norm_single, Matrix.l2_opNorm_conjTranspose,
    Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at h
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), pow_two]
  exact h.symm

private lemma single_row_complex_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (r : m) (v : n → ℝ) :
    ((Matrix.vecMulVec (Pi.single r (1 : ℝ)) v).map Complex.ofReal) *
      ((Matrix.vecMulVec (Pi.single r (1 : ℝ)) v).map Complex.ofReal)ᴴ =
      Matrix.diagonal (fun i => (((Pi.single r (∑ j, v j ^ 2) : m → ℝ) i) : ℂ)) := by
  ext i k
  by_cases hi : i = r <;> by_cases hk : k = r <;>
    simp_all [Matrix.mul_apply, Matrix.vecMulVec, Matrix.conjTranspose_apply,
      Pi.single_apply, Matrix.diagonal_apply, pow_two, ← map_sum]
  all_goals aesop

lemma single_row_schatten {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (r : m) (v : n → ℝ) (p : ℝ) (hp : 0 < p) :
    D5.S3.Quantum.Schatten.Partition.rectangularNorm
      ((Matrix.vecMulVec (Pi.single r (1 : ℝ)) v).map Complex.ofReal) p =
        Real.sqrt (∑ j, v j ^ 2) := by
  classical
  let E : ℝ := ∑ j, v j ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdiag : (Matrix.diagonal (fun i => (((Pi.single r E : m → ℝ) i) : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (by
      intro i
      change (0 : ℂ) ≤ (((Pi.single r E : m → ℝ) i) : ℂ)
      apply Complex.zero_le_real.mpr
      by_cases hi : i = r <;> simp [Pi.single_apply, hi, hE])
  apply (Real.rpow_left_inj
    (schattenNorm_nonneg _ _) (Real.sqrt_nonneg _) hp.ne').mp
  change D5.S3.Quantum.Schatten.Partition.rectangularNorm
    ((Matrix.vecMulVec (Pi.single r (1 : ℝ)) v).map Complex.ofReal) p ^ p = _
  rw [D5.S3.Quantum.Schatten.Partition.rectangularNorm_rpow _ hp,
    single_row_complex_gram]
  unfold D5.S3.Quantum.Hiai.InverseMeanVariational.tracePower
  rw [CFC.rpow_eq_cfc_real hdiag.nonneg,
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal,
    Matrix.trace_diagonal]
  try simp only [← Complex.ofReal_sum, Complex.ofReal_re]
  have hz : (0 : ℝ) ^ (p / 2) = 0 := Real.zero_rpow (by linarith)
  have he : (∑ i : m, (Pi.single r E : m → ℝ) i ^ (p / 2)) = E ^ (p / 2) := by
    simp [Pi.single_apply, hz]
  rw [he, Real.sqrt_eq_rpow, ← Real.rpow_mul hE]
  congr 1
  ring

/-- The squared Euclidean length of the four increasing IZX minors. -/
def noisyMinorEnergy (t : ℝ) : ℝ :=
  ∑ k : Fin 4, (compound 3 (noisyCoefficients t) selectedRow (selectedCols k)) ^ 2

private lemma noisy_compound_rank (t : ℝ) (ht : t ≤ 1 / 200) :
    (compound 3 (noisyCoefficients t)).rank = 1 := by
  classical
  let C := compound 3 (noisyCoefficients t)
  have hupper : C.rank ≤ 1 := by
    rw [show C = _ from noisy_compound_outer t]
    exact Matrix.rank_vecMulVec_le _ _
  have hm : C selectedRow (selectedCols 0) ≠ 0 := by
    change compound 3 (noisyCoefficients t) selectedRow (selectedCols 0) ≠ 0
    rw [minor_value]
    norm_num only [Fin.isValue, Matrix.cons_val_zero]
    have h1 : 0 < 1 - t := by linarith
    have h4 : 0 < 4 - t := by linarith
    exact ne_of_gt (by positivity)
  have hd : (C.submatrix (fun _ : Fin 1 => selectedRow)
      (fun _ : Fin 1 => selectedCols 0)).det ≠ 0 := by
    simpa only [Matrix.det_fin_one, Matrix.submatrix_apply] using hm
  have hlow := Matrix.rank_submatrix_le C (fun _ : Fin 1 => selectedRow)
    (fun _ : Fin 1 => selectedCols 0)
  rw [Matrix.rank_of_det_ne_zero hd] at hlow
  have : 1 ≤ C.rank := by simpa using hlow
  exact Nat.le_antisymm hupper this

/-- Exact third- and fourth-order compounds, including their actual finite-p and
infinity norms, over the entire closed rational noise interval. -/
theorem rational_compound_family (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 200) :
    (compound 3 (corr (noisyRho t) alice bob)).rank = 1 ∧
    (∀ r, r ≠ selectedRow → ∀ s, compound 3 (corr (noisyRho t) alice bob) r s = 0) ∧
    (∀ s, s ∉ Set.range selectedCols →
      compound 3 (corr (noisyRho t) alice bob) selectedRow s = 0) ∧
    (∀ k : Fin 4, compound 3 (corr (noisyRho t) alice bob) selectedRow (selectedCols k) =
      (![64 * ((4-t)/12) * ((1-t)/3)^2 / 25,
        4 * (t/4) * ((1-t)/3)^2 / 5,
        -4 * (t/4) * ((1-t)/3)^2 / 5,
        24 * (t/4) * ((1-t)/3)^2 / 25] : Fin 4 → ℝ) k / Real.sqrt 2 ^ 3) ∧
    cmnInf 3 (corr (noisyRho t) alice bob) = Real.sqrt (noisyMinorEnergy t) ∧
    (∀ p : ℝ, 1 ≤ p → cmnP p 3 (corr (noisyRho t) alice bob) =
      Real.sqrt (noisyMinorEnergy t)) ∧
    (∀ p : ℝ, 1 ≤ p → bound 2 4 3 < cmnP p 3 (corr (noisyRho t) alice bob)) ∧
    compound 4 (corr (noisyRho t) alice bob) = 0 ∧
    cmnInf 4 (corr (noisyRho t) alice bob) = 0 ∧
    (∀ p : ℝ, 1 ≤ p → cmnP p 4 (corr (noisyRho t) alice bob) = 0) := by
  classical
  have hi : cmnInf 3 (corr (noisyRho t) alice bob) = Real.sqrt (noisyMinorEnergy t) := by
    rw [correlation_eq]
    unfold cmnInf
    rw [noisy_compound_outer, single_row_opnorm, noisy_row_energy]
    rfl
  have hp (p : ℝ) (hp : 1 ≤ p) : cmnP p 3 (corr (noisyRho t) alice bob) =
      Real.sqrt (noisyMinorEnergy t) := by
    rw [correlation_eq]
    unfold cmnP
    rw [noisy_compound_outer, single_row_schatten _ _ p (by linarith), noisy_row_energy]
    rfl
  refine ⟨?_, ?_, ?_, ?_, hi, hp, ?_, ?_, ?_, ?_⟩
  · rw [correlation_eq]; exact noisy_compound_rank t ht1
  · intro r hr s
    rw [correlation_eq]; exact noisy_compound_other_row t r hr s
  · intro s hs
    rw [correlation_eq]
    apply noisy_compound_other_col
    intro k hk
    exact hs ⟨k, hk.symm⟩
  · intro k
    rw [correlation_eq]; exact minor_value t k
  · intro p hpp
    rw [hp p hpp, ← hi]
    exact noisy_violation t ht0 ht1
  · rw [correlation_eq]; exact noisy_compound_four_zero t
  · simp [correlation_eq, cmnInf, noisy_compound_four_zero]
  · intro p hpp
    let r : {r : Finset (Fin 4) // r.card = 4} := ⟨Finset.univ, by decide⟩
    have hz := single_row_schatten r
      (fun _ : {s : Finset (Fin 16) // s.card = 4} => (0 : ℝ)) p (by linarith)
    have hzmap : (Matrix.vecMulVec (Pi.single r (1 : ℝ))
        (fun _ : {s : Finset (Fin 16) // s.card = 4} => (0 : ℝ))).map Complex.ofReal = 0 := by
      ext i j
      simp [Matrix.vecMulVec]
    rw [hzmap] at hz
    simpa [cmnP, correlation_eq, noisy_compound_four_zero] using hz

/-- The exact fixed specialization, strengthening the historical operator lower
bound to equality without changing the original witness. -/
theorem fixed_compound_energy :
    noisyMinorEnergy (1 / 1000) = 559341805929555807 / 500000000000000000000 ∧
    (∀ p : ℝ, 1 ≤ p → cmnP p 3 (corr (noisyRho (1 / 1000)) alice bob) ^ 2 =
      559341805929555807 / 500000000000000000000) := by
  have he : noisyMinorEnergy (1 / 1000) =
      559341805929555807 / 500000000000000000000 := minor_energy
  refine ⟨he, ?_⟩
  intro p hp
  rw [(rational_compound_family (1 / 1000) (by norm_num) (by norm_num)).2.2.2.2.2.1 p hp,
    Real.sq_sqrt, he]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The separable qubit-ququart example refutes the conjecture without FNF. -/
theorem result : ¬ claim := by
  intro hc
  have hu := hc 2 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rho rho_separable alice bob alice_basis bob_basis
  rw [bound_value] at hu
  have hn : 0 ≤ cmnInf 3 (corr rho alice bob) := by unfold cmnInf; positivity
  have hb : 0 ≤ 3 / (64 * Real.sqrt 2) := by positivity
  have hsq := (sq_le_sq₀ hn hb).mpr hu
  have hv := fixed_compound_energy.2 1 (by norm_num)
  have hf := rational_compound_family (1 / 1000) (by norm_num) (by norm_num)
  have hnorm : cmnP 1 3 (corr (noisyRho (1 / 1000)) alice bob) =
      cmnInf 3 (corr (noisyRho (1 / 1000)) alice bob) :=
    (hf.2.2.2.2.2.1 1 (by norm_num)).trans hf.2.2.2.2.1.symm
  rw [hnorm] at hv
  change cmnInf 3 (corr rho alice bob) ^ 2 = _ at hv
  linarith [numerical_gap]

/-- Every member of the full closed noise interval is an actual separable density,
with its exact normalized correlation, Bob marginal, strict operator violation,
white-noise lower bound and positive definiteness away from zero noise.
Bob's nonuniform marginal rules out filter normal form. -/
theorem rational_noisy_family (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 200) :
    IsSeparable (noisyRho t) ∧ IsDensity (noisyRho t) ∧
    IsHermBasis alice ∧ IsHermBasis bob ∧
    corr (noisyRho t) alice bob = noisyCoefficients t ∧
    partialTraceLeft (noisyRho t) = Matrix.diagonal
      (![(((4-t)/12 : ℝ) : ℂ), (((4-t)/12 : ℝ) : ℂ),
        (((4-t)/12 : ℝ) : ℂ), ((t/4 : ℝ) : ℂ)] : Fin 4 → ℂ) ∧
    partialTraceLeft (noisyRho t) ≠ (1 / 4 : ℂ) • 1 ∧
    (noisyRho t - ((t / 8 : ℝ) : ℂ) • 1).PosSemidef ∧
    (0 < t → (noisyRho t).PosDef) ∧
    bound 2 4 3 < cmnInf 3 (corr (noisyRho t) alice bob) := by
  have ht : t ≤ 1 := by linarith
  exact ⟨noisy_separable t ht0 ht, noisy_density t ht0 ht, alice_basis, bob_basis,
    correlation_eq t, noisy_bob_marginal t, noisy_not_bob_mixed t ht1,
    noisy_noise_lower t ht, fun h => noisy_positive t h ht, noisy_violation t ht0 ht1⟩

end D5.S3.Quantum.Entanglement.Witness.CorrelationMinorNormFNFRefutation
