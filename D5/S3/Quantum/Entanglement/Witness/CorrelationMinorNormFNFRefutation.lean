/- GID: D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim; result=D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.result; claim=D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.claim
   digest: A separable qubit-ququart state violates the correlation-minor bound without FNF. -/

import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.FinThree
import Mathlib.Tactic

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
  if j.val < 4 then
    (!![1333/4000, 1333/4000, 1333/4000, 1/4000;
        333/1000, -999/5000, -999/5000, 0;
        0, 333/1250, -333/1250, 0;
        0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℝ) i ⟨j.val, by assumption⟩ /
      Real.sqrt 2
  else 0

private def selectedRow : {r : Finset (Fin 4) // r.card = 3} :=
  ⟨{0, 1, 2}, by decide⟩

private def selectedCols (k : Fin 4) : {s : Finset (Fin 16) // s.card = 3} :=
  ⟨![{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}] k, by fin_cases k <;> decide⟩

private lemma projectors_density (j : Fin 3) : IsDensity (projectors j) := by
  sorry

private lemma rho_separable : IsSeparable rho := by
  sorry

private lemma alice_basis : IsHermBasis alice := by
  sorry

private lemma bob_basis : IsHermBasis bob := by
  sorry

private lemma correlation_eq : corr rho alice bob = coefficients := by
  sorry

private lemma selectedCols_injective : Function.Injective selectedCols := by
  sorry

private lemma minor_energy :
    (∑ k : Fin 4, (compound 3 coefficients selectedRow (selectedCols k)) ^ 2) =
      559341805929555807 / 500000000000000000000 := by
  sorry

private lemma row_lower {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    [DecidableEq m] [DecidableEq n] (c : Matrix m n ℝ) (r : m) (s : t → n)
    (hs : Function.Injective s) : (∑ k, c r (s k) ^ 2) ≤ ‖c‖ ^ 2 := by
  sorry

private lemma witness_lower :
    559341805929555807 / 500000000000000000000 ≤ cmnInf 3 (corr rho alice bob) ^ 2 := by
  classical
  rw [correlation_eq, cmnInf, ← minor_energy]
  exact row_lower (compound 3 coefficients) selectedRow selectedCols selectedCols_injective

private lemma bound_value : bound 2 4 3 = 3 / (64 * Real.sqrt 2) := by
  sorry

private lemma numerical_gap :
    (3 / (64 * Real.sqrt 2)) ^ 2 <
      (559341805929555807 / 500000000000000000000 : ℝ) := by
  sorry

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
