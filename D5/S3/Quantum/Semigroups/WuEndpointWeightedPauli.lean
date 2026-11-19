/- GID: D5/S3/Quantum/Semigroups/WuEndpointWeightedPauli
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuEndpointWeightedPauli
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pauli expansion identifies both the actual endpoint map and the unweighted twirl. -/

import D5.S3.Quantum.Semigroups.WuEndpointPauliFrame
import Mathlib.Tactic.Module

/-! Ordered Pauli conjugations and the unweighted twirl for the signed endpoint. -/

noncomputable section

open Matrix BigOperators
open scoped Kronecker
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (letter_mul letterPhase letterProduct pauli_hermitian word_expansion pauli_trace_pair)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)

namespace WuRankOneEndpointFloor

def endpointAlpha : ℝ := (1 + lambda) / 2
def endpointBeta : ℝ := (1 - lambda) / 2

theorem endpointAlpha_add_beta : endpointAlpha + endpointBeta = 1 := by
  unfold endpointAlpha endpointBeta
  ring

theorem endpointBeta_nonneg : 0 ≤ endpointBeta := by
  have h : lambda ≤ 1 := by
    have hsq : lambda ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (2 / 3)]
  unfold endpointBeta
  linarith

theorem endpointBeta_le_alpha : endpointBeta ≤ endpointAlpha := by
  have h : 0 ≤ lambda := Real.sqrt_nonneg _
  unfold endpointAlpha endpointBeta
  linarith

private theorem endpointAlpha_sub_beta : endpointAlpha - endpointBeta = lambda := by
  unfold endpointAlpha endpointBeta
  ring

/-- The six ordered products of two of the four conjugating matrices. -/
def endpointPair : Fin 6 → TwoMode :=
  ![endpointU 0 * endpointU 1, endpointU 0 * endpointU 2, endpointU 0 * endpointU 3,
    endpointU 1 * endpointU 2, endpointU 1 * endpointU 3, endpointU 2 * endpointU 3]

/-- The homogeneous polynomial of the 16 ordered Pauli conjugations, grouped by degree. -/
def endpointConjugationSum (a b : ℂ) : MatrixMap Mode Mode ℂ :=
  a ^ 4 • LinearMap.id +
  (a ^ 3 * b) • (∑ j : Fin 4, MatrixMap.conj (endpointU j)) +
  (a ^ 2 * b ^ 2) • (∑ j : Fin 6, MatrixMap.conj (endpointPair j)) +
  (a * b ^ 3) • (∑ j : Fin 4, MatrixMap.conj (endpointTriple j)) +
  b ^ 4 • MatrixMap.conj endpointVolume

private theorem conjugation_mul (U V X : TwoMode) :
    MatrixMap.conj (U * V) X = MatrixMap.conj U (MatrixMap.conj V X) := by
  simp only [MatrixMap.conj, LinearMap.coe_mk, AddHom.coe_mk, conjTranspose_mul]
  simp only [mul_assoc]

private def pauliFlip (j : Fin 4) (p q : Pauli) : ℂ :=
  match j with
  | 0 => if (p = .X ∨ p = .Y) ≠ (q = .X ∨ q = .Z) then -1 else 1
  | 1 => if (p = .X ∨ p = .Y) ≠ (q = .Y ∨ q = .Z) then -1 else 1
  | 2 => if p = .X ∨ p = .Z then -1 else 1
  | 3 => if p = .Y ∨ p = .Z then -1 else 1

set_option maxHeartbeats 1500000 in
-- The sign table checks each of the four conjugations on all sixteen basis words.
private theorem conjugation_U_word (j : Fin 4) (p q : Pauli) :
    MatrixMap.conj (endpointU j) (pauliWord p q) = pauliFlip j p q • pauliWord p q := by
  by_cases h : p = .I ∧ q = .X
  · obtain ⟨rfl, rfl⟩ := h
    change endpointU j * endpointGamma 0 * (endpointU j)ᴴ = _
    rw [endpointU_conj_gamma]
    by_cases hj : j = 0
    · subst j
      simp [endpointGamma, pauliFlip]
    · rw [ite_eq_right hj]
      fin_cases j
      · exact (hj rfl).elim
      all_goals simp [endpointGamma, pauliFlip]
  · change endpointU j * pauliWord p q * (endpointU j)ᴴ = _
    rw [(endpointU_hermitian j).eq]
    fin_cases j <;> cases p <;> cases q <;>
      simp_all [pauliFlip, endpointU, pauliWord_mul, letterPhase, letterProduct,
        smul_smul, Complex.I_mul_I]

set_option maxHeartbeats 1500000 in
-- Expand the sixteen conjugations and compare the scalar polynomials on the Pauli basis.
private theorem conjugationSum_word (a b : ℂ) (p q : Pauli) :
    endpointConjugationSum a b (pauliWord p q) =
      ((a + b) ^ (4 - cliffordDegree p q) * (a - b) ^ cliffordDegree p q) • pauliWord p q := by
  simp only [endpointConjugationSum, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, endpointPair, endpointTriple, endpointVolume, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.succ_zero_eq_one, conjugation_mul, map_smul,
    conjugation_U_word]
  cases p <;> cases q <;> simp [pauliFlip, cliffordDegree] <;> module

private theorem word_reindex (w : Fin 2 → Pauli) :
    (wordOp w).submatrix (fun i : Mode => ![i.1, i.2])
      (fun i : Mode => ![i.1, i.2]) = pauliWord (w 0) (w 1) := by
  ext i j
  simp [wordOp, tensorOp, Fin.prod_univ_two, pauliWord]

theorem endpoint_map_eq_on_pauli {E : Type*} [AddCommMonoid E] [Module ℂ E]
    {L R : TwoMode →ₗ[ℂ] E}
    (h : ∀ p q : Pauli, L (pauliWord p q) = R (pauliWord p q)) : L = R := by
  ext X : 1
  let Y : Matrix (Fin 2 → Bit) (Fin 2 → Bit) ℂ :=
    X.submatrix (fun f => (f 0, f 1)) (fun f => (f 0, f 1))
  have hX : X = ∑ w : Fin 2 → Pauli,
      (((2 : ℂ) ^ 2)⁻¹ * (wordOp w * Y).trace) • pauliWord (w 0) (w 1) := by
    have hh := congrArg (fun B : Matrix (Fin 2 → Bit) (Fin 2 → Bit) ℂ =>
      B.submatrix (fun i : Mode => ![i.1, i.2]) (fun i : Mode => ![i.1, i.2])) (word_expansion Y)
    ext i j
    have hhij := congrArg (fun B : TwoMode => B i j) hh
    simp only [Y, Matrix.cons_val_zero,
      Matrix.cons_val_one, Prod.eta, Matrix.submatrix_apply, Matrix.sum_apply,
      Matrix.smul_apply] at hhij ⊢
    convert hhij using 1
    apply Finset.sum_congr rfl
    intro w _
    have hw := congrArg (fun B : TwoMode => B i j) (word_reindex w)
    exact congrArg (_ • ·) hw.symm
  rw [hX]
  simp only [map_sum, map_smul, h]

/-- The weighted ordered Pauli conjugations are the actual signed map `A₁`. -/
theorem A1_eq_weighted_pauli :
    A₁ = endpointConjugationSum (endpointAlpha : ℂ) (endpointBeta : ℂ) := by
  apply endpoint_map_eq_on_pauli
  intro p q
  have hab : (endpointAlpha : ℂ) + (endpointBeta : ℂ) = 1 := by
    exact_mod_cast endpointAlpha_add_beta
  have hdiff : (endpointAlpha : ℂ) - (endpointBeta : ℂ) = (lambda : ℂ) := by
    exact_mod_cast endpointAlpha_sub_beta
  rw [A1_pauliWord, conjugationSum_word, hab, hdiff, one_pow, one_mul]

private theorem pauliWord_trace (p q : Pauli) :
    (pauliWord p q).trace = if p = .I ∧ q = .I then 4 else 0 := by
  have h (r : Pauli) : (pauliMatrix r).trace = if r = .I then 2 else 0 := by
    simpa [pauliMatrix] using pauli_trace_pair r .I
  rw [pauliWord, Matrix.trace_kronecker, h, h]
  by_cases hp : p = .I <;> by_cases hq : q = .I <;> norm_num [hp, hq]

private def traceIdentity : MatrixMap Mode Mode ℂ :=
  (Matrix.traceLinearMap Mode ℂ ℂ).smulRight (1 : TwoMode)

/-- Unweighted twirl in the actual signed channel's Pauli basis. -/
theorem endpoint_pauli_twirl (X : TwoMode) :
    endpointConjugationSum 1 1 X = (4 * X.trace) • (1 : TwoMode) := by
  have h : endpointConjugationSum 1 1 = (4 : ℂ) • traceIdentity := by
    apply endpoint_map_eq_on_pauli
    intro p q
    rw [conjugationSum_word]
    change _ = (4 : ℂ) • ((pauliWord p q).trace • (1 : TwoMode))
    rw [pauliWord_trace]
    cases p <;> cases q <;> norm_num [cliffordDegree, pauliWord, pauliMatrix,
      Matrix.one_kronecker_one, smul_smul]
  rw [h]
  exact smul_smul (4 : ℂ) X.trace (1 : TwoMode)

#print axioms A1_eq_weighted_pauli
#print axioms endpoint_pauli_twirl

end WuRankOneEndpointFloor
