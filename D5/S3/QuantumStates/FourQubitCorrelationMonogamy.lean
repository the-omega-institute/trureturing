/- GID: D5/S3/QuantumStates/FourQubitCorrelationMonogamy
   generality: I
   mirror-B: D5/B/S3/QuantumStates/FourQubitCorrelationMonogamy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Three anticommuting Pauli families bound four-qubit pair correlations by three. -/

import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum

/-! Squared two-body Pauli correlations of four qubits sum to at most three. -/

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
open D5.S3.Quantum.Information.CovarianceSumBound
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Measurements.CliffordJointMeasurability

namespace D5.S3.QuantumStates.FourQubitCorrelationMonogamy

/-- Pauli `i` on A, Pauli `j` on target B, C or D, and identities elsewhere. -/
def twoBodyWord (X i j : Fin 3) : Fin 4 → Pauli :=
  fun q => if q = 0 then ![Pauli.X, Pauli.Y, Pauli.Z] i
    else if q = X.succ then ![Pauli.X, Pauli.Y, Pauli.Z] j else Pauli.I

/-- The AX reduced-state correlation entry, evaluated on the full pure state. -/
def correlation (ψ : (Fin 4 → Fin 2) → ℂ) (X i j : Fin 3) : ℝ :=
  (trace (rankOneDensity ψ * wordOp (twoBodyWord X i j))).re

/-- Cheng–Milne–Hall–Wiseman Eq. (36), for every normalized pure four-qubit state. -/
def claim : Prop :=
  ∀ ψ : (Fin 4 → Fin 2) → ℂ, star ψ ⬝ᵥ ψ = 1 →
    ∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, correlation ψ X i j ^ 2 ≤ 3

private lemma partition_sign (k : Fin 3) (u v : Fin 3 × Fin 3) (h : u ≠ v) :
    (∏ q : Fin 4, sgn (twoBodyWord u.1 (k + u.1) u.2 q)
      (twoBodyWord v.1 (k + v.1) v.2 q)) = -1 := by
  revert k u v
  decide +kernel

private lemma group_relations (k : Fin 3) :
    (∀ u : Fin 3 × Fin 3,
      (wordOp (twoBodyWord u.1 (k + u.1) u.2)).IsHermitian) ∧
    (∀ u : Fin 3 × Fin 3,
      wordOp (twoBodyWord u.1 (k + u.1) u.2) *
        wordOp (twoBodyWord u.1 (k + u.1) u.2) = 1) ∧
    (∀ u v : Fin 3 × Fin 3, u ≠ v →
      wordOp (twoBodyWord u.1 (k + u.1) u.2) *
        wordOp (twoBodyWord v.1 (k + v.1) v.2) =
      -(wordOp (twoBodyWord v.1 (k + v.1) v.2) *
        wordOp (twoBodyWord u.1 (k + u.1) u.2))) := by
  refine ⟨fun u => word_hermitian _, fun u => (wordUnit _).val_inv, ?_⟩
  intro u v h
  rw [word_comm_sign]
  have hs : (∏ q : Fin 4, (sgn (twoBodyWord u.1 (k + u.1) u.2 q)
      (twoBodyWord v.1 (k + v.1) v.2 q) : ℂ)) = -1 := by
    exact_mod_cast partition_sign k u v h
  rw [hs, neg_one_smul]

private lemma anticommuting_family_bound {n α : Type*}
    [Fintype n] [DecidableEq n] [Fintype α]
    (ρ : DensityState n) (P : α → Matrix n n ℂ)
    (hP : ∀ i, (P i).IsHermitian) (hsq : ∀ i, P i * P i = 1)
    (hanti : ∀ i j, i ≠ j → P i * P j = -(P j * P i)) :
    ∑ i, expectation ρ (P i) ^ 2 ≤ 1 := by
  classical
  let a : α → ℝ := fun i => expectation ρ (P i)
  let H : Matrix n n ℂ := ∑ i, (a i : ℂ) • P i
  let s : ℝ := ∑ i, a i ^ 2
  have hH : H.IsHermitian := by
    exact (isSelfAdjoint_sum Finset.univ fun i _ =>
      ((hP i).smul (by simp [IsSelfAdjoint])).isSelfAdjoint).isHermitian
  have hHsq : H * H = (s : ℂ) • (1 : Matrix n n ℂ) := by
    apply (smul_right_injective (Matrix n n ℂ) (by norm_num : (2 : ℂ) ≠ 0))
    dsimp only
    rw [two_smul, ← mul_smul]
    simpa only [H, s, Fintype.linearCombination_apply, Complex.ofReal_sum, pow_two,
      Complex.ofReal_mul] using
      FourierCliffordVacuum.cliffordLinear_anticommutator
        P hsq hanti (fun i => (a i : ℂ)) (fun i => (a i : ℂ))
  have hEH : expectation ρ H = s := by
    simp only [expectation, H, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, Complex.re_sum, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, s, a, pow_two]
  have hEHsq : expectation ρ (H * H) = s := by
    rw [hHsq]
    rw [Complex.coe_smul, expect_smul, expect_one, mul_one]
  have hv := variance_nonneg ρ hH
  rw [variance, hEHsq, hEH] at hv
  change s ≤ 1
  nlinarith [sq_nonneg (s - 1)]

private lemma group_bound (ρ : DensityState (Fin 4 → Fin 2)) (k : Fin 3) :
    ∑ X : Fin 3, ∑ j : Fin 3,
      expectation ρ (wordOp (twoBodyWord X (k + X) j)) ^ 2 ≤ 1 := by
  obtain ⟨hh, hs, ha⟩ := group_relations k
  simpa only [Fintype.sum_prod_type] using anticommuting_family_bound ρ
    (fun u : Fin 3 × Fin 3 => wordOp (twoBodyWord u.1 (k + u.1) u.2)) hh hs ha

private lemma partition_sum (f : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f X i j) =
      ∑ k : Fin 3, ∑ X : Fin 3, ∑ j : Fin 3, f X (k + X) j := by
  calc
    _ = ∑ X : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, f X i j := by
      apply Finset.sum_congr rfl
      intro X hX
      rw [Finset.sum_comm]
    _ = ∑ X : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f X (k + X) j := by
      apply Finset.sum_congr rfl
      intro X hX
      apply Finset.sum_congr rfl
      intro j hj
      symm
      exact Equiv.sum_comp (Equiv.addRight X) (fun k : Fin 3 => f X k j)
    _ = ∑ X : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3, f X (k + X) j := by
      apply Finset.sum_congr rfl
      intro X hX
      rw [Finset.sum_comm]
    _ = ∑ k : Fin 3, ∑ X : Fin 3, ∑ j : Fin 3, f X (k + X) j := by
      rw [Finset.sum_comm]

private lemma density_bound (ρ : DensityState (Fin 4 → Fin 2)) :
    ∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
      expectation ρ (wordOp (twoBodyWord X i j)) ^ 2 ≤ 3 := by
  rw [partition_sum]
  calc
    _ ≤ ∑ _k : Fin 3, (1 : ℝ) := Finset.sum_le_sum fun k _ => group_bound ρ k
    _ = 3 := by norm_num

private lemma pure_specialization (ψ : (Fin 4 → Fin 2) → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) :
    ∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, correlation ψ X i j ^ 2 ≤ 3 := by
  exact density_bound
    (D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.pureDensityState ψ hψ)

theorem result : claim := by
  intro ψ hψ
  exact pure_specialization ψ hψ

end D5.S3.QuantumStates.FourQubitCorrelationMonogamy
