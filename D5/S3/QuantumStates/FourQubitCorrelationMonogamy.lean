/- GID: D5/S3/QuantumStates/FourQubitCorrelationMonogamy
   generality: I
   mirror-B: D5/B/S3/QuantumStates/FourQubitCorrelationMonogamy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Three anticommuting Pauli families bound four-qubit pair correlations by three. -/

import D5.S3.Quantum.Information.CovarianceSumBound
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
open D5.S3.Quantum.Information.CovarianceSumBound
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations

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
  sorry

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
  have hs := partition_sign k
  sorry

private lemma anticommuting_family_bound {n α : Type*}
    [Fintype n] [DecidableEq n] [Fintype α] [DecidableEq α]
    (ρ : DensityState n) (P : α → Matrix n n ℂ)
    (hP : ∀ i, (P i).IsHermitian) (hsq : ∀ i, P i * P i = 1)
    (hanti : ∀ i j, i ≠ j → P i * P j = -(P j * P i)) :
    ∑ i, expectation ρ (P i) ^ 2 ≤ 1 := by
  sorry

private lemma group_bound (ρ : DensityState (Fin 4 → Fin 2)) (k : Fin 3) :
    ∑ X : Fin 3, ∑ j : Fin 3,
      expectation ρ (wordOp (twoBodyWord X (k + X) j)) ^ 2 ≤ 1 := by
  obtain ⟨hh, hs, ha⟩ := group_relations k
  simpa only [Fintype.sum_prod_type] using anticommuting_family_bound ρ
    (fun u : Fin 3 × Fin 3 => wordOp (twoBodyWord u.1 (k + u.1) u.2)) hh hs ha

private lemma partition_sum (f : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (∑ X : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, f X i j) =
      ∑ k : Fin 3, ∑ X : Fin 3, ∑ j : Fin 3, f X (k + X) j := by
  sorry

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
  sorry

theorem result : claim := by
  intro ψ hψ
  exact pure_specialization ψ hψ

end D5.S3.QuantumStates.FourQubitCorrelationMonogamy
