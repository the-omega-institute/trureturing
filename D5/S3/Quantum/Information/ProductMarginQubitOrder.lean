/- GID: D5/S3/Quantum/Information/ProductMarginQubitOrder
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ProductMarginQubitOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common positive lower matrices vanish at distinct pure local qubit margins. -/

import D5.S3.Quantum.Information.QubitNormalFormState
import D5.S3.Quantum.Hiai.CommonLowerHarmonicBound
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Information.ProductMarginQubitOrder
open Matrix
open scoped MatrixOrder ComplexOrder Kronecker
open D5.S3.Quantum.Information.QubitNormalFormState
open D5.S3.Quantum.Hiai.ParallelSumVariational
open D5.S3.Quantum.Hiai.CommonLowerHarmonicBound

private def pureSplit (x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 - (z : ℂ) / (1 - (x : ℂ) ^ 2)) / 2, -(x : ℂ) * z / (2 * (1 - (x : ℂ) ^ 2));
    (x : ℂ) * z / (2 * (1 - (x : ℂ) ^ 2)), (1 + (z : ℂ) / (1 - (x : ℂ) ^ 2)) / 2]

private lemma pure_annihilation {x z : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hpure : x ^ 2 + z ^ 2 = 1) :
    qubitMatrix x z * pureSplit x z = 0 ∧
      qubitMatrix x (-z) * (1 - pureSplit x z) = 0 := by
  have hd : (1 : ℂ) - (x : ℂ) ^ 2 ≠ 0 := by
    have hr : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
    exact_mod_cast hr
  have hp : (x : ℂ) ^ 2 + (z : ℂ) ^ 2 = 1 := by exact_mod_cast hpure
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, qubitMatrix, pureSplit] <;>
    field_simp <;> linear_combination hp

/-- A distinct pure local pair has no nonzero common positive lower matrix after tensoring
with arbitrary other margins. This includes noncommuting complex lower matrices. -/
theorem common_lower_zero_of_pure_left {n : Type*} [Fintype n] [DecidableEq n]
    {x z : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hpure : x ^ 2 + z ^ 2 = 1)
    (R S : Matrix n n ℂ) {K : Matrix (Fin 2 × n) (Fin 2 × n) ℂ}
    (hK : K.PosSemidef) (hKP : K ≤ qubitMatrix x z ⊗ₖ R)
    (hKQ : K ≤ qubitMatrix x (-z) ⊗ₖ S) : K = 0 := by
  let U := pureSplit x z ⊗ₖ (1 : Matrix n n ℂ)
  let V := (1 - pureSplit x z) ⊗ₖ (1 : Matrix n n ℂ)
  have hsum : U + V = 1 := by
    dsimp [U, V]
    rw [← Matrix.add_kronecker]
    simp
  have h := common_lower_split_bound hK hKP hKQ (U, V) hsum
  have hp := (pure_annihilation hx hx1 hpure).1
  have hq := (pure_annihilation hx hx1 hpure).2
  have henergy : splitEnergy (qubitMatrix x z ⊗ₖ R) (qubitMatrix x (-z) ⊗ₖ S) (U, V) = 0 := by
    dsimp [splitEnergy]
    have hpu : (qubitMatrix x z ⊗ₖ R) * U = 0 := by
      dsimp [U]
      rw [← Matrix.mul_kronecker_mul, hp]
      simp
    have hqv : (qubitMatrix x (-z) ⊗ₖ S) * V = 0 := by
      dsimp [V]
      rw [← Matrix.mul_kronecker_mul, hq]
      simp
    rw [Matrix.mul_assoc, hpu, Matrix.mul_assoc, hqv]
    simp
  rw [henergy, smul_zero] at h
  exact le_antisymm h hK.nonneg

#print axioms common_lower_zero_of_pure_left
end D5.S3.Quantum.Information.ProductMarginQubitOrder
