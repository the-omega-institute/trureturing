/- GID: D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/SteeringPowerPreservationRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.claim; result=D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.result; claim=D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.claim
   digest: An admissible five-dimensional projective family fails steering power preservation. -/

import D5.S3.Observer.WindowRegister
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A five-dimensional counterexample to steering power preservation. -/

namespace D5.S3.Quantum.Measurements.SteeringPowerPreservationRefutation

open scoped BigOperators
open D5.S3.Observer.WindowRegister

noncomputable section

/-- The phase coefficients of the steering substitution. -/
def coeff (d : ℕ) (φ : Fin d → Fin d → ℝ) (n : ℕ) (y k : Fin d) : ℂ :=
  (1 / (d : ℂ)) * windowRoot d ^ (k.val * n * (n - 1) / 2) *
    ∑ l : Fin d,
      Complex.exp (-Complex.I * ((∑ m ∈ Finset.range n,
        φ ⟨(l.val + m + 1) % d, Nat.mod_lt _ (Nat.zero_lt_of_lt l.isLt)⟩ y : ℝ) : ℂ)) *
        windowRoot d ^ (k.val * n * l.val)

/-- Zero total phase and orthonormal coefficient rows at every nontrivial power. -/
def Admissible (d : ℕ) (φ : Fin d → Fin d → ℝ) : Prop :=
  (∀ y, ∑ j, φ j y = 0) ∧
    ∀ n, 1 ≤ n → n ≤ d - 1 → ∀ y y',
      ∑ k, star (coeff d φ n y' k) * coeff d φ n y k =
        if y = y' then 1 else 0

/-- A family of unitary observables of order dividing the number of outcomes. -/
def IsProjectiveFamily (d : ℕ) (B : Fin d → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ y, B y ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ B y ^ d = 1

/-- The steering substitution for projective measurements. -/
def transformed (d : ℕ) (φ : Fin d → Fin d → ℝ)
    (B : Fin d → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) (k : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ y, coeff d φ n y k • B y ^ n

/-- Power preservation for all prime dimensions and all admissible projective families. -/
def claim : Prop :=
  ∀ d, Nat.Prime d → ∀ φ, Admissible d φ → ∀ B, IsProjectiveFamily d B →
    ∀ k n, 1 ≤ n → n ≤ d - 1 →
      transformed d φ B n k = (transformed d φ B 1 k) ^ n

private def t (j y : Fin 5) : ℤ :=
  ![-6 * (y.val : ℤ), 0, (y.val : ℤ) - 1, 1 + 2 * (y.val : ℤ), 3 * (y.val : ℤ)] j

private def phases (j y : Fin 5) : ℝ := (2 * Real.pi / 5) * (t j y : ℝ)

private def X : Matrix (Fin 5) (Fin 5) ℂ :=
  (shiftMatrix 5).submatrix (ZMod.finEquiv 5) (ZMod.finEquiv 5)

private def Z : Matrix (Fin 5) (Fin 5) ℂ :=
  (clockMatrix 5).submatrix (ZMod.finEquiv 5) (ZMod.finEquiv 5)

private def R (y : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  ∑ k : Fin 5, star (coeff 5 phases 1 y k) • (X * Z ^ k.val)

private def B (y : Fin 5) : Matrix (Fin 5) (Fin 5) ℂ :=
  if y = 0 then windowRoot 5 • R y else R y

private def g : ℂ := (3 + windowRoot 5 + windowRoot 5 ^ 4) / 5

private lemma root_relations :
    windowRoot 5 ^ 5 = 1 ∧
    1 + windowRoot 5 + windowRoot 5 ^ 2 + windowRoot 5 ^ 3 + windowRoot 5 ^ 4 = 0 ∧
    star (windowRoot 5) = windowRoot 5 ^ 4 := by
  have h := windowRoot_isPrimitiveRoot 5
  refine ⟨h.pow_eq_one, ?_, ?_⟩
  · simpa [Finset.sum_range_succ] using h.geom_sum_eq_zero (by norm_num)
  · have hi : (windowRoot 5)⁻¹ = windowRoot 5 ^ 4 := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [← pow_succ] using h.pow_eq_one
    exact (RCLike.inv_eq_conj (h.norm'_eq_one (by norm_num))).symm.trans hi

private lemma phases_zero (y : Fin 5) : ∑ j, phases j y = 0 := by
  simp [phases, t, Fin.sum_univ_succ]
  ring

private lemma coefficient_orthogonality (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 4)
    (y y' : Fin 5) :
    ∑ k, star (coeff 5 phases n y' k) * coeff 5 phases n y k =
      if y = y' then 1 else 0 := by
  sorry

private lemma phases_admissible : Admissible 5 phases := by
  exact ⟨phases_zero, coefficient_orthogonality⟩

private lemma reference_entry (y i j : Fin 5) :
    R y i j = if i = j + 1 then
      windowRoot 5 ^ ((![0, 4, 1, 0, 0] j + y.val * j.val) % 5) else 0 := by
  sorry

private lemma reference_projective (y : Fin 5) :
    R y ∈ Matrix.unitaryGroup (Fin 5) ℂ ∧ R y ^ 5 = 1 := by
  sorry

private lemma witness_projective : IsProjectiveFamily 5 B := by
  sorry

private lemma reconstruction :
    (∑ y, coeff 5 phases 1 y 0 • R y) = X ∧
    (∑ y, coeff 5 phases 2 y 0 • R y ^ 2) = X ^ 2 := by
  sorry

private lemma special_coefficients : coeff 5 phases 1 0 0 = g ∧
    coeff 5 phases 2 0 0 = g := by
  sorry

private lemma transformed_one :
    transformed 5 phases B 1 0 = X + ((windowRoot 5 - 1) * g) • R 0 := by
  sorry

private lemma transformed_two :
    transformed 5 phases B 2 0 = X ^ 2 + ((windowRoot 5 ^ 2 - 1) * g) • R 0 ^ 2 := by
  sorry

private lemma defect_entry :
    ((transformed 5 phases B 1 0) ^ 2 - transformed 5 phases B 2 0) 0 3 =
      g * (g - 1) * (windowRoot 5 - 1) ^ 2 := by
  sorry

private lemma g_nontrivial : g ≠ 0 ∧ g ≠ 1 := by
  have hs : (windowRoot 5 + windowRoot 5 ^ 4) ^ 2 +
      (windowRoot 5 + windowRoot 5 ^ 4) = 1 := by
    calc
      _ = windowRoot 5 ^ 8 + 2 * windowRoot 5 ^ 5 + windowRoot 5 ^ 4 +
          windowRoot 5 ^ 2 + windowRoot 5 := by ring
      _ = 1 := by
        rw [pow_eq_pow_mod 8 root_relations.1, root_relations.1]
        norm_num only [Nat.reduceMod]
        linear_combination root_relations.2.1
  constructor
  · intro hz
    have hg : windowRoot 5 + windowRoot 5 ^ 4 = -3 := by
      unfold g at hz
      linear_combination 5 * hz
    rw [hg] at hs
    norm_num at hs
  · intro ho
    have hg : windowRoot 5 + windowRoot 5 ^ 4 = 2 := by
      unfold g at ho
      linear_combination 5 * ho
    rw [hg] at hs
    norm_num at hs

theorem result : ¬ claim := by
  intro h
  have heq := h 5 Nat.prime_five phases phases_admissible B witness_projective 0 2
    (by norm_num) (by norm_num)
  have hz : g * (g - 1) * (windowRoot 5 - 1) ^ 2 = 0 := by
    rw [← defect_entry, ← heq, sub_self]
    rfl
  exact (mul_ne_zero (mul_ne_zero g_nontrivial.1 (sub_ne_zero.mpr g_nontrivial.2))
    (pow_ne_zero _ (sub_ne_zero.mpr ((windowRoot_isPrimitiveRoot 5).ne_one (by norm_num))))) hz

end

end D5.S3.Quantum.Measurements.SteeringPowerPreservationRefutation
