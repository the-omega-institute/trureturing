/- GID: D5/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/KoljancicOblakEvenPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted path continuants and their edge-parameter variations for Question 5.11. -/

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-! Branch-polynomial algebra for the complete positive-even double-path nSSP event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath

open Polynomial Matrix

/-- The ordered arcs of the double path, with exactly the specified loops. -/
def pathPattern {n : ℕ} (L : Finset (Fin n)) (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val ∨ (i = j ∧ i ∈ L)

/-- Definition 1.1: the test matrix is unrestricted and the commutator uses its transpose. -/
def HasNSSP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, A i j * X i j = 0) → A * Xᵀ - Xᵀ * A = 0 → X = 0

/-- The complete existential event of Koljančić–Oblak Question 5.11. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → Even n → ∀ L : Finset (Fin n), L.Nonempty →
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, A i j ≠ 0 ↔ pathPattern L i j) ∧ HasNSSP A

/-- Zero-diagonal branch polynomial; `q k` is the squared weight of edge `k`. -/
def continuant (q : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | k + 2 => X * continuant q (k + 1) - C (q k) * continuant q k

/-- Formal first variation in all edge parameters, including both terms in the product rule. -/
def variation (q dq : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 0
  | k + 2 => X * variation q dq (k + 1) -
      C (dq k) * continuant q k - C (q k) * variation q dq k

private lemma continuant_coeff (q : ℕ → ℝ) (n : ℕ) :
    (continuant q n).coeff n = 1 ∧
      ∀ k : ℕ, n < k → (continuant q n).coeff k = 0 := by
  induction n using Nat.twoStepInduction with
  | zero =>
      constructor
      · simp [continuant]
      · intro k hk
        exact coeff_eq_zero_of_natDegree_lt (by simpa [continuant] using hk)
  | one =>
      constructor
      · simp [continuant]
      · intro k hk
        exact coeff_eq_zero_of_natDegree_lt (by simpa [continuant] using hk)
  | more n h0 h1 =>
      constructor
      · simp only [continuant, coeff_sub, coeff_X_mul, coeff_C_mul]
        rw [h1.1, h0.2 (n + 2) (by omega)]
        simp
      · intro k hk
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
        simp only [continuant, coeff_sub, coeff_X_mul, coeff_C_mul]
        rw [h1.2 k (by omega), h0.2 (k + 1) (by omega)]
        simp

private lemma variation_coeff (q dq : ℕ → ℝ) (n k : ℕ) (h : n ≤ k) :
    (variation q dq n).coeff k = 0 := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => simp [variation]
  | one => simp [variation]
  | more n h0 h1 =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      simp only [variation, coeff_sub, coeff_X_mul, coeff_C_mul]
      rw [h1 k (by omega), (continuant_coeff q n).2 (k + 1) (by omega),
        h0 (k + 1) (by omega)]
      simp

/-- Two consecutive zero branch variations recover every edge variation, uniformly in length.
The length-zero and length-one branches have no edge parameters to recover. -/
theorem branch_variation_injective (q dq : ℕ → ℝ) (n : ℕ)
    (hq : ∀ k < n, q k ≠ 0)
    (h0 : variation q dq n = 0) (h1 : variation q dq (n + 1) = 0) :
    ∀ k < n, dq k = 0 := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
      have hr : C (dq n) * continuant q n + C (q n) * variation q dq n = 0 := by
        change X * variation q dq (n + 1) - C (dq n) * continuant q n -
          C (q n) * variation q dq n = 0 at h1
        rw [h0, mul_zero] at h1
        linear_combination -h1
      have hd : dq n = 0 := by
        have hc := congrArg (fun p : ℝ[X] => p.coeff n) hr
        simpa only [coeff_add, coeff_C_mul, (continuant_coeff q n).1,
          variation_coeff q dq n n le_rfl, coeff_zero, mul_one, mul_zero, add_zero] using hc
      have hz : variation q dq n = 0 := by
        rw [hd, C_0, zero_mul, zero_add] at hr
        exact (mul_eq_zero.mp hr).resolve_left (C_ne_zero.mpr (hq n (by omega)))
      have hi := ih (fun k hk => hq k (by omega)) hz h0
      intro k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
      · exact hi k hlt
      · exact hd

end D5.S3.Combinatorics.SpectralGraph.KoljancicOblakEvenPath
