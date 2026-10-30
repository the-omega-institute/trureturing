/- GID: D5/S3/StatisticalMechanics/CarlemanJordanChainInverse
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CarlemanJordanChainInverse
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Critical Carleman Jordan-chain inverses are increasing-path sums. -/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace D5.S3.StatisticalMechanics.CarlemanJordanChainInverse

open scoped BigOperators

noncomputable section

/-- Principal truncation of the coefficient matrix of the powers of the source series. -/
def carleman (α : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => PowerSeries.coeff (j.val + 1) ((PowerSeries.mk α) ^ (i.val + 1))

/-- The source's normalized upper triangular Jordan chain, with indices shifted by one. -/
def IsJordanChain (α : ℕ → ℝ) (n : ℕ) (w : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ j, (carleman α n - 1) *ᵥ (fun i => w i j) =
    if h : j.val = 0 then 0 else fun i => w i ⟨j.val - 1, by omega⟩) ∧
  (∀ i j, i.val = 0 → w i j = if j.val = 0 then 1 else 0) ∧
  (∀ i j, j < i → w i j = 0)

/-- Increasing-path sum: append the final edge to each shorter path from index zero.
The zero-edge path has weight one exactly at index zero. -/
def sigma (α : ℕ → ℝ) (n : ℕ) : ℕ → Fin n → ℝ
  | 0, j => if j.val = 0 then 1 else 0
  | m + 1, j => ∑ i : Fin n, if i < j then sigma α n m i * carleman α n i j else 0

/-- Every critical principal truncation has a normalized Jordan chain, and every such
chain has inverse entries given by the source's increasing-path sum. -/
def claim : Prop :=
  ∀ α : ℕ → ℝ, α 0 = 0 → α 1 = 1 → α 2 ≠ 0 →
    ∀ n : ℕ, 0 < n → (∃ w, IsJordanChain α n w) ∧
      ∀ w, IsJordanChain α n w → IsUnit w.det ∧
        ∀ k j : Fin n, k ≤ j → w⁻¹ k j = sigma α n k.val j

private lemma carleman_structure (α : ℕ → ℝ) (n : ℕ)
    (h0 : α 0 = 0) (h1 : α 1 = 1) :
    (∀ i j : Fin n, j ≤ i → (carleman α n - 1) i j = 0) ∧
    (∀ i j : Fin n, j.val = i.val + 1 →
      (carleman α n - 1) i j = (i.val + 1 : ℕ) * α 2) := by
  sorry

private lemma back_substitution (n : ℕ) (a : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i j, j ≤ i → a i j = 0)
    (hs : ∀ i j, j.val = i.val + 1 → a i j ≠ 0)
    (k : ℕ) (hk : k < n) (b : Fin n → ℝ)
    (hb : ∀ i, k ≤ i.val → b i = 0) :
    ∃ v : Fin n → ℝ, (∀ i, i.val = 0 → v i = 0) ∧
      (∀ i, k < i.val → v i = 0) ∧ a *ᵥ v = b := by
  sorry

private lemma chain_exists (α : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (ha : ∀ i j : Fin n, j ≤ i → (carleman α n - 1) i j = 0)
    (hs : ∀ i j : Fin n, j.val = i.val + 1 → (carleman α n - 1) i j ≠ 0) :
    ∃ w, IsJordanChain α n w := by
  have solve := back_substitution n (carleman α n - 1) ha hs
  sorry

private lemma chain_power (α : ℕ → ℝ) (n : ℕ)
    (w : Matrix (Fin n) (Fin n) ℝ) (hw : IsJordanChain α n w)
    (m : ℕ) (j : Fin n) :
    (carleman α n - 1) ^ m *ᵥ (fun i => w i j) =
      if h : m ≤ j.val then fun i => w i ⟨j.val - m, by omega⟩ else 0 := by
  sorry

private lemma krylov_inverse (α : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (w : Matrix (Fin n) (Fin n) ℝ) (hw : IsJordanChain α n w) :
    IsUnit w.det ∧ w⁻¹ = fun k j => ((carleman α n - 1) ^ k.val) ⟨0, hn⟩ j := by
  have powers := chain_power α n w hw
  sorry

private lemma path_expansion (α : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (ha : ∀ i j : Fin n, j ≤ i → (carleman α n - 1) i j = 0)
    (m : ℕ) (j : Fin n) :
    ((carleman α n - 1) ^ m) ⟨0, hn⟩ j = sigma α n m j := by
  sorry

theorem result : claim := by
  intro α h0 h1 h2 n hn
  obtain ⟨ha, hs⟩ := carleman_structure α n h0 h1
  have hsne : ∀ i j : Fin n, j.val = i.val + 1 →
      (carleman α n - 1) i j ≠ 0 := by
    intro i j hij
    rw [hs i j hij]
    exact mul_ne_zero (by exact_mod_cast (Nat.succ_ne_zero i.val)) h2
  refine ⟨chain_exists α n hn ha hsne, ?_⟩
  intro w hw
  obtain ⟨hu, hi⟩ := krylov_inverse α n hn w hw
  refine ⟨hu, ?_⟩
  intro k j _
  rw [hi]
  exact path_expansion α n hn ha k.val j

end

end D5.S3.StatisticalMechanics.CarlemanJordanChainInverse
