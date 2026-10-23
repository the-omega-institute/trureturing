/- GID: D5/S3/Combinatorics/Probability/FiniteCommonMarginalSupermodular
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/FiniteCommonMarginalSupermodular
   mirror-E: none(waiver:symbolic-finite-expectation-comparison)
   anchors: []
   utility: none
   digest: Diagonal maximization for real supermodular tests with four equal finite marginals. -/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators
noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Probability.FiniteCommonMarginalSupermodular

private def clippedPath {C : Type*} (b : ℕ → C) (x : Fin 4 → ℕ) (k r : ℕ) :
    Fin 4 → C :=
  fun j => b (min (x j) (if j.val < r then k + 1 else k))

private def diagonalPath {C : Type*} (b : ℕ → C) (k r : ℕ) : Fin 4 → C :=
  fun j => b (if j.val < r then k + 1 else k)

private def increment {C : Type*} (f : (Fin 4 → C) → ℝ) (b : ℕ → C)
    (k : ℕ) (i : Fin 4) : ℝ :=
  f (diagonalPath b k (i.val + 1)) - f (diagonalPath b k i.val)

private lemma clipped_increment_le {C : Type*} [LinearOrder C]
    (f : (Fin 4 → C) → ℝ)
    (hf : ∀ u v, f u + f v ≤ f (u ⊓ v) + f (u ⊔ v))
    (b : ℕ → C) (hb : Monotone b) (x : Fin 4 → ℕ) (k : ℕ) (i : Fin 4) :
    f (clippedPath b x k (i.val + 1)) - f (clippedPath b x k i.val) ≤
      if k < x i then increment f b k i else 0 := by
  classical
  by_cases hki : k < x i
  · rw [if_pos hki]
    have hmeet :
        clippedPath b x k (i.val + 1) ⊓ diagonalPath b k i.val =
          clippedPath b x k i.val := by
      funext j
      change min _ _ = _
      by_cases hji : j = i
      · subst j
        simp [clippedPath, diagonalPath, Nat.min_eq_right (by omega : k + 1 ≤ x i),
          Nat.min_eq_right (by omega : k ≤ x i),
          min_eq_right (hb (by omega : k ≤ k + 1))]
      · have he : (j.val < i.val + 1) = (j.val < i.val) := by
          apply propext
          have : j.val ≠ i.val := fun h => hji (Fin.ext h)
          omega
        simp only [clippedPath, diagonalPath, he]
        exact min_eq_left (hb (Nat.min_le_right _ _))
    have hjoin :
        clippedPath b x k (i.val + 1) ⊔ diagonalPath b k i.val =
          diagonalPath b k (i.val + 1) := by
      funext j
      change max _ _ = _
      by_cases hji : j = i
      · subst j
        simp [clippedPath, diagonalPath, Nat.min_eq_right (by omega : k + 1 ≤ x i),
          max_eq_left (hb (by omega : k ≤ k + 1))]
      · have he : (j.val < i.val + 1) = (j.val < i.val) := by
          apply propext
          have : j.val ≠ i.val := fun h => hji (Fin.ext h)
          omega
        simp only [clippedPath, diagonalPath, he]
        exact max_eq_right (hb (Nat.min_le_right _ _))
    have h := hf (clippedPath b x k (i.val + 1)) (diagonalPath b k i.val)
    rw [hmeet, hjoin] at h
    unfold increment
    linarith
  · rw [if_neg hki]
    have he : clippedPath b x k (i.val + 1) = clippedPath b x k i.val := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [clippedPath, Nat.min_eq_left (by omega : x i ≤ k),
          Nat.min_eq_left (by omega : x i ≤ k + 1)]
      · have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
        have hh : (j.val < i.val + 1) = (j.val < i.val) := by
          apply propext; omega
        simp only [clippedPath, hh]
    rw [he, sub_self]

private lemma level_increment_le {C : Type*} [LinearOrder C]
    (f : (Fin 4 → C) → ℝ)
    (hf : ∀ u v, f u + f v ≤ f (u ⊓ v) + f (u ⊔ v))
    (b : ℕ → C) (hb : Monotone b) (x : Fin 4 → ℕ) (k : ℕ) :
    f (fun j => b (min (x j) (k + 1))) - f (fun j => b (min (x j) k)) ≤
      ∑ i : Fin 4, if k < x i then increment f b k i else 0 := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => clipped_increment_le f hf b hb x k i)
  have he : (∑ i : Fin 4,
      (f (clippedPath b x k (i.val + 1)) - f (clippedPath b x k i.val))) =
        f (fun j => b (min (x j) (k + 1))) - f (fun j => b (min (x j) k)) := by
    rw [Fin.sum_univ_eq_sum_range (fun r => f (clippedPath b x k (r + 1)) -
      f (clippedPath b x k r)) 4,
      Finset.sum_range_sub (fun r => f (clippedPath b x k r))]
    congr 1; congr 1; funext j;
      simp [clippedPath, j.isLt]
  rwa [he] at h

private lemma pointwise_linearization {C : Type*} [LinearOrder C]
    (f : (Fin 4 → C) → ℝ)
    (hf : ∀ u v, f u + f v ≤ f (u ⊓ v) + f (u ⊔ v))
    (b : ℕ → C) (hb : Monotone b) (x : Fin 4 → ℕ) (N : ℕ)
    (hx : ∀ i, x i ≤ N) :
    f (fun i => b (x i)) ≤ f (fun _ => b 0) +
      ∑ i : Fin 4, ∑ k ∈ Finset.range (x i), increment f b k i := by
  have h := Finset.sum_le_sum (s := Finset.range N)
    (fun k _ => level_increment_le f hf b hb x k)
  rw [Finset.sum_range_sub (fun k => f (fun j => b (min (x j) k)))] at h
  have hend : (fun j => b (min (x j) N)) = (fun j => b (x j)) := by
    funext j; rw [Nat.min_eq_left (hx j)]
  simp only [hend, Nat.min_zero] at h
  rw [Finset.sum_comm] at h
  have hs (i : Fin 4) :
      (∑ k ∈ Finset.range N, if k < x i then increment f b k i else 0) =
        ∑ k ∈ Finset.range (x i), increment f b k i := by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    have := hx i
    omega
  simp_rw [hs] at h
  linarith

private lemma diagonal_linearization {C : Type*}
    (f : (Fin 4 → C) → ℝ) (b : ℕ → C) (n : ℕ) :
    f (fun _ => b n) = f (fun _ => b 0) +
      ∑ i : Fin 4, ∑ k ∈ Finset.range n, increment f b k i := by
  rw [Finset.sum_comm]
  have hs (k : ℕ) : (∑ i : Fin 4, increment f b k i) =
      f (fun _ => b (k + 1)) - f (fun _ => b k) := by
    unfold increment
    rw [Fin.sum_univ_eq_sum_range (fun r => f (diagonalPath b k (r + 1)) -
      f (diagonalPath b k r)) 4,
      Finset.sum_range_sub (fun r => f (diagonalPath b k r))]
    congr 1; congr 1; funext j;
      simp [diagonalPath, j.isLt]
  simp_rw [hs]
  rw [Finset.sum_range_sub (fun k => f (fun _ => b k))]
  ring

private lemma marginal_sum {C : Type*} [Fintype C] [DecidableEq C]
    (p : (Fin 4 → C) → ℝ) (m : C → ℝ)
    (hm : ∀ i t, (∑ x, if x i = t then p x else 0) = m t)
    (i : Fin 4) (g : C → ℝ) :
    (∑ x, p x * g (x i)) = ∑ t, m t * g t := by
  classical
  simp_rw [← hm i, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

/-- Every supermodular real test is maximized by the diagonal law when all four
finite coordinate marginals agree. Zero masses and signed tests are allowed. -/
theorem common_marginal_supermodular_le_diagonal
    {C : Type*} [LinearOrder C] [Fintype C] [Nonempty C]
    (p : (Fin 4 → C) → ℝ) (m : C → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hn : ∑ x, p x = 1)
    (hm : ∀ (i : Fin 4) (t : C), (∑ x, if x i = t then p x else 0) = m t)
    (f : (Fin 4 → C) → ℝ)
    (hf : ∀ x y, f x + f y ≤ f (x ⊓ y) + f (x ⊔ y)) :
    (∑ x, p x * f x) ≤ ∑ t, m t * f (fun _ => t) := by
  classical
  let e := Fintype.orderIsoFinOfCardEq C rfl
  have hcard : 0 < Fintype.card C := Fintype.card_pos
  let b : ℕ → C := fun k => e ⟨min k (Fintype.card C - 1), by omega⟩
  let rank : C → ℕ := fun t => (e.symm t).val
  have hb : Monotone b := by
    intro k l hkl
    apply e.monotone
    change min k _ ≤ min l _
    exact min_le_min_right _ hkl
  have hbr (t : C) : b (rank t) = t := by
    dsimp [b, rank]
    have ht : (e.symm t).val ≤ Fintype.card C - 1 := by
      have := (e.symm t).isLt; omega
    simp only [Nat.min_eq_left ht]
    exact e.apply_symm_apply t
  let g : Fin 4 → C → ℝ := fun i t =>
    ∑ k ∈ Finset.range (rank t), increment f b k i
  have hpoint (x : Fin 4 → C) : f x ≤ f (fun _ => b 0) + ∑ i, g i (x i) := by
    have h := pointwise_linearization f hf b hb (fun i => rank (x i))
      (Fintype.card C) (fun i => Nat.le_of_lt (e.symm (x i)).isLt)
    simpa only [hbr] using h
  have hdiag (t : C) : f (fun _ => t) = f (fun _ => b 0) + ∑ i, g i t := by
    simpa only [hbr] using diagonal_linearization f b (rank t)
  have hmone : ∑ t, m t = 1 := by
    have h := marginal_sum p m hm 0 (fun _ => 1)
    simpa [hn] using h.symm
  calc
    (∑ x, p x * f x) ≤ ∑ x, p x * (f (fun _ => b 0) + ∑ i, g i (x i)) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hp x))
    _ = f (fun _ => b 0) + ∑ i : Fin 4, ∑ t, m t * g i t := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hn, one_mul, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact marginal_sum p m hm i (g i)
    _ = ∑ t, m t * f (fun _ => t) := by
      conv_rhs => enter [2, t, 2]; rw [hdiag t]
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmone, one_mul, Finset.sum_comm]

#print axioms common_marginal_supermodular_le_diagonal

end D5.S3.Combinatorics.Probability.FiniteCommonMarginalSupermodular
