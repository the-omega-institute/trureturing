/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Lemmas
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Lemmas
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean.
Changes: module imports relocated; comment formatting, placement and blank lines adapted for the canonical weighted-graph consumer.
Matteo Cipollina. Changes: unused declarations and branches removed; retained live proof steps preserved; unused local proof terms removed. -/
/- Copyright (c) 2025 Matteo Cipollina. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: Matteo Cipollina -/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.Combinatorics.Quiver.Path
namespace Pi
lemma ne_zero_of_pos {ι α : Type*} [Nonempty ι] [Zero α] [Preorder α]
    {v : ι → α} (hv_pos : ∀ i, 0 < v i) :
    v ≠ 0 := by
  rintro rfl
  exact Nonempty.elim ‹Nonempty ι› fun i => lt_irrefl (0 : α) (hv_pos i)
end Pi
namespace Matrix
section PerronFrobenius
open Matrix Finset Quiver Quiver.Path
variable {n : Type*}
lemma positive_mul_vec_pos [Fintype n]
    {A : Matrix n n ℝ} (hA_pos : ∀ i j, 0 < A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne_zero : x ≠ 0) :
    ∀ i, 0 < (A.mulVec x) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (le_of_lt (hA_pos i j)) (hx_nonneg j)
  · have : ∃ k, 0 < x k := by
      by_contra h_all_nonpos
      push_neg at h_all_nonpos
      have h_zero : x = 0 := funext (fun j => le_antisymm (h_all_nonpos j) (hx_nonneg j))
      exact hx_ne_zero h_zero
    rcases this with ⟨k, hk_pos⟩
    refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_univ]
    · exact mul_pos (hA_pos i k) hk_pos
variable {A : Matrix n n ℝ}
lemma one_add_apply_nonneg [DecidableEq n] {A : Matrix n n ℝ} (h_nonneg : ∀ i j, 0 ≤ A i j) (i j : n) :
    0 ≤ (1 + A) i j := by
  by_cases h : i = j
  · subst h
    simp only [Matrix.add_apply, Matrix.one_apply_eq]
    linarith [h_nonneg i i]
  · simpa [Matrix.add_apply, Matrix.one_apply, h] using h_nonneg i j
lemma one_add_diag_pos [DecidableEq n] {A : Matrix n n ℝ} (h_diag : ∀ i, 0 ≤ A i i) (i : n) :
    0 < (1 + A) i i := by
  simp only [Matrix.add_apply, Matrix.one_apply_eq]
  linarith [h_diag i]
lemma forall_eq_zero_of_finset_sum_eq_zero_of_nonneg {ι : Type*} [Fintype ι] {f : ι → ℝ}
    (h_nonneg : ∀ j, 0 ≤ f j) (hsum : ∑ j, f j = 0) (j : ι) : f j = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => h_nonneg k)).1 hsum j (Finset.mem_univ j)
lemma mulVec_pos_of_exists_pos_mul_pos [Fintype n] {A : Matrix n n ℝ} {v : n → ℝ} (i j : n)
    (hA_nonneg : ∀ k, 0 ≤ A i k) (hv_pos : ∀ k, 0 < v k) (hij : 0 < A i j) :
    0 < (A *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (hA_nonneg k) (hv_pos k).le
  · refine ⟨j, ?_, ?_⟩
    · simp
    · exact mul_pos hij (hv_pos j)
lemma sum_mul_le_sum_mul_const_of_forall_le {ι : Type*} [Fintype ι] (a f : ι → ℝ) (k : ι)
    (ha : ∀ j, 0 ≤ a j) (hf : ∀ j, f j ≤ f k) :
    ∑ j, a j * f j ≤ (∑ j, a j) * f k := by
  calc
    ∑ j, a j * f j ≤ ∑ j, a j * f k := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hf j) (ha j)
    _ = (∑ j, a j) * f k := by rw [Finset.sum_mul]
lemma positive_mul_vec_of_nonneg_vec [Fintype n] (hA_pos : ∀ i j, 0 < A i j)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    ∀ i, 0 < (A *ᵥ v) i := by
  simpa only [Matrix.mulVec] using
    positive_mul_vec_pos (A := A) hA_pos hv_nonneg hv_ne_zero
lemma irreducible_one_element_implies_diagonal_pos [Fintype n]
    {A : Matrix n n ℝ} (hA_irred : IsIrreducible A)
    (h_card_one : Fintype.card n = 1) (i : n) :
    0 < A i i := by
  letI : Quiver n := toQuiver A
  obtain ⟨p, hp_pos⟩ := hA_irred.connected i i
  obtain ⟨j, p', e, rfl⟩ := Quiver.Path.path_decomposition_last_edge p hp_pos
  have h_sub : Subsingleton n := by
    rcases (Fintype.card_eq_one_iff).1 h_card_one with ⟨a, ha⟩
    exact ⟨fun x y => by simp [ha x, ha y]⟩
  haveI : Subsingleton n := h_sub
  have hji : j = i := Subsingleton.elim _ _
  have e_pos : 0 < A j i := e.down
  simpa [hji] using e_pos
lemma row_sum_pos_of_irreducible_nonneg [Fintype n] [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : IsIrreducible A) (hA_nonneg : ∀ i j, 0 ≤ A i j) (i : n) :
    0 < ∑ j, A i j := by
  rw [lt_iff_le_and_ne]
  refine ⟨Finset.sum_nonneg fun j _ => hA_nonneg i j, ?_⟩
  intro h0
  have h_sum0 : ∑ j, A i j = 0 := Eq.symm h0
  have h_zero_row : ∀ j, A i j = 0 := fun j =>
    forall_eq_zero_of_finset_sum_eq_zero_of_nonneg (fun k => hA_nonneg i k) h_sum0 j
  by_cases h_card_one : Fintype.card n = 1
  · exact lt_irrefl (0 : ℝ) <|
      (h_zero_row i).symm ▸ irreducible_one_element_implies_diagonal_pos hA_irred h_card_one i
  · have h_card_gt_one : 1 < Fintype.card n :=
      Nat.lt_of_le_of_ne (Nat.succ_le_iff.mpr Fintype.card_pos) (Ne.symm h_card_one)
    haveI : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.1 h_card_gt_one
    obtain ⟨j, hj_pos⟩ := Matrix.IsIrreducible.exists_pos (A := A) hA_irred i
    exact lt_irrefl (0 : ℝ) <| (h_zero_row j).symm ▸ hj_pos
theorem IsPrimitive.of_irreducible_pos_diagonal [Fintype n] [Nonempty n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hA_irred : IsIrreducible A) (hA_diag_pos : ∀ i, 0 < A i i) :
    IsPrimitive A := by
  let N := Fintype.card n
  let k := (N - 1) * N + 1
  have hk_pos : 0 < k := by
    have h_card_pos : 0 < N := Fintype.card_pos
    rcases Nat.eq_or_lt_of_le (Nat.one_le_of_lt h_card_pos) with hN | hN_lt
    · simp_all only [le_refl, tsub_self, List.Nat.eq_of_le_zero, zero_mul, zero_add, N, k]
    · omega
  constructor
  · exact hA_nonneg
  · use k, hk_pos
    intro i j
    letI : Quiver n := toQuiver A
    rw [Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA_nonneg k i j]
    obtain ⟨p_any, _hp_any_pos⟩ := hA_irred.connected i j
    obtain ⟨p_ij, hp_len_le⟩ :=
      Quiver.Path.exists_path_length_le_card_sub_one (a := i) (b := j) ⟨p_any⟩
    let p_loop : Path i i :=
      Quiver.Hom.toPath (⟨hA_diag_pos i⟩ : @Quiver.Hom n (toQuiver A) i i)
    have hp_loop_len : p_loop.length = 1 := by
      simp [p_loop]
    have hp_len_le_k : p_ij.length ≤ k := by
      have h_card_ge_one : 1 ≤ N := Nat.one_le_of_lt Fintype.card_pos
      have hN_pos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one h_card_ge_one
      have hk_ge : N - 1 ≤ k := by
        dsimp [k]
        calc
          N - 1 ≤ (N - 1) * N := by
            simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right (N - 1) hN_pos
          _ ≤ (N - 1) * N + 1 := Nat.le_succ _
      exact le_trans hp_len_le hk_ge
    refine ⟨⟨(Path.replicate (k - p_ij.length) p_loop).comp p_ij, ?_⟩⟩
    rw [Path.length_comp, Path.length_replicate, hp_loop_len, mul_one,
      Nat.sub_add_cancel hp_len_le_k]
section MulVecPowMap
variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] {n : Type*} [Fintype n]
  [DecidableEq n] (f : R →+* S) {A : Matrix n n R} {μ : S} {v : n → S}
end MulVecPowMap
end PerronFrobenius
end Matrix
#lint
