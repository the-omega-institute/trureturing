/- GID: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Irreducible
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Irreducible
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected MCMC finite Perron proof supporting actual weighted graphs. -/
/- Transplanted from or4nge19/MCMC@b901242fd04b6eff425a177e5c9bc6c56257bc62.
Copyright and attribution notices below retained; full license: D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/Auxiliary.lean.
Changes: module imports relocated; comment formatting, placement and blank lines adapted for the canonical weighted-graph consumer.
Matteo Cipollina. Changes: unused declarations and branches removed; retained live proof steps preserved; unused local proof terms removed. -/
/- Copyright (c) 2025 Matteo Cipollina. All rights reserved. Released under Apache 2.0 license as described in the file LICENSE. Authors: Matteo Cipollina -/
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Combinatorics.Quiver.Path
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Primitive
open Quiver.Path
namespace Matrix
open Quiver CollatzWielandt
variable {n : Type*} [DecidableEq n] {A : Matrix n n ℝ}
def pathToQuiverOfForallPosImpPos {A B : Matrix n n ℝ}
    (hAB : ∀ {u v : n}, 0 < A u v → 0 < B u v) :
    ∀ {u v : n} (p : @Quiver.Path n (toQuiver A) u v),
      Σ p' : @Quiver.Path n (toQuiver B) u v,
        PLift
          ((@Quiver.Path.length n (toQuiver B) u v p') =
            (@Quiver.Path.length n (toQuiver A) u v p))
  | u, _, @Quiver.Path.nil n (toQuiver A) u =>
      ⟨@Quiver.Path.nil n (toQuiver B) u, ⟨by simp⟩⟩
  | u, _, @Quiver.Path.cons n (toQuiver A) u b c p e =>
      let ⟨p', hp'⟩ := pathToQuiverOfForallPosImpPos hAB p
      ⟨@Quiver.Path.cons n (toQuiver B) u b c p' ⟨hAB e.down⟩, ⟨by simp [hp'.down]⟩⟩
lemma one_add_pos_of_pos {A : Matrix n n ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {i j : n} (hij : 0 < A i j) :
    0 < (1 + A) i j := by
  by_cases h : i = j
  · subst h
    simpa using Matrix.one_add_diag_pos (fun k => hA_nonneg k k) i
  · simpa [Matrix.add_apply, Matrix.one_apply, h] using hij
theorem Irreducible.add_one (h_irred : A.IsIrreducible) : (1 + A).IsIrreducible := by
  let B := (1 : Matrix n n ℝ) + A
  constructor
  · exact fun i j => Matrix.one_add_apply_nonneg h_irred.nonneg i j
  · intro i j
    letI : Quiver n := toQuiver A
    obtain ⟨pA, hpA_pos⟩ := h_irred.connected i j
    let pA' : @Quiver.Path n (toQuiver A) i j := pA
    obtain ⟨pB, hp_len⟩ := pathToQuiverOfForallPosImpPos
      (A := A) (B := B) (fun {u v} huv => by
        simpa [B] using one_add_pos_of_pos h_irred.nonneg huv) pA'
    letI : Quiver n := toQuiver B
    exact ⟨pB, by simpa [hp_len.down] using hpA_pos⟩
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}
omit [Fintype n] [DecidableEq n] in
lemma Irreducible.exists_pos_entry [Nonempty n] (hA_irred : A.IsIrreducible) :
    ∃ i j : n, 0 < A i j := by
  letI : Quiver n := toQuiver A
  exact Nonempty.elim ‹Nonempty n› fun i₀ => by
    obtain ⟨p, hp_pos⟩ := hA_irred.connected i₀ i₀
    rcases Quiver.Path.path_decomposition_first_edge p hp_pos with
      ⟨j, e, -, -, -⟩
    exact ⟨i₀, j, e.down⟩
lemma mulVec_eq_sub_one_smul_of_one_add_mulVec
    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (h : (1 + A) *ᵥ v = r • v) :
    A *ᵥ v = (r - 1) • v := by
  have h_exp : v + A *ᵥ v = r • v := by
    simpa [add_mulVec, one_mulVec] using h
  have : A *ᵥ v = r • v - v := eq_sub_of_add_eq' h_exp
  simpa [sub_smul, one_smul] using this
lemma one_lt_eigenvalue_one_add_of_irreducible [Nonempty n]
    {A : Matrix n n ℝ} (hA_irred : A.IsIrreducible)
    {r : ℝ} {v : n → ℝ} (hv_pos : ∀ i, 0 < v i)
    (h_eig : (1 + A) *ᵥ v = r • v) :
    1 < r := by
  rcases Irreducible.exists_pos_entry (A := A) hA_irred with ⟨i, j, hA_pos⟩
  have hAv_pos : 0 < (A *ᵥ v) i :=
    mulVec_pos_of_exists_pos_mul_pos i j (fun k => hA_irred.1 i k) hv_pos hA_pos
  have h_comp : v i + (A *ᵥ v) i = r * v i := by
    simpa [add_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul] using congr_fun h_eig i
  have h_lt : v i < r * v i := by linarith
  exact (mul_lt_mul_iff_of_pos_right (hv_pos i)).1 (by simpa [one_mul] using h_lt)
theorem exists_positive_eigenvector_of_irreducible [Nonempty n]
  (hA_irred : A.IsIrreducible) :
    ∃ (r : ℝ) (v : n → ℝ),
      0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  let B : Matrix n n ℝ := 1 + A
  have hB_nonneg : ∀ i j, 0 ≤ B i j := fun i j => Matrix.one_add_apply_nonneg hA_irred.nonneg i j
  have hB_diag_pos : ∀ i, 0 < B i i := fun i => Matrix.one_add_diag_pos (fun j => hA_irred.nonneg j j) i
  have hB_irred : (1 + A).IsIrreducible := Irreducible.add_one (A := A) hA_irred
  have hB_prim : B.IsPrimitive :=
    IsPrimitive.of_irreducible_pos_diagonal B hB_nonneg hB_irred hB_diag_pos
  obtain ⟨rB, v, hrB_pos, hv_pos, h_eig_B⟩ :=
    exists_positive_eigenvector_of_primitive (A := B) hB_prim hB_nonneg
  have h_eig_A : A *ᵥ v = (rB - 1) • v := by
    simpa [B] using mulVec_eq_sub_one_smul_of_one_add_mulVec h_eig_B
  have hrB_gt_one : 1 < rB := by
    simpa [B] using one_lt_eigenvalue_one_add_of_irreducible hA_irred hv_pos h_eig_B
  have hrA_pos : 0 < rB - 1 := sub_pos.mpr hrB_gt_one
  exact ⟨rB - 1, v, hrA_pos, hv_pos, h_eig_A⟩
open Finset
