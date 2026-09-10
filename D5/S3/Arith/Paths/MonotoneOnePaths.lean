/- GID: D5/S3/Arith/Paths/MonotoneOnePaths
   generality: I
   mirror-B: D5/B/S3/Arith/Paths/MonotoneOnePaths
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The mean number of all-one monotone paths in a uniform binary square matrix. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Paths.MonotoneOnePaths

open Finset

/-- A path across a (k+1)-square, encoded by the positions of its k east steps. -/
abbrev Path (k : ℕ) := ↥((range (2 * k)).powersetCard k)

private theorem path_subset {k : ℕ} (p : Path k) : p.val ⊆ range (2 * k) :=
  (mem_powersetCard.mp p.property).1

private theorem path_card {k : ℕ} (p : Path k) : p.val.card = k :=
  (mem_powersetCard.mp p.property).2

/-- At time t, count east and south steps in the prefix of length t. -/
def pathCell {k : ℕ} (p : Path k) (t : Fin (2 * k + 1)) : Fin (k + 1) × Fin (k + 1) :=
  (⟨(range t.val ∩ p.val).card, by
      have := card_le_card (inter_subset_right : range t.val ∩ p.val ⊆ p.val)
      rw [path_card p] at this
      omega⟩,
   ⟨(range t.val \ p.val).card, by
      have ht : range t.val ⊆ range (2 * k) := range_mono (by omega)
      have := card_le_card (sdiff_subset_sdiff_left p.val ht)
      rw [card_sdiff_of_subset (path_subset p), card_range, path_card p] at this
      omega⟩)

private theorem pathCell_rank {k : ℕ} (p : Path k) (t : Fin (2 * k + 1)) :
    (pathCell p t).1.val + (pathCell p t).2.val = t.val := by
  simp [pathCell]

private theorem pathCell_injective {k : ℕ} (p : Path k) :
    Function.Injective (pathCell p) := by
  intro t u h
  apply Fin.ext
  rw [← pathCell_rank p t, ← pathCell_rank p u, h]

private theorem pathCell_endpoints {k : ℕ} (p : Path k) :
    pathCell p ⟨0, by omega⟩ = (0, 0) ∧
      pathCell p ⟨2 * k, by omega⟩ = (⟨k, by omega⟩, ⟨k, by omega⟩) := by
  constructor
  · ext <;> simp [pathCell]
  · ext <;> simp [pathCell, inter_eq_right.mpr (path_subset p),
      card_sdiff_of_subset (path_subset p), path_card]
    omega

private theorem pathCell_step {k : ℕ} (p : Path k) (t : Fin (2 * k)) :
    if t.val ∈ p.val then
      (pathCell p t.succ).1.val = (pathCell p t.castSucc).1.val + 1 ∧
        (pathCell p t.succ).2.val = (pathCell p t.castSucc).2.val
    else
      (pathCell p t.succ).1.val = (pathCell p t.castSucc).1.val ∧
        (pathCell p t.succ).2.val = (pathCell p t.castSucc).2.val + 1 := by
  split_ifs with h
  · simp [pathCell, range_add_one, insert_inter_of_mem h, insert_sdiff_of_mem _ h]
  · simp [pathCell, range_add_one, insert_inter_of_notMem h, insert_sdiff_of_notMem _ h]

/-- The set of cells actually visited by the path, including both endpoints. -/
def pathCells {k : ℕ} (p : Path k) : Finset (Fin (k + 1) × Fin (k + 1)) :=
  univ.image (pathCell p)

private theorem pathCells_card {k : ℕ} (p : Path k) : (pathCells p).card = 2 * k + 1 := by
  rw [pathCells, card_image_of_injective _ (pathCell_injective p)]
  simp

/-- Count precisely the east/south paths whose visited cells are all true.
The empty matrix branch is outside the positive-size mean theorem. -/
def pathCount : {n : ℕ} → (Fin n × Fin n → Bool) → ℕ
  | 0, _ => 0
  | k + 1, M => (univ.filter fun p : Path k => ∀ c ∈ pathCells p, M c = true).card

private def freeCellsEquiv {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
    {M : α → Bool // ∀ c ∈ s, M c = true} ≃ (↥sᶜ → Bool) where
  toFun M c := M.val c.val
  invFun f := ⟨fun c => if h : c ∈ s then true else f ⟨c, mem_compl.mpr h⟩,
    by intro c hc; simp [hc]⟩
  left_inv M := by
    apply Subtype.ext
    funext c
    dsimp
    split_ifs with hc
    · exact (M.property c hc).symm
    · rfl
  right_inv f := by
    funext c
    simp [mem_compl.mp c.property]

private theorem fixed_cells_count {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) :
    (univ.filter fun M : α → Bool => ∀ c ∈ s, M c = true).card =
      2 ^ (Fintype.card α - s.card) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (freeCellsEquiv s)]
  simp

private theorem fixed_path_count {k : ℕ} (p : Path k) :
    (univ.filter fun M : Fin (k + 1) × Fin (k + 1) → Bool =>
      ∀ c ∈ pathCells p, M c = true).card = 2 ^ (k * k) := by
  rw [fixed_cells_count, pathCells_card]
  simp only [Fintype.card_prod, Fintype.card_fin]
  congr 1
  have : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by ring
  omega

private theorem total_path_count (k : ℕ) :
    (∑ M : (Fin (k + 1) × Fin (k + 1) → Bool), pathCount M) =
      Nat.choose (2 * k) k * 2 ^ (k * k) := by
  simp only [pathCount, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  simp only [← sum_filter, ← card_eq_sum_ones, fixed_path_count]
  simp

/-- The exact mean over all binary n-square matrices, for positive n. -/
theorem mean_monotone_one_paths (n : ℕ) (hn : 1 ≤ n) :
    (∑ M : (Fin n × Fin n → Bool), (pathCount M : ℚ)) / (2 : ℚ) ^ (n * n) =
      (Nat.choose (2 * n - 2) (n - 1) : ℚ) / (2 : ℚ) ^ (2 * n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have htotal : (∑ M : (Fin (k + 1) × Fin (k + 1) → Bool), (pathCount M : ℚ)) =
      (Nat.choose (2 * k) k : ℚ) * (2 : ℚ) ^ (k * k) := by
    exact_mod_cast total_path_count k
  rw [htotal]
  have hsq : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by ring
  have hsteps : 2 * (k + 1) - 2 = 2 * k := by omega
  have hcells : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [hsq, hsteps, hcells, Nat.add_sub_cancel, pow_add]
  field_simp

end D5.S3.Arith.Paths.MonotoneOnePaths
