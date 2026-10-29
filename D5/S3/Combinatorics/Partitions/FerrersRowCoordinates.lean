/- GID: D5/S3/Combinatorics/Partitions/FerrersRowCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/FerrersRowCoordinates
   mirror-E: none(waiver:bounded-ferrers-coordinate-equivalence)
   anchors: [mathlib/module/Mathlib.Combinatorics.Young.YoungDiagram]
   utility: none
   digest: Fixed ambient Ferrers coordinates retain every zero row and column. -/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.FerrersRowCoordinates

/-- Bottom-to-top row lengths, including all ambient zero rows. -/
abbrev Rows (H U : ℕ) := {r : Fin H → Fin (U + 1) // Antitone r}

/-- Source column heights, from left to right, including all ambient zero columns. -/
abbrev Board (U H : ℕ) := {b : Fin U → Fin (H + 1) // Monotone b}

private def rowList {H U : ℕ} (r : Rows H U) : List ℕ :=
  List.ofFn (fun i => (r.val i).val)

private theorem rowList_sorted {H U : ℕ} (r : Rows H U) : (rowList r).SortedGE := by
  apply List.sortedGE_iff_pairwise.mpr
  rw [rowList, List.pairwise_ofFn]
  intro i j hij
  exact Fin.le_iff_val_le_val.mp (r.property (le_of_lt hij))

/-- The underlying finite diagram forgets only the ambient padding. -/
def diagram {H U : ℕ} (r : Rows H U) : YoungDiagram :=
  YoungDiagram.ofRowLens (rowList r) (rowList_sorted r)

theorem diagram_mem {H U : ℕ} (r : Rows H U) (i j : ℕ) :
    (i,j) ∈ diagram r ↔ ∃ hi : i < H, j < (r.val ⟨i, hi⟩).val := by
  simp [diagram, YoungDiagram.mem_ofRowLens, rowList]

theorem diagram_rowLen {H U : ℕ} (r : Rows H U) (i : Fin H) :
    (diagram r).rowLen i = (r.val i).val := by
  simpa [diagram, rowList] using
    (YoungDiagram.rowLen_ofRowLens (w := rowList r) (hw := rowList_sorted r)
      ⟨i.val, by simpa [rowList] using i.isLt⟩)

private theorem diagram_transpose_bound {H U : ℕ} (r : Rows H U) (j : ℕ) :
    (diagram r).transpose.rowLen j ≤ H := by
  by_contra! h
  have hm : (j,H) ∈ (diagram r).transpose := (YoungDiagram.mem_iff_lt_rowLen).mpr h
  have ht : (H,j) ∈ diagram r := YoungDiagram.mem_transpose.mp hm
  obtain ⟨hi,_⟩ := (diagram_mem r H j).mp ht
  omega

/-- Conjugation, with both ambient dimensions retained. -/
def conjugate {H U : ℕ} (r : Rows H U) : Rows U H :=
  ⟨fun j => ⟨(diagram r).transpose.rowLen j,
      Nat.lt_succ_of_le (diagram_transpose_bound r j)⟩,
    fun i j hij => Fin.le_iff_val_le_val.mpr
      ((diagram r).transpose.rowLen_anti i j hij)⟩

private theorem diagram_conjugate {H U : ℕ} (r : Rows H U) :
    diagram (conjugate r) = (diagram r).transpose := by
  ext ⟨i,j⟩
  change (i,j) ∈ diagram (conjugate r) ↔ (i,j) ∈ (diagram r).transpose
  rw [diagram_mem, YoungDiagram.mem_iff_lt_rowLen]
  constructor
  · rintro ⟨hi,hj⟩
    exact hj
  · intro hj
    have hm : (i,j) ∈ (diagram r).transpose :=
      YoungDiagram.mem_iff_lt_rowLen.mpr hj
    have ht : (j,i) ∈ diagram r := YoungDiagram.mem_transpose.mp hm
    obtain ⟨_,hc⟩ := (diagram_mem r _ _).mp ht
    have hu : i < U := lt_of_lt_of_le hc (Nat.le_of_lt_succ (Fin.isLt _))
    exact ⟨hu,hj⟩

/-- Conjugation is an involution even for zero dimensions and padded zero entries. -/
theorem conjugate_involutive {H U : ℕ} (r : Rows H U) :
    conjugate (conjugate r) = r := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change (diagram (conjugate r)).transpose.rowLen i = (r.val i).val
  rw [diagram_conjugate, YoungDiagram.transpose_transpose, diagram_rowLen]

/-- The exact row/column coordinate bijection in a fixed rectangle. -/
def boardRowsEquiv (U H : ℕ) : Board U H ≃ Rows H U where
  toFun b := conjugate ⟨fun i => b.val i.rev, fun _ _ h => b.property (Fin.rev_le_rev.mpr h)⟩
  invFun r := ⟨fun i => (conjugate r).val i.rev,
    fun _ _ h => (conjugate r).property (Fin.rev_le_rev.mpr h)⟩
  left_inv b := by
    have hh := conjugate_involutive
      (⟨fun i => b.val i.rev, fun _ _ h => b.property (Fin.rev_le_rev.mpr h)⟩ : Rows U H)
    apply Subtype.ext
    funext i
    have hv := congrArg (fun r : Rows U H => r.val i.rev) hh
    simpa using hv
  right_inv r := by
    change conjugate ⟨fun i => (conjugate r).val i.rev.rev, _⟩ = r
    simpa using conjugate_involutive r

/-- The row coordinate is exactly the number of occupied cells in that source row. -/
private theorem boardRows_cell {U H : ℕ} (b : Board U H) (i : Fin H) (j : Fin U) :
    i.val < (b.val j).val ↔ j.rev.val < ((boardRowsEquiv U H b).val i).val := by
  let c : Rows U H := ⟨fun j => b.val j.rev,
    fun _ _ h => b.property (Fin.rev_le_rev.mpr h)⟩
  change i.val < (b.val j).val ↔ j.rev.val < ((conjugate c).val i).val
  rw [← diagram_rowLen, ← YoungDiagram.mem_iff_lt_rowLen,
    diagram_conjugate, YoungDiagram.mem_transpose, diagram_mem]
  constructor
  · intro h
    refine ⟨j.rev.isLt, ?_⟩
    change i.val < (b.val j.rev.rev).val
    simpa only [Fin.rev_rev] using h
  · rintro ⟨hj,h⟩
    change i.val < (b.val j.rev.rev).val at h
    simpa only [Fin.rev_rev] using h

/-- Counting literal source cells in a row agrees with the padded row coordinate. -/
theorem board_row_count {U H : ℕ} (b : Board U H) (i : Fin H) :
    Fintype.card {j : Fin U // i.val < (b.val j).val} =
      ((boardRowsEquiv U H b).val i).val := by
  classical
  let w := (boardRowsEquiv U H b).val i
  let e : {j : Fin U // i.val < (b.val j).val} ≃ Fin w.val :=
    { toFun := fun j => ⟨j.val.rev.val, (boardRows_cell b i j.val).mp j.property⟩
      invFun := fun k =>
        let j : Fin U := ⟨k.val, lt_of_lt_of_le k.isLt (Nat.le_of_lt_succ w.isLt)⟩
        ⟨j.rev, (boardRows_cell b i j.rev).mpr (by simpa only [Fin.rev_rev] using k.isLt)⟩
      left_inv := by intro j; apply Subtype.ext; exact Fin.rev_rev j.val
      right_inv := by intro k; apply Fin.ext; dsimp only; rw [Fin.rev_rev] }
  exact (Fintype.card_congr e).trans (Fintype.card_fin w.val)

end D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
