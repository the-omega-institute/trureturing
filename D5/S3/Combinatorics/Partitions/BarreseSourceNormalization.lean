/- GID: D5/S3/Combinatorics/Partitions/BarreseSourceNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/BarreseSourceNormalization
   mirror-E: none(waiver:positive-column-normalization)
   anchors: [D5/S3/Combinatorics/Partitions/BarreseAllWidths]
   utility: none
   digest: Positive source column tuples give the entire normalized l-fiber without a width parameter. -/

import D5.S3.Combinatorics.Partitions.BarreseAllWidths

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
open D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open D5.S3.Combinatorics.Partitions.BarreseAllWidths
open scoped BigOperators

/-- A normalized source board is its weakly increasing list of positive column heights. -/
abbrev PositiveColumns := {b : List ℕ // b.SortedLE ∧ ∀ x ∈ b, 0 < x}

/-- Horizontal reflection of transposed row notation gives source column notation. -/
def normalizedColumnsEquiv : YoungDiagram ≃ PositiveColumns where
  toFun μ := ⟨μ.transpose.rowLens.reverse, μ.transpose.rowLens_sorted.reverse,
    fun x hx => μ.transpose.pos_of_mem_rowLens x (List.mem_reverse.mp hx)⟩
  invFun b := (YoungDiagram.ofRowLens b.val.reverse b.property.1.reverse).transpose
  left_inv μ := by
    change (YoungDiagram.ofRowLens μ.transpose.rowLens _).transpose = μ
    rw [YoungDiagram.ofRowLens_to_rowLens_eq_self, YoungDiagram.transpose_transpose]
  right_inv b := by
    apply Subtype.ext
    change ((YoungDiagram.ofRowLens b.val.reverse _).transpose.transpose.rowLens).reverse = b.val
    rw [YoungDiagram.transpose_transpose, YoungDiagram.rowLens_ofRowLens_eq_self]
    · exact List.reverse_reverse _
    · intro x hx
      exact b.property.2 x (List.mem_reverse.mp hx)

private theorem column_cell (b : PositiveColumns) (r : ℕ) (i : Fin b.val.length) :
    r < b.val[i.val] ↔ i.rev.val < (normalizedColumnsEquiv.symm b).rowLen r := by
  change r < b.val[i.val] ↔ i.rev.val <
    (YoungDiagram.ofRowLens b.val.reverse b.property.1.reverse).transpose.rowLen r
  rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_transpose,
    YoungDiagram.mem_ofRowLens]
  have hrev : b.val.reverse[i.rev.val]'(by simpa using i.rev.isLt) = b.val[i.val] := by
    rw [List.getElem_reverse]
    congr 1
    have hi := i.isLt
    simp only [Fin.val_rev]
    omega
  constructor
  · intro h
    exact ⟨by simpa using i.rev.isLt, by simpa only [hrev] using h⟩
  · rintro ⟨hi,h⟩
    simpa only [hrev] using h

private theorem columns_row_bound (b : PositiveColumns) (r : ℕ) :
    (normalizedColumnsEquiv.symm b).rowLen r ≤ b.val.length := by
  by_contra! h
  have hm := YoungDiagram.mem_iff_lt_rowLen.mpr h
  change (r,b.val.length) ∈
    (YoungDiagram.ofRowLens b.val.reverse b.property.1.reverse).transpose at hm
  rw [YoungDiagram.mem_transpose, YoungDiagram.mem_ofRowLens] at hm
  obtain ⟨hi,_⟩ := hm
  simpa using hi

private theorem columns_row_count (b : PositiveColumns) (r : ℕ) :
    Fintype.card {i : Fin b.val.length // r < b.val[i.val]} =
      (normalizedColumnsEquiv.symm b).rowLen r := by
  classical
  let w := (normalizedColumnsEquiv.symm b).rowLen r
  let e : {i : Fin b.val.length // r < b.val[i.val]} ≃ Fin w :=
    { toFun := fun i => ⟨i.val.rev.val, (column_cell b r i.val).mp i.property⟩
      invFun := fun k =>
        let i : Fin b.val.length := ⟨k.val, lt_of_lt_of_le k.isLt (columns_row_bound b r)⟩
        ⟨i.rev, (column_cell b r i.rev).mpr (by simpa only [Fin.rev_rev] using k.isLt)⟩
      left_inv := by intro i; apply Subtype.ext; exact Fin.rev_rev i.val
      right_inv := by intro k; apply Fin.ext; dsimp only; rw [Fin.rev_rev] }
  exact (Fintype.card_congr e).trans (Fintype.card_fin w)

/-- Direct cell counting on positive source column tuples, at any absolute level. -/
def columnLevel (m : ℕ) (b : PositiveColumns) (p : ℕ) : ℕ :=
  ∑ j : Fin m, Fintype.card {i : Fin b.val.length // m*p+j.val < b.val[i.val]}

private theorem columnLevel_shape (m : ℕ) (b : PositiveColumns) (p : ℕ) :
    columnLevel m b p = shapeLevel m (normalizedColumnsEquiv.symm b) p := by
  apply Finset.sum_congr rfl
  intro j _
  exact columns_row_count b _

/-- Exact nonempty-level tuple equality, with l(empty) defined to be the empty tuple. -/
abbrev LFiber (m : ℕ) (c : List ℕ) :=
  {b : PositiveColumns // (∀ x ∈ c, 0 < x) ∧
    ∀ p : ℕ, columnLevel m b p = c.reverse.getD p 0}

private def sourceShapeEquiv (m : ℕ) (c : List ℕ) (hc : ∀ x ∈ c, 0 < x) :
    LFiber m c ≃ ShapeFiber m c.reverse :=
  normalizedColumnsEquiv.symm.subtypeEquiv (fun b => by
    constructor
    · intro h p
      rw [← columnLevel_shape]
      exact h.2 p
    · intro h
      refine ⟨hc, ?_⟩
      intro p
      rw [columnLevel_shape]
      exact h p)

/-- The whole normalized 2015 l-fiber is evaluated for every positive m and every target tuple. -/
theorem source2015_count (m : ℕ) (hm : 0 < m) (c : List ℕ) :
    (Nat.card (LFiber m c) : ℤ) =
      if (∀ x ∈ c, 0 < x) then
        count (m-1) (c.reverse.getD 0 0) c.reverse
          ⟨c.reverse.getD 0 0, Nat.lt_succ_self _⟩ else 0 := by
  classical
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  split_ifs with hc
  · rw [Nat.card_congr (sourceShapeEquiv (r+1) c hc), all_width_count]
  · haveI : IsEmpty (LFiber (r+1) c) := ⟨fun b => hc b.property.1⟩
    simp

end D5.S3.Combinatorics.Partitions.BarreseSourceNormalization
