/- GID: D5/S3/Combinatorics/Partitions/BarreseAllWidths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/BarreseAllWidths
   mirror-E: none(waiver:derived-width-normalization)
   anchors: [D5/S3/Combinatorics/Partitions/BarreseOrderedLevels]
   utility: none
   digest: The bottom level total bounds every normalized shape in the unrestricted-width fiber. -/

import D5.S3.Combinatorics.Partitions.BarreseOrderedLevels
import Mathlib.Data.List.GetD
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.BarreseAllWidths
open D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
open D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open D5.S3.Combinatorics.Partitions.FerrersLevelGluing
open D5.S3.Combinatorics.Partitions.BarreseOrderedLevels
open scoped BigOperators

/-- The absolute p-th bottom-up level total of a normalized finite shape. -/
def shapeLevel (m : ℕ) (μ : YoungDiagram) (p : ℕ) : ℕ :=
  ∑ j : Fin m, μ.rowLen (m*p+j.val)

/-- Prescribed level totals with zero extension above the supplied list.
    No bound on shape width or height is imposed here. -/
abbrev ShapeFiber (m : ℕ) (a : List ℕ) :=
  {μ : YoungDiagram // ∀ p : ℕ, shapeLevel m μ p = a.getD p 0}

private theorem first_row_le_level (r : ℕ) (μ : YoungDiagram) (p : ℕ) :
    μ.rowLen ((r+1)*p) ≤ shapeLevel (r+1) μ p := by
  have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (r+1)))) =>
    Nat.zero_le (μ.rowLen ((r+1)*p+j.val))) (Finset.mem_univ (0 : Fin (r+1)))
  simpa [shapeLevel] using hh

/-- Every possible positive-column width is bounded by the prescribed bottom-level total. -/
theorem width_bound (r : ℕ) (a : List ℕ) (μ : ShapeFiber (r+1) a) :
    μ.val.rowLen 0 ≤ a.getD 0 0 := by
  have hh := first_row_le_level r μ.val 0
  simpa only [Nat.mul_zero, μ.property 0] using hh

private theorem height_bound (r : ℕ) (a : List ℕ) (μ : ShapeFiber (r+1) a)
    (i j : ℕ) (h : (i,j) ∈ μ.val) : i < (r+1)*a.length := by
  have hzero : shapeLevel (r+1) μ.val a.length = 0 := by
    rw [μ.property, List.getD_eq_default _ _ (le_refl _)]
  have hf := first_row_le_level r μ.val a.length
  have hrow : μ.val.rowLen ((r+1)*a.length) = 0 := by omega
  by_contra! hn
  have hm : ((r+1)*a.length,0) ∈ μ.val := μ.val.up_left_mem hn (Nat.zero_le j) h
  have hh := YoungDiagram.mem_iff_lt_rowLen.mp hm
  omega

private def shapeRows (r : ℕ) (a : List ℕ) (μ : ShapeFiber (r+1) a) :
    Rows ((r+1)*a.length) (a.getD 0 0) :=
  ⟨fun i => ⟨μ.val.rowLen i, Nat.lt_succ_of_le
      ((μ.val.rowLen_anti 0 i (Nat.zero_le _)).trans (width_bound r a μ))⟩,
    fun i j hij => Fin.le_iff_val_le_val.mpr (μ.val.rowLen_anti i j hij)⟩

private theorem diagram_shapeRows (r : ℕ) (a : List ℕ) (μ : ShapeFiber (r+1) a) :
    diagram (shapeRows r a μ) = μ.val := by
  ext ⟨i,j⟩
  change (i,j) ∈ diagram (shapeRows r a μ) ↔ (i,j) ∈ μ.val
  rw [diagram_mem]
  constructor
  · rintro ⟨hi,hj⟩
    exact YoungDiagram.mem_iff_lt_rowLen.mpr hj
  · intro h
    exact ⟨height_bound r a μ i j h, YoungDiagram.mem_iff_lt_rowLen.mp h⟩

private def shapeFlatEquiv (r : ℕ) (a : List ℕ) :
    ShapeFiber (r+1) a ≃ FlatFiber r (a.getD 0 0) a
      ⟨a.getD 0 0, Nat.lt_succ_self _⟩ where
  toFun μ := ⟨(shapeRows r a μ).val, (shapeRows r a μ).property,
    fun j => Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ (Fin.isLt _)), by
      intro p
      have hp := μ.property p.val
      simpa [shapeLevel, shapeRows, rowIndex, List.getD_eq_getElem _ _ p.isLt] using hp⟩
  invFun x := ⟨diagram ⟨x.val,x.property.1⟩, by
    intro p
    by_cases hp : p < a.length
    · have hs := x.property.2.2 ⟨p,hp⟩
      rw [List.getD_eq_getElem _ _ hp]
      unfold shapeLevel
      apply Eq.trans _ hs
      apply Finset.sum_congr rfl
      intro j _
      exact diagram_rowLen ⟨x.val,x.property.1⟩ (rowIndex (r+1) a.length ⟨p,hp⟩ j)
    · conv_rhs => rw [List.getD_eq_default _ _ (show a.length ≤ p by omega)]
      apply Finset.sum_eq_zero
      intro j _
      apply Nat.eq_zero_of_not_pos
      intro hz
      have hm : ((r+1)*p+j.val,0) ∈ diagram ⟨x.val,x.property.1⟩ :=
        YoungDiagram.mem_iff_lt_rowLen.mpr hz
      obtain ⟨hi,_⟩ := (diagram_mem ⟨x.val,x.property.1⟩ _ _).mp hm
      have hb := Nat.mul_le_mul_left (r+1) (show a.length ≤ p by omega)
      omega⟩
  left_inv μ := by
    apply Subtype.ext
    exact diagram_shapeRows r a μ
  right_inv x := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact diagram_rowLen ⟨x.val,x.property.1⟩ i

/-- Unique padding to the width derived from the prescribed data. -/
def normalizedPaddingEquiv (r : ℕ) (a : List ℕ) :
    ShapeFiber (r+1) a ≃ NativeFiber (r+1) (a.getD 0 0) a :=
  (shapeFlatEquiv r a).trans (nativeRowsEquiv r (a.getD 0 0) a).symm

/-- All widths are counted after the width bound is derived from the original data. -/
theorem all_width_count (r : ℕ) (a : List ℕ) :
    (Nat.card (ShapeFiber (r+1) a) : ℤ) =
      count r (a.getD 0 0) a ⟨a.getD 0 0, Nat.lt_succ_self _⟩ := by
  classical
  rw [Nat.card_congr (normalizedPaddingEquiv r a), Nat.card_eq_fintype_card, native_count]

end D5.S3.Combinatorics.Partitions.BarreseAllWidths
