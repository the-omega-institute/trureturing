/- GID: D5/S3/Combinatorics/Partitions/BarreseOrderedLevels
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/BarreseOrderedLevels
   mirror-E: none(waiver:ordered-level-native-count)
   anchors: [D5/S3/Combinatorics/Partitions/FerrersLevelGluing]
   utility: none
   digest: Native fixed-slot Ferrers boards are counted by the finite Gaussian recurrence. -/

import D5.S3.Combinatorics.Partitions.FerrersLevelGluing
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.BarreseOrderedLevels
open D5.S3.Combinatorics.Partitions.FerrersRowCoordinates
open D5.S3.Combinatorics.Partitions.FerrersLevelCounting
open D5.S3.Combinatorics.Partitions.FerrersLevelGluing
open scoped BigOperators

/-- The number of literal occupied cells in a source level, counted row by row. -/
def levelTotal {m U t : ℕ} (b : Board U (m*t)) (p : Fin t) : ℕ :=
  ∑ j : Fin m, Fintype.card {i : Fin U // m*p.val+j.val < (b.val i).val}

/-- All source column tuples with the prescribed bottom-to-top level totals. -/
abbrev NativeFiber (m U : ℕ) (a : List ℕ) :=
  {b : Board U (m*a.length) // ∀ p : Fin a.length, levelTotal b p = a[p.val]}

private theorem levelTotal_rows {m U t : ℕ} (b : Board U (m*t)) (p : Fin t) :
    levelTotal b p = ∑ j : Fin m,
      ((boardRowsEquiv U (m*t) b).val (rowIndex m t p j)).val := by
  apply Finset.sum_congr rfl
  intro j _
  exact board_row_count b (rowIndex m t p j)

def nativeRowsEquiv (r U : ℕ) (a : List ℕ) :
    NativeFiber (r+1) U a ≃ FlatFiber r U a ⟨U, Nat.lt_succ_self U⟩ where
  toFun b := ⟨(boardRowsEquiv U ((r+1)*a.length) b.val).val,
    (boardRowsEquiv U ((r+1)*a.length) b.val).property,
    fun j => Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ (Fin.isLt _)), by
      intro p
      rw [← levelTotal_rows]
      exact b.property p⟩
  invFun x := ⟨(boardRowsEquiv U ((r+1)*a.length)).symm ⟨x.val,x.property.1⟩, by
    intro p
    rw [levelTotal_rows, Equiv.apply_symm_apply]
    exact x.property.2.2 p⟩
  left_inv b := by
    apply Subtype.ext
    exact (boardRowsEquiv U ((r+1)*a.length)).symm_apply_apply b.val
  right_inv x := by
    apply Subtype.ext
    change ((boardRowsEquiv U ((r+1)*a.length))
      ((boardRowsEquiv U ((r+1)*a.length)).symm ⟨x.val,x.property.1⟩)).val = x.val
    exact congrArg (fun z : Rows ((r+1)*a.length) U => z.val)
      ((boardRowsEquiv U ((r+1)*a.length)).apply_symm_apply
      ⟨x.val,x.property.1⟩)

/-- Complete fixed-width and fixed-height enumeration for every positive level size. -/
theorem native_count (r U : ℕ) (a : List ℕ) :
    (Fintype.card (NativeFiber (r+1) U a) : ℤ) =
      count r U a ⟨U, Nat.lt_succ_self U⟩ := by
  classical
  rw [Fintype.card_congr (nativeRowsEquiv r U a), flat_card]

/-- The original 2023 ambient count, with the exact top-down source orientation. -/
theorem source2023_count (m n : ℕ) (hm : 0 < m) (l : Fin n → ℕ) :
    (Fintype.card {b : Board n (m*n) //
      ∀ p : Fin n, levelTotal b p = l p.rev} : ℤ) =
      count (m-1) n (List.ofFn (fun p => l p.rev)) ⟨n, Nat.lt_succ_self n⟩ := by
  classical
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  generalize ha : List.ofFn (fun p => l p.rev) = a
  have hlen : a.length = n := by rw [← ha, List.length_ofFn]
  subst n
  have hentry (p : Fin a.length) : a[p.val] = l p.rev := by
    have hp := congrArg (fun xs : List ℕ => xs.getD p.val 0) ha
    have hpl : p.val < (List.ofFn (fun p => l p.rev)).length := by simpa using p.isLt
    rw [List.getD_eq_getElem _ _ hpl, List.getD_eq_getElem _ _ p.isLt] at hp
    simpa only [List.getElem_ofFn] using hp.symm
  let e : {b : Board a.length ((r+1)*a.length) //
      ∀ p : Fin a.length, levelTotal b p = l p.rev} ≃ NativeFiber (r+1) a.length a :=
    Equiv.subtypeEquivRight (fun b => by
      constructor
      · intro h p; rw [hentry p]; exact h p
      · intro h p; rw [← hentry p]; exact h p)
  exact (congrArg (fun z : ℕ => (z : ℤ)) (Fintype.card_congr e)).trans
    (native_count r a.length a)

end D5.S3.Combinatorics.Partitions.BarreseOrderedLevels
