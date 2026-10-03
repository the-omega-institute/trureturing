/- GID: D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements
   mirror-E: none(waiver:uniform-placement-existence-and-counts)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Basic]
   utility: none
   digest: Complete permutation-grid placements obtained by extreme deletion and size induction. -/

import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDeletions
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookPlacements

open D5.S3.Combinatorics.CrosswordRookCounts (Cell IsRookPlacement rookCount)
open D5.S3.Combinatorics.CrosswordPermutationGridRefutation (permGrid)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords
  (symmetries record_prefix_forces_neighbor placement_card)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDeletions (corner_lift interior_lift)

theorem count_positive {n : ℕ} (positive : 1 ≤ n) (w : Equiv.Perm (Fin n)) :
    0 < rookCount (permGrid w) := by
  classical
  have induction : ∀ size : ℕ, 1 ≤ size → ∀ board : Equiv.Perm (Fin size),
      0 < rookCount (permGrid board) := by
    intro size
    induction size with
    | zero => intro h; omega
    | succ size ih =>
      intro _ board
      by_cases empty : size = 0
      · subst size
        have white : permGrid board = ∅ := by
          ext cell
          have heq : board cell.1 = cell.2 := by
            apply Fin.ext
            have hfirst := (board cell.1).isLt
            have hsecond := cell.2.isLt
            omega
          simp [permGrid, heq]
        have placement : IsRookPlacement (∅ : Finset (Cell 1)) ∅ := by
          simp [IsRookPlacement]
        rw [rookCount, white, Finset.card_pos]
        exact ⟨∅, Finset.mem_filter.mpr ⟨by simp, placement⟩⟩
      · have positive_small : 1 ≤ size := by omega
        let penultimate : Fin size := ⟨size - 1, by omega⟩
        let maximum : Fin (size + 1) := Fin.last size
        let second := penultimate.castSucc
        have second_ne : second ≠ maximum := Fin.castSucc_ne_last _
        have oriented (source : Equiv.Perm (Fin (size + 1)))
            (above : source.symm second < source.symm maximum) :
            0 < rookCount (permGrid source) := by
          let pivot := source.symm maximum
          have hpivot : source pivot = Fin.last size := source.apply_symm_apply _
          have hrestrict : ∀ row : Fin (size + 1),
              row ≠ pivot ↔ source row ≠ Fin.last size := by
            intro row
            rw [← hpivot]
            exact source.injective.ne_iff.symm
          let restricted := source.subtypeEquiv
            (p := fun row => row ≠ pivot) (q := fun column => column ≠ Fin.last size) hrestrict
          let smaller : Equiv.Perm (Fin size) :=
            ((finSuccAboveEquiv pivot).trans restricted).trans
              (finSuccAboveEquiv (Fin.last size)).symm
          have inherited (row : Fin size) :
              source (pivot.succAbove row) = (smaller row).castSucc := by
            have heq := (finSuccAboveEquiv (Fin.last size)).apply_symm_apply
              (restricted (finSuccAboveEquiv pivot row))
            have hval := congrArg Subtype.val heq
            change (Fin.last size).succAbove (smaller row) =
              source (pivot.succAbove row) at hval
            rw [Fin.succAbove_last] at hval
            exact hval.symm
          have inequality : rookCount (permGrid smaller) ≤ rookCount (permGrid source) := by
            by_cases last : pivot = Fin.last size
            · apply corner_lift positive_small smaller source
              · simpa only [← last] using hpivot
              · intro row
                simpa only [last, Fin.succAbove_last] using inherited row
            · apply interior_lift positive_small smaller source pivot
              · constructor
                · have hnonzero : 0 < pivot.val := by
                    have hlt : (source.symm second).val < pivot.val := above
                    omega
                  exact hnonzero
                · exact Fin.val_lt_last last
              · exact hpivot
              · exact inherited
              · have hinverse : pivot.succAbove (smaller.symm penultimate) =
                    source.symm second := by
                  apply source.injective
                  rw [inherited, smaller.apply_symm_apply, source.apply_symm_apply]
                change pivot.succAbove (smaller.symm penultimate) < pivot
                rw [hinverse]
                exact above
          exact lt_of_lt_of_le (ih positive_small smaller) inequality
        by_cases above : board.symm second < board.symm maximum
        · exact oriented board above
        · let reflected := Fin.revPerm.trans board
          have different : board.symm second ≠ board.symm maximum :=
            board.symm.injective.ne second_ne
          have reverse : board.symm maximum < board.symm second :=
            lt_of_le_of_ne (le_of_not_gt above) different.symm
          have reflected_above : reflected.symm second < reflected.symm maximum := by
            change (board.symm second).rev < (board.symm maximum).rev
            exact Fin.rev_lt_rev.mpr reverse
          have reflection_count : rookCount (permGrid board) = rookCount (permGrid reflected) :=
            (symmetries (by omega) board).2.2.1.1
          rw [reflection_count]
          exact oriented reflected reflected_above
  exact induction n positive w

theorem overlapping_count {n : ℕ} (positive : 1 ≤ n) (w : Equiv.Perm (Fin n))
    (increasing decreasing : Finset (Fin n)) (cover : increasing ∪ decreasing = Finset.univ)
    (inc : ∀ row ∈ increasing, ∀ other ∈ increasing, row < other → w row < w other)
    (dec : ∀ row ∈ decreasing, ∀ other ∈ decreasing, row < other → w other < w row)
    (pivot : Fin n) (pivot_inc : pivot ∈ increasing) (pivot_dec : pivot ∈ decreasing) :
    rookCount (permGrid w) = 1 := by
  classical
  have west (permutation : Equiv.Perm (Fin n)) (part_inc part_dec : Finset (Fin n))
      (hcover : part_inc ∪ part_dec = Finset.univ)
      (hinc : ∀ row ∈ part_inc, ∀ other ∈ part_inc, row < other →
        permutation row < permutation other)
      (hdec : ∀ row ∈ part_dec, ∀ other ∈ part_dec, row < other →
        permutation other < permutation row)
      (center : Fin n) (hcenter_inc : center ∈ part_inc) (hcenter_dec : center ∈ part_dec)
      (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid permutation) rooks) :
      ∀ column previous : Fin n, previous.val + 1 = column.val →
        column ≤ permutation center → (permutation.symm column, previous) ∈ rooks := by
    have all (row : Fin n) : row ∈ part_inc ∨ row ∈ part_dec := by
      exact Finset.mem_union.mp (hcover.symm ▸ Finset.mem_univ row)
    have nw (row : Fin n) (hrow : row < center) (hvalue : permutation row ≤ permutation center) :
        row ∈ part_inc := by
      rcases all row with hmem | hmem
      · exact hmem
      · exact False.elim (not_lt_of_ge hvalue (hdec row hmem center hcenter_dec hrow))
    have sw (row : Fin n) (hrow : center < row) (hvalue : permutation row ≤ permutation center) :
        row ∈ part_dec := by
      rcases all row with hmem | hmem
      · exact False.elim (not_lt_of_ge hvalue (hinc center hcenter_inc row hmem hrow))
      · exact hmem
    have records : ∀ column : Fin n, column.val < (permutation center).val + 1 →
        (∀ later : Fin n, column < later → later.val < (permutation center).val + 1 →
          permutation.symm column < permutation.symm later) ∨
        (∀ later : Fin n, column < later → later.val < (permutation center).val + 1 →
          permutation.symm later < permutation.symm column) := by
      intro column hcolumn
      have hvalue : permutation (permutation.symm column) ≤ permutation center := by
        rw [permutation.apply_symm_apply]
        change column.val ≤ (permutation center).val
        omega
      rcases lt_trichotomy (permutation.symm column) center with hbefore | heq | hafter
      · left
        intro later hlt hlater
        have hcol_ne : permutation.symm later ≠ permutation.symm column :=
          permutation.symm.injective.ne (ne_of_gt hlt)
        by_contra hnot
        have hreverse : permutation.symm later < permutation.symm column :=
          lt_of_le_of_ne (le_of_not_gt hnot) hcol_ne
        have hlvalue : permutation (permutation.symm later) ≤ permutation center := by
          rw [permutation.apply_symm_apply]
          change later.val ≤ (permutation center).val
          omega
        have bad := hinc _ (nw _ (hreverse.trans hbefore) hlvalue) _
          (nw _ hbefore hvalue) hreverse
        simp only [permutation.apply_symm_apply] at bad
        exact lt_asymm hlt bad
      · left
        intro later hlt hlater
        have hcol_eq : column = permutation center := by
          rw [← heq, permutation.apply_symm_apply]
        have hval := congrArg Fin.val hcol_eq
        have hltval : column.val < later.val := hlt
        omega
      · right
        intro later hlt hlater
        have hcol_ne : permutation.symm column ≠ permutation.symm later :=
          permutation.symm.injective.ne (ne_of_lt hlt)
        by_contra hnot
        have hreverse : permutation.symm column < permutation.symm later :=
          lt_of_le_of_ne (le_of_not_gt hnot) hcol_ne
        have hlvalue : permutation (permutation.symm later) ≤ permutation center := by
          rw [permutation.apply_symm_apply]
          change later.val ≤ (permutation center).val
          omega
        have bad := hdec _ (sw _ hafter hvalue) _
          (sw _ (hafter.trans hreverse) hlvalue) hreverse
        simp only [permutation.apply_symm_apply] at bad
        exact lt_asymm hlt bad
    intro column previous hprevious hbound
    apply record_prefix_forces_neighbor positive permutation rooks placement
      ((permutation center).val + 1) records column previous hprevious
    have hle : column.val ≤ (permutation center).val := hbound
    omega
  have reflection_cover (permutation : Equiv.Perm (Fin n)) (part_inc part_dec : Finset (Fin n))
      (hinc : ∀ row ∈ part_inc, ∀ other ∈ part_inc, row < other →
        permutation row < permutation other)
      (hdec : ∀ row ∈ part_dec, ∀ other ∈ part_dec, row < other →
        permutation other < permutation row) :
      (∀ row ∈ part_dec, ∀ other ∈ part_dec, row < other →
        (permutation.trans Fin.revPerm) row < (permutation.trans Fin.revPerm) other) ∧
      (∀ row ∈ part_inc, ∀ other ∈ part_inc, row < other →
        (permutation.trans Fin.revPerm) other < (permutation.trans Fin.revPerm) row) := by
    exact ⟨fun row hrow other hother hlt => Fin.rev_lt_rev.mpr (hdec row hrow other hother hlt),
      fun row hrow other hother hlt => Fin.rev_lt_rev.mpr (hinc row hrow other hother hlt)⟩
  have inverse_cover :
      (∀ row ∈ increasing.image w, ∀ other ∈ increasing.image w, row < other →
        w.symm row < w.symm other) ∧
      (∀ row ∈ decreasing.image w, ∀ other ∈ decreasing.image w, row < other →
        w.symm other < w.symm row) := by
    constructor
    · intro row hrow other hother hlt
      obtain ⟨first, hfirst, rfl⟩ := Finset.mem_image.mp hrow
      obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp hother
      simp only [w.symm_apply_apply]
      by_contra hnot
      have hne : second ≠ first := fun heq => (ne_of_lt hlt) (congrArg w heq.symm)
      exact lt_asymm hlt (inc second hsecond first hfirst
        (lt_of_le_of_ne (le_of_not_gt hnot) hne))
    · intro row hrow other hother hlt
      obtain ⟨first, hfirst, rfl⟩ := Finset.mem_image.mp hrow
      obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp hother
      simp only [w.symm_apply_apply]
      by_contra hnot
      have hne : first ≠ second := fun heq => (ne_of_lt hlt) (congrArg w heq)
      exact lt_asymm hlt (dec first hfirst second hsecond
        (lt_of_le_of_ne (le_of_not_gt hnot) hne))
  have inverse_union : increasing.image w ∪ decreasing.image w = Finset.univ := by
    rw [← Finset.image_union, cover]
    ext column
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact w.surjective column
  have inverse_inc : w pivot ∈ increasing.image w :=
    Finset.mem_image.mpr ⟨pivot, pivot_inc, rfl⟩
  have inverse_dec : w pivot ∈ decreasing.image w :=
    Finset.mem_image.mpr ⟨pivot, pivot_dec, rfl⟩
  let black_column := fun index : Fin (n - 1) =>
    (⟨if index.val < (w pivot).val then index.val + 1 else index.val, by
      split_ifs <;> have hbound := index.isLt <;> omega⟩ : Fin n)
  let white_column := fun index : Fin (n - 1) =>
    (⟨if index.val < (w pivot).val then index.val else index.val + 1, by
      split_ifs <;> have hbound := index.isLt <;> omega⟩ : Fin n)
  let black_row := fun index : Fin (n - 1) =>
    (⟨if index.val < pivot.val then index.val + 1 else index.val, by
      split_ifs <;> have hbound := index.isLt <;> omega⟩ : Fin n)
  let white_row := fun index : Fin (n - 1) =>
    (⟨if index.val < pivot.val then index.val else index.val + 1, by
      split_ifs <;> have hbound := index.isLt <;> omega⟩ : Fin n)
  let horizontal := fun index : Fin (n - 1) => (w.symm (black_column index), white_column index)
  let vertical := fun index : Fin (n - 1) => (white_row index, w (black_row index))
  let forced := Finset.univ.image horizontal ∪ Finset.univ.image vertical
  have horizontal_injective : Function.Injective horizontal := by
    intro first second heq
    have hval := congrArg (fun cell : Cell n => cell.2.val) heq
    dsimp only [horizontal, white_column] at hval
    apply Fin.ext
    split_ifs at hval <;> omega
  have vertical_injective : Function.Injective vertical := by
    intro first second heq
    have hval := congrArg (fun cell : Cell n => cell.1.val) heq
    dsimp only [vertical, white_row] at hval
    apply Fin.ext
    split_ifs at hval <;> omega
  have all_colors (row : Fin n) : row ∈ increasing ∨ row ∈ decreasing := by
    exact Finset.mem_union.mp (cover.symm ▸ Finset.mem_univ row)
  have inc_color (row : Fin n)
      (same_side : (row ≤ pivot ∧ w row ≤ w pivot) ∨
        (pivot ≤ row ∧ w pivot ≤ w row)) :
      row ∈ increasing := by
    by_cases heq : row = pivot
    · exact heq ▸ pivot_inc
    rcases all_colors row with hmem | hmem
    · exact hmem
    · rcases same_side with hbefore | hafter
      · exact False.elim (not_lt_of_ge hbefore.2
          (dec row hmem pivot pivot_dec (lt_of_le_of_ne hbefore.1 heq)))
      · exact False.elim (not_lt_of_ge hafter.2
          (dec pivot pivot_dec row hmem (lt_of_le_of_ne hafter.1 (Ne.symm heq))))
  have dec_color (row : Fin n)
      (opposite_side : (row ≤ pivot ∧ w pivot ≤ w row) ∨
        (pivot ≤ row ∧ w row ≤ w pivot)) :
      row ∈ decreasing := by
    by_cases heq : row = pivot
    · exact heq ▸ pivot_dec
    rcases all_colors row with hmem | hmem
    · rcases opposite_side with hbefore | hafter
      · exact False.elim (not_lt_of_ge hbefore.2
          (inc row hmem pivot pivot_inc (lt_of_le_of_ne hbefore.1 heq)))
      · exact False.elim (not_lt_of_ge hafter.2
          (inc pivot pivot_inc row hmem (lt_of_le_of_ne hafter.1 (Ne.symm heq))))
    · exact hmem
  have disjoint : Disjoint (Finset.univ.image horizontal) (Finset.univ.image vertical) := by
    apply Finset.disjoint_left.mpr
    intro cell hhorizontal hvertical
    obtain ⟨column_index, _, rfl⟩ := Finset.mem_image.mp hhorizontal
    obtain ⟨row_index, _, heq⟩ := Finset.mem_image.mp hvertical
    let first := w.symm (black_column column_index)
    let second := black_row row_index
    have hrow := congrArg (fun cell : Cell n => cell.1.val) heq
    have hcol := congrArg (fun cell : Cell n => cell.2.val) heq
    have first_value := w.apply_symm_apply (black_column column_index)
    have hfirst := congrArg Fin.val first_value
    change (white_row row_index).val = first.val at hrow
    change (w second).val = (white_column column_index).val at hcol
    change (w first).val = (black_column column_index).val at hfirst
    have hsecond : second.val =
        if row_index.val < pivot.val then row_index.val + 1 else row_index.val := rfl
    simp only [white_column, black_column, white_row] at hrow hcol hfirst
    by_cases hc : column_index.val < (w pivot).val <;>
      by_cases hr : row_index.val < pivot.val
    · simp only [if_pos hc, if_pos hr] at hrow hcol hfirst hsecond
      have first_inc := inc_color first
        (Or.inl ⟨by change first.val ≤ pivot.val; omega,
          by change (w first).val ≤ (w pivot).val; omega⟩)
      have second_inc := inc_color second
        (Or.inl ⟨by change second.val ≤ pivot.val; omega,
          by change (w second).val ≤ (w pivot).val; omega⟩)
      have bad := inc _ first_inc _ second_inc
        (by change first.val < second.val; omega)
      have hbad : (w first).val < (w second).val := bad
      omega
    · simp only [if_pos hc, if_neg hr] at hrow hcol hfirst hsecond
      have first_dec := dec_color first
        (Or.inr ⟨by change pivot.val ≤ first.val; omega,
          by change (w first).val ≤ (w pivot).val; omega⟩)
      have second_dec := dec_color second
        (Or.inr ⟨by change pivot.val ≤ second.val; omega,
          by change (w second).val ≤ (w pivot).val; omega⟩)
      have bad := dec _ second_dec _ first_dec
        (by change second.val < first.val; omega)
      have hbad : (w first).val < (w second).val := bad
      omega
    · simp only [if_neg hc, if_pos hr] at hrow hcol hfirst hsecond
      have first_dec := dec_color first
        (Or.inl ⟨by change first.val ≤ pivot.val; omega,
          by change (w pivot).val ≤ (w first).val; omega⟩)
      have second_dec := dec_color second
        (Or.inl ⟨by change second.val ≤ pivot.val; omega,
          by change (w pivot).val ≤ (w second).val; omega⟩)
      have bad := dec _ first_dec _ second_dec
        (by change first.val < second.val; omega)
      have hbad : (w second).val < (w first).val := bad
      omega
    · simp only [if_neg hc, if_neg hr] at hrow hcol hfirst hsecond
      have first_inc := inc_color first
        (Or.inr ⟨by change pivot.val ≤ first.val; omega,
          by change (w pivot).val ≤ (w first).val; omega⟩)
      have second_inc := inc_color second
        (Or.inr ⟨by change pivot.val ≤ second.val; omega,
          by change (w pivot).val ≤ (w second).val; omega⟩)
      have bad := inc _ second_inc _ first_inc
        (by change second.val < first.val; omega)
      have hbad : (w second).val < (w first).val := bad
      omega
  have forced_card : forced.card = 2 * n - 2 := by
    rw [Finset.card_union_of_disjoint disjoint,
      Finset.card_image_of_injective _ horizontal_injective,
      Finset.card_image_of_injective _ vertical_injective]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have forced_subset (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid w) rooks) :
      forced ⊆ rooks := by
    have transposed := (symmetries positive w).2.2.2.1 rooks placement
    have reflected := (symmetries positive w).2.2.2.2.1 rooks placement
    have both := (symmetries positive w.symm).2.2.2.2.1 _ transposed
    have reflected_cover := reflection_cover w increasing decreasing inc dec
    have both_cover := reflection_cover w.symm (increasing.image w) (decreasing.image w)
      inverse_cover.1 inverse_cover.2
    intro cell hcell
    rcases Finset.mem_union.mp hcell with hcell | hcell
    · obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hcell
      by_cases hleft : index.val < (w pivot).val
      · apply west w increasing decreasing cover inc dec pivot pivot_inc pivot_dec rooks placement
        · simp only [white_column, black_column, if_pos hleft]
        · change (black_column index).val ≤ (w pivot).val
          simp only [black_column, if_pos hleft]
          omega
      · have hforce := west (w.trans Fin.revPerm) decreasing increasing
          (by rw [Finset.union_comm]; exact cover) reflected_cover.1 reflected_cover.2
          pivot pivot_dec pivot_inc _ reflected (black_column index).rev (white_column index).rev
          (by simp only [white_column, black_column, if_neg hleft, Fin.val_rev]; omega)
          (by change (black_column index).rev ≤ (w pivot).rev
              rw [Fin.rev_le_rev]; change (w pivot).val ≤ (black_column index).val
              simp only [black_column, if_neg hleft]; omega)
        obtain ⟨original, horiginal, heq⟩ := Finset.mem_image.mp hforce
        have hrow := congrArg Prod.fst heq
        have hcol := congrArg Prod.snd heq
        have hrow' : original.1 = w.symm (black_column index) := by
          simpa only [Equiv.symm_trans_apply, Fin.revPerm_symm, Fin.revPerm_apply,
            Fin.rev_rev] using hrow
        have hcol' : original.2 = white_column index := by
          have hback := congrArg Fin.rev hcol
          simpa only [Fin.rev_rev] using hback
        have heq' : original = horizontal index := Prod.ext hrow' hcol'
        exact heq' ▸ horiginal
    · obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hcell
      by_cases habove : index.val < pivot.val
      · have hforce := west w.symm (increasing.image w) (decreasing.image w) inverse_union
          inverse_cover.1 inverse_cover.2 (w pivot) inverse_inc inverse_dec _ transposed
          (black_row index) (white_row index)
          (by simp only [white_row, black_row, if_pos habove])
          (by rw [w.symm_apply_apply]; change (black_row index).val ≤ pivot.val
              simp only [black_row, if_pos habove]; omega)
        obtain ⟨original, horiginal, heq⟩ := Finset.mem_image.mp hforce
        have hrow := congrArg Prod.fst heq
        have hcol := congrArg Prod.snd heq
        have heq' : original = vertical index := by
          exact Prod.ext hcol (by simpa only [Equiv.symm_symm, Prod.fst_swap] using hrow)
        exact heq' ▸ horiginal
      · have hforce := west (w.symm.trans Fin.revPerm)
          (decreasing.image w) (increasing.image w)
          (by rw [Finset.union_comm]; exact inverse_union) both_cover.1 both_cover.2
          (w pivot) inverse_dec inverse_inc _ both (black_row index).rev (white_row index).rev
          (by simp only [white_row, black_row, if_neg habove, Fin.val_rev]; omega)
          (by change (black_row index).rev ≤ (w.symm (w pivot)).rev
              rw [w.symm_apply_apply, Fin.rev_le_rev]
              change pivot.val ≤ (black_row index).val
              simp only [black_row, if_neg habove]; omega)
        obtain ⟨first, hfirst, heq⟩ := Finset.mem_image.mp hforce
        obtain ⟨original, horiginal, hfirst_eq⟩ := Finset.mem_image.mp hfirst
        have hcell_eq :=
          (congrArg (fun cell : Cell n => (cell.1, cell.2.rev)) hfirst_eq).trans heq
        have hrow := congrArg Prod.fst hcell_eq
        have hcol := congrArg Prod.snd hcell_eq
        have hrow' : original.1 = white_row index := by
          have hback := congrArg Fin.rev hcol
          simpa only [Fin.rev_rev, Prod.snd_swap] using hback
        have hcol' : original.2 = w (black_row index) := by
          simpa only [Equiv.symm_trans_apply, Equiv.symm_symm, Fin.revPerm_symm,
            Fin.revPerm_apply, Fin.rev_rev, Prod.fst_swap] using hrow
        have heq' : original = vertical index := Prod.ext hrow' hcol'
        exact heq' ▸ horiginal
  have unique (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid w) rooks) :
      rooks = forced := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le (forced_subset rooks placement)
    rw [forced_card, placement_card positive w rooks placement]
  have upper : rookCount (permGrid w) ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro first hfirst second hsecond
    exact (unique first (Finset.mem_filter.mp hfirst).2).trans
      (unique second (Finset.mem_filter.mp hsecond).2).symm
  have lower := count_positive positive w
  omega

end D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookPlacements
