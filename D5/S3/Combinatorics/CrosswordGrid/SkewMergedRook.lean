/- GID: D5/S3/Combinatorics/CrosswordGrid/SkewMergedRook
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/SkewMergedRook
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Extreme-deletion descent proves the skew-merged rook-count characterization. -/

import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookForward
import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordGrid.SkewMergedRook

open D5.S3.Combinatorics.CrosswordRookCounts (rookCount)
open D5.S3.Combinatorics.CrosswordPermutationGridRefutation (permGrid)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDefs (SkewMerged)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords (symmetries)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDeletions (corner_lift interior_lift)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookRegions (skew_iff_avoidance)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookBoundary
  (boundary_minimal_classification family_count)

set_option maxHeartbeats 2400000 in
theorem result : SkewMergedRookDefs.claim := by
  classical
  have converse : ∀ size : ℕ, 1 ≤ size → ∀ board : Equiv.Perm (Fin size),
      rookCount (permGrid board) ≤ 2 → SkewMerged board := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro positive board bound
      obtain ⟨smaller_size, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
      by_cases singleton : smaller_size = 0
      · subst smaller_size
        apply (skew_iff_avoidance positive board).mpr
        intro first second third fourth hfirst hsecond hthird
        have := fourth.isLt
        have : first.val < second.val := hfirst
        have : second.val < third.val := hsecond
        have : third.val < fourth.val := hthird
        omega
      have positive_small : 1 ≤ smaller_size := by omega
      let maximum := Fin.last smaller_size
      let penultimate : Fin smaller_size := ⟨smaller_size - 1, by omega⟩
      let second := penultimate.castSucc
      have oriented_required (source : Equiv.Perm (Fin (smaller_size + 1)))
          (count_bound : rookCount (permGrid source) ≤ 2)
          (above : source.symm second < source.symm maximum)
          (first second_row third fourth : Fin (smaller_size + 1))
          (hfirst : first < second_row) (hsecond : second_row < third)
          (hthird : third < fourth)
          (bad : (source second_row < source first ∧ source first < source fourth ∧
            source fourth < source third) ∨
            (source third < source fourth ∧ source fourth < source first ∧
              source first < source second_row)) :
          source.symm maximum = first ∨ source.symm maximum = second_row ∨
            source.symm maximum = third ∨ source.symm maximum = fourth := by
        let pivot := source.symm maximum
        have hpivot : source pivot = Fin.last smaller_size := source.apply_symm_apply _
        have hrestrict : ∀ row : Fin (smaller_size + 1),
            row ≠ pivot ↔ source row ≠ Fin.last smaller_size := by
          intro row
          rw [← hpivot]
          exact source.injective.ne_iff.symm
        let restricted := source.subtypeEquiv
          (p := fun row => row ≠ pivot)
          (q := fun column => column ≠ Fin.last smaller_size) hrestrict
        let small : Equiv.Perm (Fin smaller_size) :=
          ((finSuccAboveEquiv pivot).trans restricted).trans
            (finSuccAboveEquiv (Fin.last smaller_size)).symm
        have inherited (row : Fin smaller_size) :
            source (pivot.succAbove row) = (small row).castSucc := by
          have heq := (finSuccAboveEquiv (Fin.last smaller_size)).apply_symm_apply
            (restricted (finSuccAboveEquiv pivot row))
          have hval := congrArg Subtype.val heq
          change (Fin.last smaller_size).succAbove (small row) =
            source (pivot.succAbove row) at hval
          rw [Fin.succAbove_last] at hval
          exact hval.symm
        have inequality : rookCount (permGrid small) ≤ rookCount (permGrid source) := by
          by_cases last : pivot = Fin.last smaller_size
          · apply corner_lift positive_small small source
            · simpa only [← last] using hpivot
            · intro row
              simpa only [last, Fin.succAbove_last] using inherited row
          · apply interior_lift positive_small small source pivot
            · exact ⟨by have hlt : (source.symm second).val < pivot.val := above; omega,
                Fin.val_lt_last last⟩
            · exact hpivot
            · exact inherited
            · have hinverse : pivot.succAbove (small.symm penultimate) =
                  source.symm second := by
                apply source.injective
                rw [inherited, small.apply_symm_apply, source.apply_symm_apply]
              change pivot.succAbove (small.symm penultimate) < pivot
              rw [hinverse]
              exact above
        have small_skew := ih smaller_size (by omega) positive_small small
          (inequality.trans count_bound)
        by_contra missing
        have absent : pivot ≠ first ∧ pivot ≠ second_row ∧ pivot ≠ third ∧
            pivot ≠ fourth := by simpa only [not_or] using missing
        let recover (row : Fin (smaller_size + 1)) (away : row ≠ pivot) : Fin smaller_size :=
          (finSuccAboveEquiv pivot).symm ⟨row, away⟩
        have recover_spec (row : Fin (smaller_size + 1)) (away : row ≠ pivot) :
            pivot.succAbove (recover row away) = row :=
          congrArg Subtype.val ((finSuccAboveEquiv pivot).apply_symm_apply ⟨row, away⟩)
        let low := recover first absent.1.symm
        let next := recover second_row absent.2.1.symm
        let high := recover third absent.2.2.1.symm
        let last := recover fourth absent.2.2.2.symm
        have first_eq : pivot.succAbove low = first := recover_spec _ _
        have second_eq : pivot.succAbove next = second_row := recover_spec _ _
        have third_eq : pivot.succAbove high = third := recover_spec _ _
        have fourth_eq : pivot.succAbove last = fourth := recover_spec _ _
        have first_order : low < next := by
          apply Fin.succAbove_lt_succAbove_iff.mp
          rwa [first_eq, second_eq]
        have second_order : next < high := by
          apply Fin.succAbove_lt_succAbove_iff.mp
          rwa [second_eq, third_eq]
        have third_order : high < last := by
          apply Fin.succAbove_lt_succAbove_iff.mp
          rwa [third_eq, fourth_eq]
        have obstruction := (skew_iff_avoidance positive_small small).mp small_skew
          low next high last first_order second_order third_order
        apply obstruction
        have first_value := inherited low
        have second_value := inherited next
        have third_value := inherited high
        have fourth_value := inherited last
        rw [first_eq] at first_value
        rw [second_eq] at second_value
        rw [third_eq] at third_value
        rw [fourth_eq] at fourth_value
        rw [first_value, second_value, third_value, fourth_value] at bad
        simpa only [Fin.castSucc_lt_castSucc_iff] using bad
      have maximum_required (source : Equiv.Perm (Fin (smaller_size + 1)))
          (count_bound : rookCount (permGrid source) ≤ 2)
          (first second_row third fourth : Fin (smaller_size + 1))
          (hfirst : first < second_row) (hsecond : second_row < third)
          (hthird : third < fourth)
          (bad : (source second_row < source first ∧ source first < source fourth ∧
            source fourth < source third) ∨
            (source third < source fourth ∧ source fourth < source first ∧
              source first < source second_row)) :
          source.symm maximum = first ∨ source.symm maximum = second_row ∨
            source.symm maximum = third ∨ source.symm maximum = fourth := by
        by_cases above : source.symm second < source.symm maximum
        · exact oriented_required source count_bound above first second_row third fourth
            hfirst hsecond hthird bad
        · let reflected := Fin.revPerm.trans source
          have different : source.symm second ≠ source.symm maximum :=
            source.symm.injective.ne (Fin.castSucc_ne_last _)
          have reverse : source.symm maximum < source.symm second :=
            lt_of_le_of_ne (le_of_not_gt above) different.symm
          have reflected_above : reflected.symm second < reflected.symm maximum :=
            Fin.rev_lt_rev.mpr reverse
          have reflected_bound : rookCount (permGrid reflected) ≤ 2 := by
            rwa [← (symmetries positive source).2.2.1.1]
          have reflected_bad :
              (reflected third.rev < reflected fourth.rev ∧
                reflected fourth.rev < reflected first.rev ∧
                  reflected first.rev < reflected second_row.rev) ∨
              (reflected second_row.rev < reflected first.rev ∧
                reflected first.rev < reflected fourth.rev ∧
                  reflected fourth.rev < reflected third.rev) := by
            simpa only [reflected, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev] using
              bad.symm
          have required := oriented_required reflected reflected_bound reflected_above
            fourth.rev third.rev second_row.rev first.rev (Fin.rev_lt_rev.mpr hthird)
            (Fin.rev_lt_rev.mpr hsecond) (Fin.rev_lt_rev.mpr hfirst) reflected_bad
          change (source.symm maximum).rev = fourth.rev ∨
            (source.symm maximum).rev = third.rev ∨
            (source.symm maximum).rev = second_row.rev ∨
            (source.symm maximum).rev = first.rev at required
          simp only [Fin.rev_inj] at required
          rcases required with same | same | same | same
          · exact Or.inr (Or.inr (Or.inr same))
          · exact Or.inr (Or.inr (Or.inl same))
          · exact Or.inr (Or.inl same)
          · exact Or.inl same
      have last_required (source : Equiv.Perm (Fin (smaller_size + 1)))
          (count_bound : rookCount (permGrid source) ≤ 2)
          (first second_row third fourth : Fin (smaller_size + 1))
          (hfirst : first < second_row) (hsecond : second_row < third)
          (hthird : third < fourth)
          (bad : (source second_row < source first ∧ source first < source fourth ∧
            source fourth < source third) ∨
            (source third < source fourth ∧ source fourth < source first ∧
              source first < source second_row)) :
          maximum = first ∨ maximum = second_row ∨ maximum = third ∨ maximum = fourth := by
        have inverse_bound : rookCount (permGrid source.symm) ≤ 2 := by
          rwa [← (symmetries positive source).1.1]
        rcases bad with bad | bad
        · have inverse_bad :
              (source.symm (source first) < source.symm (source second_row) ∧
                source.symm (source second_row) < source.symm (source third) ∧
                  source.symm (source third) < source.symm (source fourth)) ∨
              (source.symm (source fourth) < source.symm (source third) ∧
                source.symm (source third) < source.symm (source second_row) ∧
                  source.symm (source second_row) < source.symm (source first)) := by
            simp only [source.symm_apply_apply]
            exact Or.inl ⟨hfirst, hsecond, hthird⟩
          have required := maximum_required source.symm inverse_bound (source second_row)
            (source first) (source fourth) (source third) bad.1 bad.2.1 bad.2.2 inverse_bad
          simp only [Equiv.symm_symm, source.injective.eq_iff] at required
          rcases required with same | same | same | same
          · exact Or.inr (Or.inl same)
          · exact Or.inl same
          · exact Or.inr (Or.inr (Or.inr same))
          · exact Or.inr (Or.inr (Or.inl same))
        · have inverse_bad :
              (source.symm (source fourth) < source.symm (source third) ∧
                source.symm (source third) < source.symm (source second_row) ∧
                  source.symm (source second_row) < source.symm (source first)) ∨
              (source.symm (source first) < source.symm (source second_row) ∧
                source.symm (source second_row) < source.symm (source third) ∧
                  source.symm (source third) < source.symm (source fourth)) := by
            simp only [source.symm_apply_apply]
            exact Or.inr ⟨hfirst, hsecond, hthird⟩
          have required := maximum_required source.symm inverse_bound (source third)
            (source fourth) (source first) (source second_row) bad.1 bad.2.1 bad.2.2 inverse_bad
          simp only [Equiv.symm_symm, source.injective.eq_iff] at required
          rcases required with same | same | same | same
          · exact Or.inr (Or.inr (Or.inl same))
          · exact Or.inr (Or.inr (Or.inr same))
          · exact Or.inl same
          · exact Or.inr (Or.inl same)
      by_contra not_skew
      let first : Fin (smaller_size + 1) := ⟨0, by omega⟩
      have first_row : first.val = 0 := rfl
      have last_row : maximum.val + 1 = smaller_size + 1 := rfl
      have extreme_membership (left lower upper right : Fin (smaller_size + 1))
          (hleft : left < lower) (hmiddle : lower < upper) (hright : upper < right)
          (bad : (board lower < board left ∧ board left < board right ∧
            board right < board upper) ∨
            (board upper < board right ∧ board right < board left ∧
              board left < board lower)) :
          (first = left ∨ first = lower ∨ first = upper ∨ first = right) ∧
          (maximum = left ∨ maximum = lower ∨ maximum = upper ∨ maximum = right) ∧
          (board.symm first = left ∨ board.symm first = lower ∨
            board.symm first = upper ∨ board.symm first = right) ∧
          (board.symm maximum = left ∨ board.symm maximum = lower ∨
            board.symm maximum = upper ∨ board.symm maximum = right) := by
        have max_mem := maximum_required board bound left lower upper right
          hleft hmiddle hright bad
        have last_mem := last_required board bound left lower upper right
          hleft hmiddle hright bad
        let complemented := board.trans Fin.revPerm
        have complement_bound : rookCount (permGrid complemented) ≤ 2 := by
          rwa [← (symmetries positive board).2.1.1]
        have complement_bad :
            (complemented lower < complemented left ∧ complemented left < complemented right ∧
              complemented right < complemented upper) ∨
            (complemented upper < complemented right ∧ complemented right < complemented left ∧
              complemented left < complemented lower) := by
          change ((board lower).rev < (board left).rev ∧
            (board left).rev < (board right).rev ∧ (board right).rev < (board upper).rev) ∨
            ((board upper).rev < (board right).rev ∧
              (board right).rev < (board left).rev ∧ (board left).rev < (board lower).rev)
          simp only [Fin.rev_lt_rev]
          rcases bad with ⟨hlow, hmid, hhigh⟩ | ⟨hlow, hmid, hhigh⟩
          · exact Or.inr ⟨hhigh, hmid, hlow⟩
          · exact Or.inl ⟨hhigh, hmid, hlow⟩
        have min_mem := maximum_required complemented complement_bound left lower upper right
          hleft hmiddle hright complement_bad
        have rev_max : maximum.rev = first := by apply Fin.ext; simp [maximum, first]
        change board.symm maximum.rev = left ∨ board.symm maximum.rev = lower ∨
          board.symm maximum.rev = upper ∨ board.symm maximum.rev = right at min_mem
        rw [rev_max] at min_mem
        let reflected := Fin.revPerm.trans board
        have reflection_bound : rookCount (permGrid reflected) ≤ 2 := by
          rwa [← (symmetries positive board).2.2.1.1]
        have reflection_bad :
            (reflected upper.rev < reflected right.rev ∧
              reflected right.rev < reflected left.rev ∧
                reflected left.rev < reflected lower.rev) ∨
            (reflected lower.rev < reflected left.rev ∧
              reflected left.rev < reflected right.rev ∧
                reflected right.rev < reflected upper.rev) := by
          simpa only [reflected, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev] using bad.symm
        have first_mem := last_required reflected reflection_bound right.rev upper.rev lower.rev
          left.rev (Fin.rev_lt_rev.mpr hright) (Fin.rev_lt_rev.mpr hmiddle)
          (Fin.rev_lt_rev.mpr hleft) reflection_bad
        have rev_first : first.rev = maximum := by
          rw [← rev_max, Fin.rev_rev]
        have reversed : first = right ∨ first = upper ∨ first = lower ∨ first = left := by
          simpa only [← rev_first, Fin.rev_inj] using first_mem
        refine ⟨?_, last_mem, min_mem, max_mem⟩
        rcases reversed with same | same | same | same
        · exact Or.inr (Or.inr (Or.inr same))
        · exact Or.inr (Or.inr (Or.inl same))
        · exact Or.inr (Or.inl same)
        · exact Or.inl same
      obtain ⟨source, source_eq, minimum, top, hfirst, hmiddle, hlast,
        min_value, max_value, _, arm, middle, size_eq, shape⟩ :=
        boundary_minimal_classification positive board first maximum first_row last_row
          not_skew extreme_membership
      have source_count : rookCount (permGrid source) = rookCount (permGrid board) := by
        rcases source_eq with rfl | rfl
        · rfl
        · exact (symmetries positive board).2.1.1.symm
      have canonical (target : Equiv.Perm (Fin (smaller_size + 1)))
          (low high : Fin (smaller_size + 1))
          (hlow : low.val = arm + 1) (hhigh : high.val + 2 = smaller_size + 1)
          (vlow : target low = first) (vhigh : target high = maximum)
          (vfirst : (target first).val = 1) (vlast : (target maximum).val = middle + 2)
          (pieces : ∀ row : Fin (smaller_size + 1),
            (first < row ∧ row < low → (target row).val + row.val = smaller_size) ∧
            (low < row ∧ row < high → (target row).val = row.val - low.val + 1)) :
          3 ≤ rookCount (permGrid target) := by
        apply family_count positive arm middle size_eq target
        intro row
        have at_first : row.val = 0 → (target row).val = 1 := by
          intro same
          have : row = first := Fin.ext same
          simpa only [this] using vfirst
        have at_low : row.val = arm + 1 → (target row).val = 0 := by
          intro same
          have : row = low := Fin.ext (same.trans hlow.symm)
          simp only [this, vlow, first_row]
        have at_high : row.val = arm + middle + 2 → (target row).val = smaller_size := by
          intro same
          have : row = high := Fin.ext (by omega)
          simp only [this, vhigh, maximum, Fin.val_last]
        have at_last : row.val = smaller_size → (target row).val = middle + 2 := by
          intro same
          have : row = maximum := Fin.ext same
          simpa only [this] using vlast
        have below : 0 < row.val ∧ row.val < arm + 1 →
            (target row).val + row.val = smaller_size := by
          intro order
          exact (pieces row).1 ⟨order.1, by change row.val < low.val; omega⟩
        have between : arm + 1 < row.val ∧ row.val < arm + middle + 2 →
            (target row).val = row.val - (arm + 1) + 1 := by
          intro order
          have value := (pieces row).2 ⟨by change low.val < row.val; omega,
            by change row.val < high.val; omega⟩
          simpa only [hlow] using value
        have row_bound := row.isLt
        split_ifs <;> omega
      have three : 3 ≤ rookCount (permGrid source) := by
        rcases shape with ⟨hlow, hhigh, vfirst, vlast, pieces⟩ |
          ⟨hlow, hhigh, vfirst, vlast, pieces⟩
        · exact canonical source minimum top hlow hhigh min_value max_value
            vfirst vlast pieces
        · let half := Fin.revPerm.trans (source.trans Fin.revPerm)
          have half_count : rookCount (permGrid source) = rookCount (permGrid half) :=
            (symmetries positive source).2.1.1.trans
              (symmetries positive (source.trans Fin.revPerm)).2.2.1.1
          rw [half_count]
          apply canonical half top.rev minimum.rev
          · rw [Fin.val_rev]
            omega
          · rw [Fin.val_rev]
            omega
          · simp only [half, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]
            rw [max_value]
            apply Fin.ext
            simp [maximum, first]
          · simp only [half, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]
            rw [min_value]
            apply Fin.ext
            simp [maximum, first]
          · change ((source first.rev).rev).val = 1
            have rev_first : first.rev = maximum := by apply Fin.ext; simp [first, maximum]
            rw [rev_first]
            rw [Fin.val_rev]
            omega
          · change ((source maximum.rev).rev).val = middle + 2
            have rev_max : maximum.rev = first := by apply Fin.ext; simp [first, maximum]
            rw [rev_max]
            rw [Fin.val_rev]
            omega
          · intro row
            have rev_bound := row.rev.isLt
            have value_bound := (source row.rev).isLt
            have row_bound := row.isLt
            have row_rev : row.rev.val = smaller_size - row.val := by
              rw [Fin.val_rev]
              omega
            have top_rev : top.rev.val = smaller_size - top.val := by
              rw [Fin.val_rev]
              omega
            have min_rev : minimum.rev.val = smaller_size - minimum.val := by
              rw [Fin.val_rev]
              omega
            constructor
            · intro order
              have order_left : top < row.rev := by
                change top.val < row.rev.val
                have : row.val < top.rev.val := order.2
                rw [top_rev] at this
                omega
              have order_right : row.rev < maximum := by
                change row.rev.val < smaller_size
                have : 0 < row.val := order.1
                omega
              have value := (pieces row.rev).2 ⟨order_left, order_right⟩
              change ((source row.rev).rev).val + row.val = smaller_size
              rw [Fin.val_rev]
              omega
            · intro order
              have order_left : minimum < row.rev := by
                simpa only [Fin.rev_rev] using Fin.rev_lt_rev.mpr order.2
              have order_right : row.rev < top := by
                simpa only [Fin.rev_rev] using Fin.rev_lt_rev.mpr order.1
              have value := (pieces row.rev).1 ⟨order_left, order_right⟩
              change ((source row.rev).rev).val = row.val - top.rev.val + 1
              rw [Fin.val_rev, top_rev]
              have order_upper : row.val < minimum.rev.val := order.2
              have order_lower : top.rev.val < row.val := order.1
              rw [min_rev] at order_upper
              rw [top_rev] at order_lower
              omega
      rw [source_count] at three
      omega
  intro size positive board
  constructor
  · intro count
    exact converse size positive board (by rcases count with count | count <;> omega)
  · exact SkewMergedRookForward.forward_count positive board

end D5.S3.Combinatorics.CrosswordGrid.SkewMergedRook
