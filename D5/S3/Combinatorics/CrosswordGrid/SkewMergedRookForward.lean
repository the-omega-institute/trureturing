/- GID: D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookForward
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/SkewMergedRookForward
   mirror-E: none(waiver:skew-merged-placement-upper-bound)
   anchors: []
   utility: none
   digest: The forced words leave a residual square with at most two complete placements. -/

import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookCenterless

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookForward

open D5.S3.Combinatorics.CrosswordRookCounts
  (Cell SameAcross SameDown IsRookPlacement rookCount)
open D5.S3.Combinatorics.CrosswordPermutationGridRefutation (permGrid)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDefs (SkewMerged)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords (word_structure symmetries)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookPlacements (count_positive overlapping_count)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookCenterless (centerless_cuts)

set_option maxHeartbeats 2000000 in
theorem forward_count {n : ℕ} (positive : 1 ≤ n) (w : Equiv.Perm (Fin n))
    (skew : SkewMerged w) :
    rookCount (permGrid w) = 1 ∨ rookCount (permGrid w) = 2 := by
  classical
  by_cases overlap : ∃ first second : Finset (Fin n),
      first ∪ second = Finset.univ ∧
      (∀ row ∈ first, ∀ other ∈ first, row < other → w row < w other) ∧
      (∀ row ∈ second, ∀ other ∈ second, row < other → w other < w row) ∧
      ∃ pivot : Fin n, pivot ∈ first ∧ pivot ∈ second
  · obtain ⟨first, second, cover, inc, dec, pivot, hpfirst, hpsecond⟩ := overlap
    exact Or.inl (overlapping_count positive w first second cover inc dec pivot hpfirst hpsecond)
  obtain ⟨part, inc, dec⟩ := skew
  obtain ⟨rc, cc, hrc, hrcn, hcc, hccn, quad, _, _, _, _,
    ⟨top, bottom, left, right, htop, hbottom, hleft, hright, boundary⟩, force⟩ :=
    centerless_cuts positive w part inc dec overlap
  let neighbors := fun (permutation : Equiv.Perm (Fin n)) (row_cut column_cut : ℕ) =>
    Finset.univ.filter (fun cell : Cell n =>
      (cell.2.val + 1 = (permutation cell.1).val ∧
        (permutation cell.1).val < column_cut) ∨
      ((permutation cell.1).val + 1 = cell.2.val ∧
        column_cut ≤ (permutation cell.1).val) ∨
      (cell.1.val + 1 = (permutation.symm cell.2).val ∧
        (permutation.symm cell.2).val < row_cut) ∨
      ((permutation.symm cell.2).val + 1 = cell.1.val ∧
        row_cut ≤ (permutation.symm cell.2).val))
  let forced := neighbors w rc cc
  have forced_subset (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid w) rooks) :
      forced ⊆ rooks := by
    intro cell hcell
    exact force rooks placement cell (Finset.mem_filter.mp hcell).2
  have across_capture (permutation : Equiv.Perm (Fin n)) (increasing : Finset (Fin n))
      (row_cut column_cut : ℕ) (row_cut_bound : row_cut ≤ n)
      (hinc : ∀ row ∈ increasing, ∀ other ∈ increasing, row < other →
        permutation row < permutation other)
      (hdec : ∀ row ∉ increasing, ∀ other ∉ increasing, row < other →
        permutation other < permutation row)
      (hquad : ∀ row : Fin n, row ∈ increasing ↔
        (row.val < row_cut ↔ (permutation row).val < column_cut))
      (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid permutation) rooks)
      (hforced : neighbors permutation row_cut column_cut ⊆ rooks) :
      ∀ cell ∈ rooks, cell ∈ neighbors permutation row_cut column_cut ∨
        cell.1.val + 1 = row_cut ∨ cell.1.val = row_cut := by
    have across := (word_structure positive permutation).1
    have get (cell : Cell n) (hcell : cell ∈ rooks) (candidate : Cell n)
        (hneighbor : candidate ∈ neighbors permutation row_cut column_cut)
        (same_row : candidate.1 = cell.1)
        (same_side : candidate.2 < permutation candidate.1 ↔ cell.2 < permutation cell.1) :
        cell ∈ neighbors permutation row_cut column_cut := by
      have hcand := hforced hneighbor
      have hword := (across candidate (placement.1 hcand) cell (placement.1 hcell)).mpr
        ⟨same_row, same_side⟩
      have heq : candidate = cell := by
        by_contra bad
        exact (placement.2.1 candidate hcand cell hcell bad).1 hword
      exact heq ▸ hneighbor
    intro cell hcell
    have hwhite : permutation cell.1 ≠ cell.2 := by
      simpa only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and] using placement.1 hcell
    by_cases west : cell.2 < permutation cell.1
    all_goals by_cases low : (permutation cell.1).val < column_cut
    any_goals
        guard_hyp west : cell.2 < permutation cell.1
        guard_hyp low : (permutation cell.1).val < column_cut
        let previous : Fin n := ⟨(permutation cell.1).val - 1, by
          have := (permutation cell.1).isLt; omega⟩
        have hstep : previous.val + 1 = (permutation cell.1).val := by
          change cell.2.val < (permutation cell.1).val at west
          dsimp [previous]; omega
        apply Or.inl
        apply get cell hcell (cell.1, previous)
        · simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inl ⟨hstep, low⟩
        · rfl
        · have hprev : previous < permutation cell.1 := by
            change previous.val < (permutation cell.1).val; omega
          exact ⟨fun _ => west, fun _ => hprev⟩
    any_goals
        guard_hyp west : ¬ cell.2 < permutation cell.1
        guard_hyp low : ¬ (permutation cell.1).val < column_cut
        have high : column_cut ≤ (permutation cell.1).val := le_of_not_gt low
        have east : permutation cell.1 < cell.2 := lt_of_le_of_ne (le_of_not_gt west) hwhite
        let next : Fin n := ⟨(permutation cell.1).val + 1, by
          have := cell.2.isLt; change (permutation cell.1).val < cell.2.val at east; omega⟩
        apply Or.inl
        apply get cell hcell (cell.1, next)
        · simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inr (Or.inl ⟨rfl, high⟩)
        · rfl
        · have hnext : ¬ next < permutation cell.1 := by
            change ¬ (permutation cell.1).val + 1 < (permutation cell.1).val; omega
          exact ⟨fun h => (hnext h).elim, fun h => (west h).elim⟩
    all_goals
      by_cases hupper : cell.1.val + 1 < row_cut
      · let next : Fin n := ⟨cell.1.val + 1, by
          have := cell.1.isLt
          omega⟩
        have hrow : cell.1 < next := by change cell.1.val < cell.1.val + 1; omega
        have next_top : next.val < row_cut := hupper
        have current_top : cell.1.val < row_cut := by omega
        have direction : permutation next < permutation cell.1 ↔
            column_cut ≤ (permutation cell.1).val := by
          by_cases current_low : (permutation cell.1).val < column_cut
          · have current_inc := (hquad _).mpr ⟨fun _ => current_low, fun _ => current_top⟩
            have hvalue : permutation cell.1 < permutation next := by
              by_cases next_low : (permutation next).val < column_cut
              · have next_inc := (hquad _).mpr ⟨fun _ => next_low, fun _ => next_top⟩
                exact hinc _ current_inc _ next_inc hrow
              · change (permutation cell.1).val < (permutation next).val; omega
            exact ⟨fun h => (lt_asymm h hvalue).elim,
              fun h => (not_le_of_gt current_low h).elim⟩
          · have current_dec : cell.1 ∉ increasing := by
              intro hmem; exact current_low ((hquad _).mp hmem |>.mp current_top)
            have hvalue : permutation next < permutation cell.1 := by
              by_cases next_low : (permutation next).val < column_cut
              · change (permutation next).val < (permutation cell.1).val; omega
              · have next_dec : next ∉ increasing := by
                  intro hmem; exact next_low ((hquad _).mp hmem |>.mp next_top)
                exact hdec _ current_dec _ next_dec hrow
            exact ⟨fun _ => le_of_not_gt current_low, fun _ => hvalue⟩
        apply Or.inl
        apply get cell hcell (cell.1, permutation next)
        · simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and,
            permutation.symm_apply_apply]
          exact Or.inr (Or.inr (Or.inl ⟨rfl, next_top⟩))
        · rfl
        · rw [direction]
          omega
      · by_cases hlower : row_cut < cell.1.val
        · let previous : Fin n := ⟨cell.1.val - 1, by have := cell.1.isLt; omega⟩
          have hrow : previous < cell.1 := by change cell.1.val - 1 < cell.1.val; omega
          have previous_bottom : row_cut ≤ previous.val := by dsimp [previous]; omega
          have current_bottom : ¬ cell.1.val < row_cut := by omega
          have direction : permutation previous < permutation cell.1 ↔
              column_cut ≤ (permutation cell.1).val := by
            by_cases current_low : (permutation cell.1).val < column_cut
            · have current_dec : cell.1 ∉ increasing := by
                intro hmem; exact current_bottom ((hquad _).mp hmem |>.mpr current_low)
              have hvalue : permutation cell.1 < permutation previous := by
                by_cases previous_low : (permutation previous).val < column_cut
                · have previous_dec : previous ∉ increasing := by
                    intro hmem
                    exact not_lt_of_ge previous_bottom ((hquad _).mp hmem |>.mpr previous_low)
                  exact hdec _ previous_dec _ current_dec hrow
                · change (permutation cell.1).val < (permutation previous).val; omega
              exact ⟨fun h => (lt_asymm h hvalue).elim,
                fun h => (not_le_of_gt current_low h).elim⟩
            · have current_inc := (hquad _).mpr
                ⟨fun h => (current_bottom h).elim, fun h => (current_low h).elim⟩
              have hvalue : permutation previous < permutation cell.1 := by
                by_cases previous_low : (permutation previous).val < column_cut
                · change (permutation previous).val < (permutation cell.1).val; omega
                · have previous_inc := (hquad _).mpr
                    ⟨fun h => (not_lt_of_ge previous_bottom h).elim,
                      fun h => (previous_low h).elim⟩
                  exact hinc _ previous_inc _ current_inc hrow
              exact ⟨fun _ => le_of_not_gt current_low, fun _ => hvalue⟩
          apply Or.inl
          apply get cell hcell (cell.1, permutation previous)
          · simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and,
              permutation.symm_apply_apply]
            exact Or.inr (Or.inr (Or.inr ⟨by dsimp [previous]; omega, previous_bottom⟩))
          · rfl
          · rw [direction]
            omega
        · exact Or.inr (by omega)
  have swap_neighbors (permutation : Equiv.Perm (Fin n)) (row_cut column_cut : ℕ) :
      (neighbors permutation row_cut column_cut).image Prod.swap =
        neighbors permutation.symm column_cut row_cut := by
    ext cell
    constructor
    · rintro hmem
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hmem
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.symm_symm, Prod.fst_swap, Prod.snd_swap] at horiginal ⊢
      rcases horiginal with hwest | heast | hnorth | hsouth
      · exact Or.inr (Or.inr (Or.inl hwest))
      · exact Or.inr (Or.inr (Or.inr heast))
      · exact Or.inl hnorth
      · exact Or.inr (Or.inl hsouth)
    · intro hmem
      refine Finset.mem_image.mpr ⟨cell.swap, ?_, by simp⟩
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.symm_symm, Prod.fst_swap, Prod.snd_swap] at hmem ⊢
      rcases hmem with hwest | heast | hnorth | hsouth
      · exact Or.inr (Or.inr (Or.inl hwest))
      · exact Or.inr (Or.inr (Or.inr heast))
      · exact Or.inl hnorth
      · exact Or.inr (Or.inl hsouth)
  have inverse_inc : ∀ row ∈ part.image w, ∀ other ∈ part.image w,
      row < other → w.symm row < w.symm other := by
    intro row hr other ho hlt
    obtain ⟨first, hfirst, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp ho
    simp only [w.symm_apply_apply]
    by_contra bad
    rcases (le_of_not_gt bad).eq_or_lt with heq | hbefore
    · exact lt_irrefl _ (heq ▸ hlt)
    · exact lt_asymm hlt (inc _ hsecond _ hfirst hbefore)
  have inverse_dec : ∀ row ∉ part.image w, ∀ other ∉ part.image w,
      row < other → w.symm other < w.symm row := by
    intro row hr other ho hlt
    have hfirst : w.symm row ∉ part := by
      intro hmem; exact hr (Finset.mem_image.mpr ⟨_, hmem, w.apply_symm_apply _⟩)
    have hsecond : w.symm other ∉ part := by
      intro hmem; exact ho (Finset.mem_image.mpr ⟨_, hmem, w.apply_symm_apply _⟩)
    by_contra bad
    rcases (le_of_not_gt bad).eq_or_lt with heq | hbefore
    · exact (ne_of_lt hlt) (w.symm.injective heq)
    · have hvalue := dec _ hfirst _ hsecond hbefore
      simp only [w.apply_symm_apply] at hvalue
      exact lt_asymm hlt hvalue
  have inverse_quad (row : Fin n) : row ∈ part.image w ↔
      (row.val < cc ↔ (w.symm row).val < rc) := by
    have hmem : row ∈ part.image w ↔ w.symm row ∈ part := by
      constructor
      · intro hmem
        obtain ⟨original, horiginal, heq⟩ := Finset.mem_image.mp hmem
        have hback := congrArg w.symm heq
        simpa only [w.symm_apply_apply, hback.symm] using horiginal
      · intro hmem
        exact Finset.mem_image.mpr ⟨_, hmem, w.apply_symm_apply _⟩
    rw [hmem, quad, w.apply_symm_apply]
    exact ⟨Iff.symm, Iff.symm⟩
  have capture (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid w) rooks)
      (cell : Cell n) (hcell : cell ∈ rooks) : cell ∈ forced ∨
      ((cell.1 = top ∨ cell.1 = bottom) ∧ (cell.2 = left ∨ cell.2 = right)) := by
    rcases across_capture w part rc cc hrcn.le inc dec quad rooks placement
      (forced_subset rooks placement) cell hcell with hf | hrow
    · exact Or.inl hf
    have transpose := (symmetries positive w).2.2.2.1 rooks placement
    have hsubset : neighbors w.symm cc rc ⊆ rooks.image Prod.swap := by
      rw [← swap_neighbors]
      exact Finset.image_subset_image (forced_subset rooks placement)
    have hswap : cell.swap ∈ rooks.image Prod.swap := Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    rcases across_capture w.symm (part.image w) cc rc hccn.le inverse_inc inverse_dec inverse_quad
      _ transpose hsubset cell.swap hswap with hf | hcol
    · rw [← swap_neighbors] at hf
      obtain ⟨original, horiginal, heq⟩ := Finset.mem_image.mp hf
      have hback := congrArg Prod.swap heq
      change original = cell at hback
      exact Or.inl (hback ▸ horiginal)
    · apply Or.inr
      constructor
      · rcases hrow with hrow | hrow
        · exact Or.inl (Fin.ext (by omega))
        · exact Or.inr (Fin.ext (by omega))
      · rcases hcol with hcol | hcol
        · exact Or.inl (Fin.ext (by change cell.2.val + 1 = cc at hcol; omega))
        · exact Or.inr (Fin.ext (by change cell.2.val = cc at hcol; omega))
  have square_white (row column : Fin n) (hr : row = top ∨ row = bottom)
      (hc : column = left ∨ column = right) : (row, column) ∈ permGrid w := by
    simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcolumn : left < right := by change left.val < right.val; omega
    rcases boundary with ⟨htl, hbr, _, _⟩ | ⟨htr, hbl, _, _⟩ <;>
      rcases hr with rfl | rfl <;> rcases hc with rfl | rfl <;> intro heq
    all_goals omega
  have across := (word_structure positive w).1
  obtain ⟨data, labels⟩ := (word_structure positive w).2
  have down (first second : Cell n) (hf : first ∈ permGrid w) (hs : second ∈ permGrid w) :
      SameDown (permGrid w) first second ↔
        first.2 = second.2 ∧ (first.1 < w.symm first.2 ↔ second.1 < w.symm second.2) := by
    rw [data.down_iff first hf second hs, labels, labels]
    constructor
    · intro heq
      have hval : first.2.val = second.2.val := by split_ifs at heq <;> omega
      have hcol := Fin.ext hval
      refine ⟨hcol, ?_⟩
      by_cases hfirst : first.1 < w.symm first.2 <;>
        by_cases hsecond : second.1 < w.symm second.2 <;>
        simp only [hfirst, hsecond, ↓reduceIte, hval] at heq ⊢ <;> omega
    · rintro ⟨hcol, hside⟩
      rw [hcol]
      rw [hcol] at hside
      by_cases hfirst : first.1 < w.symm second.2
      · have hsecond := hside.mp hfirst
        simp only [hfirst, hsecond, ↓reduceIte]
      · have hsecond := mt hside.mpr hfirst
        simp only [hfirst, hsecond, ↓reduceIte]
  let a : Cell n := (top, left)
  let b : Cell n := (top, right)
  let c : Cell n := (bottom, left)
  let d : Cell n := (bottom, right)
  have white_a := square_white top left (Or.inl rfl) (Or.inl rfl)
  have white_b := square_white top right (Or.inl rfl) (Or.inr rfl)
  have white_c := square_white bottom left (Or.inr rfl) (Or.inl rfl)
  have white_d := square_white bottom right (Or.inr rfl) (Or.inr rfl)
  have row_order : top < bottom := by change top.val < bottom.val; omega
  have col_order : left < right := by change left.val < right.val; omega
  have ab : SameAcross (permGrid w) a b := by
    apply (across _ white_a _ white_b).mpr
    refine ⟨rfl, ?_⟩
    rcases boundary with ⟨htl, _, _, _⟩ | ⟨htr, _, _, _⟩
    · have hfirst := not_lt_of_ge htl.le
      have hsecond := not_lt_of_ge (htl.trans col_order).le
      exact ⟨fun h => (hfirst h).elim, fun h => (hsecond h).elim⟩
    · exact ⟨fun _ => htr, fun _ => col_order.trans htr⟩
  have cd : SameAcross (permGrid w) c d := by
    apply (across _ white_c _ white_d).mpr
    refine ⟨rfl, ?_⟩
    rcases boundary with ⟨_, hbr, _, _⟩ | ⟨_, hbl, _, _⟩
    · exact ⟨fun _ => hbr, fun _ => col_order.trans hbr⟩
    · have hfirst := not_lt_of_ge hbl.le
      have hsecond := not_lt_of_ge (hbl.trans col_order).le
      exact ⟨fun h => (hfirst h).elim, fun h => (hsecond h).elim⟩
  have ac : SameDown (permGrid w) a c := by
    apply (down _ _ white_a white_c).mpr
    refine ⟨rfl, ?_⟩
    rcases boundary with ⟨_, _, hbl, _⟩ | ⟨_, _, hlt, _⟩
    · exact ⟨fun _ => hbl, fun _ => row_order.trans hbl⟩
    · have hfirst := not_lt_of_ge hlt.le
      have hsecond := not_lt_of_ge (hlt.trans row_order).le
      exact ⟨fun h => (hfirst h).elim, fun h => (hsecond h).elim⟩
  have bd : SameDown (permGrid w) b d := by
    apply (down _ _ white_b white_d).mpr
    refine ⟨rfl, ?_⟩
    rcases boundary with ⟨_, _, _, hrt⟩ | ⟨_, _, _, hbr⟩
    · have hfirst := not_lt_of_ge hrt.le
      have hsecond := not_lt_of_ge (hrt.trans row_order).le
      exact ⟨fun h => (hfirst h).elim, fun h => (hsecond h).elim⟩
    · exact ⟨fun _ => hbr, fun _ => row_order.trans hbr⟩
  have boundary_word (permutation : Equiv.Perm (Fin n)) (row_cut column_cut : ℕ)
      (pivot cell : Cell n) (hpivot : pivot ∈ permGrid permutation)
      (hcell : cell ∈ neighbors permutation row_cut column_cut)
      (hrow : pivot.1.val + 1 = row_cut ∨ pivot.1.val = row_cut)
      (inward : ((permutation pivot.1).val < column_cut ∧
          permutation pivot.1 < pivot.2) ∨
        (column_cut ≤ (permutation pivot.1).val ∧ pivot.2 < permutation pivot.1)) :
      ¬ SameAcross (permGrid permutation) pivot cell := by
    intro hsame
    have hsubset : cell ∈ permGrid permutation := by
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hcell
      simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hcell with ⟨hstep, _⟩ | ⟨hstep, _⟩ | ⟨hstep, _⟩ | ⟨hstep, _⟩ <;>
        intro heq
      · have := congrArg Fin.val heq; omega
      · have := congrArg Fin.val heq; omega
      · have hback := congrArg permutation.symm heq
        simp only [permutation.symm_apply_apply] at hback
        have := congrArg Fin.val hback; omega
      · have hback := congrArg permutation.symm heq
        simp only [permutation.symm_apply_apply] at hback
        have := congrArg Fin.val hback; omega
    have hgeometry := ((word_structure positive permutation).1 _ hpivot _ hsubset).mp hsame
    have hsame_row := congrArg Fin.val hgeometry.1
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hcell
    rcases inward with ⟨hlow, heast⟩ | ⟨hhigh, hwest⟩ <;>
      rcases hcell with ⟨hstep, hcut⟩ | ⟨hstep, hcut⟩ | ⟨hstep, hcut⟩ |
        ⟨hstep, hcut⟩
    all_goals
      have hvalue : permutation pivot.1 = permutation cell.1 := congrArg permutation hgeometry.1
      have hvalue_nat := congrArg Fin.val hvalue
      first
      | have hside := hgeometry.2.mp hwest; omega
      | have hside : ¬ cell.2 < permutation cell.1 :=
          fun h => (not_lt_of_ge heast.le) (hgeometry.2.mpr h)
        change ¬ cell.2.val < (permutation cell.1).val at hside
        omega
  have choices (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid w) rooks) :
      (a ∈ rooks ∨ b ∈ rooks) ∧ (c ∈ rooks ∨ d ∈ rooks) ∧
        (a ∈ rooks ∨ c ∈ rooks) := by
    have inward_top : ((w top).val < cc ∧ w top < left) ∨
        (cc ≤ (w top).val ∧ left < w top) := by
      rcases boundary with ⟨htl, _, _, _⟩ | ⟨htr, _, _, _⟩
      · exact Or.inl ⟨by change (w top).val < left.val at htl; omega, htl⟩
      · exact Or.inr ⟨by change right.val < (w top).val at htr; omega, col_order.trans htr⟩
    have inward_bottom : ((w bottom).val < cc ∧ w bottom < left) ∨
        (cc ≤ (w bottom).val ∧ left < w bottom) := by
      rcases boundary with ⟨_, hbr, _, _⟩ | ⟨_, hbl, _, _⟩
      · exact Or.inr ⟨by change right.val < (w bottom).val at hbr; omega, col_order.trans hbr⟩
      · exact Or.inl ⟨by change (w bottom).val < left.val at hbl; omega, hbl⟩
    have horizontal (pivot : Cell n) (hpivot : pivot ∈ permGrid w)
        (hrow : pivot.1 = top ∨ pivot.1 = bottom)
        (inward : ((w pivot.1).val < cc ∧ w pivot.1 < pivot.2) ∨
          (cc ≤ (w pivot.1).val ∧ pivot.2 < w pivot.1)) :
        (pivot.1, left) ∈ rooks ∨ (pivot.1, right) ∈ rooks := by
      obtain ⟨rook, hrook, hword⟩ := (placement.2.2 pivot hpivot).1
      rcases capture rooks placement rook hrook with hf | ⟨_, hc⟩
      · exact False.elim (boundary_word w rc cc pivot rook hpivot hf
          (hrow.elim (fun h => Or.inl (h ▸ htop)) (fun h => Or.inr (h ▸ hbottom))) inward hword)
      · have hrow_eq := hword.1
        rcases hc with hc | hc
        · have heq : rook = (pivot.1, left) := Prod.ext hrow_eq.symm hc
          exact Or.inl (heq ▸ hrook)
        · have heq : rook = (pivot.1, right) := Prod.ext hrow_eq.symm hc
          exact Or.inr (heq ▸ hrook)
    refine ⟨horizontal a white_a (Or.inl rfl) inward_top,
      horizontal c white_c (Or.inr rfl) inward_bottom, ?_⟩
    obtain ⟨rook, hrook, hword⟩ := (placement.2.2 a white_a).2
    rcases capture rooks placement rook hrook with hf | ⟨hr, _⟩
    · have swap_white : a.swap ∈ permGrid w.symm := by
        simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
        intro heq
        exact (Finset.mem_filter.mp white_a).2 (w.symm_apply_eq.mp heq).symm
      have swap_forced : rook.swap ∈ neighbors w.symm cc rc := by
        rw [← swap_neighbors]
        exact Finset.mem_image.mpr ⟨rook, hf, rfl⟩
      have inward_left : ((w.symm left).val < rc ∧ w.symm left < top) ∨
          (rc ≤ (w.symm left).val ∧ top < w.symm left) := by
        rcases boundary with ⟨_, _, hbl, _⟩ | ⟨_, _, hlt, _⟩
        · exact Or.inr ⟨by change bottom.val < (w.symm left).val at hbl; omega,
            row_order.trans hbl⟩
        · exact Or.inl ⟨by change (w.symm left).val < top.val at hlt; omega, hlt⟩
      have swapped_word : SameAcross (permGrid w.symm) a.swap rook.swap := by
        refine ⟨hword.1, ?_⟩
        intro column hmin hmax
        have hwhite := hword.2 column hmin hmax
        simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and] at hwhite ⊢
        intro heq
        exact hwhite (w.symm_apply_eq.mp heq).symm
      exact False.elim (boundary_word w.symm cc rc a.swap rook.swap swap_white swap_forced
        (Or.inl hleft) inward_left swapped_word)
    · have hcol_eq := hword.1
      rcases hr with hr | hr
      · have heq : rook = a := Prod.ext hr hcol_eq.symm
        exact Or.inl (heq ▸ hrook)
      · have heq : rook = c := Prod.ext hr hcol_eq.symm
        exact Or.inr (heq ▸ hrook)
  have a_ne_b : a ≠ b := fun heq => (ne_of_lt col_order) (congrArg Prod.snd heq)
  have a_ne_c : a ≠ c := fun heq => (ne_of_lt row_order) (congrArg Prod.fst heq)
  have b_ne_d : b ≠ d := fun heq => (ne_of_lt row_order) (congrArg Prod.fst heq)
  have determines (first second : Finset (Cell n))
      (hfirst : IsRookPlacement (permGrid w) first)
      (hsecond : IsRookPlacement (permGrid w) second) (hbit : a ∈ first ↔ a ∈ second) :
      first ⊆ second := by
    have first_choices := choices first hfirst
    have second_choices := choices second hsecond
    intro cell hcell
    rcases capture first hfirst cell hcell with hf | ⟨hr, hc⟩
    · exact forced_subset second hsecond hf
    rcases hr with hr | hr <;> rcases hc with hc | hc
    · have heq : cell = a := Prod.ext hr hc
      exact heq ▸ (hbit.mp (heq ▸ hcell))
    · have heq : cell = b := Prod.ext hr hc
      have hb : b ∈ first := heq ▸ hcell
      have hna : a ∉ second := by
        intro ha
        exact (hfirst.2.1 a (hbit.mpr ha) b hb a_ne_b).1 ab
      exact heq ▸ (second_choices.1.resolve_left hna)
    · have heq : cell = c := Prod.ext hr hc
      have hc' : c ∈ first := heq ▸ hcell
      have hna : a ∉ second := by
        intro ha
        exact (hfirst.2.1 a (hbit.mpr ha) c hc' a_ne_c).2 ac
      exact heq ▸ (second_choices.2.2.resolve_left hna)
    · have heq : cell = d := Prod.ext hr hc
      have hd : d ∈ first := heq ▸ hcell
      have ha : a ∈ first := by
        rcases first_choices.1 with ha | hb
        · exact ha
        · exact False.elim ((hfirst.2.1 b hb d hd b_ne_d).2 bd)
      have hnc : c ∉ second := by
        intro hc'
        exact (hsecond.2.1 a (hbit.mp ha) c hc' a_ne_c).2 ac
      exact heq ▸ (second_choices.2.1.resolve_left hnc)
  have upper : rookCount (permGrid w) ≤ 2 := by
    let placements := (permGrid w).powerset.filter (IsRookPlacement (permGrid w))
    have hcard : placements.card ≤ (Finset.univ : Finset Bool).card := by
      apply Finset.card_le_card_of_injOn (fun rooks => decide (a ∈ rooks))
      · intro rooks _; exact Finset.mem_univ _
      · intro first hfirst second hsecond heq
        have hbit : a ∈ first ↔ a ∈ second := by
          simpa only [decide_eq_decide] using heq
        have hpfirst := (Finset.mem_filter.mp hfirst).2
        have hpsecond := (Finset.mem_filter.mp hsecond).2
        exact Finset.Subset.antisymm (determines first second hpfirst hpsecond hbit)
          (determines second first hpsecond hpfirst hbit.symm)
    change placements.card ≤ 2
    simpa only [Finset.card_univ, Fintype.card_bool] using hcard
  obtain ⟨initial, hinitial⟩ := Finset.card_pos.mp (count_positive positive w)
  have initial_placement := (Finset.mem_filter.mp hinitial).2
  let square : Finset (Cell n) := {a, b, c, d}
  have square_info (cell : Cell n) (hcell : cell ∈ square) :
      (cell.1 = top ∨ cell.1 = bottom) ∧ (cell.2 = left ∨ cell.2 = right) := by
    simp only [square, Finset.mem_insert, Finset.mem_singleton] at hcell
    rcases hcell with rfl | rfl | rfl | rfl <;> simp [a, b, c, d]
  have swap_white (cell : Cell n) (hcell : cell ∈ permGrid w) :
      cell.swap ∈ permGrid w.symm := by
    simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and] at hcell ⊢
    intro heq
    exact hcell (w.symm_apply_eq.mp heq).symm
  have swap_down (first second : Cell n) (hword : SameDown (permGrid w) first second) :
      SameAcross (permGrid w.symm) first.swap second.swap := by
    refine ⟨hword.1, ?_⟩
    intro column hmin hmax
    have hwhite := hword.2 column hmin hmax
    simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and] at hwhite ⊢
    intro heq
    exact hwhite (w.symm_apply_eq.mp heq).symm
  have isolated (cell : Cell n) (hcell : cell ∈ square) (other : Cell n)
      (hother : other ∈ forced) :
      ¬ SameAcross (permGrid w) cell other ∧ ¬ SameDown (permGrid w) cell other := by
    obtain ⟨hr, hc⟩ := square_info cell hcell
    have hwhite := square_white cell.1 cell.2 hr hc
    have inward : ((w cell.1).val < cc ∧ w cell.1 < cell.2) ∨
        (cc ≤ (w cell.1).val ∧ cell.2 < w cell.1) := by
      rcases hr with hr | hr <;> rcases hc with hc | hc <;> rw [hr, hc]
      all_goals rcases boundary with ⟨htl, hbr, _, _⟩ | ⟨htr, hbl, _, _⟩
      all_goals first | left; constructor <;> omega | right; constructor <;> omega
    have inward_inverse : ((w.symm cell.2).val < rc ∧ w.symm cell.2 < cell.1) ∨
        (rc ≤ (w.symm cell.2).val ∧ cell.1 < w.symm cell.2) := by
      rcases hr with hr | hr <;> rcases hc with hc | hc <;> rw [hr, hc]
      all_goals rcases boundary with ⟨_, _, hbl, hrt⟩ | ⟨_, _, hlt, hbr⟩
      all_goals first | left; constructor <;> omega | right; constructor <;> omega
    refine ⟨boundary_word w rc cc cell other hwhite hother
      (hr.elim (fun h => Or.inl (h ▸ htop)) (fun h => Or.inr (h ▸ hbottom))) inward, ?_⟩
    intro hword
    have hswap : other.swap ∈ neighbors w.symm cc rc := by
      rw [← swap_neighbors]
      exact Finset.mem_image.mpr ⟨other, hother, rfl⟩
    exact boundary_word w.symm cc rc cell.swap other.swap (swap_white cell hwhite) hswap
      (hc.elim (fun h => Or.inl (by simpa only [Prod.fst_swap, h] using hleft))
        (fun h => Or.inr (by simpa only [Prod.fst_swap, h] using hright)))
      inward_inverse (swap_down cell other hword)
  have across_trans (first middle last : Cell n)
      (hf : first ∈ permGrid w) (hm : middle ∈ permGrid w) (hl : last ∈ permGrid w)
      (hfm : SameAcross (permGrid w) first middle)
      (hml : SameAcross (permGrid w) middle last) : SameAcross (permGrid w) first last := by
    obtain ⟨hrow, hside⟩ := (across _ hf _ hm).mp hfm
    obtain ⟨hrow', hside'⟩ := (across _ hm _ hl).mp hml
    exact (across _ hf _ hl).mpr ⟨hrow.trans hrow', hside.trans hside'⟩
  have down_trans (first middle last : Cell n)
      (hf : first ∈ permGrid w) (hm : middle ∈ permGrid w) (hl : last ∈ permGrid w)
      (hfm : SameDown (permGrid w) first middle)
      (hml : SameDown (permGrid w) middle last) : SameDown (permGrid w) first last := by
    exact (data.down_iff _ hf _ hl).mpr
      (((data.down_iff _ hf _ hm).mp hfm).trans ((data.down_iff _ hm _ hl).mp hml))
  have across_sym (first second : Cell n)
      (hf : first ∈ permGrid w) (hs : second ∈ permGrid w)
      (hword : SameAcross (permGrid w) first second) : SameAcross (permGrid w) second first := by
    obtain ⟨hrow, hside⟩ := (across _ hf _ hs).mp hword
    exact (across _ hs _ hf).mpr ⟨hrow.symm, hside.symm⟩
  have down_sym (first second : Cell n)
      (hf : first ∈ permGrid w) (hs : second ∈ permGrid w)
      (hword : SameDown (permGrid w) first second) : SameDown (permGrid w) second first := by
    exact (data.down_iff _ hs _ hf).mpr ((data.down_iff _ hf _ hs).mp hword).symm
  have across_refl (cell : Cell n) (hcell : cell ∈ permGrid w) :
      SameAcross (permGrid w) cell cell := (across _ hcell _ hcell).mpr ⟨rfl, Iff.rfl⟩
  have down_refl (cell : Cell n) (hcell : cell ∈ permGrid w) :
      SameDown (permGrid w) cell cell := (data.down_iff _ hcell _ hcell).mpr rfl
  have fill (first second : Cell n) (hfirst : first ∈ square) (hsecond : second ∈ square)
      (different_row : first.1 ≠ second.1) (different_column : first.2 ≠ second.2)
      (across_cover : ∀ cell ∈ square,
        SameAcross (permGrid w) cell first ∨ SameAcross (permGrid w) cell second)
      (down_cover : ∀ cell ∈ square,
        SameDown (permGrid w) cell first ∨ SameDown (permGrid w) cell second) :
      IsRookPlacement (permGrid w) (forced ∪ {first, second}) := by
    have hwfirst := square_white _ _ (square_info _ hfirst).1 (square_info _ hfirst).2
    have hwsecond := square_white _ _ (square_info _ hsecond).1 (square_info _ hsecond).2
    have hforced := forced_subset initial initial_placement
    have hsub : forced ∪ {first, second} ⊆ permGrid w := by
      intro cell hcell
      rcases Finset.mem_union.mp hcell with hf | hp
      · exact initial_placement.1 (hforced hf)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hwfirst
        · exact hwsecond
    refine ⟨hsub, ?_, ?_⟩
    · intro cell hcell other hother hne
      rcases Finset.mem_union.mp hcell with hcf | hcp <;>
        rcases Finset.mem_union.mp hother with hof | hop
      · exact initial_placement.2.1 _ (hforced hcf) _ (hforced hof) hne
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hop
        rcases hop with rfl | rfl
        all_goals
          refine ⟨?_, ?_⟩
          · intro hword
            exact (isolated _ (by assumption) cell hcf).1
              (across_sym _ _ (hsub hcell) (hsub hother) hword)
          · intro hword
            exact (isolated _ (by assumption) cell hcf).2
              (down_sym _ _ (hsub hcell) (hsub hother) hword)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hcp
        rcases hcp with rfl | rfl
        · exact isolated _ hfirst other hof
        · exact isolated _ hsecond other hof
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hcp hop
        rcases hcp with rfl | rfl <;> rcases hop with rfl | rfl
        · exact False.elim (hne rfl)
        · exact ⟨fun h => different_row h.1, fun h => different_column h.1⟩
        · exact ⟨fun h => different_row h.1.symm, fun h => different_column h.1.symm⟩
        · exact False.elim (hne rfl)
    · intro cell hcell
      obtain ⟨old_across, h_old_across, h_across⟩ := (initial_placement.2.2 cell hcell).1
      obtain ⟨old_down, h_old_down, h_down⟩ := (initial_placement.2.2 cell hcell).2
      constructor
      · rcases capture initial initial_placement old_across h_old_across with hf | ⟨hr, hc⟩
        · exact ⟨old_across, Finset.mem_union_left _ hf, h_across⟩
        · have hsquare : old_across ∈ square := by
            simp only [square, Finset.mem_insert, Finset.mem_singleton]
            rcases hr with hr | hr <;> rcases hc with hc | hc
            · exact Or.inl (Prod.ext hr hc)
            · exact Or.inr (Or.inl (Prod.ext hr hc))
            · exact Or.inr (Or.inr (Or.inl (Prod.ext hr hc)))
            · exact Or.inr (Or.inr (Or.inr (Prod.ext hr hc)))
          rcases across_cover old_across hsquare with hword | hword
          · exact ⟨first, by simp, across_trans _ _ _ hcell
              (initial_placement.1 h_old_across) hwfirst h_across hword⟩
          · exact ⟨second, by simp, across_trans _ _ _ hcell
              (initial_placement.1 h_old_across) hwsecond h_across hword⟩
      · rcases capture initial initial_placement old_down h_old_down with hf | ⟨hr, hc⟩
        · exact ⟨old_down, Finset.mem_union_left _ hf, h_down⟩
        · have hsquare : old_down ∈ square := by
            simp only [square, Finset.mem_insert, Finset.mem_singleton]
            rcases hr with hr | hr <;> rcases hc with hc | hc
            · exact Or.inl (Prod.ext hr hc)
            · exact Or.inr (Or.inl (Prod.ext hr hc))
            · exact Or.inr (Or.inr (Or.inl (Prod.ext hr hc)))
            · exact Or.inr (Or.inr (Or.inr (Prod.ext hr hc)))
          rcases down_cover old_down hsquare with hword | hword
          · exact ⟨first, by simp, down_trans _ _ _ hcell
              (initial_placement.1 h_old_down) hwfirst h_down hword⟩
          · exact ⟨second, by simp, down_trans _ _ _ hcell
              (initial_placement.1 h_old_down) hwsecond h_down hword⟩
  have placement_ad : IsRookPlacement (permGrid w) (forced ∪ {a, d}) := by
    apply fill a d (by simp [square]) (by simp [square])
      (fun heq => (ne_of_lt row_order) heq) (fun heq => (ne_of_lt col_order) heq)
    · intro cell hcell
      simp only [square, Finset.mem_insert, Finset.mem_singleton] at hcell
      rcases hcell with rfl | rfl | rfl | rfl
      · exact Or.inl (across_refl a white_a)
      · exact Or.inl (across_sym _ _ white_a white_b ab)
      · exact Or.inr cd
      · exact Or.inr (across_refl d white_d)
    · intro cell hcell
      simp only [square, Finset.mem_insert, Finset.mem_singleton] at hcell
      rcases hcell with rfl | rfl | rfl | rfl
      · exact Or.inl (down_refl a white_a)
      · exact Or.inr bd
      · exact Or.inl (down_sym _ _ white_a white_c ac)
      · exact Or.inr (down_refl d white_d)
  have placement_bc : IsRookPlacement (permGrid w) (forced ∪ {b, c}) := by
    apply fill b c (by simp [square]) (by simp [square])
      (fun heq => (ne_of_lt row_order) heq) (fun heq => (ne_of_gt col_order) heq)
    · intro cell hcell
      simp only [square, Finset.mem_insert, Finset.mem_singleton] at hcell
      rcases hcell with rfl | rfl | rfl | rfl
      · exact Or.inl ab
      · exact Or.inl (across_refl b white_b)
      · exact Or.inr (across_refl c white_c)
      · exact Or.inr (across_sym _ _ white_c white_d cd)
    · intro cell hcell
      simp only [square, Finset.mem_insert, Finset.mem_singleton] at hcell
      rcases hcell with rfl | rfl | rfl | rfl
      · exact Or.inr ac
      · exact Or.inl (down_refl b white_b)
      · exact Or.inr (down_refl c white_c)
      · exact Or.inl (down_sym _ _ white_b white_d bd)
  have different : forced ∪ {a, d} ≠ forced ∪ {b, c} := by
    intro heq
    have ha : a ∈ forced ∪ {b, c} := heq ▸ (by simp : a ∈ forced ∪ {a, d})
    rcases Finset.mem_union.mp ha with hf | hp
    · exact (isolated a (by simp [square]) a hf).1 (across_refl a white_a)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      exact hp.elim a_ne_b a_ne_c
  have lower : 2 ≤ rookCount (permGrid w) := by
    have hmem_ad : forced ∪ {a, d} ∈
        (permGrid w).powerset.filter (IsRookPlacement (permGrid w)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr placement_ad.1, placement_ad⟩
    have hmem_bc : forced ∪ {b, c} ∈
        (permGrid w).powerset.filter (IsRookPlacement (permGrid w)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr placement_bc.1, placement_bc⟩
    exact Finset.one_lt_card.mpr ⟨_, hmem_ad, _, hmem_bc, different⟩
  exact Or.inr (by omega)

end D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookForward
