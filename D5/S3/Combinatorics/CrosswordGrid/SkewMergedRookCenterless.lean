/- GID: D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookCenterless
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/SkewMergedRookCenterless
   mirror-E: none(waiver:centerless-quadrant-structure)
   anchors: []
   utility: none
   digest: Forced-color obstructions separate centerless permutations into four quadrants. -/

import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookRegions
import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookPlacements

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookCenterless

open D5.S3.Combinatorics.CrosswordRookCounts (Cell IsRookPlacement)
open D5.S3.Combinatorics.CrosswordPermutationGridRefutation (permGrid)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords
  (symmetries record_prefix_forces_neighbor)

set_option maxHeartbeats 2000000 in
theorem centerless_cuts {n : ℕ} (positive : 1 ≤ n) (w : Equiv.Perm (Fin n))
    (increasing : Finset (Fin n))
    (inc : ∀ row ∈ increasing, ∀ other ∈ increasing, row < other → w row < w other)
    (dec : ∀ row ∉ increasing, ∀ other ∉ increasing, row < other → w other < w row)
    (no_overlap : ¬ ∃ first second : Finset (Fin n),
      first ∪ second = Finset.univ ∧
      (∀ row ∈ first, ∀ other ∈ first, row < other → w row < w other) ∧
      (∀ row ∈ second, ∀ other ∈ second, row < other → w other < w row) ∧
      ∃ pivot : Fin n, pivot ∈ first ∧ pivot ∈ second) :
    ∃ row_cut column_cut : ℕ,
      0 < row_cut ∧ row_cut < n ∧ 0 < column_cut ∧ column_cut < n ∧
      (∀ row : Fin n, row ∈ increasing ↔
        (row.val < row_cut ↔ (w row).val < column_cut)) ∧
      (∃ row : Fin n, row.val < row_cut ∧ (w row).val < column_cut) ∧
      (∃ row : Fin n, row.val < row_cut ∧ column_cut ≤ (w row).val) ∧
      (∃ row : Fin n, row_cut ≤ row.val ∧ (w row).val < column_cut) ∧
      (∃ row : Fin n, row_cut ≤ row.val ∧ column_cut ≤ (w row).val) ∧
      (∃ top bottom left right : Fin n,
        top.val + 1 = row_cut ∧ bottom.val = row_cut ∧
        left.val + 1 = column_cut ∧ right.val = column_cut ∧
        (((w top < left) ∧ (right < w bottom) ∧
          (bottom < w.symm left) ∧ (w.symm right < top)) ∨
         ((right < w top) ∧ (w bottom < left) ∧
          (w.symm left < top) ∧ (bottom < w.symm right)))) ∧
      (∀ rooks : Finset (Cell n), IsRookPlacement (permGrid w) rooks →
        ∀ cell : Cell n,
          ((cell.2.val + 1 = (w cell.1).val ∧ (w cell.1).val < column_cut) ∨
           ((w cell.1).val + 1 = cell.2.val ∧ column_cut ≤ (w cell.1).val) ∨
           (cell.1.val + 1 = (w.symm cell.2).val ∧ (w.symm cell.2).val < row_cut) ∨
           ((w.symm cell.2).val + 1 = cell.1.val ∧ row_cut ≤ (w.symm cell.2).val)) →
          cell ∈ rooks) := by
  classical
  have inc_le (row other : Fin n) (hr : row ∈ increasing) (ho : other ∈ increasing)
      (hle : row ≤ other) : w row ≤ w other := by
    rcases hle.eq_or_lt with heq | hlt
    · simp [heq]
    · exact (inc row hr other ho hlt).le
  have dec_le (row other : Fin n) (hr : row ∉ increasing) (ho : other ∉ increasing)
      (hle : row ≤ other) : w other ≤ w row := by
    rcases hle.eq_or_lt with heq | hlt
    · simp [heq]
    · exact (dec row hr other ho hlt).le
  have inc_obstruction (row : Fin n) (hr : row ∈ increasing) :
      (∃ other : Fin n, other ∉ increasing ∧ row < other ∧ w row < w other) ∨
      (∃ other : Fin n, other ∉ increasing ∧ other < row ∧ w other < w row) := by
    by_contra absent
    have compatible (other : Fin n) (ho : other ∉ increasing) :
        (row < other → w other < w row) ∧ (other < row → w row < w other) := by
      have hne : w row ≠ w other := fun heq => ho (w.injective heq ▸ hr)
      constructor
      · intro hlt
        by_contra bad
        exact absent (Or.inl ⟨other, ho, hlt, lt_of_le_of_ne (le_of_not_gt bad) hne⟩)
      · intro hlt
        by_contra bad
        exact absent (Or.inr ⟨other, ho, hlt, lt_of_le_of_ne (le_of_not_gt bad) hne.symm⟩)
    apply no_overlap
    refine ⟨increasing, insert row (Finset.univ \ increasing), by simp [hr], inc, ?_,
      row, hr, Finset.mem_insert_self _ _⟩
    intro first hfirst second hsecond hlt
    rcases Finset.mem_insert.mp hfirst with hfirst_eq | hfirst_rest <;>
      rcases Finset.mem_insert.mp hsecond with hsecond_eq | hsecond_rest
    · exact False.elim (lt_irrefl row (by simpa only [hfirst_eq, hsecond_eq] using hlt))
    · exact hfirst_eq ▸ (compatible second (Finset.mem_sdiff.mp hsecond_rest).2).1
        (hfirst_eq ▸ hlt)
    · exact hsecond_eq ▸ (compatible first (Finset.mem_sdiff.mp hfirst_rest).2).2
        (hsecond_eq ▸ hlt)
    · exact dec first (Finset.mem_sdiff.mp hfirst_rest).2 second
        (Finset.mem_sdiff.mp hsecond_rest).2 hlt
  have dec_obstruction (row : Fin n) (hr : row ∉ increasing) :
      (∃ other : Fin n, other ∈ increasing ∧ row < other ∧ w other < w row) ∨
      (∃ other : Fin n, other ∈ increasing ∧ other < row ∧ w row < w other) := by
    by_contra absent
    have compatible (other : Fin n) (ho : other ∈ increasing) :
        (row < other → w row < w other) ∧ (other < row → w other < w row) := by
      have hne : w row ≠ w other := fun heq => hr (w.injective heq ▸ ho)
      constructor
      · intro hlt
        by_contra bad
        exact absent (Or.inl ⟨other, ho, hlt, lt_of_le_of_ne (le_of_not_gt bad) hne.symm⟩)
      · intro hlt
        by_contra bad
        exact absent (Or.inr ⟨other, ho, hlt, lt_of_le_of_ne (le_of_not_gt bad) hne⟩)
    apply no_overlap
    refine ⟨insert row increasing, Finset.univ \ increasing, by simp, ?_, ?_,
      row, Finset.mem_insert_self _ _, by simp [hr]⟩
    · intro first hfirst second hsecond hlt
      rcases Finset.mem_insert.mp hfirst with hfirst_eq | hfirst_rest <;>
        rcases Finset.mem_insert.mp hsecond with hsecond_eq | hsecond_rest
      · exact False.elim (lt_irrefl row (by simpa only [hfirst_eq, hsecond_eq] using hlt))
      · exact hfirst_eq ▸ (compatible second hsecond_rest).1 (hfirst_eq ▸ hlt)
      · exact hsecond_eq ▸ (compatible first hfirst_rest).2 (hsecond_eq ▸ hlt)
      · exact inc first hfirst_rest second hsecond_rest hlt
    · intro first hfirst second hsecond hlt
      exact dec first (Finset.mem_sdiff.mp hfirst).2 second
        (Finset.mem_sdiff.mp hsecond).2 hlt
  let nw := fun row : Fin n => row ∈ increasing ∧
    ∃ other : Fin n, other ∉ increasing ∧ row < other ∧ w row < w other
  let se := fun row : Fin n => row ∈ increasing ∧
    ∃ other : Fin n, other ∉ increasing ∧ other < row ∧ w other < w row
  let ne := fun row : Fin n => row ∉ increasing ∧
    ∃ other : Fin n, other ∈ increasing ∧ row < other ∧ w other < w row
  let sw := fun row : Fin n => row ∉ increasing ∧
    ∃ other : Fin n, other ∈ increasing ∧ other < row ∧ w row < w other
  have all (row : Fin n) : (nw row ∨ se row) ∨ (ne row ∨ sw row) := by
    by_cases hr : row ∈ increasing
    · exact Or.inl ((inc_obstruction row hr).imp (And.intro hr) (And.intro hr))
    · exact Or.inr ((dec_obstruction row hr).imp (And.intro hr) (And.intro hr))
  have nw_se (first second : Fin n) (hf : nw first) (hs : se second) :
      first < second ∧ w first < w second := by
    obtain ⟨hfirst, earlier, hearlier, hebefore, hevalue⟩ := hs
    obtain ⟨hsecond, later, hlater, hlafter, hlvalue⟩ := hf
    have order : first < second := by
      by_contra bad
      have hinc := inc_le second first hfirst hsecond (le_of_not_gt bad)
      have hdec := dec earlier hearlier later hlater
        (hebefore.trans_le ((le_of_not_gt bad).trans hlafter.le))
      exact (not_lt_of_ge (hevalue.le.trans (hinc.trans hlvalue.le))) hdec
    exact ⟨order, inc first hsecond second hfirst order⟩
  have ne_sw (first second : Fin n) (hf : ne first) (hs : sw second) :
      first < second ∧ w second < w first := by
    obtain ⟨hfirst, earlier, hearlier, hebefore, hevalue⟩ := hs
    obtain ⟨hsecond, later, hlater, hlafter, hlvalue⟩ := hf
    have order : first < second := by
      by_contra bad
      have hdec := dec_le second first hfirst hsecond (le_of_not_gt bad)
      have hinc := inc earlier hearlier later hlater
        (hebefore.trans_le ((le_of_not_gt bad).trans hlafter.le))
      exact (not_lt_of_ge (hlvalue.le.trans (hdec.trans hevalue.le))) hinc
    exact ⟨order, dec first hsecond second hfirst order⟩
  have nw_sw (first second : Fin n) (hf : nw first) (hs : sw second) :
      first < second := by
    obtain ⟨hi, later, hdl, hfl, hvfl⟩ := hf
    obtain ⟨hd, earlier, hie, hes, hvse⟩ := hs
    by_contra bad
    have hif := inc earlier hie first hi (hes.trans_le (le_of_not_gt bad))
    have hdl := dec second hd later hdl ((le_of_not_gt bad).trans_lt hfl)
    exact lt_irrefl _ (hvse.trans (hif.trans (hvfl.trans hdl)))
  have ne_se (first second : Fin n) (hf : ne first) (hs : se second) :
      first < second := by
    obtain ⟨hd, later, hil, hfl, hvlf⟩ := hf
    obtain ⟨hi, earlier, hde, hes, hves⟩ := hs
    by_contra bad
    have hdf := dec earlier hde first hd (hes.trans_le (le_of_not_gt bad))
    have hil := inc second hi later hil ((le_of_not_gt bad).trans_lt hfl)
    exact lt_irrefl _ (hves.trans (hil.trans (hvlf.trans hdf)))
  have nw_ne (first second : Fin n) (hf : nw first) (hs : ne second) :
      w first < w second := by
    obtain ⟨hi, later, hdl, hfl, hvfl⟩ := hf
    obtain ⟨hd, after, hia, hsa, hvas⟩ := hs
    by_contra bad
    have hvalue : w second ≤ w first := le_of_not_gt bad
    have later_before : later < second := by
      by_contra hbad
      have hbound := dec_le second later hd hdl (le_of_not_gt hbad)
      exact (not_lt_of_ge (hbound.trans hvalue)) hvfl
    have hincrease := inc first hi after hia (hfl.trans (later_before.trans hsa))
    exact (not_lt_of_ge hvalue) (hincrease.trans hvas)
  have sw_se (first second : Fin n) (hf : sw first) (hs : se second) :
      w first < w second := by
    obtain ⟨hd, earlier, hie, hef, hvfe⟩ := hf
    obtain ⟨hi, before, hdb, hbs, hvbs⟩ := hs
    by_contra bad
    have hvalue : w second ≤ w first := le_of_not_gt bad
    have second_before : second < earlier := by
      by_contra hbad
      have hbound := inc_le earlier second hie hi (le_of_not_gt hbad)
      exact (not_lt_of_ge (hbound.trans hvalue)) hvfe
    have hdecrease := dec before hdb first hd (hbs.trans (second_before.trans hef))
    exact (not_lt_of_ge hvalue) (hdecrease.trans hvbs)
  have inc_nonempty : increasing.Nonempty := by
    let row : Fin n := ⟨0, by omega⟩
    by_cases hr : row ∈ increasing
    · exact ⟨row, hr⟩
    · rcases dec_obstruction row hr with ⟨other, ho, _⟩ | ⟨other, ho, _⟩ <;>
        exact ⟨other, ho⟩
  have dec_nonempty : (Finset.univ \ increasing).Nonempty := by
    obtain ⟨row, hr⟩ := inc_nonempty
    rcases inc_obstruction row hr with ⟨other, ho, _⟩ | ⟨other, ho, _⟩ <;>
      exact ⟨other, by simp [ho]⟩
  have exists_nw : ∃ row : Fin n, nw row := by
    obtain ⟨row, hr, hmin⟩ := increasing.exists_min_image id inc_nonempty
    rcases inc_obstruction row hr with witness | ⟨other, ho, hother, hvalue⟩
    · exact ⟨row, hr, witness⟩
    · rcases dec_obstruction other ho with ⟨later, hl, hlt, hvl⟩ | ⟨earlier, he, hlt, _⟩
      · have hbound := inc_le row later hr hl (hmin later hl)
        exact False.elim (not_lt_of_ge hbound (hvl.trans hvalue))
      · exact False.elim (not_lt_of_ge (hmin earlier he) (hlt.trans hother))
  have exists_se : ∃ row : Fin n, se row := by
    obtain ⟨row, hr, hmax⟩ := increasing.exists_max_image id inc_nonempty
    rcases inc_obstruction row hr with ⟨other, ho, hother, hvalue⟩ | witness
    · rcases dec_obstruction other ho with ⟨later, hl, hlt, _⟩ | ⟨earlier, he, hlt, hve⟩
      · exact False.elim (not_lt_of_ge (hmax later hl) (hother.trans hlt))
      · have hbound := inc_le earlier row he hr (hmax earlier he)
        exact False.elim (not_lt_of_ge hbound (hvalue.trans hve))
    · exact ⟨row, hr, witness⟩
  have exists_ne : ∃ row : Fin n, ne row := by
    obtain ⟨row, hr, hmin⟩ := (Finset.univ \ increasing).exists_min_image id dec_nonempty
    have hr' := (Finset.mem_sdiff.mp hr).2
    rcases dec_obstruction row hr' with witness | ⟨other, ho, hother, hvalue⟩
    · exact ⟨row, hr', witness⟩
    · rcases inc_obstruction other ho with ⟨later, hl, hlt, hvl⟩ | ⟨earlier, he, hlt, _⟩
      · have hbound := dec_le row later hr' hl (hmin later (by simp [hl]))
        exact False.elim (not_lt_of_ge hbound (hvalue.trans hvl))
      · exact False.elim (not_lt_of_ge (hmin earlier (by simp [he])) (hlt.trans hother))
  have exists_sw : ∃ row : Fin n, sw row := by
    obtain ⟨row, hr, hmax⟩ := (Finset.univ \ increasing).exists_max_image id dec_nonempty
    have hr' := (Finset.mem_sdiff.mp hr).2
    rcases dec_obstruction row hr' with ⟨other, ho, hother, hvalue⟩ | witness
    · rcases inc_obstruction other ho with ⟨later, hl, hlt, _⟩ | ⟨earlier, he, hlt, hve⟩
      · exact False.elim (not_lt_of_ge (hmax later (by simp [hl])) (hother.trans hlt))
      · have hbound := dec_le earlier row he hr' (hmax earlier (by simp [he]))
        exact False.elim (not_lt_of_ge hbound (hve.trans hvalue))
    · exact ⟨row, hr', witness⟩
  let early := Finset.univ.filter (fun row : Fin n => nw row ∨ ne row)
  let left := Finset.univ.filter (fun row : Fin n => nw row ∨ sw row)
  have row_separation (first second : Fin n) (hf : nw first ∨ ne first)
      (hs : sw second ∨ se second) : first < second := by
    rcases hf with hf | hf <;> rcases hs with hs | hs
    · exact nw_sw first second hf hs
    · exact (nw_se first second hf hs).1
    · exact (ne_sw first second hf hs).1
    · exact ne_se first second hf hs
  have column_separation (first second : Fin n) (hf : nw first ∨ sw first)
      (hs : ne second ∨ se second) : w first < w second := by
    rcases hf with hf | hf <;> rcases hs with hs | hs
    · exact nw_ne first second hf hs
    · exact (nw_se first second hf hs).2
    · exact (ne_sw second first hs hf).2
    · exact sw_se first second hf hs
  obtain ⟨nw_point, hnw⟩ := exists_nw
  obtain ⟨ne_point, hne⟩ := exists_ne
  obtain ⟨sw_point, hsw⟩ := exists_sw
  obtain ⟨se_point, hse⟩ := exists_se
  have early_nonempty : early.Nonempty := ⟨nw_point, by simp [early, hnw]⟩
  have left_nonempty : left.Nonempty := ⟨nw_point, by simp [left, hnw]⟩
  obtain ⟨last_row, hlast_row, row_max⟩ := early.exists_max_image Fin.val early_nonempty
  obtain ⟨last_left, hlast_left, column_max⟩ := left.exists_max_image
    (fun row => (w row).val) left_nonempty
  have hlast_row' : nw last_row ∨ ne last_row := (Finset.mem_filter.mp hlast_row).2
  have hlast_left' : nw last_left ∨ sw last_left := (Finset.mem_filter.mp hlast_left).2
  have row_iff (row : Fin n) : row.val < last_row.val + 1 ↔ nw row ∨ ne row := by
    constructor
    · intro hlt
      rcases all row with ⟨hr | hr⟩ | ⟨hr | hr⟩
      · exact Or.inl hr
      · have hbound := row_separation last_row row hlast_row' (Or.inr hr)
        change last_row.val < row.val at hbound
        omega
      · exact Or.inr hr
      · have hbound := row_separation last_row row hlast_row' (Or.inl hr)
        change last_row.val < row.val at hbound
        omega
    · intro hr
      have hbound := row_max row (by simp [early, hr])
      omega
  have column_iff (row : Fin n) : (w row).val < (w last_left).val + 1 ↔ nw row ∨ sw row := by
    constructor
    · intro hlt
      rcases all row with ⟨hr | hr⟩ | ⟨hr | hr⟩
      · exact Or.inl hr
      · have hbound := column_separation last_left row hlast_left' (Or.inr hr)
        change (w last_left).val < (w row).val at hbound
        omega
      · have hbound := column_separation last_left row hlast_left' (Or.inl hr)
        change (w last_left).val < (w row).val at hbound
        omega
      · exact Or.inr hr
    · intro hr
      have hbound := column_max row (by simp [left, hr])
      omega
  have late_not_early (row : Fin n) (hr : sw row ∨ se row) : ¬ (nw row ∨ ne row) := by
    intro he
    exact lt_irrefl _ (row_separation row row he hr)
  have right_not_left (row : Fin n) (hr : ne row ∨ se row) : ¬ (nw row ∨ sw row) := by
    intro hl
    exact lt_irrefl _ (column_separation row row hl hr)
  have row_bound : last_row.val + 1 < n := by
    have hbound := row_separation last_row se_point hlast_row' (Or.inr hse)
    have := se_point.isLt
    change last_row.val < se_point.val at hbound
    omega
  have column_bound : (w last_left).val + 1 < n := by
    have hbound := column_separation last_left se_point hlast_left' (Or.inr hse)
    have := (w se_point).isLt
    change (w last_left).val < (w se_point).val at hbound
    omega
  have partition_iff (row : Fin n) : row ∈ increasing ↔
      (row.val < last_row.val + 1 ↔ (w row).val < (w last_left).val + 1) := by
    rw [row_iff, column_iff]
    rcases all row with ⟨hr | hr⟩ | ⟨hr | hr⟩
    · have hi := hr.1
      simp only [hi, hr, true_or, iff_self]
    · have hi := hr.1
      have he := late_not_early row (Or.inr hr)
      have hl := right_not_left row (Or.inr hr)
      simp only [hi, he, hl, iff_self]
    · have hd := hr.1
      have hl := right_not_left row (Or.inl hr)
      simp only [hd, hr, or_true, hl, iff_false, not_true_eq_false]
    · have hd := hr.1
      have he := late_not_early row (Or.inl hr)
      simp only [hd, hr, or_true, he, iff_true]
  let bottom : Fin n := ⟨last_row.val + 1, row_bound⟩
  let left := w last_left
  let right : Fin n := ⟨left.val + 1, column_bound⟩
  have top_order : last_row < bottom := by change last_row.val < last_row.val + 1; omega
  have column_order : left < right := by change left.val < left.val + 1; omega
  have top_type : nw last_row ∨ ne last_row := hlast_row'
  have bottom_type : sw bottom ∨ se bottom := by
    rcases all bottom with ⟨hr | hr⟩ | ⟨hr | hr⟩
    · have early_bottom := (row_iff bottom).mpr (Or.inl hr)
      change last_row.val + 1 < last_row.val + 1 at early_bottom
      omega
    · exact Or.inr hr
    · have early_bottom := (row_iff bottom).mpr (Or.inr hr)
      change last_row.val + 1 < last_row.val + 1 at early_bottom
      omega
    · exact Or.inl hr
  have inverse_left : w (w.symm left) = left := w.apply_symm_apply _
  have inverse_right : w (w.symm right) = right := w.apply_symm_apply _
  have boundary :
      ((w last_row < left) ∧ (right < w bottom) ∧
        (bottom < w.symm left) ∧ (w.symm right < last_row)) ∨
      ((right < w last_row) ∧ (w bottom < left) ∧
        (w.symm left < last_row) ∧ (bottom < w.symm right)) := by
    rcases top_type with htop | htop
    · obtain ⟨htop_inc, later, hlater_dec, hlater, hvalue⟩ := htop
      have hlater_bound : bottom ≤ later := by change last_row.val + 1 ≤ later.val; omega
      have hlater_left : w later ≤ left := by
        have hquad := partition_iff later
        have hrow : ¬ later.val < last_row.val + 1 := by
          change ¬ later < bottom
          exact not_lt_of_ge hlater_bound
        have hcol : (w later).val < (w last_left).val + 1 := by
          by_contra hbad
          exact hlater_dec (hquad.mpr ⟨fun h => (hrow h).elim, fun h => (hbad h).elim⟩)
        change (w later).val ≤ (w last_left).val
        omega
      have top_left : w last_row < left := hvalue.trans_le hlater_left
      have bottom_inc : bottom ∈ increasing := by
        rcases bottom_type with ⟨hbottom, earlier, hearlier, hbefore, hvbefore⟩ | hbottom
        · have hearlier_top : earlier ≤ last_row := by
            change earlier.val ≤ last_row.val
            change earlier.val < last_row.val + 1 at hbefore
            omega
          have hibound := inc_le earlier last_row hearlier htop_inc hearlier_top
          have hdbound := dec_le bottom later hbottom hlater_dec hlater_bound
          exact False.elim (not_lt_of_ge (hdbound.trans (hvbefore.le.trans hibound)) hvalue)
        · exact hbottom.1
      have bottom_right : right < w bottom := by
        rcases bottom_type with hbottom | ⟨_, earlier, hearlier, hbefore, hvbefore⟩
        · exact False.elim (hbottom.1 bottom_inc)
        · have hearly : earlier.val < last_row.val + 1 := hbefore
          have hquad := partition_iff earlier
          have hcol : (w last_left).val + 1 ≤ (w earlier).val := by
            have : ¬ (w earlier).val < (w last_left).val + 1 := by
              intro hcol
              exact hearlier (hquad.mpr ⟨fun _ => hcol, fun _ => hearly⟩)
            omega
          exact (show right ≤ w earlier from hcol).trans_lt hvbefore
      have left_late : bottom < w.symm left := by
        have after_top : last_row < w.symm left := by
          by_contra bad
          have hrow : (w.symm left).val < last_row.val + 1 := by
            have hle := le_of_not_gt bad
            change (w.symm left).val ≤ last_row.val at hle
            omega
          have hcol : (w (w.symm left)).val < (w last_left).val + 1 := by
            rw [inverse_left]; change (w last_left).val < (w last_left).val + 1; omega
          have hi := (partition_iff _).mpr ⟨fun _ => hcol, fun _ => hrow⟩
          have hbound := inc_le (w.symm left) last_row hi htop_inc (le_of_not_gt bad)
          rw [inverse_left] at hbound
          exact not_lt_of_ge hbound top_left
        have hne : w.symm left ≠ bottom := by
          intro heq
          rw [heq] at inverse_left
          exact not_lt_of_ge column_order.le (inverse_left ▸ bottom_right)
        change last_row.val + 1 < (w.symm left).val
        have hneval := Fin.val_ne_of_ne hne
        change last_row.val < (w.symm left).val at after_top
        change (w.symm left).val ≠ last_row.val + 1 at hneval
        omega
      have right_early : w.symm right < last_row := by
        have before_bottom : w.symm right < bottom := by
          by_contra bad
          have hrow : ¬ (w.symm right).val < last_row.val + 1 := not_lt_of_ge (le_of_not_gt bad)
          have hcol : ¬ (w (w.symm right)).val < (w last_left).val + 1 := by
            rw [inverse_right]; change ¬ left.val + 1 < left.val + 1; omega
          have hi := (partition_iff _).mpr
            ⟨fun h => (hrow h).elim, fun h => (hcol h).elim⟩
          have hbound := inc_le bottom (w.symm right) bottom_inc hi (le_of_not_gt bad)
          rw [inverse_right] at hbound
          exact not_lt_of_ge hbound bottom_right
        have hne : w.symm right ≠ last_row := by
          intro heq
          rw [heq] at inverse_right
          exact not_lt_of_ge column_order.le (inverse_right ▸ top_left)
        have hneval := Fin.val_ne_of_ne hne
        change (w.symm right).val < last_row.val + 1 at before_bottom
        change (w.symm right).val < last_row.val
        omega
      exact Or.inl ⟨top_left, bottom_right, left_late, right_early⟩
    · obtain ⟨htop_dec, later, hlater_inc, hlater, hvalue⟩ := htop
      have hlater_bound : bottom ≤ later := by change last_row.val + 1 ≤ later.val; omega
      have hlater_right : right ≤ w later := by
        have hquad := partition_iff later
        have hrow : ¬ later.val < last_row.val + 1 := not_lt_of_ge hlater_bound
        have hcol : ¬ (w later).val < (w last_left).val + 1 := by
          intro hcol
          exact hrow ((hquad.mp hlater_inc).mpr hcol)
        change left.val + 1 ≤ (w later).val
        omega
      have top_right : right < w last_row := hlater_right.trans_lt hvalue
      have bottom_dec : bottom ∉ increasing := by
        rcases bottom_type with hbottom | ⟨hbottom, earlier, hearlier, hbefore, hvbefore⟩
        · exact hbottom.1
        · have hearlier_top : earlier ≤ last_row := by
            change earlier.val ≤ last_row.val
            change earlier.val < last_row.val + 1 at hbefore
            omega
          have hdbound := dec_le earlier last_row hearlier htop_dec hearlier_top
          have hibound := inc_le bottom later hbottom hlater_inc hlater_bound
          exact False.elim (not_lt_of_ge (hdbound.trans (hvbefore.le.trans hibound)) hvalue)
      have bottom_left : w bottom < left := by
        rcases bottom_type with ⟨_, earlier, hearlier, hbefore, hvbefore⟩ | hbottom
        · have hearly : earlier.val < last_row.val + 1 := hbefore
          have hquad := partition_iff earlier
          have hcol := (hquad.mp hearlier).mp hearly
          have hbound : w earlier ≤ left := by change (w earlier).val ≤ (w last_left).val; omega
          exact hvbefore.trans_le hbound
        · exact False.elim (bottom_dec hbottom.1)
      have left_early : w.symm left < last_row := by
        have before_bottom : w.symm left < bottom := by
          by_contra bad
          have hrow : ¬ (w.symm left).val < last_row.val + 1 := not_lt_of_ge (le_of_not_gt bad)
          have hcol : (w (w.symm left)).val < (w last_left).val + 1 := by
            rw [inverse_left]; change (w last_left).val < (w last_left).val + 1; omega
          have hd : w.symm left ∉ increasing := by
            have hquad := partition_iff (w.symm left)
            intro hi
            exact hrow ((hquad.mp hi).mpr hcol)
          have hbound := dec_le bottom (w.symm left) bottom_dec hd (le_of_not_gt bad)
          rw [inverse_left] at hbound
          exact not_lt_of_ge hbound bottom_left
        have hne : w.symm left ≠ last_row := by
          intro heq
          rw [heq] at inverse_left
          exact not_lt_of_ge column_order.le (inverse_left ▸ top_right)
        have hneval := Fin.val_ne_of_ne hne
        change (w.symm left).val < last_row.val + 1 at before_bottom
        change (w.symm left).val < last_row.val
        omega
      have right_late : bottom < w.symm right := by
        have after_top : last_row < w.symm right := by
          by_contra bad
          have hrow : (w.symm right).val < last_row.val + 1 := by
            have hle := le_of_not_gt bad
            change (w.symm right).val ≤ last_row.val at hle
            omega
          have hcol : ¬ (w (w.symm right)).val < (w last_left).val + 1 := by
            rw [inverse_right]; change ¬ left.val + 1 < left.val + 1; omega
          have hd : w.symm right ∉ increasing := by
            have hquad := partition_iff (w.symm right)
            intro hi
            exact hcol ((hquad.mp hi).mp hrow)
          have hbound := dec_le (w.symm right) last_row hd htop_dec (le_of_not_gt bad)
          rw [inverse_right] at hbound
          exact not_lt_of_ge hbound top_right
        have hne : w.symm right ≠ bottom := by
          intro heq
          rw [heq] at inverse_right
          exact not_lt_of_ge column_order.le (inverse_right ▸ bottom_left)
        have hneval := Fin.val_ne_of_ne hne
        change last_row.val + 1 < (w.symm right).val
        change last_row.val < (w.symm right).val at after_top
        change (w.symm right).val ≠ last_row.val + 1 at hneval
        omega
      exact Or.inr ⟨top_right, bottom_left, left_early, right_late⟩
  have west (permutation : Equiv.Perm (Fin n)) (part : Finset (Fin n))
      (rc cc : ℕ)
      (hinc : ∀ row ∈ part, ∀ other ∈ part, row < other →
        permutation row < permutation other)
      (hdec : ∀ row ∉ part, ∀ other ∉ part, row < other →
        permutation other < permutation row)
      (hquad : ∀ row : Fin n, row ∈ part ↔
        (row.val < rc ↔ (permutation row).val < cc))
      (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid permutation) rooks) :
      ∀ column previous : Fin n, previous.val + 1 = column.val → column.val < cc →
        (permutation.symm column, previous) ∈ rooks := by
    apply record_prefix_forces_neighbor positive permutation rooks placement cc
    intro column hcolumn
    by_cases habove : (permutation.symm column).val < rc
    · left
      intro later hlt hlater
      by_cases hlater_above : (permutation.symm later).val < rc
      · have hfirst : permutation.symm column ∈ part :=
          (hquad _).mpr ⟨fun _ => by simpa using hcolumn, fun _ => habove⟩
        have hsecond : permutation.symm later ∈ part :=
          (hquad _).mpr ⟨fun _ => by simpa using hlater, fun _ => hlater_above⟩
        by_contra bad
        rcases (le_of_not_gt bad).eq_or_lt with heq | hbefore
        · exact (ne_of_lt hlt) (permutation.symm.injective heq.symm)
        · have hvalue := hinc _ hsecond _ hfirst hbefore
          simp only [permutation.apply_symm_apply] at hvalue
          exact lt_asymm hlt hvalue
      · change (permutation.symm column).val < (permutation.symm later).val
        omega
    · right
      intro later hlt hlater
      by_cases hlater_above : (permutation.symm later).val < rc
      · change (permutation.symm later).val < (permutation.symm column).val
        omega
      · have hfirst : permutation.symm column ∉ part := by
          intro hmem
          exact habove ((hquad _).mp hmem |>.mpr (by simpa using hcolumn))
        have hsecond : permutation.symm later ∉ part := by
          intro hmem
          exact hlater_above ((hquad _).mp hmem |>.mpr (by simpa using hlater))
        by_contra bad
        rcases (le_of_not_gt bad).eq_or_lt with heq | hbefore
        · exact (ne_of_lt hlt) (permutation.symm.injective heq)
        · have hvalue := hdec _ hfirst _ hsecond hbefore
          simp only [permutation.apply_symm_apply] at hvalue
          exact lt_asymm hlt hvalue
  have reflected (permutation : Equiv.Perm (Fin n)) (part : Finset (Fin n))
      (rc cc : ℕ) (cc_bound : cc ≤ n)
      (hinc : ∀ row ∈ part, ∀ other ∈ part, row < other →
        permutation row < permutation other)
      (hdec : ∀ row ∉ part, ∀ other ∉ part, row < other →
        permutation other < permutation row)
      (hquad : ∀ row : Fin n, row ∈ part ↔
        (row.val < rc ↔ (permutation row).val < cc)) :
      (∀ row ∈ Finset.univ \ part, ∀ other ∈ Finset.univ \ part, row < other →
        (permutation row).rev < (permutation other).rev) ∧
      (∀ row ∉ Finset.univ \ part, ∀ other ∉ Finset.univ \ part, row < other →
        (permutation other).rev < (permutation row).rev) ∧
      (∀ row : Fin n, row ∈ Finset.univ \ part ↔
        (row.val < rc ↔ (permutation row).rev.val < n - cc)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro row hr other ho hlt
      exact Fin.rev_lt_rev.mpr (hdec row (Finset.mem_sdiff.mp hr).2 other
        (Finset.mem_sdiff.mp ho).2 hlt)
    · intro row hr other ho hlt
      have hr' : row ∈ part := by simpa using hr
      have ho' : other ∈ part := by simpa using ho
      exact Fin.rev_lt_rev.mpr (hinc row hr' other ho' hlt)
    · intro row
      have hvalue : (permutation row).rev.val < n - cc ↔
          ¬ (permutation row).val < cc := by
        rw [Fin.val_rev]
        have := (permutation row).isLt
        omega
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hquad, hvalue]
      by_cases hr : row.val < rc <;> simp only [hr, true_iff, false_iff, not_not]
  have inverse_inc : ∀ row ∈ increasing.image w, ∀ other ∈ increasing.image w,
      row < other → w.symm row < w.symm other := by
    intro row hr other ho hlt
    obtain ⟨first, hfirst, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp ho
    simp only [w.symm_apply_apply]
    by_contra bad
    exact not_lt_of_ge (inc_le second first hsecond hfirst (le_of_not_gt bad)) hlt
  have inverse_dec : ∀ row ∉ increasing.image w, ∀ other ∉ increasing.image w,
      row < other → w.symm other < w.symm row := by
    intro row hr other ho hlt
    have hfirst : w.symm row ∉ increasing := by
      intro hmem
      exact hr (Finset.mem_image.mpr ⟨_, hmem, w.apply_symm_apply _⟩)
    have hsecond : w.symm other ∉ increasing := by
      intro hmem
      exact ho (Finset.mem_image.mpr ⟨_, hmem, w.apply_symm_apply _⟩)
    by_contra bad
    have hvalue := dec_le (w.symm row) (w.symm other) hfirst hsecond (le_of_not_gt bad)
    simp only [w.apply_symm_apply] at hvalue
    exact not_lt_of_ge hvalue hlt
  have inverse_quad (row : Fin n) : row ∈ increasing.image w ↔
      (row.val < (w last_left).val + 1 ↔ (w.symm row).val < last_row.val + 1) := by
    have hmem : row ∈ increasing.image w ↔ w.symm row ∈ increasing := by
      constructor
      · rintro hmem
        obtain ⟨original, horiginal, heq⟩ := Finset.mem_image.mp hmem
        have hback := congrArg w.symm heq
        simpa only [w.symm_apply_apply, hback.symm] using horiginal
      · intro hmem
        exact Finset.mem_image.mpr ⟨_, hmem, w.apply_symm_apply _⟩
    rw [hmem, partition_iff, w.apply_symm_apply]
    exact ⟨Iff.symm, Iff.symm⟩
  have force_all (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid w) rooks)
      (cell : Cell n) :
      ((cell.2.val + 1 = (w cell.1).val ∧ (w cell.1).val < (w last_left).val + 1) ∨
       ((w cell.1).val + 1 = cell.2.val ∧ (w last_left).val + 1 ≤ (w cell.1).val) ∨
       (cell.1.val + 1 = (w.symm cell.2).val ∧ (w.symm cell.2).val < last_row.val + 1) ∨
       ((w.symm cell.2).val + 1 = cell.1.val ∧ last_row.val + 1 ≤ (w.symm cell.2).val)) →
        cell ∈ rooks := by
    intro hneighbor
    rcases hneighbor with hwest | heast | hnorth | hsouth
    · simpa only [w.symm_apply_apply] using west w increasing _ _ inc dec partition_iff
        rooks placement (w cell.1) cell.2 hwest.1 hwest.2
    · have hreflection := (symmetries positive w).2.2.2.2.1 rooks placement
      have hparts := reflected w increasing (last_row.val + 1) ((w last_left).val + 1)
        column_bound.le inc dec partition_iff
      have hforced := west (w.trans Fin.revPerm) (Finset.univ \ increasing)
        (last_row.val + 1) (n - ((w last_left).val + 1)) hparts.1 hparts.2.1 hparts.2.2
        _ hreflection (w cell.1).rev cell.2.rev
        (by rw [Fin.val_rev, Fin.val_rev]; have := cell.2.isLt; have := (w cell.1).isLt
            omega)
        (by rw [Fin.val_rev]; have := (w cell.1).isLt; omega)
      have hforced' : (cell.1, cell.2.rev) ∈
          rooks.image (fun original => (original.1, original.2.rev)) := by
        simpa only [Equiv.symm_trans_apply, Fin.revPerm_symm, Fin.revPerm_apply,
          Fin.rev_rev, w.symm_apply_apply] using hforced
      obtain ⟨original, horiginal, heq⟩ := Finset.mem_image.mp hforced'
      have hback := congrArg (fun original : Cell n => (original.1, original.2.rev)) heq
      simp only [Fin.rev_rev] at hback
      change original = cell at hback
      exact hback ▸ horiginal
    · have htranspose := (symmetries positive w).2.2.2.1 rooks placement
      have hforced := west w.symm (increasing.image w) _ _ inverse_inc inverse_dec
        inverse_quad _ htranspose (w.symm cell.2) cell.1 hnorth.1 hnorth.2
      have hforced' : (cell.2, cell.1) ∈ rooks.image Prod.swap := by
        simpa only [Equiv.symm_symm, w.apply_symm_apply] using hforced
      obtain ⟨original, horiginal, heq⟩ := Finset.mem_image.mp hforced'
      have hback := congrArg Prod.swap heq
      change original = cell at hback
      exact hback ▸ horiginal
    · have htranspose := (symmetries positive w).2.2.2.1 rooks placement
      have hreflection := (symmetries positive w.symm).2.2.2.2.1 _ htranspose
      have hparts := reflected w.symm (increasing.image w) ((w last_left).val + 1)
        (last_row.val + 1) row_bound.le inverse_inc inverse_dec inverse_quad
      have hforced := west (w.symm.trans Fin.revPerm) (Finset.univ \ increasing.image w)
        ((w last_left).val + 1) (n - (last_row.val + 1)) hparts.1 hparts.2.1 hparts.2.2
        _ hreflection (w.symm cell.2).rev cell.1.rev
        (by rw [Fin.val_rev, Fin.val_rev]; have := cell.1.isLt; have := (w.symm cell.2).isLt
            omega)
        (by rw [Fin.val_rev]; have := (w.symm cell.2).isLt; omega)
      have hforced' : (cell.2, cell.1.rev) ∈
          (rooks.image Prod.swap).image (fun original => (original.1, original.2.rev)) := by
        simpa only [Equiv.symm_trans_apply, Equiv.symm_symm, Fin.revPerm_symm,
          Fin.revPerm_apply, Fin.rev_rev, w.apply_symm_apply] using hforced
      obtain ⟨transposed, htransposed, heq⟩ := Finset.mem_image.mp hforced'
      obtain ⟨original, horiginal, heq'⟩ := Finset.mem_image.mp htransposed
      have hback := congrArg (fun original : Cell n => (original.2.rev, original.1))
        ((congrArg (fun original : Cell n => (original.1, original.2.rev)) heq').trans heq)
      simp only [Fin.rev_rev, Prod.fst_swap, Prod.snd_swap] at hback
      change original = cell at hback
      exact hback ▸ horiginal
  refine ⟨last_row.val + 1, (w last_left).val + 1, by omega, row_bound, by omega,
    column_bound, partition_iff, ?_, ?_, ?_, ?_, ?_, force_all⟩
  · exact ⟨nw_point, (row_iff _).mpr (Or.inl hnw), (column_iff _).mpr (Or.inl hnw)⟩
  · exact ⟨ne_point, (row_iff _).mpr (Or.inr hne),
      le_of_not_gt (mt (column_iff _).mp (right_not_left _ (Or.inl hne)))⟩
  · exact ⟨sw_point, le_of_not_gt (mt (row_iff _).mp (late_not_early _ (Or.inl hsw))),
      (column_iff _).mpr (Or.inr hsw)⟩
  · exact ⟨se_point, le_of_not_gt (mt (row_iff _).mp (late_not_early _ (Or.inr hse))),
      le_of_not_gt (mt (column_iff _).mp (right_not_left _ (Or.inr hse)))⟩
  · exact ⟨last_row, bottom, left, right, rfl, rfl, rfl, rfl, boundary⟩

end D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookCenterless
