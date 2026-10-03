/- GID: D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions
   mirror-E: none(waiver:extreme-deletion-placement-injections)
   anchors: []
   utility: none
   digest: Explicit injections on complete placements under extreme-entry insertion. -/

import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDeletions

open D5.S3.Combinatorics.CrosswordRookCounts
  (Cell SameAcross SameDown IsRookPlacement rookCount)
open D5.S3.Combinatorics.CrosswordPermutationGridRefutation (permGrid WordData)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords (word_structure)

theorem corner_lift {n : ℕ} (positive : 1 ≤ n) (small : Equiv.Perm (Fin n))
    (large : Equiv.Perm (Fin (n + 1))) (corner : large (Fin.last n) = Fin.last n)
    (inherited : ∀ row : Fin n, large row.castSucc = (small row).castSucc) :
    rookCount (permGrid small) ≤ rookCount (permGrid large) := by
  classical
  let last : Fin n := ⟨n - 1, by omega⟩
  let embed := fun cell : Cell n => (cell.1.castSucc, cell.2.castSucc)
  let bottom : Cell (n + 1) := (Fin.last n, (small last).castSucc)
  let right : Cell (n + 1) := ((small.symm last).castSucc, Fin.last n)
  let lift := fun rooks : Finset (Cell n) => insert bottom (insert right (rooks.image embed))
  obtain ⟨across_small, data_small, code_small⟩ := word_structure positive small
  obtain ⟨across_large, data_large, code_large⟩ := word_structure (by omega) large
  have inverse_inherited (column : Fin n) :
      large.symm column.castSucc = (small.symm column).castSucc := by
    apply large.injective
    rw [large.apply_symm_apply, inherited, small.apply_symm_apply]
  have inverse_corner : large.symm (Fin.last n) = Fin.last n := by
    apply large.injective
    rw [large.apply_symm_apply, corner]
  have embed_injective : Function.Injective embed := by
    intro cell other heq
    exact Prod.ext (Fin.castSucc_injective n (congrArg Prod.fst heq))
      (Fin.castSucc_injective n (congrArg Prod.snd heq))
  have down_sides {size : ℕ} (permutation : Equiv.Perm (Fin size))
      (data : WordData size (permGrid permutation))
      (code : ∀ cell : Cell size, data.downId cell =
        2 * cell.2.val + if cell.1 < permutation.symm cell.2 then 0 else 1)
      (cell other : Cell size) (hcell : cell ∈ permGrid permutation)
      (hother : other ∈ permGrid permutation) :
      SameDown (permGrid permutation) cell other ↔
        cell.2 = other.2 ∧
          (cell.1 < permutation.symm cell.2 ↔ other.1 < permutation.symm other.2) := by
    rw [data.down_iff cell hcell other hother, code, code]
    constructor
    · intro heq
      have hcol : cell.2 = other.2 := by
        apply Fin.ext
        split_ifs at heq <;> omega
      refine ⟨hcol, ?_⟩
      rw [hcol] at heq ⊢
      split_ifs at heq <;> first | tauto | omega
    · rintro ⟨hcol, hside⟩
      rw [hcol] at hside ⊢
      congr 1
      exact if_congr hside rfl rfl
  have down_small := down_sides small data_small code_small
  have down_large := down_sides large data_large code_large
  have white_embed (cell : Cell n) :
      embed cell ∈ permGrid large ↔ cell ∈ permGrid small := by
    simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
    change large cell.1.castSucc ≠ cell.2.castSucc ↔ small cell.1 ≠ cell.2
    rw [inherited]
    exact (Fin.castSucc_injective n).eq_iff.not
  have white_bottom : bottom ∈ permGrid large := by
    simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
    change large (Fin.last n) ≠ (small last).castSucc
    rw [corner]
    exact (Fin.castSucc_ne_last _).symm
  have white_right : right ∈ permGrid large := by
    simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
    change large (small.symm last).castSucc ≠ Fin.last n
    rw [inherited, small.apply_symm_apply]
    exact Fin.castSucc_ne_last _
  have embed_bottom_ne (cell : Cell n) : embed cell ≠ bottom := by
    intro heq
    exact Fin.castSucc_ne_last _ (congrArg Prod.fst heq)
  have embed_right_ne (cell : Cell n) : embed cell ≠ right := by
    intro heq
    exact Fin.castSucc_ne_last _ (congrArg Prod.snd heq)
  have membership (cell : Cell n) (rooks : Finset (Cell n)) :
      embed cell ∈ lift rooks ↔ cell ∈ rooks := by
    simp only [lift, Finset.mem_insert, embed_bottom_ne, embed_right_ne, false_or]
    constructor
    · intro hcell
      obtain ⟨original, horiginal, heq⟩ := Finset.mem_image.mp hcell
      exact embed_injective heq ▸ horiginal
    · intro hcell
      exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  have injective : Function.Injective lift := by
    intro rooks other heq
    ext cell
    rw [← membership cell rooks, ← membership cell other, heq]
  have across_embed (cell other : Cell n) (hcell : cell ∈ permGrid small)
      (hother : other ∈ permGrid small) :
      SameAcross (permGrid large) (embed cell) (embed other) ↔
        SameAcross (permGrid small) cell other := by
    rw [across_large _ ((white_embed _).mpr hcell) _ ((white_embed _).mpr hother),
      across_small _ hcell _ hother]
    change (cell.1.castSucc = other.1.castSucc ∧
      (cell.2.castSucc < large cell.1.castSucc ↔
        other.2.castSucc < large other.1.castSucc)) ↔ _
    simp only [inherited, Fin.castSucc_inj, Fin.castSucc_lt_castSucc_iff]
  have down_embed (cell other : Cell n) (hcell : cell ∈ permGrid small)
      (hother : other ∈ permGrid small) :
      SameDown (permGrid large) (embed cell) (embed other) ↔
        SameDown (permGrid small) cell other := by
    rw [down_large _ _ ((white_embed _).mpr hcell) ((white_embed _).mpr hother),
      down_small _ _ hcell hother]
    change (cell.2.castSucc = other.2.castSucc ∧
      (cell.1.castSucc < large.symm cell.2.castSucc ↔
        other.1.castSucc < large.symm other.2.castSucc)) ↔ _
    simp only [inverse_inherited, Fin.castSucc_inj, Fin.castSucc_lt_castSucc_iff]
  have bottom_across (cell : Cell n) (hcell : cell ∈ permGrid small) :
      ¬ SameAcross (permGrid large) bottom (embed cell) := by
    intro hword
    exact (Fin.castSucc_ne_last cell.1) hword.1.symm
  have right_down (cell : Cell n) (hcell : cell ∈ permGrid small) :
      ¬ SameDown (permGrid large) right (embed cell) := by
    intro hword
    exact (Fin.castSucc_ne_last cell.2) hword.1.symm
  have right_across (cell : Cell n) (hcell : cell ∈ permGrid small) :
      ¬ SameAcross (permGrid large) right (embed cell) := by
    intro hword
    have hgeo := (across_large _ white_right _ ((white_embed _).mpr hcell)).mp hword
    have hrow : small.symm last = cell.1 := Fin.castSucc_injective n hgeo.1
    have hblack : small cell.1 = last := by rw [← hrow, small.apply_symm_apply]
    have hne : cell.2 ≠ last := by
      have hwhite : small cell.1 ≠ cell.2 := by simpa [permGrid] using hcell
      rw [hblack] at hwhite
      exact hwhite.symm
    have hlt : cell.2 < last := by
      have hbound := cell.2.isLt
      have hneq : cell.2.val ≠ n - 1 := fun heq => hne (Fin.ext heq)
      change cell.2.val < n - 1
      omega
    have hsides := hgeo.2
    change ((Fin.last n) < large (small.symm last).castSucc ↔
      cell.2.castSucc < large cell.1.castSucc) at hsides
    rw [inherited, inherited, small.apply_symm_apply, hblack] at hsides
    exact (not_lt_of_gt (Fin.castSucc_lt_last last))
      (hsides.mpr (Fin.castSucc_lt_castSucc_iff.mpr hlt))
  have bottom_down (cell : Cell n) (hcell : cell ∈ permGrid small) :
      ¬ SameDown (permGrid large) bottom (embed cell) := by
    intro hword
    have hgeo := (down_large _ _ white_bottom ((white_embed _).mpr hcell)).mp hword
    have hcol : small last = cell.2 := Fin.castSucc_injective n hgeo.1
    have hblack : small.symm cell.2 = last := by rw [← hcol, small.symm_apply_apply]
    have hne : cell.1 ≠ last := by
      intro heq
      have hwhite : small cell.1 ≠ cell.2 := by simpa [permGrid] using hcell
      exact hwhite (heq ▸ hcol)
    have hlt : cell.1 < last := by
      have hbound := cell.1.isLt
      have hneq : cell.1.val ≠ n - 1 := fun heq => hne (Fin.ext heq)
      change cell.1.val < n - 1
      omega
    have hsides := hgeo.2
    change ((Fin.last n) < large.symm (small last).castSucc ↔
      cell.1.castSucc < large.symm cell.2.castSucc) at hsides
    rw [inverse_inherited, inverse_inherited, small.symm_apply_apply, hblack] at hsides
    exact (not_lt_of_gt (Fin.castSucc_lt_last last))
      (hsides.mpr (Fin.castSucc_lt_castSucc_iff.mpr hlt))
  have corners_across : ¬ SameAcross (permGrid large) bottom right := by
    intro hword
    exact (Fin.castSucc_ne_last (small.symm last)) hword.1.symm
  have corners_down : ¬ SameDown (permGrid large) bottom right := by
    intro hword
    exact (Fin.castSucc_ne_last (small last)) hword.1
  have preserve (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid small) rooks) :
      IsRookPlacement (permGrid large) (lift rooks) := by
    have white_lift : lift rooks ⊆ permGrid large := by
      intro cell hcell
      rcases Finset.mem_insert.mp hcell with rfl | hcell
      · exact white_bottom
      rcases Finset.mem_insert.mp hcell with rfl | hcell
      · exact white_right
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
      exact (white_embed original).mpr (placement.1 horiginal)
    have across_symmetric (cell other : Cell (n + 1))
        (hcell : cell ∈ permGrid large) (hother : other ∈ permGrid large)
        (hword : SameAcross (permGrid large) cell other) :
        SameAcross (permGrid large) other cell := by
      have hgeo := (across_large cell hcell other hother).mp hword
      exact (across_large other hother cell hcell).mpr ⟨hgeo.1.symm, hgeo.2.symm⟩
    have down_symmetric (cell other : Cell (n + 1))
        (hcell : cell ∈ permGrid large) (hother : other ∈ permGrid large)
        (hword : SameDown (permGrid large) cell other) :
        SameDown (permGrid large) other cell := by
      have hgeo := (down_large cell other hcell hother).mp hword
      exact (down_large other cell hother hcell).mpr ⟨hgeo.1.symm, hgeo.2.symm⟩
    refine ⟨white_lift, ?_, ?_⟩
    · intro cell hcell other hother hne
      have hcwhite := white_lift hcell
      have hdwhite := white_lift hother
      rcases Finset.mem_insert.mp hcell with rfl | hcell
      · rcases Finset.mem_insert.mp hother with heq | hother
        · exact False.elim (hne heq.symm)
        rcases Finset.mem_insert.mp hother with rfl | hother
        · exact ⟨corners_across, corners_down⟩
        obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hother
        exact ⟨bottom_across original (placement.1 horiginal),
          bottom_down original (placement.1 horiginal)⟩
      rcases Finset.mem_insert.mp hcell with rfl | hcell
      · rcases Finset.mem_insert.mp hother with rfl | hother
        · exact ⟨fun h => corners_across (across_symmetric _ _ hcwhite hdwhite h),
            fun h => corners_down (down_symmetric _ _ hcwhite hdwhite h)⟩
        rcases Finset.mem_insert.mp hother with heq | hother
        · exact False.elim (hne heq.symm)
        obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hother
        exact ⟨right_across original (placement.1 horiginal),
          right_down original (placement.1 horiginal)⟩
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
      rcases Finset.mem_insert.mp hother with rfl | hother
      · exact ⟨fun h => bottom_across original (placement.1 horiginal)
          (across_symmetric _ _ hcwhite hdwhite h),
          fun h => bottom_down original (placement.1 horiginal)
            (down_symmetric _ _ hcwhite hdwhite h)⟩
      rcases Finset.mem_insert.mp hother with rfl | hother
      · exact ⟨fun h => right_across original (placement.1 horiginal)
          (across_symmetric _ _ hcwhite hdwhite h),
          fun h => right_down original (placement.1 horiginal)
            (down_symmetric _ _ hcwhite hdwhite h)⟩
      obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp hother
      have hdistinct : original ≠ second := fun heq => hne (congrArg embed heq)
      have hpair := placement.2.1 original horiginal second hsecond hdistinct
      exact ⟨fun h => hpair.1 ((across_embed _ _ (placement.1 horiginal)
        (placement.1 hsecond)).mp h),
        fun h => hpair.2 ((down_embed _ _ (placement.1 horiginal)
          (placement.1 hsecond)).mp h)⟩
    · intro cell hcell
      have bottom_mem : bottom ∈ lift rooks := Finset.mem_insert_self _ _
      have right_mem : right ∈ lift rooks :=
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have col_case : cell.2 = Fin.last n ∨ ∃ column : Fin n, cell.2 = column.castSucc := by
        by_cases heq : cell.2 = Fin.last n
        · exact Or.inl heq
        · have hlt : cell.2.val < n := by
            have hbound := cell.2.isLt
            have hne : cell.2.val ≠ n := fun h => heq (Fin.ext h)
            omega
          exact Or.inr ⟨⟨cell.2.val, hlt⟩, Fin.ext rfl⟩
      have row_case : cell.1 = Fin.last n ∨ ∃ row : Fin n, cell.1 = row.castSucc := by
        by_cases heq : cell.1 = Fin.last n
        · exact Or.inl heq
        · have hlt : cell.1.val < n := by
            have hbound := cell.1.isLt
            have hne : cell.1.val ≠ n := fun h => heq (Fin.ext h)
            omega
          exact Or.inr ⟨⟨cell.1.val, hlt⟩, Fin.ext rfl⟩
      rcases row_case with hrow | ⟨row, hrow⟩
      · have hcolne : cell.2 ≠ Fin.last n := by
          intro heq
          have hwhite : large cell.1 ≠ cell.2 := by simpa [permGrid] using hcell
          exact hwhite (by rw [hrow, heq, corner])
        rcases col_case with hcol | ⟨column, hcol⟩
        · exact False.elim (hcolne hcol)
        have hacross : SameAcross (permGrid large) cell bottom := by
          apply (across_large _ hcell _ white_bottom).mpr
          refine ⟨hrow, ?_⟩
          simp only [bottom, hrow, corner]
          simp [hcol]
        refine ⟨⟨bottom, bottom_mem, hacross⟩, ?_⟩
        by_cases hcolumn : column = small last
        · refine ⟨bottom, bottom_mem, (down_large _ _ hcell white_bottom).mpr ?_⟩
          refine ⟨by simpa [bottom, hcolumn] using hcol, ?_⟩
          simp only [hrow, hcol, hcolumn]
          exact Iff.rfl
        · have hwhite : (last, column) ∈ permGrid small := by
            simp [permGrid, ne_comm, hcolumn]
          obtain ⟨rook, hrook, hword⟩ := (placement.2.2 (last, column) hwhite).2
          have hgeo := (down_small _ _ hwhite (placement.1 hrook)).mp hword
          have hblack : small.symm column < last := by
            have hne : small.symm column ≠ last := by
              intro heq
              exact hcolumn (by rw [← heq, small.apply_symm_apply])
            have hbound := (small.symm column).isLt
            have hneq : (small.symm column).val ≠ n - 1 := fun h => hne (Fin.ext h)
            change (small.symm column).val < n - 1
            omega
          refine ⟨embed rook, (membership rook rooks).mpr hrook,
            (down_large _ _ hcell ((white_embed _).mpr (placement.1 hrook))).mpr ?_⟩
          refine ⟨hcol.trans (congrArg Fin.castSucc hgeo.1), ?_⟩
          change (cell.1 < large.symm cell.2 ↔
            rook.1.castSucc < large.symm rook.2.castSucc)
          rw [hrow, hcol, inverse_inherited, inverse_inherited, ← hgeo.1]
          have hfalse : ¬ last < small.symm column := not_lt_of_gt hblack
          have hsides := hgeo.2
          rw [← hgeo.1] at hsides
          have hrookside : ¬ rook.1 < small.symm column := mt hsides.mpr hfalse
          exact iff_of_false (not_lt_of_gt (Fin.castSucc_lt_last _))
            (by simpa only [Fin.castSucc_lt_castSucc_iff] using hrookside)
      · rcases col_case with hcol | ⟨column, hcol⟩
        · have hdown : SameDown (permGrid large) cell right := by
            apply (down_large _ _ hcell white_right).mpr
            refine ⟨hcol, ?_⟩
            change (cell.1 < large.symm cell.2 ↔
              (small.symm last).castSucc < large.symm (Fin.last n))
            rw [hcol, inverse_corner]
            simp [hrow]
          refine ⟨?_, ⟨right, right_mem, hdown⟩⟩
          by_cases hspecial : row = small.symm last
          · refine ⟨right, right_mem, (across_large _ hcell _ white_right).mpr ?_⟩
            exact ⟨by simpa [right, hspecial] using hrow,
              by simp only [right, hrow, hspecial, hcol]⟩
          · have hwhite : (row, last) ∈ permGrid small := by
              simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
              exact fun heq => hspecial (small.eq_symm_apply.mpr heq)
            obtain ⟨rook, hrook, hword⟩ := (placement.2.2 (row, last) hwhite).1
            have hgeo := (across_small _ hwhite _ (placement.1 hrook)).mp hword
            have hblack : small row < last := by
              have hne : small row ≠ last := by simpa [permGrid] using hwhite
              have hbound := (small row).isLt
              have hneq : (small row).val ≠ n - 1 := fun h => hne (Fin.ext h)
              change (small row).val < n - 1
              omega
            refine ⟨embed rook, (membership rook rooks).mpr hrook,
              (across_large _ hcell _ ((white_embed _).mpr (placement.1 hrook))).mpr ?_⟩
            refine ⟨hrow.trans (congrArg Fin.castSucc hgeo.1), ?_⟩
            change (cell.2 < large cell.1 ↔ rook.2.castSucc < large rook.1.castSucc)
            rw [hrow, hcol, inherited, inherited, ← hgeo.1]
            have hfalse : ¬ last < small row := not_lt_of_gt hblack
            have hsides := hgeo.2
            rw [← hgeo.1] at hsides
            have hrookside : ¬ rook.2 < small row := mt hsides.mpr hfalse
            exact iff_of_false (not_lt_of_gt (Fin.castSucc_lt_last _))
              (by simpa only [Fin.castSucc_lt_castSucc_iff] using hrookside)
        · have hcell_eq : cell = embed (row, column) := Prod.ext hrow hcol
          have hwhite := (white_embed (row, column)).mp (hcell_eq ▸ hcell)
          obtain ⟨arook, harook, haword⟩ := (placement.2.2 (row, column) hwhite).1
          obtain ⟨drook, hdrook, hdword⟩ := (placement.2.2 (row, column) hwhite).2
          constructor
          · refine ⟨embed arook, (membership arook rooks).mpr harook, ?_⟩
            rw [hcell_eq]
            exact (across_embed _ _ hwhite (placement.1 harook)).mpr haword
          · refine ⟨embed drook, (membership drook rooks).mpr hdrook, ?_⟩
            rw [hcell_eq]
            exact (down_embed _ _ hwhite (placement.1 hdrook)).mpr hdword
  unfold rookCount
  apply Finset.card_le_card_of_injOn lift
  · intro rooks hrooks
    have hplacement := preserve rooks (Finset.mem_filter.mp hrooks).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hplacement.1, hplacement⟩
  · intro rooks _ other _ heq
    exact injective heq

theorem interior_lift {n : ℕ} (positive : 1 ≤ n) (small : Equiv.Perm (Fin n))
    (large : Equiv.Perm (Fin (n + 1))) (pivot : Fin (n + 1))
    (interior : 0 < pivot.val ∧ pivot.val < n) (maximum : large pivot = Fin.last n)
    (inherited : ∀ row : Fin n, large (pivot.succAbove row) = (small row).castSucc)
    (upper : pivot.succAbove (small.symm ⟨n - 1, by omega⟩) < pivot) :
    rookCount (permGrid small) ≤ rookCount (permGrid large) := by
  classical
  let last : Fin n := ⟨n - 1, by omega⟩
  let next : Fin n := ⟨pivot.val, interior.2⟩
  let previous : Fin n := ⟨pivot.val - 1, by omega⟩
  let top := small.symm last
  let moved := fun cell : Cell n => cell.1 = next ∧ small next < cell.2
  let embed := fun cell : Cell n => (pivot.succAbove cell.1, cell.2.castSucc)
  let transfer := fun cell : Cell n =>
    (if moved cell then pivot else pivot.succAbove cell.1, cell.2.castSucc)
  let north : Cell (n + 1) := (pivot.succAbove top, Fin.last n)
  let south : Cell (n + 1) := (pivot.succAbove next, Fin.last n)
  let lift := fun rooks : Finset (Cell n) => insert north (insert south (rooks.image transfer))
  obtain ⟨across_small, data_small, code_small⟩ := word_structure positive small
  obtain ⟨across_large, data_large, code_large⟩ := word_structure (by omega) large
  have inverse (column : Fin n) :
      large.symm column.castSucc = pivot.succAbove (small.symm column) := by
    apply large.injective
    rw [large.apply_symm_apply, inherited, small.apply_symm_apply]
  have inverse_max : large.symm (Fin.last n) = pivot := by
    apply large.injective
    rw [large.apply_symm_apply, maximum]
  have top_lt : top < next := by
    have h := (Fin.succAbove_lt_iff_castSucc_lt pivot top).mp upper
    exact h
  have next_ne_top : next ≠ top := ne_of_gt top_lt
  have next_small : small next < last := by
    have hne : small next ≠ last := by
      intro heq
      apply next_ne_top
      exact small.eq_symm_apply.mpr heq
    have hbound := (small next).isLt
    have hneq : (small next).val ≠ n - 1 := fun heq => hne (Fin.ext heq)
    change (small next).val < n - 1
    omega
  have down_sides {size : ℕ} (permutation : Equiv.Perm (Fin size))
      (data : WordData size (permGrid permutation))
      (code : ∀ cell : Cell size, data.downId cell =
        2 * cell.2.val + if cell.1 < permutation.symm cell.2 then 0 else 1)
      (cell other : Cell size) (hcell : cell ∈ permGrid permutation)
      (hother : other ∈ permGrid permutation) :
      SameDown (permGrid permutation) cell other ↔
        cell.2 = other.2 ∧
          (cell.1 < permutation.symm cell.2 ↔ other.1 < permutation.symm other.2) := by
    rw [data.down_iff cell hcell other hother, code, code]
    constructor
    · intro heq
      have hcol : cell.2 = other.2 := by
        apply Fin.ext
        split_ifs at heq <;> omega
      refine ⟨hcol, ?_⟩
      rw [hcol] at heq ⊢
      split_ifs at heq <;> first | tauto | omega
    · rintro ⟨hcol, hside⟩
      rw [hcol] at hside ⊢
      congr 1
      exact if_congr hside rfl rfl
  have down_small := down_sides small data_small code_small
  have down_large := down_sides large data_large code_large
  have white_embed (cell : Cell n) :
      embed cell ∈ permGrid large ↔ cell ∈ permGrid small := by
    simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
    change large (pivot.succAbove cell.1) ≠ cell.2.castSucc ↔ small cell.1 ≠ cell.2
    rw [inherited]
    exact (Fin.castSucc_injective n).eq_iff.not
  have white_transfer (cell : Cell n) (hcell : cell ∈ permGrid small) :
      transfer cell ∈ permGrid large := by
    by_cases hmove : moved cell
    · simp only [transfer, if_pos hmove, permGrid, Finset.mem_filter,
        Finset.mem_univ, true_and, maximum]
      exact (Fin.castSucc_ne_last _).symm
    · simpa only [transfer, if_neg hmove] using (white_embed cell).mpr hcell
  have white_north : north ∈ permGrid large := by
    simp [north, permGrid, inherited]
  have white_south : south ∈ permGrid large := by
    simp [south, permGrid, inherited]
  have transfer_injective : Function.Injective transfer := by
    intro cell other heq
    have hcol : cell.2 = other.2 := Fin.castSucc_injective n (congrArg Prod.snd heq)
    have hrow := congrArg Prod.fst heq
    dsimp only [transfer] at hrow
    by_cases hfirst : moved cell <;> by_cases hsecond : moved other
    · exact Prod.ext (hfirst.1.trans hsecond.1.symm) hcol
    · simp only [if_pos hfirst, if_neg hsecond] at hrow
      exact False.elim (Fin.ne_succAbove _ _ hrow)
    · simp only [if_neg hfirst, if_pos hsecond] at hrow
      exact False.elim (Fin.succAbove_ne _ _ hrow)
    · simp only [if_neg hfirst, if_neg hsecond] at hrow
      exact Prod.ext (Fin.succAbove_right_injective hrow) hcol
  have horizontal (cell other : Cell n) (hcell : cell ∈ permGrid small)
      (hother : other ∈ permGrid small) :
      SameAcross (permGrid large) (transfer cell) (transfer other) ↔
        SameAcross (permGrid small) cell other := by
    rw [across_large _ (white_transfer cell hcell) _ (white_transfer other hother),
      across_small _ hcell _ hother]
    by_cases hfirst : moved cell <;> by_cases hsecond : moved other
    · simp only [transfer, if_pos hfirst, if_pos hsecond, maximum]
      have hrow : cell.1 = other.1 := hfirst.1.trans hsecond.1.symm
      have hside : ¬ cell.2 < small cell.1 := by
        rw [hfirst.1]
        exact not_lt_of_gt hfirst.2
      have hside' : ¬ other.2 < small other.1 := by
        rw [hsecond.1]
        exact not_lt_of_gt hsecond.2
      exact ⟨fun _ => ⟨hrow, iff_of_false hside hside'⟩,
        fun _ => ⟨trivial, iff_of_true (Fin.castSucc_lt_last _) (Fin.castSucc_lt_last _)⟩⟩
    · simp only [transfer, if_pos hfirst, if_neg hsecond]
      constructor
      · rintro ⟨hrow, _⟩
        exact False.elim (Fin.ne_succAbove _ _ hrow)
      · rintro ⟨hrow, hside⟩
        apply False.elim
        apply hsecond
        refine ⟨hrow.symm.trans hfirst.1, ?_⟩
        have hwhite : small other.1 ≠ other.2 := by simpa [permGrid] using hother
        have hnot : ¬ other.2 < small other.1 := by
          apply mt hside.mpr
          rw [hfirst.1]
          exact not_lt_of_gt hfirst.2
        rw [← hfirst.1, hrow]
        exact lt_of_le_of_ne (le_of_not_gt hnot) hwhite
    · simp only [transfer, if_neg hfirst, if_pos hsecond]
      constructor
      · rintro ⟨hrow, _⟩
        exact False.elim (Fin.succAbove_ne _ _ hrow)
      · rintro ⟨hrow, hside⟩
        apply False.elim
        apply hfirst
        refine ⟨hrow.trans hsecond.1, ?_⟩
        have hwhite : small cell.1 ≠ cell.2 := by simpa [permGrid] using hcell
        have hnot : ¬ cell.2 < small cell.1 := by
          apply mt hside.mp
          rw [hsecond.1]
          exact not_lt_of_gt hsecond.2
        rw [← hsecond.1, ← hrow]
        exact lt_of_le_of_ne (le_of_not_gt hnot) hwhite
    · simp only [transfer, if_neg hfirst, if_neg hsecond, inherited,
        Fin.succAbove_right_inj, Fin.castSucc_lt_castSucc_iff]
  have vertical_side (cell : Cell n) :
      (transfer cell).1 < large.symm (transfer cell).2 ↔ cell.1 < small.symm cell.2 := by
    by_cases hmove : moved cell
    · have hne : next ≠ small.symm cell.2 := by
        intro heq
        have heq' : small next = cell.2 := by rw [heq, small.apply_symm_apply]
        exact (ne_of_lt hmove.2) heq'
      simp only [transfer, if_pos hmove, inverse, Fin.lt_succAbove_iff_le_castSucc]
      rw [hmove.1]
      change next ≤ small.symm cell.2 ↔ next < small.symm cell.2
      exact ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
    · simp only [transfer, if_neg hmove, inverse, Fin.succAbove_lt_succAbove_iff]
  have vertical (cell other : Cell n) (hcell : cell ∈ permGrid small)
      (hother : other ∈ permGrid small) :
      SameDown (permGrid large) (transfer cell) (transfer other) ↔
        SameDown (permGrid small) cell other := by
    rw [down_large _ _ (white_transfer cell hcell) (white_transfer other hother),
      down_small _ _ hcell hother, vertical_side, vertical_side]
    simp only [transfer, Fin.castSucc_inj]
  have fixed_across (fixed : Cell (n + 1)) (hfixed : fixed = north ∨ fixed = south)
      (cell : Cell n) (hcell : cell ∈ permGrid small) :
      ¬ SameAcross (permGrid large) fixed (transfer cell) := by
    have hfwhite : fixed ∈ permGrid large := hfixed.elim (· ▸ white_north) (· ▸ white_south)
    intro hword
    have hgeo := (across_large _ hfwhite _ (white_transfer cell hcell)).mp hword
    by_cases hmove : moved cell
    · have hrow := hgeo.1
      simp only [transfer, if_pos hmove] at hrow
      rcases hfixed with rfl | rfl <;> exact Fin.succAbove_ne _ _ hrow
    · simp only [transfer, if_neg hmove] at hgeo
      rcases hfixed with rfl | rfl
      · have hrow : top = cell.1 := Fin.succAbove_right_injective hgeo.1
        have hblack : small cell.1 = last := by rw [← hrow, small.apply_symm_apply]
        have hwhite : small cell.1 ≠ cell.2 := by simpa [permGrid] using hcell
        have hlt : cell.2 < last := by
          have hbound := cell.2.isLt
          have hneq : cell.2.val ≠ n - 1 := fun h => (hwhite (hblack.trans (Fin.ext h).symm))
          change cell.2.val < n - 1
          omega
        have hside := hgeo.2
        simp only [north, inherited, hblack, top, small.apply_symm_apply] at hside
        exact (not_lt_of_gt (Fin.castSucc_lt_last last))
          (hside.mpr (Fin.castSucc_lt_castSucc_iff.mpr hlt))
      · have hrow : next = cell.1 := Fin.succAbove_right_injective hgeo.1
        have hwhite : small cell.1 ≠ cell.2 := by simpa [permGrid] using hcell
        have hside := hgeo.2
        simp only [south, inherited, ← hrow, Fin.castSucc_lt_castSucc_iff] at hside
        have hnot : ¬ cell.2 < small next :=
          mt hside.mpr (not_lt_of_gt (Fin.castSucc_lt_last _))
        apply hmove
        exact ⟨hrow.symm, lt_of_le_of_ne (le_of_not_gt hnot) (hrow ▸ hwhite)⟩
  have fixed_down (fixed : Cell (n + 1)) (hfixed : fixed = north ∨ fixed = south)
      (cell : Cell n) : ¬ SameDown (permGrid large) fixed (transfer cell) := by
    intro hword
    rcases hfixed with rfl | rfl <;>
      exact (Fin.castSucc_ne_last cell.2) hword.1.symm
  have two_across : ¬ SameAcross (permGrid large) north south := by
    intro hword
    exact (ne_of_lt top_lt) (Fin.succAbove_right_injective hword.1)
  have two_down : ¬ SameDown (permGrid large) north south := by
    intro hword
    have hsides := ((down_large _ _ white_north white_south).mp hword).2
    change (pivot.succAbove top < large.symm (Fin.last n) ↔
      pivot.succAbove next < large.symm (Fin.last n)) at hsides
    rw [inverse_max] at hsides
    have hbelow : ¬ pivot.succAbove next < pivot := by
      rw [Fin.succAbove_lt_iff_castSucc_lt]
      exact lt_irrefl pivot
    exact hbelow (hsides.mp upper)
  have transfer_mem (cell : Cell n) (rooks : Finset (Cell n)) :
      transfer cell ∈ lift rooks ↔ cell ∈ rooks := by
    have hn : transfer cell ≠ north := fun heq =>
      Fin.castSucc_ne_last cell.2 (congrArg Prod.snd heq)
    have hs : transfer cell ≠ south := fun heq =>
      Fin.castSucc_ne_last cell.2 (congrArg Prod.snd heq)
    simp only [lift, Finset.mem_insert, hn, hs, false_or]
    exact Finset.mem_image.trans (by simp [transfer_injective.eq_iff])
  have preserve (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid small) rooks) :
      IsRookPlacement (permGrid large) (lift rooks) := by
    have subset : lift rooks ⊆ permGrid large := by
      intro cell hcell
      rcases Finset.mem_insert.mp hcell with rfl | hcell
      · exact white_north
      rcases Finset.mem_insert.mp hcell with rfl | hcell
      · exact white_south
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
      exact white_transfer original (placement.1 horiginal)
    have symmetric (cell other : Cell (n + 1)) (hcell : cell ∈ permGrid large)
        (hother : other ∈ permGrid large) :
        (SameAcross (permGrid large) cell other ↔ SameAcross (permGrid large) other cell) ∧
        (SameDown (permGrid large) cell other ↔ SameDown (permGrid large) other cell) := by
      rw [across_large _ hcell _ hother, across_large _ hother _ hcell,
        down_large _ _ hcell hother, down_large _ _ hother hcell]
      exact ⟨by tauto, by tauto⟩
    refine ⟨subset, ?_, ?_⟩
    · intro cell hcell other hother hne
      have hcwhite := subset hcell
      have howhite := subset hother
      simp only [lift, Finset.mem_insert] at hcell hother
      rcases hcell with rfl | rfl | hcell <;> rcases hother with rfl | rfl | hother
      · exact False.elim (hne rfl)
      · exact ⟨two_across, two_down⟩
      · obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hother
        exact ⟨fixed_across north (Or.inl rfl) original (placement.1 horiginal),
          fixed_down north (Or.inl rfl) original⟩
      · exact ⟨fun h => two_across ((symmetric _ _ hcwhite howhite).1.mp h),
          fun h => two_down ((symmetric _ _ hcwhite howhite).2.mp h)⟩
      · exact False.elim (hne rfl)
      · obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hother
        exact ⟨fixed_across south (Or.inr rfl) original (placement.1 horiginal),
          fixed_down south (Or.inr rfl) original⟩
      · obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
        exact ⟨fun h => fixed_across north (Or.inl rfl) original (placement.1 horiginal)
            ((symmetric _ _ hcwhite howhite).1.mp h),
          fun h => fixed_down north (Or.inl rfl) original
            ((symmetric _ _ hcwhite howhite).2.mp h)⟩
      · obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
        exact ⟨fun h => fixed_across south (Or.inr rfl) original (placement.1 horiginal)
            ((symmetric _ _ hcwhite howhite).1.mp h),
          fun h => fixed_down south (Or.inr rfl) original
            ((symmetric _ _ hcwhite howhite).2.mp h)⟩
      · obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
        obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp hother
        have hdifferent : original ≠ second := fun heq => hne (congrArg transfer heq)
        have hpair := placement.2.1 original horiginal second hsecond hdifferent
        exact ⟨fun h => hpair.1 ((horizontal _ _ (placement.1 horiginal)
            (placement.1 hsecond)).mp h),
          fun h => hpair.2 ((vertical _ _ (placement.1 horiginal)
            (placement.1 hsecond)).mp h)⟩
    · intro cell hcell
      have north_mem : north ∈ lift rooks := Finset.mem_insert_self _ _
      have south_mem : south ∈ lift rooks := Finset.mem_insert_of_mem
        (Finset.mem_insert_self _ _)
      have across_next (hrow : cell.1 = pivot.succAbove next)
          (hside : ¬ cell.2 < large cell.1) :
          ∃ rook ∈ lift rooks, SameAcross (permGrid large) cell rook := by
        refine ⟨south, south_mem, (across_large _ hcell _ white_south).mpr ?_⟩
        refine ⟨hrow, iff_of_false hside ?_⟩
        change ¬ Fin.last n < large (pivot.succAbove next)
        rw [inherited]
        exact not_lt_of_gt (Fin.castSucc_lt_last _)
      constructor
      · by_cases hpivot : cell.1 = pivot
        · have hwhite : (next, last) ∈ permGrid small := by
            simpa [permGrid] using ne_of_lt next_small
          obtain ⟨rook, hrook, hword⟩ := (placement.2.2 (next, last) hwhite).1
          have hgeo := (across_small _ hwhite _ (placement.1 hrook)).mp hword
          dsimp only [Prod.fst, Prod.snd] at hgeo
          have hmove : moved rook := by
            refine ⟨hgeo.1.symm, ?_⟩
            have hwhite' : small rook.1 ≠ rook.2 := by simpa [permGrid] using placement.1 hrook
            have hnot : ¬ rook.2 < small next := by
              have hside := hgeo.2
              rw [← hgeo.1] at hside
              exact mt hside.mpr (not_lt_of_gt next_small)
            rw [← hgeo.1] at hwhite'
            exact lt_of_le_of_ne (le_of_not_gt hnot) hwhite'
          refine ⟨transfer rook, (transfer_mem _ _).mpr hrook,
            (across_large _ hcell _ (white_transfer _ (placement.1 hrook))).mpr ?_⟩
          simp only [transfer, if_pos hmove, hpivot, maximum]
          have hcol : cell.2 < Fin.last n := by
            have hne : Fin.last n ≠ cell.2 := by simpa [permGrid, hpivot, maximum] using hcell
            exact lt_of_le_of_ne cell.2.le_last hne.symm
          simp [hcol]
        · obtain ⟨row, hrow⟩ := Fin.exists_succAbove_eq hpivot
          by_cases hcol : cell.2 = Fin.last n
          · by_cases htop : row = top
            · refine ⟨north, north_mem, (across_large _ hcell _ white_north).mpr ?_⟩
              simp [north, ← hrow, htop, hcol]
            · have hwhite : (row, last) ∈ permGrid small := by
                simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
                intro heq
                exact htop (small.eq_symm_apply.mpr heq)
              by_cases hnext : row = next
              · apply across_next (by rw [← hrow, hnext])
                rw [hcol]
                rw [← hrow, inherited]
                exact not_lt_of_gt (Fin.castSucc_lt_last _)
              · obtain ⟨rook, hrook, hword⟩ := (placement.2.2 (row, last) hwhite).1
                have hgeo := (across_small _ hwhite _ (placement.1 hrook)).mp hword
                dsimp only [Prod.fst, Prod.snd] at hgeo
                have hmove : ¬ moved rook := fun h => hnext (hgeo.1.trans h.1)
                refine ⟨transfer rook, (transfer_mem _ _).mpr hrook,
                  (across_large _ hcell _ (white_transfer _ (placement.1 hrook))).mpr ?_⟩
                refine ⟨?_, ?_⟩
                · simp only [transfer, if_neg hmove]
                  rw [← hgeo.1, hrow]
                · have hnot : ¬ last < small row := by
                    exact not_lt_of_ge (by change (small row).val ≤ n - 1; omega)
                  have hside : ¬ rook.2 < small rook.1 := mt hgeo.2.mpr hnot
                  simpa only [transfer, if_neg hmove, hcol, ← hrow, inherited,
                    Fin.castSucc_lt_castSucc_iff] using
                    iff_of_false (not_lt_of_gt (Fin.castSucc_lt_last (small row))) hside
          · obtain ⟨column, hcolumn⟩ := Fin.eq_castSucc_of_ne_last hcol
            have heq : cell = embed (row, column) := Prod.ext hrow.symm hcolumn.symm
            have hwhite := (white_embed (row, column)).mp (heq ▸ hcell)
            by_cases hmove : moved (row, column)
            · have hrow_next : row = next := hmove.1
              apply across_next (by rw [← hrow, hrow_next])
              simpa only [heq, embed, inherited, hrow_next, Fin.castSucc_lt_castSucc_iff]
                using not_lt_of_gt hmove.2
            · obtain ⟨rook, hrook, hword⟩ := (placement.2.2 (row, column) hwhite).1
              refine ⟨transfer rook, (transfer_mem _ _).mpr hrook, ?_⟩
              have heq' : cell = transfer (row, column) := by
                simpa only [transfer, if_neg hmove] using heq
              rw [heq']
              exact (horizontal _ _ hwhite (placement.1 hrook)).mpr hword
      · by_cases hcol : cell.2 = Fin.last n
        · by_cases habove : cell.1 < pivot
          · refine ⟨north, north_mem, (down_large _ _ hcell white_north).mpr ?_⟩
            refine ⟨hcol, ?_⟩
            change (cell.1 < large.symm cell.2 ↔
              pivot.succAbove top < large.symm (Fin.last n))
            rw [hcol, inverse_max]
            exact iff_of_true habove upper
          · refine ⟨south, south_mem, (down_large _ _ hcell white_south).mpr ?_⟩
            have hbelow : ¬ pivot.succAbove next < pivot := by
              rw [Fin.succAbove_lt_iff_castSucc_lt]
              exact lt_irrefl pivot
            refine ⟨hcol, ?_⟩
            change (cell.1 < large.symm cell.2 ↔
              pivot.succAbove next < large.symm (Fin.last n))
            rw [hcol, inverse_max]
            exact iff_of_false habove hbelow
        · obtain ⟨column, hcolumn⟩ := Fin.eq_castSucc_of_ne_last hcol
          by_cases hpivot : cell.1 = pivot
          · let row : Fin n := if column = small next then previous else next
            have hwhite : (row, column) ∈ permGrid small := by
              simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
              dsimp only [row]
              split_ifs with heq
              · rw [heq]
                apply small.injective.ne
                intro heq'
                have hval := congrArg Fin.val heq'
                change pivot.val - 1 = pivot.val at hval
                omega
              · exact Ne.symm heq
            obtain ⟨rook, hrook, hword⟩ := (placement.2.2 (row, column) hwhite).2
            have hgeo := (down_small _ _ hwhite (placement.1 hrook)).mp hword
            refine ⟨transfer rook, (transfer_mem _ _).mpr hrook,
              (down_large _ _ hcell (white_transfer _ (placement.1 hrook))).mpr ?_⟩
            refine ⟨hcolumn.symm.trans (congrArg Fin.castSucc hgeo.1), ?_⟩
            rw [vertical_side, ← hcolumn, inverse, hpivot]
            apply Iff.trans ?_ hgeo.2
            rw [Fin.lt_succAbove_iff_le_castSucc]
            change next ≤ small.symm column ↔ row < small.symm column
            dsimp only [row]
            split_ifs with heq
            · rw [heq, small.symm_apply_apply]
              have hprev : previous < next := by change pivot.val - 1 < pivot.val; omega
              exact iff_of_true le_rfl hprev
            · have hne : next ≠ small.symm column := by
                intro heq'
                exact heq (by rw [heq', small.apply_symm_apply])
              exact ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
          · obtain ⟨row, hrow⟩ := Fin.exists_succAbove_eq hpivot
            have heq : cell = embed (row, column) := Prod.ext hrow.symm hcolumn.symm
            have hwhite := (white_embed (row, column)).mp (heq ▸ hcell)
            obtain ⟨rook, hrook, hword⟩ := (placement.2.2 (row, column) hwhite).2
            have hgeo := (down_small _ _ hwhite (placement.1 hrook)).mp hword
            refine ⟨transfer rook, (transfer_mem _ _).mpr hrook,
              (down_large _ _ hcell (white_transfer _ (placement.1 hrook))).mpr ?_⟩
            refine ⟨hcolumn.symm.trans (congrArg Fin.castSucc hgeo.1), ?_⟩
            rw [vertical_side, ← hcolumn, inverse, ← hrow, Fin.succAbove_lt_succAbove_iff]
            exact hgeo.2
  unfold rookCount
  apply Finset.card_le_card_of_injOn lift
  · intro rooks hrooks
    have hplacement := preserve rooks (Finset.mem_filter.mp hrooks).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hplacement.1, hplacement⟩
  · intro rooks _ other _ heq
    ext cell
    rw [← transfer_mem cell rooks, ← transfer_mem cell other, heq]

end D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDeletions
