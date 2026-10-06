/- GID: D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CrosswordGrid/SkewMergedRookWords
   mirror-E: none(waiver:permutation-word-graph-construction)
   anchors: []
   utility: none
   digest: Permutation-grid word graphs and the uniform size of complete rook placements. -/

import D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords

open D5.S3.Combinatorics.CrosswordRookCounts
  (Cell SameAcross SameDown IsRookPlacement rookCount)
open D5.S3.Combinatorics.CrosswordPermutationGridRefutation
  (permGrid WordData IsWordMatching rookPlacement_iff_wordMatching)
open D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookDefs (SkewMerged)

theorem word_structure {n : ℕ} (_positive : 1 ≤ n) (w : Equiv.Perm (Fin n)) :
    (∀ c ∈ permGrid w, ∀ d ∈ permGrid w,
      SameAcross (permGrid w) c d ↔
        c.1 = d.1 ∧ (c.2 < w c.1 ↔ d.2 < w d.1)) ∧
    ∃ data : WordData n (permGrid w), ∀ cell : Cell n,
      data.downId cell = 2 * cell.2.val + if cell.1 < w.symm cell.2 then 0 else 1 := by
  classical
  let white := permGrid w
  let word := fun c : Cell n => white.filter fun d =>
    c.1 = d.1 ∧ (c.2 < w c.1 ↔ d.2 < w d.1)
  let down := fun c : Cell n => 2 * c.2.val + if c.1 < w.symm c.2 then 0 else 1
  have white_iff (c : Cell n) : c ∈ white ↔ w c.1 ≠ c.2 := by
    simp [white, permGrid]
  have across_iff (c d : Cell n) (hc : c ∈ white) (hd : d ∈ white) :
      SameAcross white c d ↔ c.1 = d.1 ∧ (c.2 < w c.1 ↔ d.2 < w d.1) := by
    constructor
    · rintro ⟨hrow, hinterval⟩
      refine ⟨hrow, ?_⟩
      have hcne := (white_iff c).mp hc
      have hdne := (white_iff d).mp hd
      rw [← hrow] at hdne ⊢
      by_contra hside
      have hmin : min c.2 d.2 ≤ w c.1 := by
        by_cases h : c.2 < w c.1
        · exact (min_le_left _ _).trans (le_of_lt h)
        · have h : d.2 < w c.1 := by tauto
          exact (min_le_right _ _).trans (le_of_lt h)
      have hmax : w c.1 ≤ max c.2 d.2 := by
        by_cases h : c.2 < w c.1
        · have h : ¬ d.2 < w c.1 := by tauto
          exact (le_of_not_gt h).trans (le_max_right _ _)
        · exact (le_of_not_gt h).trans (le_max_left _ _)
      exact ((white_iff _).mp (hinterval _ hmin hmax)) rfl
    · rintro ⟨hrow, hside⟩
      refine ⟨hrow, ?_⟩
      intro column hmin hmax
      apply (white_iff _).mpr
      have hcne := (white_iff c).mp hc
      have hdne := (white_iff d).mp hd
      rw [← hrow] at hdne hside
      by_cases h : c.2 < w c.1
      · have hbound : max c.2 d.2 < w c.1 := max_lt h (hside.mp h)
        exact ne_of_gt (hmax.trans_lt hbound)
      · have hleft : w c.1 < c.2 := lt_of_le_of_ne (le_of_not_gt h) hcne
        have hright : w c.1 < d.2 :=
          lt_of_le_of_ne (le_of_not_gt (mt hside.mpr h)) hdne
        exact ne_of_lt ((lt_min hleft hright).trans_le hmin)
  have down_iff (c d : Cell n) (hc : c ∈ white) (hd : d ∈ white) :
      SameDown white c d ↔ down c = down d := by
    have hcne : w.symm c.2 ≠ c.1 := by
      intro heq
      apply (white_iff c).mp hc
      rw [← heq, w.apply_symm_apply]
    have hdne : w.symm d.2 ≠ d.1 := by
      intro heq
      apply (white_iff d).mp hd
      rw [← heq, w.apply_symm_apply]
    have geometric : SameDown white c d ↔
        c.2 = d.2 ∧ (c.1 < w.symm c.2 ↔ d.1 < w.symm d.2) := by
      constructor
      · rintro ⟨hcol, hinterval⟩
        refine ⟨hcol, ?_⟩
        rw [← hcol]
        by_contra hside
        have hmin : min c.1 d.1 ≤ w.symm c.2 := by
          by_cases h : c.1 < w.symm c.2
          · exact (min_le_left _ _).trans (le_of_lt h)
          · have h : d.1 < w.symm c.2 := by tauto
            exact (min_le_right _ _).trans (le_of_lt h)
        have hmax : w.symm c.2 ≤ max c.1 d.1 := by
          by_cases h : c.1 < w.symm c.2
          · have h : ¬ d.1 < w.symm c.2 := by tauto
            exact (le_of_not_gt h).trans (le_max_right _ _)
          · exact (le_of_not_gt h).trans (le_max_left _ _)
        have hblack := (white_iff _).mp (hinterval _ hmin hmax)
        exact hblack (w.apply_symm_apply _)
      · rintro ⟨hcol, hside⟩
        refine ⟨hcol, ?_⟩
        intro row hmin hmax
        apply (white_iff _).mpr
        intro hblack
        have hrow : row = w.symm c.2 := ((w.symm_apply_eq).mpr hblack.symm).symm
        rw [hrow] at hmin hmax
        rw [← hcol] at hdne hside
        by_cases h : c.1 < w.symm c.2
        · exact (not_le_of_gt (max_lt h (hside.mp h))) hmax
        · have hleft : w.symm c.2 < c.1 := lt_of_le_of_ne (le_of_not_gt h) hcne
          have hright : w.symm c.2 < d.1 :=
            lt_of_le_of_ne (le_of_not_gt (mt hside.mpr h)) hdne
          exact (not_le_of_gt (lt_min hleft hright)) hmin
    rw [geometric]
    constructor
    · rintro ⟨hcol, hside⟩
      rw [hcol] at hside
      simp only [down, hcol]
      congr 1
      exact if_congr hside rfl rfl
    · intro heq
      have hcol : c.2 = d.2 := by
        apply Fin.ext
        dsimp [down] at heq
        split_ifs at heq <;> omega
      refine ⟨hcol, ?_⟩
      dsimp [down] at heq
      rw [hcol] at heq ⊢
      split_ifs at heq <;> first | tauto | omega
  have word_mem (c d : Cell n) :
      d ∈ word c ↔ d ∈ white ∧
        c.1 = d.1 ∧ (c.2 < w c.1 ↔ d.2 < w d.1) := by
    simp [word]
  have word_eq (c d : Cell n)
      (h : c.1 = d.1 ∧ (c.2 < w c.1 ↔ d.2 < w d.1)) : word c = word d := by
    ext cell
    rw [word_mem, word_mem]
    constructor
    · rintro ⟨hwhite, hrow, hside⟩
      exact ⟨hwhite, h.1.symm.trans hrow, h.2.symm.trans hside⟩
    · rintro ⟨hwhite, hrow, hside⟩
      exact ⟨hwhite, h.1.trans hrow, h.2.trans hside⟩
  refine ⟨fun c hc d hd => across_iff c d hc hd, ?_⟩
  refine ⟨
    { across := (white.image word).toList
      downId := down
      downIds := white.image down
      word_subset := ?_
      word_nonempty := ?_
      word_unique := ?_
      across_iff := ?_
      down_iff := fun c hc d hd => down_iff c d hc hd
      ids_eq := rfl }, fun _ => rfl⟩
  · intro across hacross
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hacross)
    exact Finset.filter_subset _ _
  · intro across hacross
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hacross)
    exact ⟨c, (word_mem c c).mpr ⟨hc, rfl, Iff.rfl⟩⟩
  · intro c hc
    refine ⟨word c, ⟨?_, (word_mem c c).mpr ⟨hc, rfl, Iff.rfl⟩⟩, ?_⟩
    · exact Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
    · intro across hacross
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hacross.1)
      exact word_eq d c ((word_mem d c).mp hacross.2).2
  · intro c hc d hd
    constructor
    · intro h
      refine ⟨word c, ?_, (word_mem c c).mpr ⟨hc, rfl, Iff.rfl⟩, ?_⟩
      · exact Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
      · exact (word_mem c d).mpr ⟨hd, (across_iff c d hc hd).mp h⟩
    · rintro ⟨across, hacross, hcA, hdA⟩
      obtain ⟨cell, hcell, rfl⟩ :=
        Finset.mem_image.mp (Finset.mem_toList.mp hacross)
      have hfirst := ((word_mem cell c).mp hcA).2
      have hsecond := ((word_mem cell d).mp hdA).2
      exact (across_iff c d hc hd).mpr
        ⟨hfirst.1.symm.trans hsecond.1, hfirst.2.symm.trans hsecond.2⟩

theorem placement_card {n : ℕ} (positive : 1 ≤ n) (w : Equiv.Perm (Fin n))
    (rooks : Finset (Cell n)) (placement : IsRookPlacement (permGrid w) rooks) :
    rooks.card = 2 * n - 2 := by
  classical
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  obtain ⟨_, data, label⟩ := word_structure positive w
  let north := (Finset.univ.erase first).image fun row : Fin n => 2 * (w row).val
  let south := (Finset.univ.erase last).image fun row : Fin n => 2 * (w row).val + 1
  have label_set : (permGrid w).image data.downId = north ∪ south := by
    ext identifier
    constructor
    · rintro hidentifier
      obtain ⟨cell, hcell, rfl⟩ := Finset.mem_image.mp hidentifier
      have hwhite : w cell.1 ≠ cell.2 := by simpa [permGrid] using hcell
      have hrowne : cell.1 ≠ w.symm cell.2 := by
        intro heq
        exact hwhite (w.eq_symm_apply.mp heq)
      rw [label]
      by_cases habove : cell.1 < w.symm cell.2
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨w.symm cell.2, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · intro heq
          have hzero : (w.symm cell.2).val = 0 := congrArg Fin.val heq
          have := cell.1.isLt
          omega
        · simp [w.apply_symm_apply, habove]
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨w.symm cell.2, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · intro heq
          have hlast : (w.symm cell.2).val = n - 1 := congrArg Fin.val heq
          have hlt : w.symm cell.2 < cell.1 := lt_of_le_of_ne (le_of_not_gt habove)
            hrowne.symm
          have := cell.1.isLt
          omega
        · simp [w.apply_symm_apply, habove]
    · intro hidentifier
      rcases Finset.mem_union.mp hidentifier with hnorth | hsouth
      · obtain ⟨row, hrow, rfl⟩ := Finset.mem_image.mp hnorth
        have hne := (Finset.mem_erase.mp hrow).1
        have hpos : 0 < row.val := by
          by_contra hnonpos
          apply hne
          apply Fin.ext
          dsimp [first]
          omega
        refine Finset.mem_image.mpr ⟨(first, w row), ?_, ?_⟩
        · simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun heq => hne (w.injective heq).symm
        · rw [label, w.symm_apply_apply]
          have habove : first < row := hpos
          simp [habove]
      · obtain ⟨row, hrow, rfl⟩ := Finset.mem_image.mp hsouth
        have hne := (Finset.mem_erase.mp hrow).1
        have hbelow : row < last := by
          have hbound := row.isLt
          have hvalne : row.val ≠ n - 1 := by
            intro heq
            exact hne (Fin.ext heq)
          change row.val < n - 1
          omega
        refine Finset.mem_image.mpr ⟨(last, w row), ?_, ?_⟩
        · simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun heq => hne (w.injective heq).symm
        · rw [label, w.symm_apply_apply]
          simp [not_lt_of_gt hbelow]
  have disjoint : Disjoint north south := by
    apply Finset.disjoint_left.mpr
    intro identifier hnorth hsouth
    obtain ⟨row, _, hrow⟩ := Finset.mem_image.mp hnorth
    obtain ⟨other, _, hother⟩ := Finset.mem_image.mp hsouth
    omega
  have north_card : north.card = n - 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro row other heq
      dsimp at heq
      apply w.injective
      apply Fin.ext
      omega
  have south_card : south.card = n - 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro row other heq
      dsimp at heq
      apply w.injective
      apply Fin.ext
      omega
  have matching := (rookPlacement_iff_wordMatching data rooks).mp placement
  have injective : Set.InjOn data.downId rooks := by
    intro cell hcell other hother heq
    by_contra hne
    exact matching.2.2.1 cell hcell other hother hne heq
  have hcard : rooks.card = north.card + south.card := by
    calc
      rooks.card = (rooks.image data.downId).card :=
        (Finset.card_image_iff.mpr injective).symm
      _ = data.downIds.card := congrArg Finset.card matching.2.2.2
      _ = ((permGrid w).image data.downId).card := congrArg Finset.card data.ids_eq.symm
      _ = (north ∪ south).card := congrArg Finset.card label_set
      _ = north.card + south.card := Finset.card_union_of_disjoint disjoint
  rw [north_card, south_card] at hcard
  omega

theorem record_prefix_forces_neighbor {n : ℕ} (_positive : 1 ≤ n)
    (w : Equiv.Perm (Fin n)) (rooks : Finset (Cell n))
    (placement : IsRookPlacement (permGrid w) rooks) (bound : ℕ)
    (records : ∀ column : Fin n, column.val < bound →
      (∀ later : Fin n, column < later → later.val < bound →
        w.symm column < w.symm later) ∨
      (∀ later : Fin n, column < later → later.val < bound →
        w.symm later < w.symm column)) :
    ∀ column previous : Fin n, previous.val + 1 = column.val → column.val < bound →
      (w.symm column, previous) ∈ rooks := by
  classical
  have force : ∀ height : ℕ, ∀ column previous : Fin n,
      column.val = height → previous.val + 1 = column.val → column.val < bound →
        (w.symm column, previous) ∈ rooks := by
    intro height
    induction height using Nat.strong_induction_on with
    | h height induction_hyp =>
      intro column previous hheight hstep hbound
      have hprevious : previous < column := by omega
      have hwhite : (w.symm column, previous) ∈ permGrid w := by
        simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa using ne_of_gt hprevious
      obtain ⟨rook, hrook, hword⟩ := (placement.2.2 _ hwhite).1
      have hrow : rook.1 = w.symm column := hword.1.symm
      have hcol : rook.2 < column := by
        by_contra hnot
        have hmin : min previous rook.2 ≤ column :=
          (min_le_left _ _).trans (le_of_lt hprevious)
        have hmax : column ≤ max previous rook.2 :=
          (le_of_not_gt hnot).trans (le_max_right _ _)
        have hblack := hword.2 column hmin hmax
        simp [permGrid] at hblack
      have hle : rook.2 ≤ previous := by omega
      have heq : rook.2 = previous := by
        by_contra hne
        have hlt : rook.2 < previous := lt_of_le_of_ne hle hne
        let next : Fin n := ⟨rook.2.val + 1, by omega⟩
        have hnext : next < column := by change rook.2.val + 1 < column.val; omega
        have hsuccessor : rook.2 < next := Nat.lt_succ_self _
        have hnext_bound : next.val < bound := lt_trans hnext hbound
        have hforced : (w.symm next, rook.2) ∈ rooks :=
          induction_hyp next.val (by omega) next rook.2 rfl rfl hnext_bound
        have hdistinct : rook ≠ (w.symm next, rook.2) := by
          intro heq
          have hrows : w.symm column = w.symm next :=
            hrow.symm.trans (congrArg Prod.fst heq)
          exact (ne_of_gt hnext) (w.symm.injective hrows)
        have hdown : SameDown (permGrid w) rook (w.symm next, rook.2) := by
          refine ⟨rfl, ?_⟩
          intro row hmin hmax
          simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
          intro hblack
          have hblackrow : row = w.symm rook.2 := w.eq_symm_apply.mpr hblack
          rw [hblackrow, hrow] at hmin hmax
          rcases records rook.2 (by omega) with habove | hbelow
          · have hfirst := habove column hcol hbound
            have hsecond := habove next hsuccessor hnext_bound
            exact (not_le_of_gt (lt_min hfirst hsecond)) hmin
          · have hfirst := hbelow column hcol hbound
            have hsecond := hbelow next hsuccessor hnext_bound
            exact (not_le_of_gt (max_lt hfirst hsecond)) hmax
        exact (placement.2.1 rook hrook _ hforced hdistinct).2 hdown
      have hcell : rook = (w.symm column, previous) := Prod.ext hrow heq
      exact hcell ▸ hrook
  intro column previous hstep hbound
  exact force column.val column previous rfl hstep hbound

theorem symmetries {n : ℕ} (_positive : 1 ≤ n) (w : Equiv.Perm (Fin n)) :
    (rookCount (permGrid w) = rookCount (permGrid w.symm) ∧
      (SkewMerged w ↔ SkewMerged w.symm)) ∧
    (rookCount (permGrid w) = rookCount (permGrid (w.trans Fin.revPerm)) ∧
      (SkewMerged w ↔ SkewMerged (w.trans Fin.revPerm))) ∧
    (rookCount (permGrid w) = rookCount (permGrid (Fin.revPerm.trans w)) ∧
      (SkewMerged w ↔ SkewMerged (Fin.revPerm.trans w))) ∧
    (∀ rooks, IsRookPlacement (permGrid w) rooks →
      IsRookPlacement (permGrid w.symm) (rooks.image Prod.swap)) ∧
    (∀ rooks, IsRookPlacement (permGrid w) rooks →
      IsRookPlacement (permGrid (w.trans Fin.revPerm))
        (rooks.image fun cell => (cell.1, cell.2.rev))) ∧
    (∀ rooks, IsRookPlacement (permGrid w) rooks →
      IsRookPlacement (permGrid (Fin.revPerm.trans w))
        (rooks.image fun cell => (cell.1.rev, cell.2))) := by
  classical
  have count_transfer (source target : Equiv.Perm (Fin n)) (map : Cell n → Cell n)
      (inverse : Function.Involutive map)
      (forward : ∀ rooks, IsRookPlacement (permGrid source) rooks →
        IsRookPlacement (permGrid target) (rooks.image map))
      (backward : ∀ rooks, IsRookPlacement (permGrid target) rooks →
        IsRookPlacement (permGrid source) (rooks.image map)) :
      rookCount (permGrid source) = rookCount (permGrid target) := by
    unfold rookCount
    apply Finset.card_bij (fun rooks _ => rooks.image map)
    · intro rooks hrooks
      have hplacement := forward rooks (Finset.mem_filter.mp hrooks).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hplacement.1, hplacement⟩
    · intro rooks _ other _ heq
      exact Finset.image_injective inverse.injective heq
    · intro rooks hrooks
      have hplacement := backward rooks (Finset.mem_filter.mp hrooks).2
      refine ⟨rooks.image map,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hplacement.1, hplacement⟩, ?_⟩
      simp [Finset.image_image, inverse]
  have transpose_placement (source : Equiv.Perm (Fin n)) (rooks : Finset (Cell n))
      (placement : IsRookPlacement (permGrid source) rooks) :
      IsRookPlacement (permGrid source.symm) (rooks.image Prod.swap) := by
    have white (cell : Cell n) :
        cell.swap ∈ permGrid source.symm ↔ cell ∈ permGrid source := by
      simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hne heq
        exact hne (source.eq_symm_apply.mpr heq).symm
      · intro hne heq
        exact hne (source.eq_symm_apply.mp heq.symm)
    have across (cell other : Cell n) :
        SameDown (permGrid source.symm) cell.swap other.swap ↔
          SameAcross (permGrid source) cell other := by
      simp only [SameDown, SameAcross, Prod.fst_swap, Prod.snd_swap]
      constructor
      · rintro ⟨hrow, hinterval⟩
        exact ⟨hrow, fun column hmin hmax =>
          (white (cell.1, column)).mp (hinterval column hmin hmax)⟩
      · rintro ⟨hrow, hinterval⟩
        exact ⟨hrow, fun column hmin hmax =>
          (white (cell.1, column)).mpr (hinterval column hmin hmax)⟩
    have down (cell other : Cell n) :
        SameAcross (permGrid source.symm) cell.swap other.swap ↔
          SameDown (permGrid source) cell other := by
      simp only [SameDown, SameAcross, Prod.fst_swap, Prod.snd_swap]
      constructor
      · rintro ⟨hcol, hinterval⟩
        exact ⟨hcol, fun row hmin hmax =>
          (white (row, cell.2)).mp (hinterval row hmin hmax)⟩
      · rintro ⟨hcol, hinterval⟩
        exact ⟨hcol, fun row hmin hmax =>
          (white (row, cell.2)).mpr (hinterval row hmin hmax)⟩
    refine ⟨?_, ?_, ?_⟩
    · intro cell hcell
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
      exact (white original).mpr (placement.1 horiginal)
    · intro cell hcell other hother hne
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
      obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp hother
      have hdistinct : original ≠ second := fun heq => hne (congrArg Prod.swap heq)
      have hpair := placement.2.1 original horiginal second hsecond hdistinct
      exact ⟨fun hword => hpair.2 ((down _ _).mp hword),
        fun hword => hpair.1 ((across _ _).mp hword)⟩
    · intro cell hcell
      have hwhite := (white cell.swap).mp (by simpa using hcell)
      obtain ⟨arook, harook, haword⟩ := (placement.2.2 cell.swap hwhite).1
      obtain ⟨drook, hdrook, hdword⟩ := (placement.2.2 cell.swap hwhite).2
      constructor
      · refine ⟨drook.swap, Finset.mem_image.mpr ⟨drook, hdrook, rfl⟩, ?_⟩
        simpa using (down cell.swap drook).mpr hdword
      · refine ⟨arook.swap, Finset.mem_image.mpr ⟨arook, harook, rfl⟩, ?_⟩
        simpa using (across cell.swap arook).mpr haword
  have transpose_count (source : Equiv.Perm (Fin n)) :
      rookCount (permGrid source) = rookCount (permGrid source.symm) := by
    apply count_transfer source source.symm Prod.swap (fun _ => Prod.swap_swap _)
    · exact transpose_placement source
    · intro rooks placement
      simpa using transpose_placement source.symm rooks placement
  let reflect := fun cell : Cell n => (cell.1, Fin.rev cell.2)
  have reflect_involution : Function.Involutive reflect := by
    intro cell
    exact Prod.ext rfl (Fin.rev_rev _)
  have reflect_twice (cell : Cell n) : reflect (reflect cell) = cell :=
    reflect_involution cell
  have twice (source : Equiv.Perm (Fin n)) :
      (source.trans Fin.revPerm).trans Fin.revPerm = source := by
    apply Equiv.ext
    intro row
    exact Fin.rev_rev _
  have column_across (source : Equiv.Perm (Fin n)) (cell other : Cell n)
      (word : SameAcross (permGrid source) cell other) :
      SameAcross (permGrid (source.trans Fin.revPerm)) (reflect cell) (reflect other) := by
    have white (original : Cell n) :
        reflect original ∈ permGrid (source.trans Fin.revPerm) ↔
          original ∈ permGrid source := by
      simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
      change (Fin.rev (source original.1) ≠ Fin.rev original.2) ↔
        source original.1 ≠ original.2
      exact Fin.rev_inj.not
    refine ⟨word.1, ?_⟩
    intro column hmin hmax
    have hleft : min cell.2 other.2 ≤ Fin.rev column := by
      change column ≤ max (Fin.rev cell.2) (Fin.rev other.2) at hmax
      rcases le_max_iff.mp hmax with hcell | hother
      · exact (min_le_left _ _).trans (Fin.le_rev_iff.mp hcell)
      · exact (min_le_right _ _).trans (Fin.le_rev_iff.mp hother)
    have hright : Fin.rev column ≤ max cell.2 other.2 := by
      change min (Fin.rev cell.2) (Fin.rev other.2) ≤ column at hmin
      rcases min_le_iff.mp hmin with hcell | hother
      · exact (Fin.rev_le_iff.mp hcell).trans (le_max_left _ _)
      · exact (Fin.rev_le_iff.mp hother).trans (le_max_right _ _)
    have hwhite := (white (cell.1, Fin.rev column)).mpr (word.2 _ hleft hright)
    simpa [reflect] using hwhite
  have column_down (source : Equiv.Perm (Fin n)) (cell other : Cell n)
      (word : SameDown (permGrid source) cell other) :
      SameDown (permGrid (source.trans Fin.revPerm)) (reflect cell) (reflect other) := by
    refine ⟨congrArg Fin.rev word.1, ?_⟩
    intro row hmin hmax
    have hwhite := word.2 row hmin hmax
    simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and] at hwhite ⊢
    exact Fin.rev_inj.not.mpr hwhite
  have column_placement (source : Equiv.Perm (Fin n)) (rooks : Finset (Cell n))
      (placement : IsRookPlacement (permGrid source) rooks) :
      IsRookPlacement (permGrid (source.trans Fin.revPerm)) (rooks.image reflect) := by
    have white (cell : Cell n) :
        reflect cell ∈ permGrid (source.trans Fin.revPerm) ↔ cell ∈ permGrid source := by
      simp only [permGrid, Finset.mem_filter, Finset.mem_univ, true_and]
      change (Fin.rev (source cell.1) ≠ Fin.rev cell.2) ↔ source cell.1 ≠ cell.2
      exact Fin.rev_inj.not
    refine ⟨?_, ?_, ?_⟩
    · intro cell hcell
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
      exact (white original).mpr (placement.1 horiginal)
    · intro cell hcell other hother hne
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
      obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp hother
      have hdistinct : original ≠ second := fun heq => hne (congrArg reflect heq)
      have hpair := placement.2.1 original horiginal second hsecond hdistinct
      constructor
      · intro hword
        have hback := column_across (source.trans Fin.revPerm) _ _ hword
        exact hpair.1 (by simpa only [twice, reflect_twice] using hback)
      · intro hword
        have hback := column_down (source.trans Fin.revPerm) _ _ hword
        exact hpair.2 (by simpa only [twice, reflect_twice] using hback)
    · intro cell hcell
      have hwhite := (white (reflect cell)).mp (by simpa only [reflect_twice] using hcell)
      obtain ⟨arook, harook, haword⟩ := (placement.2.2 (reflect cell) hwhite).1
      obtain ⟨drook, hdrook, hdword⟩ := (placement.2.2 (reflect cell) hwhite).2
      constructor
      · refine ⟨reflect arook, Finset.mem_image.mpr ⟨arook, harook, rfl⟩, ?_⟩
        simpa only [reflect_twice] using column_across source _ _ haword
      · refine ⟨reflect drook, Finset.mem_image.mpr ⟨drook, hdrook, rfl⟩, ?_⟩
        simpa only [reflect_twice] using column_down source _ _ hdword
  have column_count (source : Equiv.Perm (Fin n)) :
      rookCount (permGrid source) = rookCount (permGrid (source.trans Fin.revPerm)) := by
    apply count_transfer source (source.trans Fin.revPerm) reflect reflect_involution
    · exact column_placement source
    · intro rooks placement
      simpa only [twice] using column_placement (source.trans Fin.revPerm) rooks placement
  have inverse_skew (source : Equiv.Perm (Fin n)) (skew : SkewMerged source) :
      SkewMerged source.symm := by
    obtain ⟨increasing, hinc, hdec⟩ := skew
    refine ⟨increasing.image source, ?_, ?_⟩
    · intro row hrow other hother hlt
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hrow
      obtain ⟨second, hsecond, rfl⟩ := Finset.mem_image.mp hother
      simp only [source.symm_apply_apply]
      by_contra hnot
      have hne : second ≠ original := fun heq => (ne_of_lt hlt) (congrArg source heq.symm)
      have hreverse := hinc second hsecond original horiginal
        (lt_of_le_of_ne (le_of_not_gt hnot) hne)
      exact (lt_asymm hlt hreverse)
    · intro row hrow other hother hlt
      have hfirst : source.symm row ∉ increasing := by
        intro hmem
        exact hrow (Finset.mem_image.mpr ⟨_, hmem, source.apply_symm_apply _⟩)
      have hsecond : source.symm other ∉ increasing := by
        intro hmem
        exact hother (Finset.mem_image.mpr ⟨_, hmem, source.apply_symm_apply _⟩)
      by_contra hnot
      have hne : source.symm row ≠ source.symm other :=
        fun heq => (ne_of_lt hlt) (source.symm.injective heq)
      have hreverse := hdec _ hfirst _ hsecond
        (lt_of_le_of_ne (le_of_not_gt hnot) hne)
      simp only [source.apply_symm_apply] at hreverse
      exact lt_asymm hlt hreverse
  have transpose_skew (source : Equiv.Perm (Fin n)) :
      SkewMerged source ↔ SkewMerged source.symm := by
    exact ⟨inverse_skew source, fun h => by simpa using inverse_skew source.symm h⟩
  have reflect_skew (source : Equiv.Perm (Fin n)) (skew : SkewMerged source) :
      SkewMerged (source.trans Fin.revPerm) := by
    obtain ⟨increasing, hinc, hdec⟩ := skew
    refine ⟨Finset.univ \ increasing, ?_, ?_⟩
    · intro row hrow other hother hlt
      have hfirst : row ∉ increasing := (Finset.mem_sdiff.mp hrow).2
      have hsecond : other ∉ increasing := (Finset.mem_sdiff.mp hother).2
      exact Fin.rev_lt_rev.mpr (hdec row hfirst other hsecond hlt)
    · intro row hrow other hother hlt
      have hfirst : row ∈ increasing := by simpa using hrow
      have hsecond : other ∈ increasing := by simpa using hother
      exact Fin.rev_lt_rev.mpr (hinc row hfirst other hsecond hlt)
  have column_skew (source : Equiv.Perm (Fin n)) :
      SkewMerged source ↔ SkewMerged (source.trans Fin.revPerm) := by
    exact ⟨reflect_skew source,
      fun h => by simpa only [twice] using reflect_skew (source.trans Fin.revPerm) h⟩
  have row_identity : (w.symm.trans Fin.revPerm).symm = Fin.revPerm.trans w := by
    ext row
    rfl
  refine ⟨⟨transpose_count w, transpose_skew w⟩,
    ⟨column_count w, column_skew w⟩, ?_, transpose_placement w, column_placement w, ?_⟩
  · constructor
    · exact (transpose_count w).trans
        ((column_count w.symm).trans ((transpose_count (w.symm.trans Fin.revPerm)).trans
          (congrArg (fun permutation => rookCount (permGrid permutation)) row_identity)))
    · exact (transpose_skew w).trans
        ((column_skew w.symm).trans ((transpose_skew (w.symm.trans Fin.revPerm)).trans
          (iff_of_eq (congrArg SkewMerged row_identity))))
  · intro rooks placement
    have first := transpose_placement w rooks placement
    have second := column_placement w.symm _ first
    have third := transpose_placement (w.symm.trans Fin.revPerm) _ second
    simpa only [row_identity, Finset.image_image, Function.comp_def, reflect,
      Prod.swap, Prod.fst, Prod.snd] using third

end D5.S3.Combinatorics.CrosswordGrid.SkewMergedRookWords
