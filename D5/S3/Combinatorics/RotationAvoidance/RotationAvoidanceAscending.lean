/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending
   mirror-E: none(waiver:minimum-split-ascending-class)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Minimum-split occurrence witnesses characterize the ascending circular class. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCounts
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscending

open D5.S3.Combinatorics Nonnesting.NonnestingDefs

theorem minimum_split_ascending (left right : List ℕ)
    (hnodup : (left ++ 1 :: right).Nodup)
    (hleast : ∀ value ∈ left ++ right, 1 < value) :
    (¬ Occurs [1, 2, 3] (left ++ 1 :: right) ∧
      ¬ Occurs [3, 4, 1, 2] (left ++ 1 :: right)) ↔
    (¬ Occurs [1, 2, 3] left ∧ ¬ Occurs [3, 4, 1, 2] left) ∧
      right.Pairwise (· > ·) ∧
      (∀ lower upper, [lower, upper].Sublist left → lower < upper →
        ∀ middle ∈ right, lower < middle ∧ middle < upper) := by
  classical
  have build (pattern word : List ℕ) (size : ℕ)
      (hpattern : pattern.Perm (List.range' 1 size)) (hletters : letters pattern = size)
      (witness : ℕ → ℕ)
      (hincreasing : ∀ rank, 1 ≤ rank → rank < size →
        witness rank < witness (rank + 1))
      (hsub : (pattern.map witness).Sublist word) : Occurs pattern word := by
    refine ⟨witness, ?_, ?_, hsub, by simp⟩
    · simpa [hletters] using hincreasing
    · intro rank hlow hhigh
      rw [hletters] at hhigh
      apply hsub.subset
      apply List.mem_map_of_mem
      apply hpattern.mem_iff.mpr
      simp only [List.mem_range'_1]
      omega
  have inherited (pattern smaller larger : List ℕ) (hsublist : smaller.Sublist larger) :
      Occurs pattern smaller → Occurs pattern larger := by
    rintro ⟨witness, hincreasing, hmem, hsub, _⟩
    exact ⟨witness, hincreasing, fun rank hlo hhi => hsublist.subset (hmem rank hlo hhi),
      hsub.trans hsublist, by simp⟩
  have split_selected (selected : List ℕ)
      (hsub : selected.Sublist (left ++ 1 :: right)) :
      ∃ cut ≤ selected.length,
        (selected.take cut).Sublist left ∧ (selected.drop cut).Sublist (1 :: right) := by
    obtain ⟨first, last, heq, hfirst, hlast⟩ := List.sublist_append_iff.mp hsub
    refine ⟨first.length, ?_, ?_, ?_⟩
    · rw [heq, List.length_append]; omega
    · simpa [heq] using hfirst
    · simpa [heq] using hlast
  have positive (value : ℕ) (hvalue : value ∈ left ++ 1 :: right) : 1 ≤ value := by
    simp only [List.mem_append, List.mem_cons] at hvalue
    rcases hvalue with hleft | rfl | hright
    · exact Nat.le_of_lt (hleast _ (by simp [hleft]))
    · omega
    · exact Nat.le_of_lt (hleast _ (by simp [hright]))
  have leftSub : left.Sublist (left ++ 1 :: right) := List.sublist_append_left _ _
  constructor
  · rintro ⟨h123, h3412⟩
    have descending : right.Pairwise (· > ·) := by
      rw [List.pairwise_iff_forall_sublist]
      intro upper lower hpair
      have hne : upper ≠ lower := by
        have := hnodup.sublist ((hpair.cons 1).trans (List.sublist_append_right _ _))
        simpa using this
      by_contra hnot
      have hfirst : 1 < upper := hleast _ (by simp [hpair.subset (by simp : upper ∈
        [upper, lower])])
      have hsecond : upper < lower := by omega
      apply h123
      apply build _ _ 3 (by decide) (by rfl)
        (fun rank => if rank = 1 then 1 else if rank = 2 then upper else lower)
      · intro rank hlo hhi
        have : rank = 1 ∨ rank = 2 := by omega
        rcases this with rfl | rfl <;> simp <;> omega
      · simpa using (hpair.cons_cons 1).trans (List.sublist_append_right _ _)
    refine ⟨⟨fun hocc => h123 (inherited _ _ _ leftSub hocc),
      fun hocc => h3412 (inherited _ _ _ leftSub hocc)⟩, descending, ?_⟩
    intro lower upper hpair hascent middle hmiddle
    have hupper : upper ∈ left := hpair.subset (by simp)
    have hlower : lower ∈ left := hpair.subset (by simp)
    have hlow : 1 < lower := hleast _ (by simp [hlower])
    have hmid : 1 < middle := hleast _ (by simp [hmiddle])
    have hneLow : lower ≠ middle := (List.nodup_append.mp hnodup).2.2 _ hlower _
      (by simp [hmiddle])
    have hneHigh : upper ≠ middle := (List.nodup_append.mp hnodup).2.2 _ hupper _
      (by simp [hmiddle])
    constructor
    · by_contra hnot
      have hmiddleLow : middle < lower := by omega
      apply h3412
      apply build _ _ 4 (by decide) (by rfl)
        (fun rank => if rank = 1 then 1 else if rank = 2 then middle
          else if rank = 3 then lower else upper)
      · intro rank hlo hhi
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl <;> simp <;> omega
      · simpa using hpair.append ((List.singleton_sublist.mpr hmiddle).cons_cons 1)
    · by_contra hnot
      have hupperMiddle : upper < middle := by omega
      apply h123
      apply build _ _ 3 (by decide) (by rfl)
        (fun rank => if rank = 1 then lower else if rank = 2 then upper else middle)
      · intro rank hlo hhi
        have : rank = 1 ∨ rank = 2 := by omega
        rcases this with rfl | rfl <;> simp <;> omega
      · simpa using hpair.append ((List.singleton_sublist.mpr hmiddle).cons 1)
  · rintro ⟨⟨hleft123, hleft3412⟩, descending, interval⟩
    constructor
    · rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have hpositive : 1 ≤ witness 1 := positive _ (hmem 1 (by omega) (by decide))
      change [witness 1, witness 2, witness 3].Sublist (left ++ 1 :: right) at hsub
      obtain ⟨cut, hcut, hprefix, hsuffix⟩ := split_selected _ hsub
      have : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 := by simp at hcut; omega
      rcases this with rfl | rfl | rfl | rfl
      · simp only [List.drop_zero] at hsuffix
        have hpair : [witness 2, witness 3].Sublist right := hsuffix.of_cons_cons
        have := List.pairwise_iff_forall_sublist.mp descending hpair
        omega
      · have hselected : [witness 2, witness 3].Sublist (1 :: right) := by
          simpa using hsuffix
        have hpair : [witness 2, witness 3].Sublist right :=
          List.Sublist.of_cons_of_ne (by omega) hselected
        have := List.pairwise_iff_forall_sublist.mp descending hpair
        omega
      · have hpair : [witness 1, witness 2].Sublist left := by simpa using hprefix
        have hselected : [witness 3].Sublist (1 :: right) := by simpa using hsuffix
        have hlast : witness 3 ∈ right :=
          (List.Sublist.of_cons_of_ne (by omega) hselected).subset (by simp)
        have := interval _ _ hpair h12 _ hlast
        omega
      · apply hleft123
        exact build _ _ 3 (by decide) (by rfl) witness
          (by intro rank hlo hhi; exact hincreasing rank hlo hhi) (by simpa using hprefix)
    · rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have h34 : witness 3 < witness 4 := hincreasing 3 (by omega) (by decide)
      have hpositive : 1 ≤ witness 1 := positive _ (hmem 1 (by omega) (by decide))
      change [witness 3, witness 4, witness 1, witness 2].Sublist
        (left ++ 1 :: right) at hsub
      obtain ⟨cut, hcut, hprefix, hsuffix⟩ := split_selected _ hsub
      have : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 := by
        simp at hcut; omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simp only [List.drop_zero] at hsuffix
        have hselected : [witness 3, witness 4, witness 1, witness 2].Sublist right :=
          List.Sublist.of_cons_of_ne (by omega) hsuffix
        have hpair : [witness 3, witness 4].Sublist right :=
          (by decide : [3, 4].Sublist [3, 4, 1, 2]).map witness |>.trans hselected
        have := List.pairwise_iff_forall_sublist.mp descending hpair
        omega
      · have hselected : [witness 4, witness 1, witness 2].Sublist (1 :: right) := by
          simpa using hsuffix
        have hrest : [witness 4, witness 1, witness 2].Sublist right :=
          List.Sublist.of_cons_of_ne (by omega) hselected
        have hpair : [witness 1, witness 2].Sublist right :=
          (by decide : [1, 2].Sublist [4, 1, 2]).map witness |>.trans hrest
        have := List.pairwise_iff_forall_sublist.mp descending hpair
        omega
      · have hpair : [witness 3, witness 4].Sublist left := by simpa using hprefix
        have hselected : [witness 1, witness 2].Sublist (1 :: right) := by
          simpa using hsuffix
        have hlast : witness 2 ∈ right := hselected.of_cons_cons.subset (by simp)
        have := interval _ _ hpair h34 _ hlast
        omega
      · have hpair : [witness 3, witness 4].Sublist left :=
          (by decide : [3, 4].Sublist [3, 4, 1]).map witness |>.trans
            (by simpa using hprefix)
        have hselected : [witness 2].Sublist (1 :: right) := by simpa using hsuffix
        have hlast : witness 2 ∈ right :=
          (List.Sublist.of_cons_of_ne (by omega) hselected).subset (by simp)
        have := interval _ _ hpair h34 _ hlast
        omega
      · apply hleft3412
        exact build _ _ 4 (by decide) (by rfl) witness
          (by intro rank hlo hhi; exact hincreasing rank hlo hhi) (by simpa using hprefix)

theorem ascending_middle_interval (n : ℕ) (left right : List ℕ)
    (hperm : (left ++ 1 :: right).Perm (List.range' 1 n))
    (havoid : ¬ Occurs [1, 2, 3] (left ++ 1 :: right) ∧
      ¬ Occurs [3, 4, 1, 2] (left ++ 1 :: right))
    (hascent : ¬ left.Pairwise (· > ·)) :
    (∀ low ∈ right, ∀ high ∈ right, ∀ middle, low < middle → middle < high →
      middle ∈ right) ∧
    (∀ middle ∈ right,
      (left.filter (fun value => decide (value < middle))).Pairwise (· > ·) ∧
      (left.filter (fun value => decide (middle < value))).Pairwise (· > ·)) := by
  classical
  have hnodup : (left ++ 1 :: right).Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hleast : ∀ value ∈ left ++ right, 1 < value := by
    intro value hvalue
    have hne : value ≠ 1 := by
      have hl := (List.nodup_append.mp hnodup).2.2
      have hr := (List.nodup_append.mp hnodup).2.1
      rcases List.mem_append.mp hvalue with hvalue | hvalue
      · exact hl _ hvalue 1 (by simp)
      · exact fun heq => (List.nodup_cons.mp hr).1 (heq ▸ hvalue)
    have hmem : value ∈ left ++ 1 :: right := by
      rcases List.mem_append.mp hvalue with hl | hr
      · exact List.mem_append_left _ hl
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    have := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
    omega
  obtain ⟨_, _, sandwich⟩ := (minimum_split_ascending _ _ hnodup hleast).mp havoid
  have hleftNodup : left.Nodup := (List.nodup_append.mp hnodup).1
  have gap_impossible (word : List ℕ) (lower upper low high middle : ℕ)
      (hpair : [lower, upper].Sublist word) (horder : lower < low ∧ high < upper)
      (hgap : low < middle ∧ middle < high)
      (hbound : ∀ first last, [first, last].Sublist word → first < last →
        first < low ∧ high < last) (hmiddle : middle ∈ word) : False := by
    induction word with
    | nil => simp at hmiddle
    | cons first rest ih =>
      by_cases hfirst : first = lower
      · subst first
        have hmem : middle ∈ rest :=
          (List.mem_cons.mp hmiddle).resolve_left (by omega)
        have hselected : [lower, middle].Sublist (lower :: rest) :=
          (List.singleton_sublist.mpr hmem).cons_cons lower
        have := hbound _ _ hselected (by omega)
        omega
      · have htailPair : [lower, upper].Sublist rest :=
          List.Sublist.of_cons_of_ne (Ne.symm hfirst) hpair
        by_cases hfirstMiddle : first = middle
        · subst first
          have hmem : upper ∈ rest := htailPair.subset (by simp)
          have hselected : [middle, upper].Sublist (middle :: rest) :=
            (List.singleton_sublist.mpr hmem).cons_cons middle
          have := hbound _ _ hselected (by omega)
          omega
        · apply ih htailPair
          · intro first last hselected hlt
            exact hbound first last (hselected.cons _) hlt
          · exact (List.mem_cons.mp hmiddle).resolve_left (Ne.symm hfirstMiddle)
  have hexists : ∃ lower upper, [lower, upper].Sublist left ∧ lower < upper := by
    rw [List.pairwise_iff_forall_sublist] at hascent
    push Not at hascent
    obtain ⟨lower, upper, hpair, hnot⟩ := hascent
    have hne : lower ≠ upper := by simpa using hleftNodup.sublist hpair
    exact ⟨lower, upper, hpair, by omega⟩
  constructor
  · intro low hlow high hhigh middle hlowMiddle hmiddleHigh
    have hlo : 1 < low := hleast _ (List.mem_append_right _ hlow)
    have hhi : high ≤ n := by
      have hm : high ∈ left ++ 1 :: right :=
        List.mem_append_right _ (List.mem_cons_of_mem _ hhigh)
      have := List.mem_range'_1.mp (hperm.mem_iff.mp hm)
      omega
    have hmem : middle ∈ left ++ 1 :: right := hperm.mem_iff.mpr
      (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    rcases List.mem_append.mp hmem with hleft | hright
    · obtain ⟨lower, upper, hpair, hlt⟩ := hexists
      have hbound : lower < low ∧ high < upper :=
        ⟨(sandwich _ _ hpair hlt _ hlow).1, (sandwich _ _ hpair hlt _ hhigh).2⟩
      exact False.elim (gap_impossible left lower upper low high middle hpair hbound
        ⟨hlowMiddle, hmiddleHigh⟩ (by
          intro first last hselected hlt
          exact ⟨(sandwich _ _ hselected hlt _ hlow).1,
            (sandwich _ _ hselected hlt _ hhigh).2⟩) hleft)
    · exact (List.mem_cons.mp hright).resolve_left (by omega)
  · intro middle hmiddle
    have filtered (predicate : ℕ → Bool)
        (hside : (∀ value ∈ left.filter predicate, value < middle) ∨
          (∀ value ∈ left.filter predicate, middle < value)) :
        (left.filter predicate).Pairwise (· > ·) := by
      rw [List.pairwise_iff_forall_sublist]
      intro first last hpair
      have hselected : [first, last].Sublist left := hpair.trans List.filter_sublist
      have hne : first ≠ last := by simpa using hleftNodup.sublist hselected
      by_contra hnot
      have hlt : first < last := by omega
      have hsandwich := sandwich _ _ hselected hlt _ hmiddle
      rcases hside with hlow | hhigh
      · have := hlow last (hpair.subset (by simp))
        omega
      · have := hhigh first (hpair.subset (by simp))
        omega
    constructor
    · apply filtered
      left
      intro value hvalue
      exact of_decide_eq_true (List.mem_filter.mp hvalue).2
    · apply filtered
      right
      intro value hvalue
      exact of_decide_eq_true (List.mem_filter.mp hvalue).2

theorem ascending_shuffle_normal_form (n : ℕ) (left right : List ℕ) (middle : ℕ)
    (hperm : (left ++ 1 :: right).Perm (List.range' 1 n))
    (hmiddle : middle ∈ right) (hascent : ¬ left.Pairwise (· > ·)) :
    (¬ Occurs [1, 2, 3] (left ++ 1 :: right) ∧
      ¬ Occurs [3, 4, 1, 2] (left ++ 1 :: right)) ↔
    right.Pairwise (· > ·) ∧
      (∀ value ∈ left,
        (∀ other ∈ right, value < other) ∨ (∀ other ∈ right, other < value)) ∧
      (left.filter (fun value => decide (value < middle))).Pairwise (· > ·) ∧
      (left.filter (fun value => decide (middle < value))).Pairwise (· > ·) := by
  classical
  have hnodup := hperm.nodup_iff.mpr List.nodup_range'
  have hdisjoint : ∀ value ∈ left, value ∉ right := by
    intro value hvalue hright
    exact (List.nodup_append.mp hnodup).2.2 _ hvalue _ (by simp [hright]) rfl
  have hleast : ∀ value ∈ left ++ right, 1 < value := by
    intro value hvalue
    have hnot : value ≠ 1 := by
      rcases List.mem_append.mp hvalue with hl | hr
      · exact (List.nodup_append.mp hnodup).2.2 _ hl 1 (by simp)
      · exact fun heq => (List.nodup_cons.mp
          (List.nodup_append.mp hnodup).2.1).1 (heq ▸ hr)
    have hmem : value ∈ left ++ 1 :: right := by
      rcases List.mem_append.mp hvalue with hl | hr
      · exact List.mem_append_left _ hl
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    have := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
    omega
  constructor
  · intro havoid
    obtain ⟨_, hdescending, _⟩ := (minimum_split_ascending _ _ hnodup hleast).mp havoid
    obtain ⟨hinterval, hfilters⟩ := ascending_middle_interval n left right hperm
      havoid hascent
    refine ⟨hdescending, ?_, (hfilters middle hmiddle).1, (hfilters middle hmiddle).2⟩
    intro value hvalue
    have hne : value ≠ middle := fun heq => hdisjoint value hvalue (heq ▸ hmiddle)
    by_cases hlow : value < middle
    · left
      intro other hother
      have hneOther : value ≠ other := fun heq => hdisjoint value hvalue (heq ▸ hother)
      by_contra hnot
      have hgap : value ∈ right := hinterval other hother middle hmiddle value
        (by omega) hlow
      exact hdisjoint value hvalue hgap
    · right
      intro other hother
      have hneOther : value ≠ other := fun heq => hdisjoint value hvalue (heq ▸ hother)
      by_contra hnot
      have hgap : value ∈ right := hinterval middle hmiddle other hother value
        (by omega) (by omega)
      exact hdisjoint value hvalue hgap
  · rintro ⟨hdescending, houtside, hlowDescending, hhighDescending⟩
    have crossing (lower upper : ℕ) (hpair : [lower, upper].Sublist left)
        (horder : lower < upper) :
        (∀ other ∈ right, lower < other) ∧ (∀ other ∈ right, other < upper) := by
      have hlower : lower ∈ left := hpair.subset (by simp)
      have hupper : upper ∈ left := hpair.subset (by simp)
      have hneLow : lower ≠ middle := fun heq =>
        hdisjoint lower hlower (heq ▸ hmiddle)
      have hneHigh : upper ≠ middle := fun heq =>
        hdisjoint upper hupper (heq ▸ hmiddle)
      have hlow : lower < middle := by
        by_contra hnot
        have hfiltered : [lower, upper].Sublist
            (left.filter (fun value => decide (middle < value))) := by
          have := hpair.filter (fun value => decide (middle < value))
          simpa [show middle < lower by omega, show middle < upper by omega] using this
        have := List.pairwise_iff_forall_sublist.mp hhighDescending hfiltered
        omega
      have hhigh : middle < upper := by
        by_contra hnot
        have hfiltered : [lower, upper].Sublist
            (left.filter (fun value => decide (value < middle))) := by
          have := hpair.filter (fun value => decide (value < middle))
          simpa [show lower < middle by omega, show upper < middle by omega] using this
        have := List.pairwise_iff_forall_sublist.mp hlowDescending hfiltered
        omega
      constructor
      · rcases houtside lower hlower with hl | hh
        · exact hl
        · have := hh middle hmiddle
          omega
      · rcases houtside upper hupper with hl | hh
        · have := hl middle hmiddle
          omega
        · exact hh
    apply (minimum_split_ascending _ _ hnodup hleast).mpr
    refine ⟨⟨?_, ?_⟩, hdescending, ?_⟩
    · rintro ⟨witness, hincreasing, _, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have firstPair := (by decide : [1, 2].Sublist [1, 2, 3]).map witness |>.trans hsub
      have lastPair := (by decide : [2, 3].Sublist [1, 2, 3]).map witness |>.trans hsub
      have hfirst := (crossing _ _ firstPair h12).2 middle hmiddle
      have hlast := (crossing _ _ lastPair h23).1 middle hmiddle
      omega
    · rintro ⟨witness, hincreasing, _, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have h34 : witness 3 < witness 4 := hincreasing 3 (by omega) (by decide)
      have firstPair := (by decide : [3, 4].Sublist [3, 4, 1, 2]).map witness
        |>.trans hsub
      have lastPair := (by decide : [1, 2].Sublist [3, 4, 1, 2]).map witness
        |>.trans hsub
      have hfirst := (crossing _ _ firstPair h34).1 middle hmiddle
      have hlast := (crossing _ _ lastPair h12).2 middle hmiddle
      omega
    · intro lower upper hpair horder other hother
      exact ⟨(crossing _ _ hpair horder).1 other hother,
        (crossing _ _ hpair horder).2 other hother⟩

theorem shuffle_count (predicate : ℕ → Bool) (low high : List ℕ)
    (hlow : ∀ value ∈ low, predicate value = true)
    (hhigh : ∀ value ∈ high, predicate value = false) :
    ({word : List ℕ | word.Perm (low ++ high) ∧ word.filter predicate = low ∧
      word.filter (fun value => !(predicate value)) = high} : Set (List ℕ)).ncard =
      (low.length + high.length).choose low.length := by
  classical
  let words := fun first last : List ℕ =>
    {word : List ℕ | word.Perm (first ++ last) ∧ word.filter predicate = first ∧
      word.filter (fun value => !(predicate value)) = last}
  have finite_words (first last : List ℕ) : (words first last).Finite := by
    apply (List.finite_toSet (first ++ last).permutations).subset
    intro word hword
    exact List.mem_permutations.mpr hword.1
  have empty_low (last : List ℕ) (hlast : ∀ value ∈ last, predicate value = false) :
      words [] last = {last} := by
    ext word
    constructor
    · rintro ⟨hperm, _, hfilter⟩
      have hself : word.filter (fun value => !(predicate value)) = word := by
        apply List.filter_eq_self.mpr
        intro value hvalue
        have hlastValue : value ∈ last := by simpa using hperm.mem_iff.mp hvalue
        simp [hlast value hlastValue]
      rw [hself] at hfilter
      exact Set.mem_singleton_iff.mpr hfilter
    · intro hword
      have : word = last := Set.mem_singleton_iff.mp hword
      subst word
      refine ⟨by simp, ?_, ?_⟩
      · apply List.filter_eq_nil_iff.mpr
        intro value hvalue
        simp [hlast value hvalue]
      · apply List.filter_eq_self.mpr
        intro value hvalue
        simp [hlast value hvalue]
  have empty_high (first : List ℕ) (hfirst : ∀ value ∈ first, predicate value = true) :
      words first [] = {first} := by
    ext word
    constructor
    · rintro ⟨hperm, hfilter, _⟩
      have hself : word.filter predicate = word := by
        apply List.filter_eq_self.mpr
        intro value hvalue
        have hfirstValue : value ∈ first := by simpa using hperm.mem_iff.mp hvalue
        exact hfirst value hfirstValue
      rw [hself] at hfilter
      exact Set.mem_singleton_iff.mpr hfilter
    · intro hword
      have : word = first := Set.mem_singleton_iff.mp hword
      subst word
      refine ⟨by simp, List.filter_eq_self.mpr hfirst, ?_⟩
      apply List.filter_eq_nil_iff.mpr
      intro value hvalue
      simp [hfirst value hvalue]
  change (words low high).ncard = _
  induction low generalizing high with
  | nil => simp [empty_low high hhigh]
  | cons lower low ihLow =>
    have hlower : predicate lower = true := hlow lower (by simp)
    have hlowTail : ∀ value ∈ low, predicate value = true := by
      intro value hvalue
      exact hlow value (by simp [hvalue])
    induction high with
    | nil => simp [empty_high _ hlow]
    | cons upper high ihHigh =>
      have hupper : predicate upper = false := hhigh upper (by simp)
      have hhighTail : ∀ value ∈ high, predicate value = false := by
        intro value hvalue
        exact hhigh value (by simp [hvalue])
      have hne : lower ≠ upper := by
        intro heq
        rw [heq, hupper] at hlower
        contradiction
      have decomposition : words (lower :: low) (upper :: high) =
          (List.cons lower '' words low (upper :: high)) ∪
            (List.cons upper '' words (lower :: low) high) := by
        ext word
        constructor
        · rintro ⟨hperm, hfilterLow, hfilterHigh⟩
          cases word with
          | nil => simp at hfilterLow
          | cons first rest =>
            cases hfirst : predicate first with
            | false =>
              have hhead : first = upper := by
                simpa [List.filter_cons, hfirst] using congrArg List.head? hfilterHigh
              subst first
              right
              refine ⟨rest, ⟨?_, ?_, ?_⟩, rfl⟩
              · apply List.Perm.cons_inv
                apply hperm.trans
                simpa using List.perm_middle (a := upper) (l₁ := lower :: low)
                  (l₂ := high)
              · simpa [List.filter_cons, hupper] using hfilterLow
              · simpa [List.filter_cons, hupper] using hfilterHigh
            | true =>
              have hhead : first = lower := by
                simpa [List.filter_cons, hfirst] using congrArg List.head? hfilterLow
              subst first
              left
              refine ⟨rest, ⟨List.Perm.cons_inv hperm, ?_, ?_⟩, rfl⟩
              · simpa [List.filter_cons, hlower] using hfilterLow
              · simpa [List.filter_cons, hlower] using hfilterHigh
        · rintro (⟨rest, ⟨hperm, hfilterLow, hfilterHigh⟩, rfl⟩ |
              ⟨rest, ⟨hperm, hfilterLow, hfilterHigh⟩, rfl⟩)
          · exact ⟨hperm.cons lower, by simpa [hlower] using hfilterLow,
              by simpa [hlower] using hfilterHigh⟩
          · refine ⟨?_, by simpa [hupper] using hfilterLow,
              by simpa [hupper] using hfilterHigh⟩
            apply (hperm.cons upper).trans
            simpa using (List.perm_middle (a := upper) (l₁ := lower :: low)
              (l₂ := high)).symm
      have hdisjoint : Disjoint (List.cons lower '' words low (upper :: high))
          (List.cons upper '' words (lower :: low) high) := by
        rw [Set.disjoint_left]
        rintro word ⟨first, _, hfirst⟩ ⟨last, _, hlast⟩
        exact hne (List.cons.inj (hfirst.trans hlast.symm)).1
      rw [decomposition, Set.ncard_union_eq hdisjoint
        ((finite_words _ _).image _) ((finite_words _ _).image _),
        Set.ncard_image_of_injective _ (fun _ _ heq => (List.cons.inj heq).2),
        Set.ncard_image_of_injective _ (fun _ _ heq => (List.cons.inj heq).2),
        ihLow _ hlowTail hhigh, ihHigh hhighTail]
      simp only [List.length_cons]
      rw [show low.length + (high.length + 1) = low.length + high.length + 1 by omega,
        show low.length + 1 + high.length = low.length + high.length + 1 by omega,
        show low.length + 1 + (high.length + 1) = low.length + high.length + 1 + 1
          by omega]
      exact (Nat.choose_succ_succ' (low.length + high.length + 1) low.length).symm

theorem ascending_interval_ranks (size : ℕ) (left right : List ℕ)
    (hperm : (left ++ 1 :: right).Perm (List.range' 1 size))
    (havoid : ¬ Occurs [1, 2, 3] (left ++ 1 :: right) ∧
      ¬ Occurs [3, 4, 1, 2] (left ++ 1 :: right))
    (hascent : ¬ left.Pairwise (· > ·)) (hnonempty : right ≠ []) :
    ∃ low high : ℕ, 1 ≤ low ∧ 1 ≤ high ∧ low + high + right.length + 1 = size ∧
      right = (List.range' (low + 2) right.length).reverse ∧
      left.filter (fun value => decide (value < low + 2)) =
        (List.range' 2 low).reverse ∧
      left.filter (fun value => decide (low + right.length + 1 < value)) =
        (List.range' (low + right.length + 2) high).reverse := by
  classical
  have hnodup := hperm.nodup_iff.mpr List.nodup_range'
  have hleftNodup := (List.nodup_append.mp hnodup).1
  have bounds (value : ℕ) (hvalue : value ∈ left ++ right) :
      2 ≤ value ∧ value ≤ size := by
    have hnot : value ≠ 1 := by
      rcases List.mem_append.mp hvalue with hl | hr
      · exact (List.nodup_append.mp hnodup).2.2 _ hl 1 (by simp)
      · exact fun heq => (List.nodup_cons.mp
          (List.nodup_append.mp hnodup).2.1).1 (heq ▸ hr)
    have hmem : value ∈ left ++ 1 :: right := by
      rcases List.mem_append.mp hvalue with hl | hr
      · exact List.mem_append_left _ hl
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    have := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
    omega
  obtain ⟨hconvex, hfilters⟩ := ascending_middle_interval size left right hperm havoid hascent
  obtain ⟨_, hdescending, sandwich⟩ := (minimum_split_ascending _ _ hnodup (by
    intro value hvalue
    exact (bounds value hvalue).1)).mp havoid
  have interval (word : List ℕ) (hword : word ≠ [])
      (hdecreasing : word.Pairwise (· > ·))
      (hfull : ∀ low ∈ word, ∀ high ∈ word, ∀ value, low < value → value < high →
        value ∈ word) :
      ∃ first, word = (List.range' first word.length).reverse := by
    induction word with
    | nil => contradiction
    | cons head tail ih =>
      cases tail with
      | nil => exact ⟨head, by simp⟩
      | cons next rest =>
        have hhead : ∀ value ∈ next :: rest, value < head :=
          (List.pairwise_cons.mp hdecreasing).1
        have htailDescending := (List.pairwise_cons.mp hdecreasing).2
        have htailFull : ∀ low ∈ next :: rest, ∀ high ∈ next :: rest, ∀ value,
            low < value → value < high → value ∈ next :: rest := by
          intro low hlow high hhigh value hlo hhi
          have hmem := hfull low (by simp [hlow]) high (by simp [hhigh]) value hlo hhi
          exact (List.mem_cons.mp hmem).resolve_left (by
            have := hhead high hhigh
            omega)
        obtain ⟨first, htail⟩ := ih (by simp) htailDescending htailFull
        have hlength : 0 < (next :: rest).length := by simp
        have hfirst : first ∈ next :: rest := by
          rw [htail, List.mem_reverse]
          simp only [List.mem_range'_1]
          omega
        have hlast : first + (next :: rest).length - 1 ∈ next :: rest := by
          rw [htail, List.mem_reverse]
          simp only [List.mem_range'_1, List.length_reverse, List.length_range']
          omega
        have hupper := hhead _ hlast
        have hnext : head = first + (next :: rest).length := by
          by_contra hnot
          have hgap : first + (next :: rest).length ∈ head :: next :: rest :=
            hfull first (by simp [hfirst]) head (by simp) _ (by omega) (by omega)
          have hgapTail : first + (next :: rest).length ∈ next :: rest :=
            (List.mem_cons.mp hgap).resolve_left (by omega)
          rw [htail, List.mem_reverse] at hgapTail
          have := List.mem_range'_1.mp hgapTail
          simp only [List.length_reverse, List.length_range'] at this
          omega
        refine ⟨first, ?_⟩
        rw [List.length_cons, List.range'_concat]
        simpa [← htail, hnext]
  obtain ⟨first, hright⟩ := interval right hnonempty hdescending hconvex
  have hlength : 0 < right.length := List.length_pos_iff.mpr hnonempty
  have hfirst : first ∈ right := by
    rw [hright, List.mem_reverse]
    simp only [List.mem_range'_1]
    omega
  have hlast : first + right.length - 1 ∈ right := by
    rw [hright, List.mem_reverse]
    simp only [List.mem_range'_1, List.length_reverse, List.length_range']
    omega
  have hfirstBound := bounds first (by simp [hfirst])
  have hlastBound := bounds (first + right.length - 1) (by simp [hlast])
  let low := first - 2
  let high := size - low - right.length - 1
  have hfirstEq : first = low + 2 := by dsimp [low]; omega
  have hsum : low + high + right.length + 1 = size := by dsimp [low, high]; omega
  have hlowNodup := hleftNodup.filter (fun value => decide (value < low + 2))
  have hhighNodup := hleftNodup.filter
    (fun value => decide (low + right.length + 1 < value))
  have filter_membership (value : ℕ) :
      value ∈ left.filter (fun value => decide (value < low + 2)) ↔
        value ∈ List.range' 2 low := by
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨hvalue, hlt⟩
      have := bounds value (by simp [hvalue])
      omega
    · rintro ⟨hlo, hhi⟩
      have hmem : value ∈ left ++ 1 :: right := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hnot : value ∉ right := by
        rw [hright, List.mem_reverse]
        intro hvalue
        have := List.mem_range'_1.mp hvalue
        omega
      rcases List.mem_append.mp hmem with hl | hr
      · exact ⟨hl, by omega⟩
      · simp only [List.mem_cons] at hr
        rcases hr with heq | hr
        · omega
        · exact False.elim (hnot hr)
  have high_membership (value : ℕ) :
      value ∈ left.filter (fun value => decide (low + right.length + 1 < value)) ↔
        value ∈ List.range' (low + right.length + 2) high := by
    simp only [List.mem_filter, decide_eq_true_eq, List.mem_range'_1]
    constructor
    · rintro ⟨hvalue, hlt⟩
      have := bounds value (by simp [hvalue])
      omega
    · rintro ⟨hlo, hhi⟩
      have hmem : value ∈ left ++ 1 :: right := hperm.mem_iff.mpr
        (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      have hnot : value ∉ right := by
        rw [hright, List.mem_reverse]
        intro hvalue
        have := List.mem_range'_1.mp hvalue
        omega
      rcases List.mem_append.mp hmem with hl | hr
      · exact ⟨hl, by omega⟩
      · simp only [List.mem_cons] at hr
        rcases hr with heq | hr
        · omega
        · exact False.elim (hnot hr)
  have hloDesc := (hfilters first hfirst).1
  have hhiDesc := (hfilters (first + right.length - 1) hlast).2
  have low_word : left.filter (fun value => decide (value < low + 2)) =
      (List.range' 2 low).reverse := by
    have hp : (left.filter (fun value => decide (value < low + 2))).Perm
        (List.range' 2 low).reverse := by
      apply (List.perm_ext_iff_of_nodup hlowNodup
        (List.nodup_reverse.mpr List.nodup_range')).mpr
      intro value
      simpa only [List.mem_reverse] using filter_membership value
    exact hp.eq_of_pairwise (by intro first last hfirst hlast; omega)
      (by simpa [hfirstEq] using hloDesc)
      (List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega)))
  have high_word : left.filter (fun value => decide (low + right.length + 1 < value)) =
      (List.range' (low + right.length + 2) high).reverse := by
    have hp : (left.filter (fun value => decide (low + right.length + 1 < value))).Perm
        (List.range' (low + right.length + 2) high).reverse := by
      apply (List.perm_ext_iff_of_nodup hhighNodup
        (List.nodup_reverse.mpr List.nodup_range')).mpr
      intro value
      simpa only [List.mem_reverse] using high_membership value
    exact hp.eq_of_pairwise (by intro first last hfirst hlast; omega)
      (by simpa [hfirstEq, show low + 2 + right.length - 1 = low + right.length + 1
        by omega] using hhiDesc)
      (List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega)))
  have hexists : ∃ lower upper, [lower, upper].Sublist left ∧ lower < upper := by
    rw [List.pairwise_iff_forall_sublist] at hascent
    push Not at hascent
    obtain ⟨lower, upper, hpair, hnot⟩ := hascent
    have hne : lower ≠ upper := by simpa using hleftNodup.sublist hpair
    exact ⟨lower, upper, hpair, by omega⟩
  obtain ⟨lower, upper, hpair, horder⟩ := hexists
  have hlower : lower ∈ left := hpair.subset (by simp)
  have hupper : upper ∈ left := hpair.subset (by simp)
  have hsandLow := (sandwich lower upper hpair horder first hfirst).1
  have hsandHigh := (sandwich lower upper hpair horder _ hlast).2
  have hlowerBound := bounds lower (by simp [hlower])
  have hupperBound := bounds upper (by simp [hupper])
  refine ⟨low, high, ?_, ?_, hsum, ?_, low_word, high_word⟩
  · omega
  · omega
  · simpa [hfirstEq] using hright

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceAscending
