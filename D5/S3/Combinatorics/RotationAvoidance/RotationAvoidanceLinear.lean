/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear
   mirror-E: none(waiver:maximum-split-linear-enumeration)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Maximum-split witnesses and bijections enumerate the second circular class. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceCounts
import D5.S3.Combinatorics.ArcherCyclicPadovanBlocks
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLinear

open D5.S3.Combinatorics Nonnesting.NonnestingDefs RotationAvoidanceCounts

theorem maximum_split_binary (left right : List ℕ) (pivot : ℕ)
    (hnodup : (left ++ pivot :: right).Nodup)
    (hgreatest : ∀ value ∈ left ++ right, value < pivot) :
    (¬ Occurs [2, 3, 1] (left ++ pivot :: right) ∧
      ¬ Occurs [2, 1, 3, 4] (left ++ pivot :: right) ∧
      ¬ Occurs [4, 2, 1, 3] (left ++ pivot :: right)) ↔
    (∀ low ∈ left, ∀ high ∈ right, low < high) ∧
      (¬ Occurs [2, 1, 3] left ∧ ¬ Occurs [2, 3, 1] left) ∧
      (¬ Occurs [2, 1, 3] right ∧ ¬ Occurs [2, 3, 1] right) ∧
      (left.Pairwise (· < ·) ∨ right.Pairwise (· > ·)) := by
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
      (hsub : selected.Sublist (left ++ pivot :: right)) :
      ∃ cut ≤ selected.length,
        (selected.take cut).Sublist left ∧
          (selected.drop cut).Sublist (pivot :: right) := by
    obtain ⟨first, last, heq, hfirst, hlast⟩ := List.sublist_append_iff.mp hsub
    refine ⟨first.length, ?_, ?_, ?_⟩
    · rw [heq, List.length_append]; omega
    · simpa [heq] using hfirst
    · simpa [heq] using hlast
  have below (value : ℕ) (hvalue : value ∈ left ++ pivot :: right) : value ≤ pivot := by
    simp only [List.mem_append, List.mem_cons] at hvalue
    rcases hvalue with hleft | rfl | hright
    · exact Nat.le_of_lt (hgreatest _ (by simp [hleft]))
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (hgreatest _ (by simp [hright]))
  have leftSub : left.Sublist (left ++ pivot :: right) := List.sublist_append_left _ _
  have rightSub : right.Sublist (left ++ pivot :: right) :=
    (List.sublist_cons_self _ _).trans (List.sublist_append_right _ _)
  constructor
  · rintro ⟨h231, h2134, h4213⟩
    have separation : ∀ low ∈ left, ∀ high ∈ right, low < high := by
      intro low hlow high hhigh
      have hne : low ≠ high := by
        have hd := List.nodup_append.mp hnodup
        exact hd.2.2 low hlow high (by simp [hhigh])
      by_contra hnot
      have hh : high < low := by omega
      have hl : low < pivot := hgreatest _ (by simp [hlow])
      apply h231
      apply build _ _ 3 (by decide) (by rfl)
        (fun rank => if rank = 1 then high else if rank = 2 then low else pivot)
      · intro rank hlo hhi
        have : rank = 1 ∨ rank = 2 := by omega
        rcases this with rfl | rfl <;> simp <;> omega
      · simpa using (List.singleton_sublist.mpr hlow).append
          ((List.singleton_sublist.mpr hhigh).cons_cons pivot)
    have append213 (word : List ℕ) (hword : word.Sublist left) :
        ¬ Occurs [2, 1, 3] word := by
      rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have htop : witness 3 < pivot := hgreatest _ (by
        apply List.mem_append_left
        exact hword.subset (hmem 3 (by omega) (by decide)))
      apply h2134
      apply build _ _ 4 (by decide) (by rfl)
        (fun rank => if rank = 4 then pivot else witness rank)
      · intro rank hlo hhi
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl <;> simp <;> omega
      · change [witness 2, witness 1, witness 3].Sublist word at hsub
        simpa using (hsub.trans hword).append
          (List.singleton_sublist.mpr (List.mem_cons_self : pivot ∈ pivot :: right))
    have prepend213 : ¬ Occurs [2, 1, 3] right := by
      rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have htop : witness 3 < pivot := hgreatest _ (by
        apply List.mem_append_right
        exact hmem 3 (by omega) (by decide))
      apply h4213
      apply build _ _ 4 (by decide) (by rfl)
        (fun rank => if rank = 4 then pivot else witness rank)
      · intro rank hlo hhi
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl <;> simp <;> omega
      · change [witness 2, witness 1, witness 3].Sublist right at hsub
        simpa using (hsub.cons_cons pivot).trans (List.sublist_append_right _ _)
    refine ⟨separation, ⟨append213 left (List.Sublist.refl _),
      fun hocc => h231 (inherited _ _ _ leftSub hocc)⟩,
      ⟨prepend213, fun hocc => h231 (inherited _ _ _ rightSub hocc)⟩, ?_⟩
    by_contra hnot
    have hl : ¬ left.Pairwise (· < ·) := fun h => hnot (Or.inl h)
    have hr : ¬ right.Pairwise (· > ·) := fun h => hnot (Or.inr h)
    rw [List.pairwise_iff_forall_sublist] at hl hr
    push Not at hl hr
    obtain ⟨upper, lower, hleftPair, hleftNot⟩ := hl
    obtain ⟨low, high, hrightPair, hrightNot⟩ := hr
    have hneLeft : upper ≠ lower := by
      have := hnodup.sublist (hleftPair.trans leftSub)
      simpa using this
    have hneRight : low ≠ high := by
      have := hnodup.sublist (hrightPair.trans rightSub)
      simpa using this
    have h1 : lower < upper := by omega
    have h2 : upper < low := separation _ (hleftPair.subset (by simp)) _
      (hrightPair.subset (by simp))
    have h3 : low < high := by omega
    apply h2134
    apply build _ _ 4 (by decide) (by rfl)
      (fun rank => if rank = 1 then lower else if rank = 2 then upper
        else if rank = 3 then low else high)
    · intro rank hlo hhi
      have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases this with rfl | rfl | rfl <;> simp <;> omega
    · simpa using hleftPair.append (hrightPair.cons pivot)
  · rintro ⟨separation, ⟨hleft213, hleft231⟩, ⟨hright213, hright231⟩, monotone⟩
    have forbid213 (word : List ℕ) (havoid : ¬ Occurs [2, 1, 3] word)
        (witness : ℕ → ℕ) (h12 : witness 1 < witness 2)
        (h23 : witness 2 < witness 3)
        (hsub : [witness 2, witness 1, witness 3].Sublist word) : False := by
      apply havoid
      apply build _ _ 3 (by decide) (by rfl) witness
      · intro rank hlo hhi
        have : rank = 1 ∨ rank = 2 := by omega
        rcases this with rfl | rfl <;> omega
      · simpa using hsub
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have htop : witness 3 ≤ pivot := below _ (hmem 3 (by omega) (by decide))
      change [witness 2, witness 3, witness 1].Sublist (left ++ pivot :: right) at hsub
      obtain ⟨cut, hcut, hprefix, hsuffix⟩ := split_selected _ hsub
      have : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 := by simp at hcut; omega
      rcases this with rfl | rfl | rfl | rfl
      · simp only [List.drop_zero] at hsuffix
        have hselected : [witness 2, witness 3, witness 1].Sublist right :=
          List.Sublist.of_cons_of_ne (by omega) hsuffix
        apply hright231
        exact build _ _ 3 (by decide) (by rfl) witness
          (by intro rank hlo hhi; exact hincreasing rank hlo hhi) (by simpa using hselected)
      · have hlow : witness 2 ∈ left := hprefix.subset (by simp)
        have hselected : [witness 3, witness 1].Sublist (pivot :: right) := by
          simpa using hsuffix
        have hhigh : witness 1 ∈ right := hselected.of_cons_cons.subset (by simp)
        have := separation _ hlow _ hhigh
        omega
      · have hlow : witness 2 ∈ left := hprefix.subset (by simp)
        have hselected : [witness 1].Sublist (pivot :: right) := by simpa using hsuffix
        have hhigh : witness 1 ∈ right :=
          (List.Sublist.of_cons_of_ne (by omega) hselected).subset (by simp)
        have := separation _ hlow _ hhigh
        omega
      · have hselected : [witness 2, witness 3, witness 1].Sublist left := by
          simpa using hprefix
        apply hleft231
        exact build _ _ 3 (by decide) (by rfl) witness
          (by intro rank hlo hhi; exact hincreasing rank hlo hhi) (by simpa using hselected)
    · rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have h34 : witness 3 < witness 4 := hincreasing 3 (by omega) (by decide)
      have htop : witness 4 ≤ pivot := below _ (hmem 4 (by omega) (by decide))
      change [witness 2, witness 1, witness 3, witness 4].Sublist
        (left ++ pivot :: right) at hsub
      obtain ⟨cut, hcut, hprefix, hsuffix⟩ := split_selected _ hsub
      have : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 := by
        simp at hcut; omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simp only [List.drop_zero] at hsuffix
        have hselected : [witness 2, witness 1, witness 3, witness 4].Sublist right :=
          List.Sublist.of_cons_of_ne (by omega) hsuffix
        exact forbid213 _ hright213 witness h12 h23
          ((by decide : [2, 1, 3].Sublist [2, 1, 3, 4]).map witness |>.trans hselected)
      · have hlow : witness 2 ∈ left := hprefix.subset (by simp)
        have hselected : [witness 1, witness 3, witness 4].Sublist (pivot :: right) := by
          simpa using hsuffix
        have hhigh : witness 1 ∈ right :=
          (List.Sublist.of_cons_of_ne (by omega) hselected).subset (by simp)
        have := separation _ hlow _ hhigh
        omega
      · have hlpair : [witness 2, witness 1].Sublist left := by simpa using hprefix
        have hselected : [witness 3, witness 4].Sublist (pivot :: right) := by
          simpa using hsuffix
        have hrpair : [witness 3, witness 4].Sublist right :=
          List.Sublist.of_cons_of_ne (by omega) hselected
        rcases monotone with hl | hr
        · have := List.pairwise_iff_forall_sublist.mp hl hlpair
          omega
        · have := List.pairwise_iff_forall_sublist.mp hr hrpair
          omega
      · exact forbid213 _ hleft213 witness h12 h23 (by simpa using hprefix)
      · have hselected : [witness 2, witness 1, witness 3, witness 4].Sublist left := by
          simpa using hprefix
        exact forbid213 _ hleft213 witness h12 h23
          ((by decide : [2, 1, 3].Sublist [2, 1, 3, 4]).map witness |>.trans hselected)
    · rintro ⟨witness, hincreasing, hmem, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      have h34 : witness 3 < witness 4 := hincreasing 3 (by omega) (by decide)
      have htop : witness 4 ≤ pivot := below _ (hmem 4 (by omega) (by decide))
      change [witness 4, witness 2, witness 1, witness 3].Sublist
        (left ++ pivot :: right) at hsub
      obtain ⟨cut, hcut, hprefix, hsuffix⟩ := split_selected _ hsub
      have : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 := by
        simp at hcut; omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simp only [List.drop_zero] at hsuffix
        exact forbid213 _ hright213 witness h12 h23 hsuffix.of_cons_cons
      · have hselected : [witness 2, witness 1, witness 3].Sublist (pivot :: right) := by
          simpa using hsuffix
        exact forbid213 _ hright213 witness h12 h23
          (List.Sublist.of_cons_of_ne (by omega) hselected)
      · have hlow : witness 4 ∈ left := hprefix.subset (by simp)
        have hselected : [witness 1, witness 3].Sublist (pivot :: right) := by
          simpa using hsuffix
        have hhigh : witness 3 ∈ right := hselected.of_cons_cons.subset (by simp)
        have := separation _ hlow _ hhigh
        omega
      · have hlow : witness 4 ∈ left := hprefix.subset (by simp)
        have hselected : [witness 3].Sublist (pivot :: right) := by simpa using hsuffix
        have hhigh : witness 3 ∈ right :=
          (List.Sublist.of_cons_of_ne (by omega) hselected).subset (by simp)
        have := separation _ hlow _ hhigh
        omega
      · have hselected : [witness 4, witness 2, witness 1, witness 3].Sublist left := by
          simpa using hprefix
        exact forbid213 _ hleft213 witness h12 h23
          ((by decide : [2, 1, 3].Sublist [4, 2, 1, 3]).map witness |>.trans hselected)

set_option maxHeartbeats 1600000 in
theorem binary_separator_count (n : ℕ) :
    (Fishburn.FishburnClassicalDefs.classicalAvoiders n
      [[2, 3, 1], [2, 1, 3, 4], [4, 2, 1, 3]]).ncard = 2 ^ n - n := by
  classical
  let words := fun size => Fishburn.FishburnClassicalDefs.classicalAvoiders size
    [[2, 3, 1], [2, 1, 3, 4], [4, 2, 1, 3]]
  let binary := fun size => Fishburn.FishburnClassicalDefs.classicalAvoiders size
    [[2, 1, 3], [2, 3, 1]]
  have membership (size : ℕ) (word : List ℕ) : word ∈ words size ↔
      word.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] word ∧
        ¬ Occurs [2, 1, 3, 4] word ∧ ¬ Occurs [4, 2, 1, 3] word := by
    simp [words, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have binaryMember (size : ℕ) (word : List ℕ) : word ∈ binary size ↔
      word.Perm (List.range' 1 size) ∧
        ¬ Occurs [2, 1, 3] word ∧ ¬ Occurs [2, 3, 1] word := by
    simp [binary, Fishburn.FishburnClassicalDefs.classicalAvoiders]
  have finite_binary (size : ℕ) : (binary size).Finite := by
    apply (List.finite_toSet ((List.range' 1 size).permutations)).subset
    intro word hword
    exact List.mem_permutations.mpr ((binaryMember size word).mp hword).1
  have monotoneAvoids (word : List ℕ)
      (hword : word.Pairwise (· < ·) ∨ word.Pairwise (· > ·)) :
      ¬ Occurs [2, 1, 3] word ∧ ¬ Occurs [2, 3, 1] word := by
    constructor
    · rintro ⟨witness, hincreasing, _, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      rcases hword with hword | hword
      · have hpair := (by decide : [2, 1].Sublist [2, 1, 3]).map witness |>.trans hsub
        have := List.pairwise_iff_forall_sublist.mp hword hpair
        omega
      · have hpair := (by decide : [1, 3].Sublist [2, 1, 3]).map witness |>.trans hsub
        have := List.pairwise_iff_forall_sublist.mp hword hpair
        omega
    · rintro ⟨witness, hincreasing, _, hsub, _⟩
      have h12 : witness 1 < witness 2 := hincreasing 1 (by omega) (by decide)
      have h23 : witness 2 < witness 3 := hincreasing 2 (by omega) (by decide)
      rcases hword with hword | hword
      · have hpair := (by decide : [3, 1].Sublist [2, 3, 1]).map witness |>.trans hsub
        have := List.pairwise_iff_forall_sublist.mp hword hpair
        omega
      · have hpair := (by decide : [2, 3].Sublist [2, 3, 1]).map witness |>.trans hsub
        have := List.pairwise_iff_forall_sublist.mp hword hpair
        omega
  have canonical (size : ℕ) : List.range' 1 size ∈ binary size ∧
      (List.range' 1 size).reverse ∈ binary size := by
    have hi : (List.range' 1 size).Pairwise (· < ·) :=
      List.pairwise_lt_range' _ (by omega)
    have hd : (List.range' 1 size).reverse.Pairwise (· > ·) := by
      exact List.pairwise_reverse.mpr hi
    exact ⟨(binaryMember _ _).mpr ⟨List.Perm.refl _, monotoneAvoids _ (Or.inl hi)⟩,
      (binaryMember _ _).mpr ⟨List.reverse_perm _, monotoneAvoids _ (Or.inr hd)⟩⟩
  have shift (pattern word : List ℕ) (offset : ℕ)
      (hpattern : pattern ∈ [[2, 1, 3], [2, 3, 1]]) :
      Occurs pattern (word.map (offset + ·)) ↔ Occurs pattern word := by
    have hletters : letters pattern = pattern.length := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl <;> rfl
    unfold Occurs
    rw [hletters]
    exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word (offset + ·)
      (by intro low high hlt; dsimp; omega)
  have empty_binary : binary 0 = {[]} := by
    ext word
    rw [binaryMember]
    constructor
    · rintro ⟨hperm, _⟩
      have : word = [] := by simpa using hperm
      simp [this]
    · intro hword
      have : word = [] := by simpa using hword
      subst word
      exact ⟨List.Perm.refl _, ((binaryMember _ _).mp (canonical 0).1).2⟩
  have sum_binary (size : ℕ) :
      ∑ index : Fin (size + 1), (binary index.val).ncard = 2 ^ size := by
    induction size with
    | zero => simp [empty_binary]
    | succ size ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, binary_extreme_count (size + 1) (by omega)]
      simp only [Nat.add_sub_cancel, pow_succ]
      omega
  have enumeration (size : ℕ) : (words (size + 1)).ncard + (size + 1) =
      2 ^ (size + 1) := by
    let slices := fun cut =>
      ({List.range' 1 cut} ×ˢ binary (size - cut)) ∪
        (binary cut ×ˢ {(List.range' 1 (size - cut)).reverse})
    have finite_slices (cut : ℕ) : (slices cut).Finite :=
      ((Set.finite_singleton _).prod (finite_binary _)).union
        ((finite_binary _).prod (Set.finite_singleton _))
    have sliceMember (cut : ℕ) (pair : List ℕ × List ℕ) (hpair : pair ∈ slices cut) :
        pair.1 ∈ binary cut ∧ pair.2 ∈ binary (size - cut) ∧
          (pair.1.Pairwise (· < ·) ∨ pair.2.Pairwise (· > ·)) := by
      rcases hpair with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
      · have : pair.1 = List.range' 1 cut := by simpa using hleft
        rw [this]
        exact ⟨(canonical _).1, hright, Or.inl (List.pairwise_lt_range' _ (by omega))⟩
      · have : pair.2 = (List.range' 1 (size - cut)).reverse := by simpa using hright
        rw [this]
        exact ⟨hleft, (canonical _).2,
          Or.inr (List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega)))⟩
    let assemble := fun (cut : ℕ) (pair : List ℕ × List ℕ) =>
      pair.1 ++ (size + 1) :: pair.2.map (cut + ·)
    have assembled (cut : ℕ) (hcut : cut ≤ size) (pair : List ℕ × List ℕ)
        (hpair : pair ∈ slices cut) : assemble cut pair ∈ words (size + 1) := by
      obtain ⟨hleft, hright, hmonotone⟩ := sliceMember _ _ hpair
      obtain ⟨hleftPerm, hleftAvoid⟩ := (binaryMember _ _).mp hleft
      obtain ⟨hrightPerm, hrightAvoid⟩ := (binaryMember _ _).mp hright
      have hmapPerm : (pair.2.map (cut + ·)).Perm
          (List.range' (cut + 1) (size - cut)) := by
        simpa [List.map_add_range'] using hrightPerm.map (cut + ·)
      have hrange : List.range' 1 cut ++ List.range' (cut + 1) (size - cut) =
          List.range' 1 size := by
        simpa [Nat.add_sub_of_le hcut, Nat.add_comm] using
          (List.range'_append_1 (s := 1) (m := cut) (n := size - cut))
      have hperm : (assemble cut pair).Perm (List.range' 1 (size + 1)) := by
        apply List.perm_middle.trans
        have hrest : (pair.1 ++ pair.2.map (cut + ·)).Perm (List.range' 1 size) := by
          rw [← hrange]
          exact hleftPerm.append hmapPerm
        apply (hrest.cons _).trans
        have hlast := List.perm_append_comm (l₁ := [size + 1])
          (l₂ := List.range' 1 size)
        simpa [List.range'_concat, Nat.add_comm] using hlast
      have hgreatest : ∀ value ∈ pair.1 ++ pair.2.map (cut + ·), value < size + 1 := by
        intro value hvalue
        rcases List.mem_append.mp hvalue with hvalue | hvalue
        · have := List.mem_range'_1.mp (hleftPerm.mem_iff.mp hvalue)
          omega
        · have := List.mem_range'.mp (hmapPerm.mem_iff.mp hvalue)
          omega
      have hsep : ∀ low ∈ pair.1, ∀ high ∈ pair.2.map (cut + ·), low < high := by
        intro low hlow high hhigh
        have := List.mem_range'_1.mp (hleftPerm.mem_iff.mp hlow)
        have := List.mem_range'.mp (hmapPerm.mem_iff.mp hhigh)
        omega
      apply (membership _ _).mpr
      refine ⟨hperm, ?_⟩
      apply (maximum_split_binary _ _ _ (hperm.nodup_iff.mpr List.nodup_range')
        hgreatest).mpr
      refine ⟨hsep, hleftAvoid, ⟨?_, ?_⟩, ?_⟩
      · exact fun hocc => hrightAvoid.1 ((shift _ _ _ (by simp)).mp hocc)
      · exact fun hocc => hrightAvoid.2 ((shift _ _ _ (by simp)).mp hocc)
      · rcases hmonotone with hi | hd
        · exact Or.inl hi
        · right
          rw [List.pairwise_map]
          exact hd.imp (by intro low high hlt; omega)
    let Domain := Σ cut : Fin (size + 1), slices cut.val
    have (cut : Fin (size + 1)) : Finite (slices cut.val) :=
      (finite_slices _).to_subtype
    let emit : Domain → words (size + 1) := fun input =>
      ⟨assemble input.1.val input.2.val, assembled _ (by omega) _ input.2.property⟩
    have assembledCut (cut : ℕ) (hcut : cut ≤ size) (pair : List ℕ × List ℕ)
        (hpair : pair ∈ slices cut) :
        (assemble cut pair).idxOf (size + 1) = cut := by
      have hperm := (binaryMember _ _).mp (sliceMember _ _ hpair).1 |>.1
      have hlength : pair.1.length = cut := by simpa using hperm.length_eq
      have hnot : size + 1 ∉ pair.1 := by
        intro hmem
        have := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
        omega
      simp [assemble, List.idxOf_append_of_notMem hnot, hlength]
    have emitInjective : Function.Injective emit := by
      rintro ⟨cut, pair⟩ ⟨otherCut, otherPair⟩ heq
      have hwords := congrArg Subtype.val heq
      have hcuts := congrArg (List.idxOf (size + 1)) hwords
      change (assemble cut.val pair.val).idxOf (size + 1) =
        (assemble otherCut.val otherPair.val).idxOf (size + 1) at hcuts
      rw [assembledCut _ (by omega) _ pair.property,
        assembledCut _ (by omega) _ otherPair.property] at hcuts
      have hcut : cut = otherCut := Fin.ext hcuts
      subst otherCut
      apply congrArg (Sigma.mk cut)
      apply Subtype.ext
      have hlength : pair.val.1.length = cut.val := by
        simpa using ((binaryMember _ _).mp (sliceMember _ _ pair.property).1).1.length_eq
      have hotherLength : otherPair.val.1.length = cut.val := by
        simpa using ((binaryMember _ _).mp (sliceMember _ _ otherPair.property).1).1.length_eq
      have htake := congrArg (List.take cut.val) hwords
      have hleft : pair.val.1 = otherPair.val.1 := by
        simpa [emit, assemble, hlength, hotherLength] using htake
      have hdrop := congrArg (List.drop (cut.val + 1)) hwords
      have hdropLeft : pair.val.1.drop (cut.val + 1) = [] := by
        apply List.drop_eq_nil_of_le
        omega
      have hdropOther : otherPair.val.1.drop (cut.val + 1) = [] := by
        apply List.drop_eq_nil_of_le
        omega
      have hmap : pair.val.2.map (cut.val + ·) = otherPair.val.2.map (cut.val + ·) := by
        simpa [emit, assemble, List.drop_append, hlength, hotherLength,
          hdropLeft, hdropOther] using hdrop
      exact Prod.ext hleft ((List.map_inj_right (by intro low high heq; omega)).mp hmap)
    have emitSurjective : Function.Surjective emit := by
      intro output
      obtain ⟨hperm, h231, h2134, h4213⟩ := (membership _ _).mp output.property
      have hmax : size + 1 ∈ output.val := hperm.mem_iff.mpr (by simp)
      obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp hmax
      have hlength : left.length + right.length = size := by
        have := hperm.length_eq
        simp [hsplit] at this
        omega
      have hnodup : (left ++ (size + 1) :: right).Nodup := by
        rw [← hsplit]
        exact hperm.nodup_iff.mpr List.nodup_range'
      have hgreatest : ∀ value ∈ left ++ right, value < size + 1 := by
        intro value hvalue
        have hne : value ≠ size + 1 := by
          have hleft := (List.nodup_append.mp hnodup).2.2
          have hright := (List.nodup_append.mp hnodup).2.1
          rcases List.mem_append.mp hvalue with hvalue | hvalue
          · exact hleft value hvalue (size + 1) (by simp)
          · exact fun heq => (List.nodup_cons.mp hright).1 (heq ▸ hvalue)
        have hmem : value ∈ output.val := by simp [hsplit]; aesop
        have := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
        omega
      obtain ⟨hsep, hleftAvoid, hrightAvoid, hmonotone⟩ :=
        (maximum_split_binary _ _ _ hnodup hgreatest).mp
          (by simpa only [← hsplit] using And.intro h231 (And.intro h2134 h4213))
      have hrestPerm : (left ++ right).Perm (List.range' 1 size) := by
        have hperm' := List.perm_middle.symm.trans (by simpa [hsplit] using hperm)
        have hrange : (List.range' 1 (size + 1)).Perm
            ((size + 1) :: List.range' 1 size) := by
          simpa [List.range'_concat, Nat.add_comm] using
            (List.perm_append_comm (l₁ := List.range' 1 size) (l₂ := [size + 1]))
        exact (hperm'.trans hrange).cons_inv
      have hleftPerm : left.Perm (List.range' 1 left.length) := by
        apply ArcherCyclicPadovanBlocks.low_block_perm_initial 1 left right
        · simpa [hlength] using hrestPerm
        · exact hsep
      have hrightPerm : right.Perm (List.range' (left.length + 1) right.length) := by
        have hrange := List.range'_append_1 (s := 1) (m := left.length)
          (n := right.length)
        have hfull := hleftPerm.symm.append_right right |>.trans hrestPerm
        have : (List.range' 1 left.length ++ right).Perm
            (List.range' 1 left.length ++ List.range' (left.length + 1) right.length) := by
          simpa [← hlength, ← hrange, Nat.add_comm] using hfull
        exact (List.perm_append_left_iff _).mp this
      let parent := right.map (fun value => value - left.length)
      have hparentPerm : parent.Perm (List.range' 1 right.length) := by
        simpa [parent, List.map_sub_range' (by omega : left.length ≤ left.length + 1)]
          using hrightPerm.map (fun value => value - left.length)
      have hrecover : parent.map (left.length + ·) = right := by
        dsimp [parent]
        rw [List.map_map]
        calc
          right.map ((left.length + ·) ∘ (fun value => value - left.length)) =
              right.map id := by
            apply List.map_congr_left
            intro value hvalue
            have := List.mem_range'.mp (hrightPerm.mem_iff.mp hvalue)
            simp
            omega
          _ = right := List.map_id right
      have hparent : parent ∈ binary (size - left.length) := by
        apply (binaryMember _ _).mpr
        refine ⟨by simpa [show size - left.length = right.length by omega] using hparentPerm,
          ?_, ?_⟩
        · intro hocc
          apply hrightAvoid.1
          rw [← hrecover]
          exact (shift _ _ _ (by simp)).mpr hocc
        · intro hocc
          apply hrightAvoid.2
          rw [← hrecover]
          exact (shift _ _ _ (by simp)).mpr hocc
      have hleft : left ∈ binary left.length := (binaryMember _ _).mpr
        ⟨hleftPerm, hleftAvoid⟩
      have hpair : (left, parent) ∈ slices left.length := by
        rcases hmonotone with hi | hd
        · left
          refine ⟨?_, hparent⟩
          exact Set.mem_singleton_iff.mpr (hleftPerm.eq_of_pairwise' hi
            (List.pairwise_lt_range' _ (by omega)))
        · right
          refine ⟨hleft, ?_⟩
          apply Set.mem_singleton_iff.mpr
          have heq : right = (List.range' (left.length + 1) right.length).reverse := by
            exact (hrightPerm.trans (List.reverse_perm _).symm).eq_of_pairwise' hd
              (List.pairwise_reverse.mpr (List.pairwise_lt_range' _ (by omega)))
          have hmap := congrArg (List.map (fun value => value - left.length)) heq
          change parent = (List.range' 1 (size - left.length)).reverse
          calc
            parent = ((List.range' (left.length + 1) right.length).reverse).map
                (fun value => value - left.length) := hmap
            _ = (List.range' 1 (size - left.length)).reverse := by
              rw [List.map_reverse, List.map_sub_range' (by omega)]
              congr 2 <;> omega
      refine ⟨⟨⟨left.length, by omega⟩, ⟨(left, parent), hpair⟩⟩, Subtype.ext ?_⟩
      change assemble left.length (left, parent) = output.val
      simp [assemble, hrecover, hsplit]
    have sliceCard (cut : ℕ) : (slices cut).ncard + 1 =
        (binary cut).ncard + (binary (size - cut)).ncard := by
      have hinter : ({List.range' 1 cut} ×ˢ binary (size - cut)) ∩
          (binary cut ×ˢ {(List.range' 1 (size - cut)).reverse}) =
          {(List.range' 1 cut, (List.range' 1 (size - cut)).reverse)} := by
        ext pair
        rcases pair with ⟨low, high⟩
        simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨hl, _⟩, ⟨_, hr⟩⟩
          exact ⟨hl, hr⟩
        · rintro ⟨hl, hr⟩
          exact ⟨⟨hl, hr ▸ (canonical _).2⟩, ⟨hl ▸ (canonical _).1, hr⟩⟩
      have hcount := Set.ncard_union_add_ncard_inter
        ({List.range' 1 cut} ×ˢ binary (size - cut))
        (binary cut ×ˢ {(List.range' 1 (size - cut)).reverse})
        ((Set.finite_singleton _).prod (finite_binary _))
        ((finite_binary _).prod (Set.finite_singleton _))
      simpa only [hinter, Set.ncard_singleton, Set.ncard_prod, one_mul, mul_one,
        Nat.add_comm] using hcount
    have hcard := Nat.card_congr (Equiv.ofBijective emit ⟨emitInjective, emitSurjective⟩)
    rw [Nat.card_sigma, Nat.card_coe_set_eq] at hcard
    have hsum : (words (size + 1)).ncard + (size + 1) =
        ∑ index : Fin (size + 1), ((slices index.val).ncard + 1) := by
      rw [Finset.sum_add_distrib]
      simpa only [Nat.card_coe_set_eq, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one] using congrArg (· + (size + 1)) hcard.symm
    rw [hsum]
    simp only [sliceCard, Finset.sum_add_distrib]
    have hreverse : ∑ index : Fin (size + 1), (binary (size - index.val)).ncard =
        ∑ index : Fin (size + 1), (binary index.val).ncard := by
      simpa [Fin.rev, Nat.add_sub_add_right] using
        (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (size + 1)))
          (fun index : Fin (size + 1) => (binary index.val).ncard))
    rw [hreverse, sum_binary, pow_succ]
    omega
  cases n with
  | zero =>
    have hzero : words 0 = {[]} := by
      ext word
      rw [membership]
      constructor
      · rintro ⟨hperm, _⟩
        have : word = [] := by simpa using hperm
        simp [this]
      · intro hword
        have : word = [] := by simpa using hword
        subst word
        refine ⟨List.Perm.refl _, ?_, ?_, ?_⟩
        all_goals
          rintro ⟨witness, _, _, hsub, _⟩
          have := hsub.length_le
          simp at this
    change (words 0).ncard = 2 ^ 0 - 0
    simp [hzero]
  | succ size =>
    have := enumeration size
    change (words (size + 1)).ncard = 2 ^ (size + 1) - (size + 1)
    omega

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLinear
