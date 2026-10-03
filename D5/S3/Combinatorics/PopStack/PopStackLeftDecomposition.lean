/- GID: D5/S3/Combinatorics/PopStack/PopStackLeftDecomposition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackLeftDecomposition
   mirror-E: none(waiver:first-entry-two-decomposition)
   anchors: []
   utility: none
   digest: The first-entry-two family splits into simple predecessors and minimum inflations. -/

import D5.S3.Combinatorics.PopStack.PopStackLeft
import D5.S3.Combinatorics.PopStack.PopStackReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackLeftDecomposition

open PopStackDefs PopStackInflation PopStackReconstruction

theorem prepend_two_decomposition (permutation : List ℕ)
    (hperm : permutation.Perm (List.range' 1 permutation.length))
    (hlength : 3 ≤ permutation.length) (hminimum : permutation.getD 1 0 = 1) :
    (IsSimple (2 :: permutation.map (fun entry => if entry = 1 then 1 else entry + 1)) ↔
      (∀ start count lower, 2 ≤ count → count < permutation.length →
        start + count ≤ permutation.length →
        ((permutation.drop start).take count).Perm (List.range' lower count) →
        start = 1 ∧ count = 2 ∧ lower = 1)) ∧
    ((InC (2 :: permutation.map (fun entry => if entry = 1 then 1 else entry + 1)) ∧
      IsSimple (2 :: permutation.map (fun entry => if entry = 1 then 1 else entry + 1))) ↔
      Xor (InC permutation ∧ IsSimple permutation)
        (∃! skeleton : List ℕ, skeleton.Perm (List.range' 1 skeleton.length) ∧
          InC skeleton ∧ IsSimple skeleton ∧ skeleton.getD 1 0 = 1 ∧
          (skeleton.length = 2 ∨ 4 ≤ skeleton.length) ∧
          skeleton.length + 1 = permutation.length ∧
          permutation = inflate skeleton 1 [1, 2])) := by
  classical
  have hcriterion :
      IsSimple (2 :: permutation.map (fun entry => if entry = 1 then 1 else entry + 1)) ↔
        (∀ start count lower, 2 ≤ count → count < permutation.length →
          start + count ≤ permutation.length →
          ((permutation.drop start).take count).Perm (List.range' lower count) →
          start = 1 ∧ count = 2 ∧ lower = 1) := by
    let shift := fun entry : ℕ => if entry = 1 then 1 else entry + 1
    let down := fun entry : ℕ => if entry = 1 then 1 else entry - 1
    let expanded := 2 :: permutation.map shift
    change IsSimple expanded ↔ _
    have hexpandedLength : expanded.length = permutation.length + 1 := by simp [expanded]
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hpositive : ∀ entry ∈ permutation, 1 ≤ entry := by
      intro entry hentry
      have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hentry)
      omega
    have hinverse : ∀ entry, 1 ≤ entry → down (shift entry) = entry := by
      intro entry hentry
      dsimp [down, shift]
      split_ifs <;> omega
    have hmissing : 2 ∉ permutation.map shift := by
      intro hmem
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
      have hh := hpositive entry hentry
      dsimp [shift] at heq
      split_ifs at heq <;> omega
    have hminGet : permutation[1]? = some 1 := by
      rw [List.getElem?_eq_getElem (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
      exact congrArg some hminimum
    have hdrop : permutation.drop 1 = 1 :: permutation.drop 2 := by
      have hh := List.drop_eq_getElem?_toList_append (l := permutation) (i := 1)
      simpa only [hminGet, Option.toList_some, List.singleton_append] using hh
    have hmapInverse : ∀ selected : List ℕ, selected.Sublist permutation →
        (selected.map shift).map down = selected := by
      intro selected hselected
      rw [List.map_map]
      calc
        selected.map (down ∘ shift) = selected.map id := by
          apply List.map_congr_left
          intro entry hentry
          exact hinverse entry (hpositive entry (hselected.subset hentry))
        _ = selected := List.map_id _
    have hrangeShift : ∀ lower count, 2 ≤ lower →
        (List.range' lower count).map shift = List.range' (lower + 1) count := by
      intro lower count hlow
      simp only [List.range'_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro offset _
      dsimp [Function.comp_def, shift]
      rw [if_neg (by omega)]
      omega
    have hrangeDown : ∀ lower count, 3 ≤ lower →
        (List.range' lower count).map down = List.range' (lower - 1) count := by
      intro lower count hlow
      simp only [List.range'_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro offset _
      dsimp [Function.comp_def, down]
      rw [if_neg (by omega)]
      omega
    have hbottomShift : ∀ count, 1 ≤ count →
        (List.range' 1 count).map shift = 1 :: List.range' 3 (count - 1) := by
      intro count hcount
      rw [show count = (count - 1) + 1 by omega, List.range'_succ,
        List.map_cons, hrangeShift 2 _ (by omega)]
      simp [shift]
    have hbottomDown : ∀ count, 1 ≤ count →
        (1 :: List.range' 3 (count - 1)).map down = List.range' 1 count := by
      intro count hcount
      rw [List.map_cons, hrangeDown 3 _ (by omega)]
      simp only [down, ↓reduceIte, Nat.reduceSub]
      rw [show count = (count - 1) + 1 by omega, List.range'_succ]
      simp only [Nat.add_sub_cancel, Nat.reduceAdd]
    have hprefixRange : ∀ (selected : List ℕ) count,
        selected.Sublist permutation → 1 ≤ count →
        ((2 :: selected.map shift).Perm (List.range' 1 (count + 1)) ↔
          selected.Perm (List.range' 1 count)) := by
      intro selected count hselected hcount
      have hrange : List.range' 1 (count + 1) = 1 :: 2 :: List.range' 3 (count - 1) := by
        rw [List.range'_succ, show count = (count - 1) + 1 by omega, List.range'_succ]
        simp only [Nat.reduceAdd, Nat.add_sub_cancel]
      rw [hrange]
      constructor
      · intro hh
        have ht : (selected.map shift).Perm (1 :: List.range' 3 (count - 1)) :=
          (hh.trans (List.Perm.swap 2 1 _)).cons_inv
        simpa only [hmapInverse selected hselected, hbottomDown count hcount] using ht.map down
      · intro hh
        have ht := hh.map shift
        rw [hbottomShift count hcount] at ht
        exact (ht.cons 2).trans (List.Perm.swap 1 2 _)
    have hsegment : ∀ start count,
        ((expanded.drop (start + 1)).take count) =
          ((permutation.drop start).take count).map shift := by
      intro start count
      simp [expanded, List.drop_succ_cons, List.map_drop, List.map_take]
    have hprefix : ∀ count, 1 ≤ count →
        expanded.take count = 2 :: (permutation.take (count - 1)).map shift := by
      intro count hcount
      rw [show count = (count - 1) + 1 by omega]
      simp [expanded, List.map_take]
    have hfirstNe : permutation.getD 0 0 ≠ 1 := by
      intro heq
      have hfirstGet : permutation[0]? = some 1 := by
        rw [List.getElem?_eq_getElem (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
        exact congrArg some heq
      have hh := (List.getElem?_inj (by omega) hnodup).mp (hfirstGet.trans hminGet.symm)
      omega
    constructor
    · intro hsimple start count lower hcount hproper hbound hinterval
      let selected := (permutation.drop start).take count
      have hselected : selected.Sublist permutation :=
        (List.take_sublist _ _).trans (List.drop_sublist _ _)
      have hlow : 1 ≤ lower := by
        have hm : lower ∈ selected :=
          hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
        exact hpositive lower (hselected.subset hm)
      have hlower : lower = 1 := by
        by_contra hne
        have hh := hinterval.map shift
        rw [hrangeShift lower count (by omega)] at hh
        apply hsimple (start + 1) count (lower + 1) hcount (by omega) (by omega)
        rw [hsegment]
        exact hh
      subst lower
      have hone : 1 ∈ selected :=
        hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
      obtain ⟨offset, hoffset⟩ := List.mem_iff_getElem?.mp hone
      have hoffsetBound : offset < count := by
        have hb := (List.getElem?_eq_some_iff.mp hoffset).1
        have hs : selected.length = count := by
          simp only [selected, List.length_take, List.length_drop]
          omega
        omega
      have hget : permutation[start + offset]? = some 1 := by
        simpa only [selected, List.getElem?_take_of_lt hoffsetBound, List.getElem?_drop]
          using hoffset
      have hposition : start + offset = 1 :=
        (List.getElem?_inj (by omega) hnodup).mp (hget.trans hminGet.symm)
      have hstart : start = 1 := by
        by_contra hne
        have hzero : start = 0 := by omega
        subst start
        have ht : (2 :: (permutation.take count).map shift).Perm
            (List.range' 1 (count + 1)) :=
          (hprefixRange (permutation.take count) count (List.take_sublist _ _) (by omega)).mpr
            (by simpa only [List.drop_zero] using hinterval)
        apply hsimple 0 (count + 1) 1 (by omega) (by omega) (by omega)
        simpa only [List.drop_zero, hprefix (count + 1) (by omega), Nat.add_sub_cancel] using ht
      subst start
      have hcountTwo : count = 2 := by
        by_contra hne
        have htail : ((permutation.drop 2).take (count - 1)).Perm
            (List.range' 2 (count - 1)) := by
          rw [hdrop, show count = (count - 1) + 1 by omega, List.take_succ_cons,
            List.range'_succ] at hinterval
          exact hinterval.cons_inv
        have ht := htail.map shift
        rw [hrangeShift 2 _ (by omega)] at ht
        apply hsimple 3 (count - 1) 3 (by omega) (by omega) (by omega)
        simpa only [show 3 = 2 + 1 by omega, hsegment] using ht
      exact ⟨rfl, hcountTwo, rfl⟩
    · intro hrestriction start count lower hcount hproper hbound hinterval
      have hpositiveExpanded : ∀ entry ∈ expanded, 1 ≤ entry := by
        intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | hentry
        · omega
        · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hentry
          have hb := hpositive old hold
          dsimp [shift]
          split <;> omega
      have hlow : 1 ≤ lower := by
        have hm : lower ∈ (expanded.drop start).take count :=
          hinterval.mem_iff.mpr (List.mem_range'_1.mpr (by omega))
        exact hpositiveExpanded lower
          (((List.take_sublist _ _).trans (List.drop_sublist _ _)).subset hm)
      by_cases hstart : start = 0
      · subst start
        rw [List.drop_zero, hprefix count (by omega)] at hinterval
        by_cases htwo : count = 2
        · subst count
          have hqfirst : permutation.take 1 = [permutation.getD 0 0] := by
            have hh := List.take_succ_eq_append_getElem (l := permutation) (i := 0) (by omega)
            rw [List.getD_eq_getElem permutation 0 (by omega)]
            simpa only [List.take_zero, List.nil_append, Nat.zero_add] using hh
          rw [hqfirst] at hinterval
          have hentry : shift (permutation.getD 0 0) = 3 := by
            simp only [List.map_cons, List.map_nil] at hinterval
            have hfirstPos := hpositive (permutation.getD 0 0)
              (by rw [List.getD_eq_getElem _ 0 (by omega)]; exact List.getElem_mem (by omega))
            have htwoBounds := List.mem_range'_1.mp
              (hinterval.mem_iff.mp (by simp : 2 ∈ [2, shift (permutation.getD 0 0)]))
            have hentryBounds := List.mem_range'_1.mp
              (hinterval.mem_iff.mp
                (by simp : shift (permutation.getD 0 0) ∈ [2, shift (permutation.getD 0 0)]))
            dsimp [shift] at hentryBounds ⊢
            rw [if_neg hfirstNe] at hentryBounds ⊢
            omega
          have hfirstTwo : permutation.getD 0 0 = 2 := by
            dsimp [shift] at hentry
            split_ifs at hentry <;> omega
          have hpair : (permutation.take 2).Perm (List.range' 1 2) := by
            have hh := List.take_succ_eq_append_getElem (l := permutation) (i := 1) (by omega)
            rw [hh, hqfirst, ← List.getD_eq_getElem _ 0 (by omega), hminimum, hfirstTwo]
            simpa [List.range'_succ] using List.Perm.swap 1 2 []
          have hh := hrestriction 0 2 1 (by omega) (by omega) (by omega)
            (by simpa only [List.drop_zero] using hpair)
          omega
        · have hone : 1 ∈ 2 :: (permutation.take (count - 1)).map shift := by
            have hget : (permutation.take (count - 1))[1]? = some 1 := by
              rw [List.getElem?_take_of_lt (by omega), hminGet]
            have hm := List.mem_of_getElem? hget
            have hh : shift 1 = 1 := by simp [shift]
            exact List.mem_cons_of_mem 2 (hh ▸ List.mem_map_of_mem hm)
          have hbottom : lower = 1 := by
            have hh := List.mem_range'_1.mp (hinterval.mem_iff.mp hone)
            omega
          subst lower
          have hqinterval := (hprefixRange (permutation.take (count - 1)) (count - 1)
            (List.take_sublist _ _) (by omega)).mp
              (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ count)] using hinterval)
          have hh := hrestriction 0 (count - 1) 1 (by omega) (by omega) (by omega)
            (by simpa only [List.drop_zero] using hqinterval)
          omega
      · obtain ⟨index, hindex⟩ := Nat.exists_eq_add_of_le (show 1 ≤ start by omega)
        have hstartEq : start = index + 1 := by omega
        rw [hstartEq, hsegment] at hinterval
        have hnoTwo : 2 ∉ ((permutation.drop index).take count).map shift := by
          intro hmem
          apply hmissing
          exact (List.Sublist.map shift
            ((List.take_sublist _ _).trans (List.drop_sublist _ _))).subset hmem
        have hbottom : 3 ≤ lower := by
          by_contra hn
          have hm : 2 ∈ List.range' lower count := List.mem_range'_1.mpr (by omega)
          exact hnoTwo (hinterval.mem_iff.mpr hm)
        have hqinterval : ((permutation.drop index).take count).Perm
            (List.range' (lower - 1) count) := by
          have hh := hinterval.map down
          rw [hmapInverse _ ((List.take_sublist _ _).trans (List.drop_sublist _ _)),
            hrangeDown lower count hbottom] at hh
          exact hh
        by_cases hwhole : count = permutation.length
        · have hzero : index = 0 := by omega
          subst index
          subst count
          simp only [List.drop_zero, List.take_length] at hqinterval
          have hone : 1 ∈ permutation := List.mem_of_getElem? hminGet
          have hh := List.mem_range'_1.mp (hqinterval.mem_iff.mp hone)
          omega
        · have hh := hrestriction index count (lower - 1) hcount (by omega) (by omega)
            hqinterval
          omega
  refine ⟨hcriterion, ?_⟩
  rw [hcriterion]
  have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hpositive : ∀ entry ∈ permutation, 1 ≤ entry := by
    intro entry hentry
    exact (List.mem_range'_1.mp (hperm.mem_iff.mp hentry)).1
  have hminGet : permutation[1]? = some 1 := by
    rw [List.getElem?_eq_getElem (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
    exact congrArg some hminimum
  have hdrop : permutation.drop 1 = 1 :: permutation.drop 2 := by
    have hh := List.drop_eq_getElem?_toList_append (l := permutation) (i := 1)
    simpa only [hminGet, Option.toList_some, List.singleton_append] using hh
  let down := fun entry : ℕ => if entry = 1 then 1 else entry - 1
  have hrecovery : ∀ skeleton : List ℕ,
      skeleton.Perm (List.range' 1 skeleton.length) → skeleton.getD 1 0 = 1 →
      2 ≤ skeleton.length → ((inflate skeleton 1 [1, 2]).eraseIdx 2).map down = skeleton := by
    intro skeleton hskeletonPerm hskeletonMin hskeletonLength
    have hpositive : ∀ entry ∈ skeleton, 1 ≤ entry := by
      intro entry hentry
      exact (List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp hentry)).1
    cases skeleton with
    | nil => simp at hskeletonLength
    | cons first rest =>
      cases rest with
      | nil => simp at hskeletonLength
      | cons second tail =>
        have hsecond : second = 1 := by simpa using hskeletonMin
        subst second
        let shift := fun entry : ℕ => if 1 < entry then entry + 1 else entry
        have hinverse : ∀ entry, 1 ≤ entry → down (shift entry) = entry := by
          intro entry hentry
          dsimp [down, shift]
          split_ifs <;> omega
        have hfirstPositive : 1 ≤ first := hpositive first (by simp)
        have htailInverse : (tail.map shift).map down = tail := by
          rw [List.map_map]
          calc
            tail.map (down ∘ shift) = tail.map id := by
              apply List.map_congr_left
              intro entry hentry
              exact hinverse entry (hpositive entry (by simp [hentry]))
            _ = tail := List.map_id _
        have hinflate : inflate (first :: 1 :: tail) 1 [1, 2] =
            shift first :: 1 :: 2 :: tail.map shift := by
          simp [inflate, shift]
        rw [hinflate]
        simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, List.map_cons,
          hinverse first hfirstPositive, htailInverse]
        simp [down]
  have hinflatedNonsimple : ∀ skeleton : List ℕ, skeleton.getD 1 0 = 1 →
      2 ≤ skeleton.length → ¬ IsSimple (inflate skeleton 1 [1, 2]) := by
    intro skeleton hminimum hlength hsimple
    cases skeleton with
    | nil => simp at hlength
    | cons first rest =>
      cases rest with
      | nil => simp at hlength
      | cons second tail =>
        have hsecond : second = 1 := by simpa using hminimum
        subst second
        have hshape : inflate (first :: 1 :: tail) 1 [1, 2] =
            (if 1 < first then first + 1 else first) :: 1 :: 2 ::
              tail.map (fun entry => if 1 < entry then entry + 1 else entry) := by
          simp [inflate]
        apply hsimple 1 2 1 (by decide) (by simp [hshape]) (by simp [hshape])
        simp only [hshape, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
          List.take_zero]
        exact List.Perm.refl _
  have hthreeImpossible : ∀ list : List ℕ, list.Perm (List.range' 1 list.length) →
      IsSimple list → list.length ≠ 3 := by
    intro list hlistPerm hsimple hthree
    obtain ⟨first, second, third, hshape⟩ := List.length_eq_three.mp hthree
    have hpermThree : [first, second, third].Perm (List.range' 1 3) := by
      simpa only [hshape, List.length_cons, List.length_nil, Nat.reduceAdd] using hlistPerm
    have hentries : ∀ entry ∈ [first, second, third],
        entry = 1 ∨ entry = 2 ∨ entry = 3 := by
      intro entry hentry
      have hh := hpermThree.mem_iff.mp hentry
      simpa only [List.range'_succ, List.range'_zero, List.mem_cons, List.not_mem_nil,
        or_false, Nat.reduceAdd] using hh
    have hfirst := hentries first (by simp)
    have hsecond := hentries second (by simp)
    have hthird := hentries third (by simp)
    have hnd := hpermThree.nodup_iff.mpr (List.nodup_range' _)
    rw [hshape] at hsimple
    rcases hfirst with rfl | rfl | rfl <;> rcases hsecond with rfl | rfl | rfl <;>
      rcases hthird with rfl | rfl | rfl
    all_goals try simp at hnd
    all_goals first
      | exact hsimple 0 2 1 (by decide) (by decide) (by decide) (by decide)
      | exact hsimple 0 2 2 (by decide) (by decide) (by decide) (by decide)
      | exact hsimple 1 2 1 (by decide) (by decide) (by decide) (by decide)
      | exact hsimple 1 2 2 (by decide) (by decide) (by decide) (by decide)
  constructor
  · intro ⟨hexpandedClass, hrestriction⟩
    have hclass := (PopStackLeft.prepend_two_inC permutation hnodup hpositive hminimum).mp
      hexpandedClass
    by_cases hsimple : IsSimple permutation
    · refine Or.inl ⟨⟨hclass, hsimple⟩, ?_⟩
      rintro ⟨skeleton, ⟨_, _, _, hmin, hsizes, _, hinflate⟩, _⟩
      rw [hinflate] at hsimple
      exact hinflatedNonsimple skeleton hmin (by omega) hsimple
    refine Or.inr ⟨?_, fun hh => hsimple hh.2⟩
    obtain ⟨start, count, lower, hcount, hproper, hbound, hinterval⟩ := by
      simpa only [IsSimple, not_forall, not_not, Classical.not_imp] using hsimple
    obtain ⟨rfl, rfl, rfl⟩ := hrestriction start count lower hcount hproper hbound hinterval
    have hthird : permutation.getD 2 0 = 2 := by
      rw [hdrop] at hinterval
      have htail : ((permutation.drop 2).take 1).Perm [2] := by
        simpa only [List.take_succ_cons, List.range'_succ, List.range'_zero, Nat.reduceAdd]
          using hinterval.cons_inv
      have ht : (permutation.drop 2).take 1 = [2] := List.perm_singleton.mp htail
      have hg : ((permutation.drop 2).take 1)[0]? = some 2 := by simp [ht]
      have hg' : permutation[2]? = some 2 := by
        simpa only [List.getElem?_take_of_lt (by omega : 0 < 1), List.getElem?_drop,
          Nat.add_zero] using hg
      simp only [List.getD_eq_getElem?_getD, hg', Option.getD_some]
    have hvalues : (permutation.drop 1).take 2 = [1, 2] := by
      rw [hdrop]
      simp only [List.take_succ_cons]
      have hget : permutation[2]? = some 2 := by
        rw [List.getElem?_eq_getElem (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
        exact congrArg some hthird
      have hh := List.take_one (l := permutation.drop 2)
      simpa only [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero, hget,
        Option.toList_some] using
        congrArg (List.cons 1) hh
    let before := permutation.take 1
    let after := permutation.drop 3
    have hbeforeLength : before.length = 1 := by simp [before]; omega
    have hwhole : before ++ [1, 2] ++ after = permutation := by
      rw [← hvalues]
      dsimp only [before, after]
      have hh := List.take_append_drop 2 (permutation.drop 1)
      rw [List.drop_drop] at hh
      have hh' := List.take_append_drop 1 permutation
      rw [← hh] at hh'
      simpa only [List.append_assoc, Nat.reduceAdd] using hh'
    obtain ⟨skeleton, block, hskeletonPerm, hblockPerm, hskeletonLength,
      hblockLength, hinflate, hrecover⟩ := reconstruct_interval before [1, 2] after 1
        (by rw [hwhole]; exact hperm) (by decide) (by decide)
    have hblockSize : block.length = 2 := by simpa using hblockLength
    have hsize : skeleton.length + 1 = permutation.length := by
      simp only [before, after, List.length_take, List.length_drop] at hskeletonLength
      omega
    have hskeletonPositive : ∀ entry ∈ skeleton, 1 ≤ entry := by
      intro entry hentry
      exact (List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp hentry)).1
    have hindex : 1 < skeleton.length := by omega
    let pivot := skeleton.getD 1 0
    have hpivotPositive : 1 ≤ pivot := by
      apply hskeletonPositive
      dsimp only [pivot]
      rw [List.getD_eq_getElem _ _ hindex]
      exact List.getElem_mem hindex
    have hblockBounds : ∀ entry ∈ block, 1 ≤ entry ∧ entry ≤ 2 := by
      intro entry hentry
      have hh := List.mem_range'_1.mp (hblockPerm.mem_iff.mp hentry)
      omega
    have hinflate' : inflate skeleton 1 block = permutation := by
      simpa only [hbeforeLength, hwhole] using hinflate
    have hscaled : block.map (fun entry => pivot + entry - 1) = [1, 2] := by
      have hh : ((inflate skeleton 1 block).drop 1).take 2 =
          block.map (fun entry => pivot + entry - 1) := by
        let shift := fun entry => if pivot < entry then entry + block.length - 1 else entry
        have ht : (skeleton.take 1).length = 1 := by simp; omega
        dsimp only [inflate]
        change (((skeleton.take 1).map shift ++
          block.map (fun entry => pivot + entry - 1) ++ (skeleton.drop 2).map shift).drop
          1).take 2 = _
        rw [List.append_assoc, List.drop_append,
          List.drop_eq_nil_iff.mpr (by simp only [List.length_map, ht]; omega),
          List.nil_append]
        simp only [List.length_map, ht, Nat.sub_self, List.drop_zero]
        rw [List.take_append_of_le_length (by simp [hblockSize])]
        exact List.take_of_length_le (by simp [hblockSize])
      rw [hinflate', hvalues] at hh
      exact hh.symm
    have hpivot : pivot = 1 := by
      obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp
        (by rw [hscaled]; simp : 1 ∈ block.map (fun entry => pivot + entry - 1))
      have hb := hblockBounds entry hentry
      omega
    have hblock : block = [1, 2] := by
      simpa only [hpivot, Nat.add_sub_cancel_left, List.map_id'] using hscaled
    obtain ⟨_, hskeletonSimple, hskeletonC⟩ := hrecover (by
      intro index size bottom hsizeTwo hsizeProper hsizeBound hinterval
      rw [hwhole] at hsizeProper hsizeBound hinterval
      obtain ⟨rfl, rfl, _⟩ := hrestriction index size bottom hsizeTwo hsizeProper
        hsizeBound hinterval
      simp [hbeforeLength])
    have hskeletonClass := hskeletonC (by rw [hwhole]; exact hclass)
    have hskeletonNotThree := hthreeImpossible skeleton hskeletonPerm hskeletonSimple
    refine ⟨skeleton, ⟨hskeletonPerm, hskeletonClass, hskeletonSimple, hpivot,
      by omega, hsize, ?_⟩, ?_⟩
    · rw [← hblock]
      exact hinflate'.symm
    · rintro alternative ⟨haltPerm, _, _, haltMin, haltSizes, _, haltInflate⟩
      have hskeletonInverse := hrecovery skeleton hskeletonPerm hpivot (by omega)
      have haltInverse := hrecovery alternative haltPerm haltMin (by omega)
      have hsame : inflate skeleton 1 [1, 2] = inflate alternative 1 [1, 2] := by
        calc
          inflate skeleton 1 [1, 2] = inflate skeleton 1 block := by rw [hblock]
          _ = permutation := hinflate'
          _ = inflate alternative 1 [1, 2] := haltInflate
      rw [hsame] at hskeletonInverse
      exact haltInverse.symm.trans hskeletonInverse
  · rintro (⟨⟨hqClass, hsimple⟩, _⟩ |
      ⟨⟨skeleton, ⟨hskeletonPerm, hskeletonC, hskeletonSimple,
      hmin, hsizeCases, hsize, hinflate⟩, _⟩, _⟩)
    · refine ⟨(PopStackLeft.prepend_two_inC permutation hnodup hpositive hminimum).mpr
        hqClass, ?_⟩
      intro start count lower hcount hproper hbound hinterval
      exact False.elim (hsimple start count lower hcount hproper hbound hinterval)
    · have hindex : 1 < skeleton.length := by omega
      have hqClass : InC permutation := by
        rw [hinflate]
        have hskeletonPositive : ∀ entry ∈ skeleton, 1 ≤ entry := by
          intro entry hentry
          exact (List.mem_range'_1.mp (hskeletonPerm.mem_iff.mp hentry)).1
        have hskeletonNodup := hskeletonPerm.nodup_iff.mpr (List.nodup_range' 1)
        cases skeleton with
        | nil => simp at hindex
        | cons first rest =>
          cases rest with
          | nil => simp at hindex
          | cons second tail =>
            have hsecond : second = 1 := by simpa using hmin
            subst second
            have hfirst : 2 ≤ first := by
              have hb := hskeletonPositive first (by simp)
              have hn : first ≠ 1 := fun heq =>
                (List.nodup_cons.mp hskeletonNodup).1 (by simp [heq])
              omega
            have htail : ∀ entry ∈ tail, 2 ≤ entry := by
              intro entry hentry
              have hb := hskeletonPositive entry (by simp [hentry])
              have hn : entry ≠ 1 := fun heq =>
                (List.nodup_cons.mp (List.nodup_cons.mp hskeletonNodup).2).1 (heq ▸ hentry)
              omega
            have hmap : tail.map (fun entry => if 1 < entry then entry + 1 else entry) =
                tail.map Nat.succ := by
              apply List.map_congr_left
              intro entry hentry
              have hb := htail entry hentry
              rw [if_pos (by omega)]
            have hshape : inflate (first :: 1 :: tail) 1 [1, 2] =
                (first + 1) :: 1 :: 2 :: tail.map Nat.succ := by
              simp [inflate, if_pos (show 1 < first by omega), hmap]
            rw [hshape]
            exact PopStackIncreasing.increasing_minimum_inflation [first] tail
              (by intro entry hentry; simp only [List.mem_singleton] at hentry;
                  exact hentry ▸ hfirst)
              htail hskeletonC
      refine ⟨(PopStackLeft.prepend_two_inC permutation hnodup hpositive hminimum).mpr
        hqClass, ?_⟩
      intro start count lower hcount hproper hbound hinterval
      rcases hsizeCases with htwo | hlarge
      · obtain ⟨first, second, hshape⟩ := List.length_eq_two.mp htwo
        have hsecond : second = 1 := by simpa [hshape] using hmin
        subst second
        have hfirst : first = 2 := by
          have hp : [first, 1].Perm (List.range' 1 2) := by
            simpa only [hshape, List.length_cons, List.length_nil, Nat.reduceAdd]
              using hskeletonPerm
          have hb := List.mem_range'_1.mp (hp.mem_iff.mp (by simp : first ∈ [first, 1]))
          have hnd := hp.nodup_iff.mpr (List.nodup_range' _)
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
            List.nodup_nil, not_false_eq_true, and_true] at hnd
          omega
        subst first
        have hpermutation : permutation = [3, 1, 2] := by
          rw [hinflate, hshape]
          simp [inflate]
        rw [hpermutation] at hproper hbound hinterval
        have hcountTwo : count = 2 := by
          simp only [List.length_cons, List.length_nil] at hproper
          omega
        subst count
        have hstartCases : start = 0 ∨ start = 1 := by
          simp only [List.length_cons, List.length_nil] at hbound
          omega
        rcases hstartCases with rfl | rfl
        · have hlowBounds := List.mem_range'_1.mp
            (hinterval.mem_iff.mp (by simp : 1 ∈ ([3, 1, 2].drop 0).take 2))
          have hhighBounds := List.mem_range'_1.mp
            (hinterval.mem_iff.mp (by simp : 3 ∈ ([3, 1, 2].drop 0).take 2))
          omega
        · have hlowBounds := List.mem_range'_1.mp
            (hinterval.mem_iff.mp (by simp : 1 ∈ ([3, 1, 2].drop 1).take 2))
          have hpositive : 1 ≤ lower := by
            have hh : lower ∈ [1, 2] := hinterval.mem_iff.mpr
              (List.mem_range'_1.mpr (by omega))
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
            omega
          exact ⟨rfl, rfl, by omega⟩
      · have hinside := (PopStackPrime.inflation_intervals skeleton [1, 2] 1
          hskeletonPerm hskeletonSimple hlarge hindex (by decide) (by decide)).1
          start count lower hcount (by rw [← hinflate]; exact hproper)
          (by rw [← hinflate]; exact hbound) (by rw [← hinflate]; exact hinterval)
        have hstart : start = 1 := by
          simp only [List.length_cons, List.length_nil] at hinside
          omega
        have hcountTwo : count = 2 := by
          simp only [List.length_cons, List.length_nil] at hinside
          omega
        subst start
        subst count
        have hvalues : (permutation.drop 1).take 2 = [1, 2] := by
          rw [hdrop]
          have hentry : permutation[2]? = some 2 := by
            rw [hinflate]
            simp [inflate, -List.getD_eq_getElem?_getD, hmin,
              List.getElem?_append_right, List.length_take,
              Nat.min_eq_left (by omega : 1 ≤ skeleton.length)]
          have hh := List.take_one (l := permutation.drop 2)
          simpa only [List.take_succ_cons, List.head?_eq_getElem?, List.getElem?_drop,
            Nat.add_zero, hentry, Option.toList_some] using congrArg (List.cons 1) hh
        rw [hvalues] at hinterval
        have hlower : lower = 1 := by
          have hb := List.mem_range'_1.mp (hinterval.mem_iff.mp (by simp : 1 ∈ [1, 2]))
          have hh : lower ∈ [1, 2] := hinterval.mem_iff.mpr
            (List.mem_range'_1.mpr (by omega))
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          omega
        exact ⟨rfl, rfl, hlower⟩

end D5.S3.Combinatorics.PopStack.PopStackLeftDecomposition
