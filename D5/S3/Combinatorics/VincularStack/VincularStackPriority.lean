/- GID: D5/S3/Combinatorics/VincularStack/VincularStackPriority
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackPriority
   mirror-E: none(waiver:maximum-insertion-counting)
   anchors: []
   utility: none
   digest: Adjacent sites persist and distinct markers follow their original output gaps. -/

import D5.S3.Combinatorics.VincularStack.VincularStackCharacterization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackPriority

open VincularStackDefs VincularStackBasic VincularStackCuts VincularStackMarkers
open VincularStackRun VincularStackSites VincularStackPrefixes
open scoped List

theorem adjacent_sites_active (front suffix : List ℕ) (maximum larger : ℕ)
    (hnodup : (front ++ suffix).Nodup)
    (hbound : ∀ value ∈ front ++ suffix, value < maximum) (hlarge : maximum < larger)
    (hactive : ¬ Contains231 (SC (front ++ maximum :: suffix))) :
    ¬ Contains231 (SC (front ++ larger :: maximum :: suffix)) ∧
      ¬ Contains231 (SC (front ++ maximum :: larger :: suffix)) := by
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  have htop : ∀ top current, ¬ ContainsV current →
      (∀ value ∈ current, value < top) → ¬ ContainsV (top :: current) := by
    intro top current hcurrent hvalues
    cases current with
    | nil =>
      rintro ⟨position, hposition, later, hlater, hgap, _⟩
      simp only [List.length_cons, List.length_nil] at hposition hlater
      omega
    | cons next current =>
      rw [push_test]
      rintro (hpattern | ⟨hascent, _⟩)
      · exact hcurrent hpattern
      · exact (not_lt_of_gt (hvalues next List.mem_cons_self)) hascent
  have hpush : ∀ entry current, ¬ ContainsV (entry :: current) →
      Push entry current = ([], entry :: current) := by
    intro entry current hlegal
    cases current with
    | nil => rfl
    | cons top current => simp only [Push, if_neg hlegal]
  have hsplit : ∀ processed unread current : List ℕ,
      Process (processed ++ unread) current =
        (snapshot processed current).1 ++ Process unread (snapshot processed current).2 := by
    intro processed
    induction processed with
    | nil => intro unread current; rfl
    | cons entry processed ih =>
      intro unread current
      simp only [List.cons_append, Process, snapshot, ih, List.append_assoc]
  have hstate : ¬ ContainsV (snapshot front []).2 ∧
      ((snapshot front []).1 ++ (snapshot front []).2).Perm front := by
    have hvalid : ∀ processed current, ¬ ContainsV current →
        ¬ ContainsV (snapshot processed current).2 := by
      intro processed
      induction processed with
      | nil => intro current hcurrent; exact hcurrent
      | cons entry processed ih =>
        intro current hcurrent
        exact ih (Push entry current).2 (push_preserves entry current hcurrent).1
    refine ⟨hvalid front [] hnil, ?_⟩
    have hconserve := (process_preserves front [] hnil).1
    have hdecomp : Process front [] = (snapshot front []).1 ++ (snapshot front []).2 := by
      simpa only [List.append_nil, Process] using hsplit front [] []
    rw [hdecomp] at hconserve
    simpa only [Process, List.append_nil] using hconserve
  have hstackbound : ∀ value ∈ (snapshot front []).2, value < maximum := by
    intro value hvalue
    exact hbound value (List.mem_append_left _
      (hstate.2.mem_iff.mp (List.mem_append_right _ hvalue)))
  have hmaxlegal := htop maximum (snapshot front []).2 hstate.1 hstackbound
  have hdoublelegal := htop larger (maximum :: (snapshot front []).2) hmaxlegal (by
    intro value hvalue
    rcases List.mem_cons.mp hvalue with rfl | hvalue
    · exact hlarge
    · exact lt_trans (hstackbound value hvalue) hlarge)
  have houtputPerm : (SC (front ++ suffix)).Perm (front ++ suffix) := by
    simpa [SC] using (process_preserves (front ++ suffix) [] hnil).1
  have hmarker := (maximum_insertion front suffix maximum hbound).1
  let left := (SC (front ++ suffix)).take (outputGap front suffix)
  let right := (SC (front ++ suffix)).drop (outputGap front suffix)
  have houtsplit : left ++ right = SC (front ++ suffix) := List.take_append_drop _ _
  have houtputNodup : (left ++ right).Nodup := by
    rw [houtsplit]
    exact houtputPerm.nodup_iff.mpr hnodup
  have houtputBound : ∀ value ∈ left ++ right, value < maximum := by
    rw [houtsplit]
    exact fun value hvalue => hbound value (houtputPerm.mem_iff.mp hvalue)
  have hbase : ¬ Contains231 (left ++ maximum :: right) := by
    simpa only [left, right, hmarker] using hactive
  have hcut := ((maximum_cut left right maximum houtputNodup houtputBound).mp hbase).2
  have hnewNodup : (left ++ maximum :: right).Nodup := by
    have hnot : maximum ∉ left ++ right := by
      intro hmem
      exact (lt_irrefl maximum) (houtputBound maximum hmem)
    obtain ⟨hl, hr, hdisjoint⟩ := List.nodup_append.mp houtputNodup
    apply List.nodup_append.mpr
    refine ⟨hl, List.nodup_cons.mpr ⟨fun hm => hnot (List.mem_append_right _ hm), hr⟩, ?_⟩
    intro value hvalue other hother heq
    rcases List.mem_cons.mp hother with rfl | hother
    · exact hnot (heq ▸ List.mem_append_left _ hvalue)
    · exact hdisjoint value hvalue other hother heq
  have hnewBound : ∀ value ∈ left ++ maximum :: right, value < larger := by
    intro value hvalue
    rcases List.mem_append.mp hvalue with hleft | hrest
    · exact lt_trans (houtputBound value (List.mem_append_left _ hleft)) hlarge
    · rcases List.mem_cons.mp hrest with rfl | hright
      · exact hlarge
      · exact lt_trans (houtputBound value (List.mem_append_right _ hright)) hlarge
  have hdoubleAvoid : ¬ Contains231 (left ++ larger :: maximum :: right) := by
    apply (maximum_cut left (maximum :: right) larger hnewNodup hnewBound).mpr
    refine ⟨hbase, ?_⟩
    simp only [separatingCut, List.take_append_length, List.drop_append_length] at hcut ⊢
    intro value hvalue other hother
    rcases List.mem_cons.mp hother with rfl | hother
    · exact houtputBound value (List.mem_append_left _ hvalue)
    · exact hcut value hvalue other hother
  have hdoubleRun : ∀ unread current, ¬ ContainsV current →
      (∀ value ∈ current ++ unread, value < maximum) →
      Process unread (larger :: maximum :: current) =
        match unread with
        | [] => larger :: maximum :: current
        | entry :: rest =>
          if ∃ lower ∈ current, lower < entry
          then larger :: maximum :: Process unread current
          else Process unread [] ++ larger :: maximum :: current := by
    intro unread current hcurrent hvalues
    cases unread with
    | nil => rfl
    | cons entry rest =>
      have hentry := hvalues entry (by simp)
      have hcurrentbound : ∀ value ∈ current, value < maximum := by
        intro value hvalue
        exact hvalues value (List.mem_append_left _ hvalue)
      have hone := htop maximum current hcurrent hcurrentbound
      have htwo := htop larger (maximum :: current) hone (by
        intro value hvalue
        rcases List.mem_cons.mp hvalue with rfl | hvalue
        · exact hlarge
        · exact lt_trans (hcurrentbound value hvalue) hlarge)
      by_cases htemporary : ∃ lower ∈ current, lower < entry
      · have hpopOne : ContainsV (entry :: maximum :: current) :=
          (push_test entry maximum current).mpr (Or.inr ⟨hentry, htemporary⟩)
        have hpopTwo : ContainsV (entry :: larger :: maximum :: current) := by
          apply (push_test entry larger (maximum :: current)).mpr
          exact Or.inr ⟨lt_trans hentry hlarge, by
            obtain ⟨lower, hlower, hless⟩ := htemporary
            exact ⟨lower, List.mem_cons_of_mem maximum hlower, hless⟩⟩
        simp only [htemporary, if_true, Process, Push, if_pos hpopOne,
          if_pos hpopTwo, List.cons_append]
      · have hlegal : ¬ ContainsV (entry :: larger :: maximum :: current) := by
          rw [push_test]
          rintro (hpattern | ⟨_, lower, hlower, hless⟩)
          · exact htwo hpattern
          · rcases List.mem_cons.mp hlower with rfl | hlower
            · omega
            · exact htemporary ⟨lower, hlower, hless⟩
        have hprotect := protected_suffix rest [entry] (larger :: maximum :: current)
          entry hlegal (by simp) (by simp) (by
            intro value hvalue
            rcases List.mem_cons.mp hvalue with rfl | hvalue
            · omega
            · rcases List.mem_cons.mp hvalue with rfl | hvalue
              · omega
              · exact Nat.le_of_not_gt (fun hlt => htemporary ⟨value, hvalue, hlt⟩))
        simp only [htemporary, if_false, Process, hpush entry _ hlegal, List.nil_append]
        simpa only [Process, Push, List.nil_append, List.cons_append] using hprotect
  have hdoubleSC : SC (front ++ maximum :: larger :: suffix) =
      (snapshot front []).1 ++
        Process suffix (larger :: maximum :: (snapshot front []).2) := by
    rw [SC, hsplit, Process, hpush maximum _ hmaxlegal, Process,
      hpush larger _ hdoublelegal]
    simp
  have hdoubleOutput : SC (front ++ maximum :: larger :: suffix) =
      left ++ larger :: maximum :: right := by
    have hvalues : ∀ value ∈ (snapshot front []).2 ++ suffix, value < maximum := by
      intro value hvalue
      rcases List.mem_append.mp hvalue with hstack | hsuffix
      · exact hstackbound value hstack
      · exact hbound value (List.mem_append_right _ hsuffix)
    have hrun := hdoubleRun suffix (snapshot front []).2 hstate.1 hvalues
    have horiginal : SC (front ++ suffix) =
        (snapshot front []).1 ++ Process suffix (snapshot front []).2 := hsplit front suffix []
    have hlength : (SC suffix).length = suffix.length := by
      simpa [SC] using (process_preserves suffix [] hnil).1.length_eq
    by_cases hfront : front = []
    · subst front
      cases suffix with
      | nil => rfl
      | cons entry rest =>
        rw [hdoubleSC]
        simp only [left, right, outputGap, if_true, List.nil_append, ← hlength,
          List.take_length, List.drop_length, snapshot]
        simpa only [snapshot, List.not_mem_nil, false_and, exists_false, if_false, SC]
          using hrun
    · cases suffix with
      | nil =>
        have horig : SC front = (snapshot front []).1 ++ (snapshot front []).2 := by
          simpa only [List.append_nil, Process] using horiginal
        rw [hdoubleSC]
        simp [left, right, outputGap, hfront, horig, Process]
      | cons entry rest =>
        by_cases htemporary : ∃ lower ∈ (snapshot front []).2, lower < entry
        · simp only [htemporary, if_true] at hrun
          rw [hdoubleSC, hrun]
          simp [left, right, outputGap, hfront, htemporary, horiginal]
        · simp only [htemporary, if_false] at hrun
          have hentryStack : ∀ value ∈ (snapshot front []).2, entry ≤ value := by
            intro value hvalue
            exact Nat.le_of_not_gt (fun hlt => htemporary ⟨value, hvalue, hlt⟩)
          have hlegal : ¬ ContainsV (entry :: (snapshot front []).2) := by
            cases hstack : (snapshot front []).2 with
            | nil => exact htop entry [] hnil (by simp)
            | cons top current =>
              rw [push_test]
              rintro (hpattern | ⟨_, lower, hlower, hless⟩)
              · exact hstate.1 (by simpa only [hstack] using hpattern)
              · have := hentryStack lower (by simp [hstack, hlower])
                omega
          have hprotect := protected_suffix rest [entry] (snapshot front []).2 entry hlegal
            (by simp) (by simp) hentryStack
          have hold : Process (entry :: rest) (snapshot front []).2 =
              Process (entry :: rest) [] ++ (snapshot front []).2 := by
            simpa only [Process, hpush entry _ hlegal, Push, List.nil_append,
              List.cons_append] using hprotect
          have hgap : outputGap front (entry :: rest) =
              ((snapshot front []).1 ++ Process (entry :: rest) []).length := by
            have hstatelength := hstate.2.length_eq
            simp only [outputGap, if_neg hfront, if_neg htemporary, List.length_append,
              List.length_cons]
            simp only [List.length_append] at hstatelength
            simp only [SC, List.length_cons] at hlength
            omega
          rw [hdoubleSC, hrun]
          simp only [left, right, hgap, horiginal, hold, ← List.append_assoc,
            List.take_append_length, List.drop_append_length]
  refine ⟨?_, by rw [hdoubleOutput]; exact hdoubleAvoid⟩
  by_cases hfront : front = []
  · subst front
    have hvalues : ∀ value ∈ maximum :: suffix, value < larger := by
      intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact hlarge
      · exact lt_trans (hbound value (by simpa using hvalue)) hlarge
    have hinsert := (maximum_insertion [] (maximum :: suffix) larger
      (by simpa using hvalues)).1
    have hchildPerm : (SC (maximum :: suffix)).Perm (maximum :: suffix) := by
      simpa [SC] using (process_preserves (maximum :: suffix) [] hnil).1
    have hchildNodup : (maximum :: suffix).Nodup := by
      refine List.nodup_cons.mpr ⟨?_, by simpa using hnodup⟩
      intro hmem
      exact lt_irrefl maximum (hbound maximum (by simpa using hmem))
    have hlength := hchildPerm.length_eq
    have houtput : SC (larger :: maximum :: suffix) = SC (maximum :: suffix) ++ [larger] := by
      simpa [outputGap, ← hlength] using hinsert
    rw [List.nil_append, houtput]
    exact (maximum_cut (SC (maximum :: suffix)) [] larger
      (by simpa using hchildPerm.nodup_iff.mpr hchildNodup)
      (by simpa using fun value hvalue => hvalues value (hchildPerm.mem_iff.mp hvalue))).mpr
      ⟨by simpa using hactive, by simp [separatingCut]⟩
  · have hseparating : separatingCut (SC (front ++ suffix)) (outputGap front suffix) := by
      have hgapBound : outputGap front suffix ≤ (SC (front ++ suffix)).length := by
        have hgap := (maximum_insertion front suffix maximum hbound).2 hfront
        have hlen := houtputPerm.length_eq
        omega
      simpa only [left, List.length_take, Nat.min_eq_left hgapBound, houtsplit] using hcut
    have hempty : (snapshot front []).1 = [] := by
      have hrecords := ((separating_gap front suffix).mp hseparating).resolve_left hfront
      exact (no_pop_iff_records front).mpr hrecords.1
    obtain ⟨minimum, hminimum⟩ := Option.isSome_iff_exists.mp
      (List.isSome_min?_of_ne_nil hfront)
    obtain ⟨hminmem, hminbound⟩ := List.min?_eq_some_iff.mp hminimum
    have hstackmem := (snapshot_minimum front [] minimum hnil
      (by simpa using hminmem) (by simpa using hminbound)).2.1
    have hminmax := hbound minimum (List.mem_append_left _ hminmem)
    have hlargerlegal := htop larger (snapshot front []).2 hstate.1 (by
      intro value hvalue
      exact lt_trans (hstackbound value hvalue) hlarge)
    have hillegal : ContainsV (maximum :: larger :: (snapshot front []).2) :=
      (push_test maximum larger (snapshot front []).2).mpr
        (Or.inr ⟨hlarge, minimum, hstackmem, hminmax⟩)
    have hbefore : SC (front ++ larger :: maximum :: suffix) =
        larger :: SC (front ++ maximum :: suffix) := by
      rw [SC, hsplit, hempty, List.nil_append, Process, hpush larger _ hlargerlegal,
        Process, Push, if_pos hillegal]
      rw [SC, hsplit, hempty, List.nil_append, Process]
      simp only [List.cons_append, List.nil_append]
    rw [hbefore]
    have hchildPerm : (SC (front ++ maximum :: suffix)).Perm
        (front ++ maximum :: suffix) := by
      simpa [SC] using (process_preserves (front ++ maximum :: suffix) [] hnil).1
    have hchildNodup : (front ++ maximum :: suffix).Nodup := by
      have hperm : (front ++ maximum :: suffix).Perm (maximum :: (front ++ suffix)) :=
        List.perm_middle
      apply hperm.nodup_iff.mpr
      refine List.nodup_cons.mpr ⟨?_, hnodup⟩
      intro hmem
      exact lt_irrefl maximum (hbound maximum hmem)
    exact (maximum_cut [] (SC (front ++ maximum :: suffix)) larger
      (by simpa using hchildPerm.nodup_iff.mpr hchildNodup)
      (by
        intro value hvalue
        have hsource := hchildPerm.mem_iff.mp (by simpa using hvalue)
        rcases List.mem_append.mp hsource with hfront | hrest
        · exact lt_trans (hbound value (List.mem_append_left _ hfront)) hlarge
        · rcases List.mem_cons.mp hrest with rfl | hsuffix
          · exact hlarge
          · exact lt_trans (hbound value (List.mem_append_right _ hsuffix)) hlarge)).mpr
      ⟨by simpa using hactive, by simp [separatingCut]⟩

theorem two_marker_order (front : List ℕ) (entry : ℕ) (middle suffix : List ℕ)
    (first second : ℕ)
    (hfirst : ∀ value ∈ front ++ entry :: (middle ++ suffix), value < first)
    (hsecond : ∀ value ∈ front ++ entry :: (middle ++ suffix), value < second) :
    ∃ left between right : List ℕ,
      SC (front ++ entry :: (middle ++ suffix)) = left ++ between ++ right ∧
        ((outputGap front (entry :: (middle ++ suffix)) ≤
            outputGap (front ++ entry :: middle) suffix ∧
          SC (front ++ first :: entry :: (middle ++ second :: suffix)) =
            left ++ first :: (between ++ second :: right) ∧
          left.length = outputGap front (entry :: (middle ++ suffix)) ∧
          (left ++ between).length = outputGap (front ++ entry :: middle) suffix) ∨
        (outputGap (front ++ entry :: middle) suffix <
            outputGap front (entry :: (middle ++ suffix)) ∧
          SC (front ++ first :: entry :: (middle ++ second :: suffix)) =
            left ++ second :: (between ++ first :: right) ∧
          left.length = outputGap (front ++ entry :: middle) suffix ∧
          (left ++ between).length = outputGap front (entry :: (middle ++ suffix)))) := by
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  have htop : ∀ top current, ¬ ContainsV current →
      (∀ value ∈ current, value < top) → ¬ ContainsV (top :: current) := by
    intro top current hcurrent hvalues
    cases current with
    | nil =>
      rintro ⟨position, hposition, later, hlater, hgap, _⟩
      simp only [List.length_cons, List.length_nil] at hposition hlater
      omega
    | cons next current =>
      rw [push_test]
      rintro (hpattern | ⟨hascent, _⟩)
      · exact hcurrent hpattern
      · exact (not_lt_of_gt (hvalues next List.mem_cons_self)) hascent
  have hpush : ∀ value current, ¬ ContainsV (value :: current) →
      Push value current = ([], value :: current) := by
    intro value current hlegal
    cases current with
    | nil => rfl
    | cons top current => simp only [Push, if_neg hlegal]
  have hsplit : ∀ processed unread current : List ℕ,
      Process (processed ++ unread) current =
        (snapshot processed current).1 ++ Process unread (snapshot processed current).2 := by
    intro processed
    induction processed with
    | nil => intro unread current; rfl
    | cons value processed ih =>
      intro unread current
      simp only [List.cons_append, Process, snapshot, ih, List.append_assoc]
  have hstate : ¬ ContainsV (snapshot front []).2 ∧
      ((snapshot front []).1 ++ (snapshot front []).2).Perm front := by
    have hvalid : ∀ processed current, ¬ ContainsV current →
        ¬ ContainsV (snapshot processed current).2 := by
      intro processed
      induction processed with
      | nil => intro current hcurrent; exact hcurrent
      | cons value processed ih =>
        intro current hcurrent
        exact ih (Push value current).2 (push_preserves value current hcurrent).1
    refine ⟨hvalid front [] hnil, ?_⟩
    have hconserve := (process_preserves front [] hnil).1
    have hdecomp : Process front [] = (snapshot front []).1 ++ (snapshot front []).2 := by
      simpa only [List.append_nil, Process] using hsplit front [] []
    rw [hdecomp] at hconserve
    simpa only [List.append_nil] using hconserve
  let emitted := (snapshot front []).1
  let stack := (snapshot front []).2
  let original := SC (front ++ entry :: (middle ++ suffix))
  let later := SC ((front ++ entry :: middle) ++ second :: suffix)
  let gap := outputGap (front ++ entry :: middle) suffix
  have hstackfirst : ∀ value ∈ stack, value < first := by
    intro value hvalue
    exact hfirst value (List.mem_append_left _
      (hstate.2.mem_iff.mp (List.mem_append_right _ hvalue)))
  have hnotEmitted : second ∉ emitted := by
    intro hmem
    have := hsecond second (List.mem_append_left _
      (hstate.2.mem_iff.mp (List.mem_append_left _ hmem)))
    omega
  have hnotOriginal : second ∉ original := by
    intro hmem
    have hperm := (process_preserves (front ++ entry :: (middle ++ suffix)) [] hnil).1
    have := hsecond second (by simpa only [List.append_nil, SC] using hperm.mem_iff.mp hmem)
    omega
  have hsecondBound : ∀ value ∈ (front ++ entry :: middle) ++ suffix, value < second := by
    simpa only [List.append_assoc, List.cons_append] using hsecond
  have hmarker := maximum_insertion (front ++ entry :: middle) suffix second hsecondBound
  have hprefixNonempty : front ++ entry :: middle ≠ [] := by simp
  have hgaplt : gap < original.length := by
    have hlen : original.length = (front ++ entry :: (middle ++ suffix)).length := by
      simpa only [original, SC, List.append_nil] using
        (process_preserves (front ++ entry :: (middle ++ suffix)) [] hnil).1.length_eq
    have hlt : gap < (front ++ entry :: (middle ++ suffix)).length := by
      simpa only [List.append_assoc, List.cons_append, gap] using hmarker.2 hprefixNonempty
    omega
  have hlaterOutput : later = original.take gap ++ second :: original.drop gap := by
    simpa only [later, original, gap, List.append_assoc, List.cons_append] using hmarker.1
  have hlaterIndex : later.idxOf second = gap := by
    rw [hlaterOutput, List.idxOf_append_of_notMem
      (fun hmem => hnotOriginal ((List.take_sublist gap original).subset hmem)),
      List.idxOf_cons_self, Nat.add_zero, List.length_take, Nat.min_eq_left (by omega)]
  have horiginal : original = emitted ++ Process (entry :: (middle ++ suffix)) stack :=
    hsplit front (entry :: (middle ++ suffix)) []
  have hlater : later = emitted ++ Process (entry :: (middle ++ second :: suffix)) stack := by
    simpa only [later, emitted, stack, List.append_assoc, List.cons_append, SC] using
      hsplit front (entry :: (middle ++ second :: suffix)) []
  have hfirstlegal := htop first stack hstate.1 hstackfirst
  have hdouble : SC (front ++ first :: entry :: (middle ++ second :: suffix)) =
      emitted ++ Process (entry :: (middle ++ second :: suffix)) (first :: stack) := by
    rw [SC, hsplit, Process, hpush first _ hfirstlegal]
    simp only [List.nil_append, emitted]
  have hentryfirst : entry < first := hfirst entry (by simp)
  by_cases htemporary : ∃ lower ∈ stack, lower < entry
  · have hfront : front ≠ [] := by
      intro heq
      simp [stack, heq, snapshot] at htemporary
    have hgapfirst : outputGap front (entry :: (middle ++ suffix)) = emitted.length := by
      simp only [outputGap, if_neg hfront]
      exact if_pos htemporary
    have hillegal : ContainsV (entry :: first :: stack) :=
      (push_test entry first stack).mpr (Or.inr ⟨hentryfirst, htemporary⟩)
    have hrun : ∀ unread, Process (entry :: unread) (first :: stack) =
        first :: Process (entry :: unread) stack := by
      intro unread
      simp only [Process, Push, if_pos hillegal, List.cons_append]
    have hgapge : emitted.length ≤ gap := by
      rw [hlater, List.idxOf_append_of_notMem hnotEmitted] at hlaterIndex
      omega
    let remainder := Process (entry :: (middle ++ suffix)) stack
    let offset := gap - emitted.length
    have hgapadd : gap = emitted.length + offset := by dsimp only [offset]; omega
    have hoffset : offset ≤ remainder.length := by
      have hlen : original.length = emitted.length + remainder.length := by
        rw [horiginal, List.length_append]
      omega
    have htail : Process (entry :: (middle ++ second :: suffix)) stack =
        remainder.take offset ++ second :: remainder.drop offset := by
      rw [hlater, horiginal, hgapadd] at hlaterOutput
      simp only [List.take_append, List.drop_append, Nat.add_sub_cancel_left,
        List.take_of_length_le (by omega : emitted.length ≤ emitted.length + offset),
        List.drop_eq_nil_of_le (by omega : emitted.length ≤ emitted.length + offset),
        List.nil_append, List.append_assoc] at hlaterOutput
      exact List.append_cancel_left hlaterOutput
    refine ⟨emitted, remainder.take offset, remainder.drop offset, ?_, Or.inl ?_⟩
    · rw [List.append_assoc, List.take_append_drop]
      exact horiginal
    · refine ⟨by rw [hgapfirst]; exact hgapge, ?_, hgapfirst.symm, ?_⟩
      · rw [hdouble, hrun, htail]
      · simp only [List.length_append, List.length_take, Nat.min_eq_left hoffset]
        exact hgapadd.symm
  · have hentryStack : ∀ value ∈ stack, entry ≤ value := by
      intro value hvalue
      exact Nat.le_of_not_gt (fun hlt => htemporary ⟨value, hvalue, hlt⟩)
    have hentrylegal : ¬ ContainsV (entry :: stack) := by
      cases hcurrent : stack with
      | nil => exact htop entry [] hnil (by simp)
      | cons top current =>
        rw [push_test]
        rintro (hpattern | ⟨_, lower, hlower, hless⟩)
        · exact hstate.1 (by simpa only [stack, hcurrent] using hpattern)
        · have := hentryStack lower (by simp [hcurrent, hlower])
          omega
    have hmarkedlegal : ¬ ContainsV (entry :: first :: stack) := by
      rw [push_test]
      rintro (hpattern | ⟨_, hexists⟩)
      · exact hfirstlegal hpattern
      · exact htemporary hexists
    have hprotected : ∀ unread, Process (entry :: unread) stack =
        Process (entry :: unread) [] ++ stack := by
      intro unread
      have hprotect := protected_suffix unread [entry] stack entry hentrylegal
        (by simp) (by simp) hentryStack
      simpa only [Process, hpush entry stack hentrylegal, Push, List.nil_append,
        List.cons_append] using hprotect
    have hmarked : ∀ unread, Process (entry :: unread) (first :: stack) =
        Process (entry :: unread) [] ++ first :: stack := by
      intro unread
      have hprotect := protected_suffix unread [entry] (first :: stack) entry hmarkedlegal
        (by simp) (by simp) (by
          intro value hvalue
          rcases List.mem_cons.mp hvalue with rfl | hvalue
          · exact le_of_lt hentryfirst
          · exact hentryStack value hvalue)
      simpa only [Process, hpush entry _ hmarkedlegal, Push, if_neg hmarkedlegal, List.nil_append,
        List.cons_append] using hprotect
    let localOutput := SC (entry :: (middle ++ suffix))
    let localGap := outputGap (entry :: middle) suffix
    have hlocalLength : localOutput.length = (entry :: (middle ++ suffix)).length := by
      simpa only [localOutput, SC, List.append_nil] using
        (process_preserves (entry :: (middle ++ suffix)) [] hnil).1.length_eq
    have hlocalBound : ∀ value ∈ (entry :: middle) ++ suffix, value < second := by
      intro value hvalue
      apply hsecond value
      apply List.mem_append_right
      simpa only [List.cons_append] using hvalue
    have hlocal := maximum_insertion (entry :: middle) suffix second hlocalBound
    have hlocalLt : localGap < localOutput.length := by
      have := hlocal.2 (by simp)
      simp only [List.length_append, List.length_cons] at this hlocalLength
      dsimp only [localGap]
      omega
    have hlocalOutput : SC (entry :: (middle ++ second :: suffix)) =
        localOutput.take localGap ++ second :: localOutput.drop localGap := by
      simpa only [localOutput, localGap, List.cons_append] using hlocal.1
    have horig : original = emitted ++ localOutput ++ stack := by
      rw [horiginal, hprotected]
      simp only [localOutput, SC, List.append_assoc]
    have hlaterNew : later =
        (emitted ++ localOutput.take localGap) ++ second :: (localOutput.drop localGap ++ stack) :=
      by
        rw [hlater, hprotected]
        change emitted ++ (SC (entry :: (middle ++ second :: suffix)) ++ stack) = _
        simp only [hlocalOutput, List.append_assoc, List.cons_append]
    have hgapNew : gap = emitted.length + localGap := by
      have hnotLocal : second ∉ localOutput := by
        intro hmem
        have hperm := (process_preserves (entry :: (middle ++ suffix)) [] hnil).1
        have hsource := hperm.mem_iff.mp hmem
        have := hsecond second (List.mem_append_right _ (by
          simpa only [List.append_nil] using hsource))
        omega
      rw [hlaterNew, List.idxOf_append_of_notMem (by
        intro hmem
        rcases List.mem_append.mp hmem with hemitted | hlocal
        · exact hnotEmitted hemitted
        · exact hnotLocal ((List.take_sublist localGap localOutput).subset hlocal)),
        List.idxOf_cons_self, Nat.add_zero, List.length_append, List.length_take,
        Nat.min_eq_left (by omega)] at hlaterIndex
      exact hlaterIndex.symm
    have hgapfirst : outputGap front (entry :: (middle ++ suffix)) =
        emitted.length + localOutput.length := by
      have hstatelength := hstate.2.length_eq
      by_cases hfront : front = []
      · subst front
        simpa only [outputGap, if_true, emitted, snapshot, List.length_nil, Nat.zero_add]
          using hlocalLength.symm
      · have hnotTemp : ¬ ∃ lower ∈ (snapshot front []).2, lower < entry := htemporary
        simp only [outputGap, if_neg hfront, if_neg hnotTemp, List.length_append,
          List.length_cons]
        change front.length + (middle.length + suffix.length + 1) - stack.length =
          emitted.length + localOutput.length
        simp only [List.length_append] at hstatelength
        change emitted.length + stack.length = front.length at hstatelength
        simp only [List.length_cons, List.length_append] at hlocalLength
        omega
    refine ⟨emitted ++ localOutput.take localGap, localOutput.drop localGap, stack,
      ?_, Or.inr ?_⟩
    · rw [List.append_assoc emitted (localOutput.take localGap) (localOutput.drop localGap),
        List.take_append_drop]
      exact horig
    · refine ⟨?_, ?_, ?_, ?_⟩
      · change gap < outputGap front (entry :: (middle ++ suffix))
        rw [hgapfirst, hgapNew]
        omega
      · rw [hdouble, hmarked]
        change emitted ++ (SC (entry :: (middle ++ second :: suffix)) ++ first :: stack) = _
        simp only [hlocalOutput, List.append_assoc, List.cons_append]
      · simp only [List.length_append, List.length_take,
          Nat.min_eq_left (le_of_lt hlocalLt)]
        exact hgapNew.symm
      · rw [List.append_assoc emitted (localOutput.take localGap) (localOutput.drop localGap),
          List.take_append_drop]
        simp only [List.length_append]
        exact hgapfirst.symm

theorem later_site_activity (front : List ℕ) (entry : ℕ) (middle suffix : List ℕ)
    (maximum larger : ℕ)
    (hnodup : (front ++ entry :: (middle ++ suffix)).Nodup)
    (hbound : ∀ value ∈ front ++ entry :: (middle ++ suffix), value < maximum)
    (hlarge : maximum < larger)
    (hactive : ¬ Contains231 (SC (front ++ maximum :: entry :: (middle ++ suffix)))) :
    ¬ Contains231 (SC (front ++ maximum :: entry :: (middle ++ larger :: suffix))) ↔
      ¬ Contains231 (SC ((front ++ entry :: middle) ++ larger :: suffix)) ∧
        outputGap (front ++ entry :: middle) suffix <
          outputGap front (entry :: (middle ++ suffix)) := by
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  have hvalues : ∀ value ∈ front ++ entry :: (middle ++ suffix), value < larger :=
    fun value hvalue => lt_trans (hbound value hvalue) hlarge
  have hmaximum := (maximum_insertion front (entry :: (middle ++ suffix)) maximum hbound).1
  have hlargerBound : ∀ value ∈ (front ++ entry :: middle) ++ suffix, value < larger := by
    simpa only [List.append_assoc, List.cons_append] using hvalues
  have hlarger := maximum_insertion (front ++ entry :: middle) suffix larger hlargerBound
  obtain ⟨left, between, right, hsplit, horder⟩ :=
    two_marker_order front entry middle suffix maximum larger hbound hvalues
  have houtputPerm : (SC (front ++ entry :: (middle ++ suffix))).Perm
      (front ++ entry :: (middle ++ suffix)) := by
    simpa [SC] using (process_preserves (front ++ entry :: (middle ++ suffix)) [] hnil).1
  have houtputNodup : (left ++ between ++ right).Nodup := by
    rw [← hsplit]
    exact houtputPerm.nodup_iff.mpr hnodup
  have houtputBound : ∀ value ∈ left ++ between ++ right, value < maximum := by
    rw [← hsplit]
    exact fun value hvalue => hbound value (houtputPerm.mem_iff.mp hvalue)
  rcases horder with ⟨hgap, hdouble, hleft, hbetween⟩ |
    ⟨hgap, hdouble, hleft, hbetween⟩
  · have hgaplt := hlarger.2 (by simp)
    have houtputLength := houtputPerm.length_eq
    have hright : right ≠ [] := by
      intro heq
      rw [heq, List.append_nil] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons] at hgaplt houtputLength
      simp only [List.length_append] at hlen hbetween
      omega
    cases right with
    | nil => exact False.elim (hright rfl)
    | cons last rest =>
      have hlast : last < maximum := houtputBound last (by simp)
      have hpattern : Contains231
          (left ++ maximum :: (between ++ larger :: last :: rest)) := by
        refine ⟨left.length, left.length + between.length + 1,
          left.length + between.length + 2, by omega, by omega, by simp; omega, ?_, ?_⟩
        · simp only [List.getD_append_right left _ 0 left.length (by omega), Nat.sub_self,
            List.getD_cons_zero]
          rw [List.getD_append_right left _ 0 (left.length + between.length + 2) (by omega)]
          simp only [Nat.add_assoc, Nat.add_sub_cancel_left, List.getD_cons_succ]
          rw [List.getD_append_right between _ 0 (between.length + 1) (by omega)]
          simpa using hlast
        · simp only [List.getD_append_right left _ 0 left.length (by omega), Nat.sub_self,
            List.getD_cons_zero]
          rw [List.getD_append_right left _ 0 (left.length + between.length + 1) (by omega)]
          simp only [Nat.add_assoc, Nat.add_sub_cancel_left, List.getD_cons_succ]
          rw [List.getD_append_right between _ 0 between.length (by omega)]
          simpa using hlarge
      rw [hdouble]
      constructor
      · exact fun hnot => False.elim (hnot hpattern)
      · rintro ⟨_, hless⟩
        omega
  · have hmaximumOutput : SC (front ++ maximum :: entry :: (middle ++ suffix)) =
        (left ++ between) ++ maximum :: right := by
      rw [hmaximum, hsplit, ← hbetween, List.take_append_length, List.drop_append_length]
    have hlargerOutput : SC ((front ++ entry :: middle) ++ larger :: suffix) =
        left ++ larger :: (between ++ right) := by
      rw [hlarger.1]
      simp only [List.append_assoc, List.cons_append]
      rw [hsplit, ← hleft, List.append_assoc,
        List.take_append_length, List.drop_append_length]
    have hbase : ¬ Contains231 ((left ++ between) ++ maximum :: right) := by
      rwa [hmaximumOutput] at hactive
    have hnot : maximum ∉ left ++ between ++ right := by
      intro hmem
      exact lt_irrefl maximum (houtputBound maximum hmem)
    have hperm : (left ++ (between ++ maximum :: right)).Perm
        (maximum :: (left ++ between ++ right)) := by
      have hmove : ((left ++ between) ++ maximum :: right).Perm
          (maximum :: ((left ++ between) ++ right)) := List.perm_middle
      simpa only [List.append_assoc] using hmove
    have hchildNodup : (left ++ (between ++ maximum :: right)).Nodup :=
      hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hnot, houtputNodup⟩)
    have hchildBound : ∀ value ∈ left ++ (between ++ maximum :: right), value < larger := by
      intro value hvalue
      rcases List.mem_append.mp hvalue with hl | hrest
      · exact lt_trans (houtputBound value (by simp [hl])) hlarge
      · rcases List.mem_append.mp hrest with hb | hrest
        · exact lt_trans (houtputBound value (by simp [hb])) hlarge
        · rcases List.mem_cons.mp hrest with rfl | hr
          · exact hlarge
          · exact lt_trans (houtputBound value (by simp [hr])) hlarge
    have hcutEquiv : separatingCut (left ++ (between ++ maximum :: right)) left.length ↔
        separatingCut (left ++ (between ++ right)) left.length := by
      simp only [separatingCut, List.take_append_length, List.drop_append_length]
      constructor
      · intro hcut value hvalue other hother
        rcases List.mem_append.mp hother with hb | hr
        · exact hcut value hvalue other (List.mem_append_left _ hb)
        · exact hcut value hvalue other
            (List.mem_append_right _ (List.mem_cons_of_mem maximum hr))
      · intro hcut value hvalue other hother
        rcases List.mem_append.mp hother with hb | hrest
        · exact hcut value hvalue other (List.mem_append_left _ hb)
        · rcases List.mem_cons.mp hrest with rfl | hr
          · exact houtputBound value (by simp [hvalue])
          · exact hcut value hvalue other (List.mem_append_right _ hr)
    have htwoTest := maximum_cut left (between ++ maximum :: right) larger
      hchildNodup hchildBound
    have honeTest := maximum_cut left (between ++ right) larger
      (by simpa only [List.append_assoc] using houtputNodup)
      (by
        intro value hvalue
        exact lt_trans (houtputBound value (by
          simpa only [List.append_assoc] using hvalue)) hlarge)
    have hparent : ¬ Contains231 (left ++ (between ++ right)) := by
      have hparentTest := maximum_cut (left ++ between) right maximum
        houtputNodup houtputBound
      simpa only [List.append_assoc] using (hparentTest.mp hbase).1
    rw [hdouble, hlargerOutput]
    constructor
    · intro hnot
      have hcut := (htwoTest.mp hnot).2
      exact ⟨honeTest.mpr ⟨hparent, hcutEquiv.mp hcut⟩, hgap⟩
    · rintro ⟨hone, _⟩
      apply htwoTest.mpr
      exact ⟨by simpa only [List.append_assoc] using hbase,
        hcutEquiv.mpr (honeTest.mp hone).2⟩

end D5.S3.Combinatorics.VincularStack.VincularStackPriority
