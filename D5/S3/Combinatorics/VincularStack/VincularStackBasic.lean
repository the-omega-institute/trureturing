/- GID: D5/S3/Combinatorics/VincularStack/VincularStackBasic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackBasic
   mirror-E: none(waiver:stack-transition-invariants)
   anchors: [mathlib/module/Mathlib.Data.List.GetD]
   utility: none
   digest: Stack invariants and marker simulations identify the exact maximum-output cut. -/

import D5.S3.Combinatorics.VincularStack.VincularStackDefs
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackBasic

open VincularStackDefs
open scoped List

theorem push_test (entry top : ℕ) (stack : List ℕ) :
    ContainsV (entry :: top :: stack) ↔
      ContainsV (top :: stack) ∨ (entry < top ∧ ∃ lower ∈ stack, lower < entry) := by
  constructor
  · rintro ⟨position, hposition, later, hlater, hgap, hascent, hlower⟩
    cases position with
    | zero =>
      right
      refine ⟨by simpa using hascent, ?_⟩
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ later)
      have hbound : offset < stack.length := by simp only [List.length_cons] at hlater; omega
      refine ⟨stack.getD offset 0, ?_, ?_⟩
      · rw [List.getD_eq_getElem stack 0 hbound]
        exact List.getElem_mem hbound
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlower
    | succ position =>
      left
      cases later with
      | zero => omega
      | succ later =>
        refine ⟨position, by simpa using hposition, later, by simpa using hlater,
          by omega, ?_, ?_⟩ <;> simpa using ‹_›
  · rintro (hpattern | ⟨hascent, lower, hmem, hlower⟩)
    · obtain ⟨position, hposition, later, hlater, hgap, hascent, hlower⟩ := hpattern
      refine ⟨position + 1, by simpa using hposition, later + 1, by simpa using hlater,
        by omega, ?_, ?_⟩ <;> simpa using ‹_›
    · obtain ⟨offset, hbound, hvalue⟩ := List.mem_iff_getElem.mp hmem
      refine ⟨0, by simp, offset + 2, by simp; omega, by omega, ?_, ?_⟩
      · simpa using hascent
      · change stack.getD offset 0 < entry
        rw [List.getD_eq_getElem stack 0 hbound, hvalue]
        exact hlower

theorem push_preserves (entry : ℕ) (stack : List ℕ) (havoid : ¬ ContainsV stack) :
    ¬ ContainsV (Push entry stack).2 ∧
      ((Push entry stack).1 ++ (Push entry stack).2).Perm (entry :: stack) ∧
      stack <+ (Push entry stack).1 ++ (Push entry stack).2 := by
  induction stack with
  | nil =>
    have hshort : ¬ ContainsV [entry] := by
      rintro ⟨position, hposition, later, hlater, hgap, _, _⟩
      simp only [List.length_cons, List.length_nil] at hposition hlater
      omega
    simp only [Push, List.nil_append]
    exact ⟨hshort, List.Perm.refl [entry], List.nil_sublist [entry]⟩
  | cons top stack inductionHypothesis =>
    have htail : ¬ ContainsV stack := by
      intro hpattern
      obtain ⟨position, hposition, later, hlater, hgap, hascent, hlower⟩ := hpattern
      apply havoid
      refine ⟨position + 1, by simpa using hposition, later + 1, by simpa using hlater,
        by omega, ?_, ?_⟩ <;> simpa using ‹_›
    by_cases hillegal : ContainsV (entry :: top :: stack)
    · obtain ⟨hfinal, hperm, hretained⟩ := inductionHypothesis htail
      simp only [Push, if_pos hillegal, List.cons_append]
      refine ⟨hfinal, ?_, hretained.cons_cons top⟩
      exact (hperm.cons top).trans (List.Perm.swap entry top stack)
    · simp only [Push, if_neg hillegal, List.nil_append]
      exact ⟨hillegal, List.Perm.refl _, List.sublist_cons_self _ _⟩

theorem push_minimum (entry minimum : ℕ) (stack : List ℕ)
    (havoid : ¬ ContainsV stack) (hmem : minimum ∈ stack)
    (hminimum : ∀ value ∈ stack, minimum ≤ value) (hentry : minimum ≤ entry) :
    minimum ∈ (Push entry stack).2 ∧
      (∀ value ∈ (Push entry stack).1, minimum < value) := by
  induction stack with
  | nil => simp at hmem
  | cons top stack inductionHypothesis =>
    by_cases hillegal : ContainsV (entry :: top :: stack)
    · obtain ⟨hentrytop, lower, hlower, hlowerentry⟩ :=
        (push_test entry top stack).mp hillegal |>.resolve_left havoid
      have htop : minimum < top := lt_of_le_of_lt hentry hentrytop
      have htailmem : minimum ∈ stack := by
        rcases List.mem_cons.mp hmem with heq | htailmem
        · omega
        · exact htailmem
      have htail : ¬ ContainsV stack := by
        intro hpattern
        obtain ⟨position, hposition, later, hlater, hgap, hascent, hsmall⟩ := hpattern
        apply havoid
        refine ⟨position + 1, by simpa using hposition, later + 1, by simpa using hlater,
          by omega, ?_, ?_⟩ <;> simpa using ‹_›
      obtain ⟨hretained, hpopped⟩ := inductionHypothesis htail htailmem
        (fun value hvalue => hminimum value (List.mem_cons_of_mem top hvalue))
      simp only [Push, if_pos hillegal]
      refine ⟨hretained, ?_⟩
      intro value hvalue
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact htop
      · exact hpopped value hvalue
    · simp only [Push, if_neg hillegal]
      exact ⟨List.mem_cons_of_mem entry hmem, by simp⟩

theorem process_preserves (input stack : List ℕ) (havoid : ¬ ContainsV stack) :
    (Process input stack).Perm (input ++ stack) ∧ stack <+ Process input stack := by
  induction input generalizing stack with
  | nil => exact ⟨List.Perm.refl _, List.Sublist.refl _⟩
  | cons entry input inductionHypothesis =>
    obtain ⟨hfinal, hpushperm, hpushretained⟩ := push_preserves entry stack havoid
    obtain ⟨hrunperm, hrunretained⟩ := inductionHypothesis (Push entry stack).2 hfinal
    simp only [Process]
    refine ⟨?_, hpushretained.trans (hrunretained.append_left _)⟩
    calc
      (Push entry stack).1 ++ Process input (Push entry stack).2
          ~ (Push entry stack).1 ++ (input ++ (Push entry stack).2) :=
        List.Perm.append_left _ hrunperm
      _ ~ input ++ ((Push entry stack).1 ++ (Push entry stack).2) :=
        List.perm_append_comm_assoc _ _ _
      _ ~ input ++ (entry :: stack) := List.Perm.append_left _ hpushperm
      _ ~ (entry :: input) ++ stack := List.perm_middle

end D5.S3.Combinatorics.VincularStack.VincularStackBasic

namespace D5.S3.Combinatorics.VincularStack.VincularStackRun

open VincularStackDefs VincularStackBasic
open scoped List

def snapshot : List ℕ → List ℕ → List ℕ × List ℕ
  | [], stack => ([], stack)
  | entry :: input, stack =>
    let step := Push entry stack
    let rest := snapshot input step.2
    (step.1 ++ rest.1, rest.2)

theorem snapshot_minimum (input stack : List ℕ) (minimum : ℕ)
    (havoid : ¬ ContainsV stack) (hmem : minimum ∈ input ++ stack)
    (hbound : ∀ value ∈ input ++ stack, minimum ≤ value) :
    ¬ ContainsV (snapshot input stack).2 ∧
      minimum ∈ (snapshot input stack).2 ∧
      (∀ value ∈ (snapshot input stack).1, minimum < value) ∧
      Process input stack = (snapshot input stack).1 ++ (snapshot input stack).2 := by
  have hpush : ∀ entry current, ¬ ContainsV current →
      (∀ value ∈ current, minimum ≤ value) → minimum ≤ entry →
      (∀ value ∈ (Push entry current).1, minimum < value) := by
    intro entry current
    induction current with
    | nil => simp [Push]
    | cons top current inductionHypothesis =>
      intro hcurrent hcurrentbound hentry
      by_cases hillegal : ContainsV (entry :: top :: current)
      · have hascent := ((push_test entry top current).mp hillegal).resolve_left hcurrent
        have htail : ¬ ContainsV current := by
          intro hpattern
          obtain ⟨position, hposition, later, hlater, hgap, hlarge, hsmall⟩ := hpattern
          apply hcurrent
          refine ⟨position + 1, by simpa using hposition,
            later + 1, by simpa using hlater, by omega, ?_, ?_⟩ <;> simpa using ‹_›
        have hrest := inductionHypothesis htail
          (fun value hvalue => hcurrentbound value (List.mem_cons_of_mem top hvalue)) hentry
        simp only [Push, if_pos hillegal]
        intro value hvalue
        rcases List.mem_cons.mp hvalue with rfl | hvalue
        · exact lt_of_le_of_lt hentry hascent.1
        · exact hrest value hvalue
      · simp [Push, hillegal]
  induction input generalizing stack with
  | nil =>
    simp only [List.nil_append] at hmem hbound
    exact ⟨havoid, hmem, by simp [snapshot], rfl⟩
  | cons entry input inductionHypothesis =>
    obtain ⟨hfinal, hperm, _⟩ := push_preserves entry stack havoid
    have hentry : minimum ≤ entry := hbound entry (by simp)
    have hstackbound : ∀ value ∈ stack, minimum ≤ value :=
      fun value hvalue => hbound value (by simp [hvalue])
    have hpopped := hpush entry stack havoid hstackbound hentry
    have hnextbound : ∀ value ∈ input ++ (Push entry stack).2, minimum ≤ value := by
      intro value hvalue
      rcases List.mem_append.mp hvalue with hinput | hfinalmem
      · exact hbound value (by simp [hinput])
      · have horiginal := hperm.mem_iff.mp (List.mem_append_right _ hfinalmem)
        rcases List.mem_cons.mp horiginal with rfl | hstack
        · exact hentry
        · exact hstackbound value hstack
    have hnextmem : minimum ∈ input ++ (Push entry stack).2 := by
      have horiginal : minimum ∈ entry :: (input ++ stack) := by simpa using hmem
      rcases List.mem_cons.mp horiginal with heq | hrest
      · have hpushmem : minimum ∈ (Push entry stack).1 ++ (Push entry stack).2 :=
          hperm.mem_iff.mpr (by simp [heq])
        rcases List.mem_append.mp hpushmem with hpoppedmem | hfinalmem
        · exact False.elim (lt_irrefl minimum (hpopped minimum hpoppedmem))
        · exact List.mem_append_right _ hfinalmem
      · rcases List.mem_append.mp hrest with hinput | hstack
        · exact List.mem_append_left _ hinput
        · have hpushmem := hperm.mem_iff.mpr (List.mem_cons_of_mem entry hstack)
          rcases List.mem_append.mp hpushmem with hpoppedmem | hfinalmem
          · exact False.elim (lt_irrefl minimum (hpopped minimum hpoppedmem))
          · exact List.mem_append_right _ hfinalmem
    obtain ⟨hretainedavoid, hretained, hrestpopped, hprocess⟩ :=
      inductionHypothesis (Push entry stack).2 hfinal hnextmem hnextbound
    simp only [snapshot]
    refine ⟨hretainedavoid, hretained, ?_, ?_⟩
    · intro value hvalue
      rcases List.mem_append.mp hvalue with hfirst | hrest
      · exact hpopped value hfirst
      · exact hrestpopped value hrest
    · simp only [Process, hprocess, List.append_assoc]

end D5.S3.Combinatorics.VincularStack.VincularStackRun

namespace D5.S3.Combinatorics.VincularStack.VincularStackMarkers

open VincularStackDefs VincularStackBasic VincularStackRun
open scoped List

theorem protected_suffix (input upper bottom : List ℕ) (minimum : ℕ)
    (havoid : ¬ ContainsV (upper ++ bottom)) (hmem : minimum ∈ upper)
    (hupper : ∀ value ∈ upper, minimum ≤ value)
    (hbottom : ∀ value ∈ bottom, minimum ≤ value) :
    Process input (upper ++ bottom) = Process input upper ++ bottom := by
  have hprefix : ∀ front back : List ℕ,
      ¬ ContainsV (front ++ back) → ¬ ContainsV front := by
    intro front back hcurrent hpattern
    obtain ⟨position, hposition, later, hlater, hgap, hascent, hlower⟩ := hpattern
    apply hcurrent
    refine ⟨position, by simp; omega, later, by simp; omega, hgap, ?_, ?_⟩
    · rw [List.getD_append front back 0 position hposition,
        List.getD_append front back 0 (position + 1) (by omega)]
      exact hascent
    · rw [List.getD_append front back 0 later hlater,
        List.getD_append front back 0 position hposition]
      exact hlower
  have htail : ∀ top : ℕ, ∀ current : List ℕ,
      ¬ ContainsV (top :: current) → ¬ ContainsV current := by
    intro top current hcurrent hpattern
    obtain ⟨position, hposition, later, hlater, hgap, hascent, hlower⟩ := hpattern
    apply hcurrent
    refine ⟨position + 1, by simpa using hposition,
      later + 1, by simpa using hlater, by omega, ?_, ?_⟩ <;> simpa using ‹_›
  have hpush : ∀ entry current minimum, ¬ ContainsV (current ++ bottom) →
      minimum ∈ current → (∀ value ∈ current, minimum ≤ value) →
      (∀ value ∈ bottom, minimum ≤ value) →
      (Push entry (current ++ bottom)).1 = (Push entry current).1 ∧
      (Push entry (current ++ bottom)).2 = (Push entry current).2 ++ bottom := by
    intro entry current
    induction current with
    | nil => intro minimum _ hcurrent; simp at hcurrent
    | cons top current inductionHypothesis =>
      intro minimum hcurrent hcurrentmem hcurrentbound hbottomBound
      have hsmallavoid := hprefix (top :: current) bottom hcurrent
      change ¬ ContainsV (top :: (current ++ bottom)) at hcurrent
      have htest : ContainsV (entry :: top :: (current ++ bottom)) ↔
          ContainsV (entry :: top :: current) := by
        rw [push_test, push_test]
        simp only [hcurrent, hsmallavoid, false_or]
        constructor
        · rintro ⟨hascent, lower, hlower, hcomparison⟩
          refine ⟨hascent, ?_⟩
          rcases List.mem_append.mp hlower with hrest | hbottommem
          · exact ⟨lower, hrest, hcomparison⟩
          · have hminimumEntry := lt_of_le_of_lt (hbottomBound lower hbottommem) hcomparison
            have hminimumTail : minimum ∈ current := by
              rcases List.mem_cons.mp hcurrentmem with heq | hrest
              · omega
              · exact hrest
            exact ⟨minimum, hminimumTail, hminimumEntry⟩
        · rintro ⟨hascent, lower, hlower, hcomparison⟩
          exact ⟨hascent, lower, List.mem_append_left _ hlower, hcomparison⟩
      by_cases hillegal : ContainsV (entry :: top :: current)
      · have hascent := ((push_test entry top current).mp hillegal).resolve_left hsmallavoid
        have hminimumEntry : minimum < entry := by
          obtain ⟨lower, hlower, hcomparison⟩ := hascent.2
          exact lt_of_le_of_lt (hcurrentbound lower (List.mem_cons_of_mem top hlower))
            hcomparison
        have hminimumTail : minimum ∈ current := by
          rcases List.mem_cons.mp hcurrentmem with heq | hrest
          · omega
          · exact hrest
        have hrest := inductionHypothesis minimum (htail top (current ++ bottom) hcurrent)
          hminimumTail (fun value hvalue =>
            hcurrentbound value (List.mem_cons_of_mem top hvalue)) hbottomBound
        simp only [List.cons_append, Push, if_pos hillegal, if_pos (htest.mpr hillegal)]
        exact ⟨congrArg (List.cons top) hrest.1, hrest.2⟩
      · simp [Push, hillegal, mt htest.mp hillegal]
  induction input generalizing upper minimum with
  | nil => rfl
  | cons entry input inductionHypothesis =>
    have hupperavoid := hprefix upper bottom havoid
    obtain ⟨hemitted, hstack⟩ := hpush entry upper minimum havoid hmem hupper hbottom
    obtain ⟨hnextavoid, hnextperm, _⟩ := push_preserves entry upper hupperavoid
    have hnextcombined : ¬ ContainsV ((Push entry upper).2 ++ bottom) := by
      rw [← hstack]
      exact (push_preserves entry (upper ++ bottom) havoid).1
    have hnextbound : ∀ value ∈ (Push entry upper).2, min minimum entry ≤ value := by
      intro value hvalue
      have hsource := hnextperm.mem_iff.mp (List.mem_append_right _ hvalue)
      rcases List.mem_cons.mp hsource with rfl | hsource
      · exact min_le_right _ _
      · exact le_trans (min_le_left _ _) (hupper value hsource)
    have hnextmem : min minimum entry ∈ (Push entry upper).2 := by
      by_cases hentry : minimum ≤ entry
      · rw [min_eq_left hentry]
        exact (push_minimum entry minimum upper hupperavoid hmem hupper hentry).1
      · have hless : entry < minimum := by omega
        have hlegal : ¬ ContainsV (entry :: upper) := by
          cases upper with
          | nil => simp at hmem
          | cons top current =>
            rw [push_test]
            rintro (hpattern | ⟨_, lower, hlower, hcomparison⟩)
            · exact hupperavoid hpattern
            · have := hupper lower (List.mem_cons_of_mem top hlower)
              omega
        cases upper with
        | nil => simp at hmem
        | cons top current =>
          simp only [Push, if_neg hlegal, min_eq_right (le_of_lt hless)]
          exact List.mem_cons_self
    have hnextbottom : ∀ value ∈ bottom, min minimum entry ≤ value :=
      fun value hvalue => le_trans (min_le_left _ _) (hbottom value hvalue)
    have hrest := inductionHypothesis (Push entry upper).2 (min minimum entry)
      hnextcombined hnextmem hnextbound hnextbottom
    simp only [Process, hemitted, hstack, hrest, List.append_assoc]

def outputGap (front suffix : List ℕ) : ℕ :=
  if front = [] then suffix.length
  else
    match suffix with
    | [] => (snapshot front []).1.length
    | entry :: _ =>
      if ∃ lower ∈ (snapshot front []).2, lower < entry
      then (snapshot front []).1.length
      else (front ++ suffix).length - (snapshot front []).2.length

theorem maximum_insertion (front suffix : List ℕ) (maximum : ℕ)
    (hbound : ∀ value ∈ front ++ suffix, value < maximum) :
    SC (front ++ maximum :: suffix) =
      (SC (front ++ suffix)).take (outputGap front suffix) ++
        maximum :: (SC (front ++ suffix)).drop (outputGap front suffix) ∧
      (front ≠ [] → outputGap front suffix < (front ++ suffix).length) := by
  have hnil : ¬ ContainsV [] := by
    rintro ⟨position, hposition, _⟩
    simp at hposition
  have hcons : ∀ top current, ¬ ContainsV current →
      (∀ value ∈ current, value < top) → ¬ ContainsV (top :: current) := by
    intro top current hcurrent hcurrentbound
    cases current with
    | nil =>
      rintro ⟨position, hposition, later, hlater, hgap, _, _⟩
      simp only [List.length_cons, List.length_nil] at hposition hlater
      omega
    | cons next current =>
      rw [push_test]
      rintro (hpattern | ⟨hascent, _⟩)
      · exact hcurrent hpattern
      · have := hcurrentbound next List.mem_cons_self
        omega
  have hsplit : ∀ front back current : List ℕ,
      Process (front ++ back) current =
        (snapshot front current).1 ++ Process back (snapshot front current).2 := by
    intro front
    induction front with
    | nil => intro back current; rfl
    | cons entry front inductionHypothesis =>
      intro back current
      simp only [List.cons_append, Process, snapshot, inductionHypothesis, List.append_assoc]
  have hmarker : ∀ unread current : List ℕ, ¬ ContainsV current →
      (∀ value ∈ current ++ unread, value < maximum) →
      Process unread (maximum :: current) =
        match unread with
        | [] => maximum :: current
        | entry :: rest =>
          if ∃ lower ∈ current, lower < entry
          then maximum :: Process unread current
          else Process unread [] ++ maximum :: current := by
    intro unread current hcurrent hcurrentbound
    cases unread with
    | nil => rfl
    | cons entry rest =>
      have hentry : entry < maximum := hcurrentbound entry (by simp)
      have hmaximumavoid := hcons maximum current hcurrent
        (fun value hvalue => hcurrentbound value (by simp [hvalue]))
      by_cases htemporary : ∃ lower ∈ current, lower < entry
      · have hillegal : ContainsV (entry :: maximum :: current) :=
          (push_test entry maximum current).mpr (Or.inr ⟨hentry, htemporary⟩)
        simp only [htemporary, if_pos, Process, Push, if_pos hillegal, List.cons_append]
      · have hlegal : ¬ ContainsV (entry :: maximum :: current) := by
          rw [push_test]
          rintro (hpattern | ⟨_, hexists⟩)
          · exact hmaximumavoid hpattern
          · exact htemporary hexists
        have hprotected := protected_suffix rest [entry] (maximum :: current) entry hlegal
          (by simp) (by simp) (by
            intro value hvalue
            rcases List.mem_cons.mp hvalue with rfl | hvalue
            · exact le_of_lt hentry
            · exact Nat.le_of_not_gt (fun hless => htemporary ⟨value, hvalue, hless⟩))
        simp only [htemporary, if_false, Process, Push, if_neg hlegal, List.nil_append]
        exact hprotected
  have hlength (word : List ℕ) : (SC word).length = word.length := by
    simpa [SC] using (process_preserves word [] hnil).1.length_eq
  by_cases hprefix : front = []
  · subst front
    constructor
    · simp only [outputGap, if_true, List.nil_append]
      rw [← hlength suffix, List.take_length, List.drop_length]
      cases suffix with
      | nil => rfl
      | cons entry suffix =>
        have hbehavior := hmarker (entry :: suffix) [] hnil (by simpa using hbound)
        simp only [List.not_mem_nil, false_and, exists_false, if_false] at hbehavior
        change Process (entry :: suffix) [maximum] = Process (entry :: suffix) [] ++ [maximum]
        exact hbehavior
    · simp
  · obtain ⟨minimum, hminimum⟩ := Option.isSome_iff_exists.mp
      (List.isSome_min?_of_ne_nil hprefix)
    obtain ⟨hminmem, hminbound⟩ := List.min?_eq_some_iff.mp hminimum
    obtain ⟨hstackavoid, hstackmin, hpopped, hprefixstate⟩ :=
      snapshot_minimum front [] minimum hnil (by simpa using hminmem)
        (by simpa using hminbound)
    have hstateperm :
        ((snapshot front []).1 ++ (snapshot front []).2).Perm front := by
      rw [← hprefixstate]
      simpa using (process_preserves front [] hnil).1
    have hstackbound : ∀ value ∈ (snapshot front []).2, value < maximum := by
      intro value hvalue
      have hsource := hstateperm.mem_iff.mp (List.mem_append_right _ hvalue)
      exact hbound value (List.mem_append_left _ hsource)
    have hmarkerbound : ∀ value ∈ (snapshot front []).2 ++ suffix, value < maximum := by
      intro value hvalue
      rcases List.mem_append.mp hvalue with hstack | hsuffix
      · exact hstackbound value hstack
      · exact hbound value (List.mem_append_right _ hsuffix)
    have hmaxlegal : ¬ ContainsV (maximum :: (snapshot front []).2) :=
      hcons maximum (snapshot front []).2 hstackavoid hstackbound
    have hpushmax : Push maximum (snapshot front []).2 =
        ([], maximum :: (snapshot front []).2) := by
      cases hstack : (snapshot front []).2 with
      | nil => rfl
      | cons top current => simp only [Push, if_neg (by simpa [hstack] using hmaxlegal)]
    have hinsert : SC (front ++ maximum :: suffix) =
        (snapshot front []).1 ++ Process suffix (maximum :: (snapshot front []).2) := by
      rw [SC, hsplit, Process, hpushmax]
      simp
    have horiginal : SC (front ++ suffix) =
        (snapshot front []).1 ++ Process suffix (snapshot front []).2 := hsplit front suffix []
    have hstatelength := hstateperm.length_eq
    have hpositive : 0 < (snapshot front []).2.length := List.length_pos_of_mem hstackmin
    cases suffix with
    | nil =>
      have horig : SC front = (snapshot front []).1 ++ (snapshot front []).2 := by
        simpa only [List.append_nil, Process] using horiginal
      constructor
      · simp only [outputGap, if_neg hprefix, hinsert, List.append_nil, horig, Process,
          List.take_append_length, List.drop_append_length]
      · simp only [outputGap, if_neg hprefix, List.append_nil]
        intro _
        simp only [List.length_append] at hstatelength
        omega
    | cons entry rest =>
      by_cases htemporary : ∃ lower ∈ (snapshot front []).2, lower < entry
      · have hbehavior := hmarker (entry :: rest) (snapshot front []).2 hstackavoid hmarkerbound
        simp only [htemporary, if_pos] at hbehavior
        constructor
        · simp only [outputGap, if_neg hprefix, if_pos htemporary, hinsert, hbehavior,
            horiginal, List.take_append, List.take_length, Nat.sub_self, List.take_zero,
            List.drop_append, List.drop_length, List.drop_zero, List.append_nil,
            List.nil_append]
        · simp only [outputGap, if_neg hprefix, if_pos htemporary,
            List.length_append, List.length_cons] at ⊢ hstatelength
          intro _
          omega
      · have hbehavior := hmarker (entry :: rest) (snapshot front []).2 hstackavoid hmarkerbound
        simp only [htemporary, if_false] at hbehavior
        have hentryStack : ∀ value ∈ (snapshot front []).2, entry ≤ value :=
          fun value hvalue => Nat.le_of_not_gt
            (fun hless => htemporary ⟨value, hvalue, hless⟩)
        have hlegal : ¬ ContainsV (entry :: (snapshot front []).2) := by
          cases hcurrent : (snapshot front []).2 with
          | nil => simp [hcurrent] at hstackmin
          | cons top current =>
            rw [push_test]
            rintro (hpattern | ⟨_, lower, hlower, hless⟩)
            · exact hstackavoid (by simpa [hcurrent] using hpattern)
            · have := hentryStack lower (by simp [hcurrent, hlower])
              omega
        have hprotected := protected_suffix rest [entry] (snapshot front []).2 entry hlegal
          (by simp) (by simp) hentryStack
        have hpushentry : Push entry (snapshot front []).2 =
            ([], entry :: (snapshot front []).2) := by
          cases hcurrent : (snapshot front []).2 with
          | nil => rfl
          | cons top current => simp only [Push, if_neg (by simpa [hcurrent] using hlegal)]
        have hold : Process (entry :: rest) (snapshot front []).2 =
            Process (entry :: rest) [] ++ (snapshot front []).2 := by
          simpa only [Process, Push, hpushentry, List.nil_append, List.cons_append]
            using hprotected
        have hgap : outputGap front (entry :: rest) =
            ((snapshot front []).1 ++ Process (entry :: rest) []).length := by
          simp only [outputGap, if_neg hprefix, if_neg htemporary,
            List.length_append, List.length_cons]
          have hrunlength := hlength (entry :: rest)
          simp only [SC, List.length_cons] at hrunlength
          simp only [List.length_append] at hstatelength ⊢
          omega
        constructor
        · rw [hinsert, hbehavior, hgap, horiginal, hold]
          simp only [← List.append_assoc, List.take_append_length, List.drop_append_length]
        · simp only [outputGap, if_neg hprefix, if_neg htemporary]
          intro _
          have : 0 < (front ++ entry :: rest).length := by simp
          omega

end D5.S3.Combinatorics.VincularStack.VincularStackMarkers

namespace D5.S3.Combinatorics.VincularStack.VincularStackCuts

open VincularStackDefs VincularStackBasic VincularStackRun VincularStackMarkers

def separatingCut (word : List ℕ) (gap : ℕ) : Prop :=
  ∀ left ∈ word.take gap, ∀ right ∈ word.drop gap, left < right

theorem maximum_cut (front back : List ℕ) (maximum : ℕ)
    (hnodup : (front ++ back).Nodup)
    (hbound : ∀ value ∈ front ++ back, value < maximum) :
    ¬ Contains231 (front ++ maximum :: back) ↔
      ¬ Contains231 (front ++ back) ∧ separatingCut (front ++ back) front.length := by
  let insertIndex (position : ℕ) := if position < front.length then position else position + 1
  let eraseIndex (position : ℕ) := if position < front.length then position else position - 1
  have hinsertRead : ∀ position < (front ++ back).length,
      (front ++ maximum :: back).getD (insertIndex position) 0 =
        (front ++ back).getD position 0 := by
    intro position hposition
    dsimp only [insertIndex]
    split_ifs with hfront
    · rw [List.getD_append front (maximum :: back) 0 position hfront,
        List.getD_append front back 0 position hfront]
    · rw [List.getD_append_right front (maximum :: back) 0 (position + 1) (by omega),
        List.getD_append_right front back 0 position (by omega)]
      have hshift : position + 1 - front.length = (position - front.length) + 1 := by omega
      rw [hshift, List.getD_cons_succ]
  have heraseRead : ∀ position < (front ++ maximum :: back).length,
      position ≠ front.length →
      (front ++ back).getD (eraseIndex position) 0 =
        (front ++ maximum :: back).getD position 0 := by
    intro position hposition hmarker
    dsimp only [eraseIndex]
    split_ifs with hfront
    · rw [List.getD_append front (maximum :: back) 0 position hfront,
        List.getD_append front back 0 position hfront]
    · rw [List.getD_append_right front back 0 (position - 1) (by omega),
        List.getD_append_right front (maximum :: back) 0 position (by omega)]
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le
        (by omega : front.length + 1 ≤ position)
      subst position
      have hleft : front.length + 1 + offset - 1 - front.length = offset := by omega
      have hright : front.length + 1 + offset - front.length = offset + 1 := by omega
      rw [hleft, hright, List.getD_cons_succ]
  have hmaximum : (front ++ maximum :: back).getD front.length 0 = maximum := by
    rw [List.getD_append_right front (maximum :: back) 0 front.length (by omega)]
    simp
  have hnewbound : ∀ position < (front ++ maximum :: back).length,
      (front ++ maximum :: back).getD position 0 ≤ maximum := by
    intro position hposition
    rw [List.getD_eq_getElem _ 0 hposition]
    have hmem := List.getElem_mem hposition
    rcases List.mem_append.mp hmem with hfront | hback
    · exact le_of_lt (hbound _ (List.mem_append_left _ hfront))
    · rcases List.mem_cons.mp hback with heq | hback
      · exact le_of_eq heq
      · exact le_of_lt (hbound _ (List.mem_append_right _ hback))
  constructor
  · intro havoid
    constructor
    · rintro ⟨first, middle, last, hfirst, hmiddle, hlast, hsmall, hlarge⟩
      apply havoid
      refine ⟨insertIndex first, insertIndex middle, insertIndex last, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [insertIndex]
        split_ifs <;> omega
      · dsimp only [insertIndex]
        split_ifs <;> omega
      · dsimp only [insertIndex]
        simp only [List.length_append, List.length_cons] at hlast ⊢
        split_ifs <;> omega
      · rw [hinsertRead last hlast, hinsertRead first (by omega)]
        exact hsmall
      · rw [hinsertRead first (by omega), hinsertRead middle (by omega)]
        exact hlarge
    · simp only [separatingCut, List.take_append_length, List.drop_append_length]
      intro left hleft right hright
      by_contra hcomparison
      have hneq := (List.nodup_append.mp hnodup).2.2 left hleft right hright
      have hless : right < left := by omega
      obtain ⟨first, hfirst, hleftvalue⟩ := List.mem_iff_getElem.mp hleft
      obtain ⟨last, hlast, hrightvalue⟩ := List.mem_iff_getElem.mp hright
      apply havoid
      refine ⟨first, front.length, front.length + last + 1, hfirst, by omega,
        by simp; omega, ?_, ?_⟩
      · rw [List.getD_append_right front (maximum :: back) 0
          (front.length + last + 1) (by omega),
          List.getD_append front (maximum :: back) 0 first hfirst]
        have hshift : front.length + last + 1 - front.length = last + 1 := by omega
        rw [hshift, List.getD_cons_succ, List.getD_eq_getElem back 0 hlast,
          List.getD_eq_getElem front 0 hfirst, hleftvalue, hrightvalue]
        exact hless
      · rw [hmaximum, List.getD_append front (maximum :: back) 0 first hfirst,
          List.getD_eq_getElem front 0 hfirst, hleftvalue]
        exact hbound left (List.mem_append_left _ hleft)
  · rintro ⟨holdavoid, hcut⟩ ⟨first, middle, last, hfirst, hmiddle, hlast, hsmall, hlarge⟩
    have hfirstmarker : first ≠ front.length := by
      intro heq
      rw [heq, hmaximum] at hlarge
      have := hnewbound middle (by omega)
      omega
    have hlastmarker : last ≠ front.length := by
      intro heq
      rw [heq, hmaximum] at hsmall
      have := hnewbound first (by omega)
      omega
    by_cases hmiddlemarker : middle = front.length
    · subst middle
      have hleftmem : (front ++ maximum :: back).getD first 0 ∈ front := by
        rw [List.getD_append front (maximum :: back) 0 first hfirst,
          List.getD_eq_getElem front 0 hfirst]
        exact List.getElem_mem hfirst
      have hrightmem : (front ++ maximum :: back).getD last 0 ∈ back := by
        rw [List.getD_append_right front (maximum :: back) 0 last (by omega)]
        obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le
          (by omega : front.length + 1 ≤ last)
        subst last
        have hoffsetbound : offset < back.length := by
          simp only [List.length_append, List.length_cons] at hlast
          omega
        have hshift : front.length + 1 + offset - front.length = offset + 1 := by omega
        rw [hshift, List.getD_cons_succ, List.getD_eq_getElem back 0 hoffsetbound]
        exact List.getElem_mem hoffsetbound
      simp only [separatingCut, List.take_append_length, List.drop_append_length] at hcut
      have := hcut _ hleftmem _ hrightmem
      omega
    · apply holdavoid
      refine ⟨eraseIndex first, eraseIndex middle, eraseIndex last, ?_, ?_, ?_, ?_, ?_⟩
      · dsimp only [eraseIndex]
        split_ifs <;> omega
      · dsimp only [eraseIndex]
        split_ifs <;> omega
      · dsimp only [eraseIndex]
        simp only [List.length_append, List.length_cons] at hlast ⊢
        split_ifs <;> omega
      · rw [heraseRead last hlast hlastmarker, heraseRead first (by omega) hfirstmarker]
        exact hsmall
      · rw [heraseRead first (by omega) hfirstmarker,
          heraseRead middle (by omega) hmiddlemarker]
        exact hlarge

end D5.S3.Combinatorics.VincularStack.VincularStackCuts
