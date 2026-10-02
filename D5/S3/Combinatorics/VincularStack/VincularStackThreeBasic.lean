/- GID: D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackThreeBasic
   mirror-E: none(waiver:three-stack-transition-invariants)
   anchors: [mathlib/module/Mathlib.Data.List.Nodup, mathlib/module/Mathlib.Data.List.GetD]
   utility: none
   digest: Adjacent descent witnesses and recursive transitions preserve stack order and letters. -/

import D5.S3.Combinatorics.VincularStack.VincularStackThreeDefs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackThreeBasic

open VincularStackThreeDefs
open scoped List

theorem classical_adjacent (word : List ℕ) (hnodup : word.Nodup) :
    Contains312 false false word ↔ Contains312 true false word := by
  have hscan : ∀ distance first middle last : ℕ,
      middle - first = distance → first < middle → middle < last → last < word.length →
      word.getD middle 0 < word.getD last 0 → word.getD last 0 < word.getD first 0 →
      Contains312 true false word := by
    intro distance
    induction distance using Nat.strong_induction_on with
    | h distance inductionHypothesis =>
      intro first middle last hdistance hfirst hmiddle hlast hlower hupper
      by_cases hadjacent : middle = first + 1
      · exact ⟨first, by omega, middle, by omega, last, hlast, hfirst, hmiddle,
          hlower, hupper, fun _ => hadjacent, by simp⟩
      · have hnext : first + 1 < middle := by omega
        have hne : word.getD (first + 1) 0 ≠ word.getD last 0 := by
          rw [List.getD_eq_getElem word 0 (by omega),
            List.getD_eq_getElem word 0 hlast]
          exact fun heq => (by omega : first + 1 ≠ last)
            ((hnodup.getElem_inj_iff).mp heq)
        rcases lt_or_gt_of_ne hne with hbelow | habove
        · exact ⟨first, by omega, first + 1, by omega, last, hlast, by omega,
            by omega, hbelow, hupper, by simp, by simp⟩
        · exact inductionHypothesis (middle - (first + 1)) (by omega)
            (first + 1) middle last rfl hnext hmiddle hlast hlower habove
  constructor
  · rintro ⟨first, hfirst, middle, hmiddle, last, hlast, hfm, hml, hlower, hupper, _, _⟩
    exact hscan (middle - first) first middle last rfl hfm hml hlast hlower hupper
  · rintro ⟨first, hfirst, middle, hmiddle, last, hlast, hfm, hml, hlower, hupper, _, _⟩
    exact ⟨first, hfirst, middle, hmiddle, last, hlast, hfm, hml, hlower, hupper,
      by simp, by simp⟩

theorem push_preserves (adj31 adj12 : Bool) (entry : ℕ) (stack : List ℕ)
    (havoid : ¬ Contains312 adj31 adj12 stack) :
    ¬ Contains312 adj31 adj12 (Push adj31 adj12 entry stack).2 ∧
      ((Push adj31 adj12 entry stack).1 ++ (Push adj31 adj12 entry stack).2).Perm
        (entry :: stack) ∧
      stack <+ (Push adj31 adj12 entry stack).1 ++ (Push adj31 adj12 entry stack).2 := by
  induction stack with
  | nil =>
    have hshort : ¬ Contains312 adj31 adj12 [entry] := by
      rintro ⟨first, hfirst, middle, hmiddle, last, hlast, hfm, hml, _⟩
      simp only [List.length_cons, List.length_nil] at hfirst hmiddle hlast
      omega
    exact ⟨hshort, List.Perm.refl _, List.nil_sublist _⟩
  | cons top stack inductionHypothesis =>
    have htail : ¬ Contains312 adj31 adj12 stack := by
      rintro ⟨first, hfirst, middle, hmiddle, last, hlast, hfm, hml, hlower, hupper,
        hadj31, hadj12⟩
      apply havoid
      refine ⟨first + 1, by simpa using hfirst, middle + 1, by simpa using hmiddle,
        last + 1, by simpa using hlast, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · simpa using hlower
      · simpa using hupper
      · intro hflag; have := hadj31 hflag; omega
      · intro hflag; have := hadj12 hflag; omega
    by_cases hillegal : Contains312 adj31 adj12 (entry :: top :: stack)
    · obtain ⟨hfinal, hperm, hretained⟩ := inductionHypothesis htail
      simp only [Push, if_pos hillegal, List.cons_append]
      exact ⟨hfinal, (hperm.cons top).trans (List.Perm.swap entry top stack),
        hretained.cons_cons top⟩
    · simp only [Push, if_neg hillegal, List.nil_append]
      exact ⟨hillegal, List.Perm.refl _, List.sublist_cons_self _ _⟩

theorem process_preserves (adj31 adj12 : Bool) (input stack : List ℕ)
    (havoid : ¬ Contains312 adj31 adj12 stack) :
    (Process adj31 adj12 input stack).Perm (input ++ stack) ∧
      stack <+ Process adj31 adj12 input stack := by
  induction input generalizing stack with
  | nil => exact ⟨List.Perm.refl _, List.Sublist.refl _⟩
  | cons entry input inductionHypothesis =>
    obtain ⟨hfinal, hpushperm, hpushretained⟩ :=
      push_preserves adj31 adj12 entry stack havoid
    obtain ⟨hrunperm, hrunretained⟩ :=
      inductionHypothesis (Push adj31 adj12 entry stack).2 hfinal
    simp only [Process]
    refine ⟨?_, hpushretained.trans (hrunretained.append_left _)⟩
    calc
      (Push adj31 adj12 entry stack).1 ++
          Process adj31 adj12 input (Push adj31 adj12 entry stack).2
          ~ (Push adj31 adj12 entry stack).1 ++
            (input ++ (Push adj31 adj12 entry stack).2) :=
        List.Perm.append_left _ hrunperm
      _ ~ input ++ ((Push adj31 adj12 entry stack).1 ++
          (Push adj31 adj12 entry stack).2) := List.perm_append_comm_assoc _ _ _
      _ ~ input ++ (entry :: stack) := List.Perm.append_left _ hpushperm
      _ ~ (entry :: input) ++ stack := List.perm_middle

end D5.S3.Combinatorics.VincularStack.VincularStackThreeBasic
