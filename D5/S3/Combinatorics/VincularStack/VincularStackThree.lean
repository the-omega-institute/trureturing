/- GID: D5/S3/Combinatorics/VincularStack/VincularStackThree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VincularStack/VincularStackThree
   mirror-E: none(waiver:three-stack-sorting-class-equality)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Coupled retries either agree or permanently force 231 in both outputs. -/

import D5.S3.Combinatorics.VincularStack.VincularStackThreeDivergence
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VincularStack.VincularStackThree

open VincularStackThreeDefs VincularStackThreeBasic VincularStackThreeDivergence
open VincularStackDefs (Contains231)
open scoped List

theorem result : VincularStackThreeDefs.claim := by
  have hclassical : ∀ adj31 adj12 : Bool, ∀ word : List ℕ,
      Contains312 adj31 adj12 word → Contains312 false false word := by
    rintro adj31 adj12 word
      ⟨first, hfirst, middle, hmiddle, last, hlast, hfm, hml, hlower, hupper, _, _⟩
    exact ⟨first, hfirst, middle, hmiddle, last, hlast, hfm, hml, hlower, hupper,
      by simp, by simp⟩
  have hnil : ∀ adj31 adj12 : Bool, ¬ Contains312 adj31 adj12 [] := by
    rintro adj31 adj12 ⟨first, hfirst, _⟩
    simp at hfirst
  have hmono : ∀ small large : List ℕ, small <+ large →
      Contains231 small → Contains231 large := by
    intro small large hsub hpattern
    obtain ⟨embedding, hread⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    obtain ⟨first, middle, last, hfm, hml, hlast, hlower, hupper⟩ := hpattern
    let firstIndex : Fin small.length := ⟨first, by omega⟩
    let middleIndex : Fin small.length := ⟨middle, by omega⟩
    let lastIndex : Fin small.length := ⟨last, hlast⟩
    have hvalue : ∀ position : Fin small.length,
        small.getD position 0 = large.getD (embedding position) 0 := by
      intro position
      rw [List.getD_eq_get small 0 position, List.getD_eq_get large 0 (embedding position)]
      exact hread position
    refine ⟨(embedding firstIndex).val, (embedding middleIndex).val,
      (embedding lastIndex).val, embedding.strictMono (show firstIndex < middleIndex from hfm),
      embedding.strictMono (show middleIndex < lastIndex from hml),
      (embedding lastIndex).isLt, ?_, ?_⟩
    · rw [← hvalue lastIndex, ← hvalue firstIndex]
      exact hlower
    · rw [← hvalue firstIndex, ← hvalue middleIndex]
      exact hupper
  have hpushA : ∀ entry : ℕ, ∀ stack : List ℕ, (entry :: stack).Nodup →
      Push false false entry stack = Push true false entry stack := by
    intro entry stack
    induction stack with
    | nil => intro hnodup; rfl
    | cons top stack inductionHypothesis =>
      intro hnodup
      have htest := classical_adjacent (entry :: top :: stack) hnodup
      have htail : (entry :: stack).Nodup :=
        hnodup.sublist ((List.sublist_cons_self top stack).cons_cons entry)
      by_cases hillegal : Contains312 false false (entry :: top :: stack)
      · have hillegalA := htest.mp hillegal
        simp only [Push, if_pos hillegal, if_pos hillegalA]
        rw [inductionHypothesis htail]
      · have hlegalA : ¬ Contains312 true false (entry :: top :: stack) :=
          fun hpattern => hillegal (htest.mpr hpattern)
        simp only [Push, if_neg hillegal, if_neg hlegalA]
  have hprocessA : ∀ input stack : List ℕ, (input ++ stack).Nodup →
      ¬ Contains312 false false stack →
      Process false false input stack = Process true false input stack := by
    intro input
    induction input with
    | nil => intro stack hnodup havoid; rfl
    | cons entry input inductionHypothesis =>
      intro stack hnodup havoid
      have hxstack : (entry :: stack).Nodup :=
        hnodup.sublist ((List.sublist_append_right input stack).cons_cons entry)
      obtain ⟨hfinal, hperm, _⟩ := push_preserves false false entry stack havoid
      have hsource : (input ++ entry :: stack).Nodup :=
        List.perm_middle.nodup_iff.mpr hnodup
      have hnext : (input ++ (Push false false entry stack).2).Nodup :=
        ((List.Perm.append_left input hperm).nodup_iff.mpr hsource).sublist
          ((List.sublist_append_right (Push false false entry stack).1
            (Push false false entry stack).2).append_left input)
      simp only [Process]
      rw [← hpushA entry stack hxstack,
        inductionHypothesis (Push false false entry stack).2 hnext hfinal]
  have hpushCouple : ∀ entry : ℕ, ∀ stack : List ℕ, (entry :: stack).Nodup →
      ¬ Contains312 false false stack →
      Push false false entry stack = Push false true entry stack ∨
        Contains231 ((Push false false entry stack).1 ++ (Push false false entry stack).2) ∧
        Contains231 ((Push false true entry stack).1 ++ (Push false true entry stack).2) := by
    intro entry stack
    induction stack with
    | nil => intro hnodup havoid; exact Or.inl rfl
    | cons top stack inductionHypothesis =>
      intro hnodup havoid
      have htail : ¬ Contains312 false false stack := by
        rintro ⟨first, hfirst, middle, hmiddle, last, hlast, hfm, hml, hlower, hupper, _, _⟩
        apply havoid
        exact ⟨first + 1, by simpa using hfirst, middle + 1, by simpa using hmiddle,
          last + 1, by simpa using hlast, by omega, by omega, by simpa using hlower,
          by simpa using hupper, by simp, by simp⟩
      have htailnodup : (entry :: stack).Nodup :=
        hnodup.sublist ((List.sublist_cons_self top stack).cons_cons entry)
      by_cases hillegal : Contains312 false false (entry :: top :: stack)
      · by_cases hillegalB : Contains312 false true (entry :: top :: stack)
        · rcases inductionHypothesis htailnodup htail with hequal | ⟨hbadC, hbadB⟩
          · left
            simp only [Push, if_pos hillegal, if_pos hillegalB]
            rw [hequal]
          · right
            constructor
            · simpa only [Push, if_pos hillegal, List.cons_append] using
                hmono _ _ (List.sublist_cons_self top _) hbadC
            · simpa only [Push, if_pos hillegalB, List.cons_append] using
                hmono _ _ (List.sublist_cons_self top _) hbadB
        · obtain ⟨popped, high, tail, low, _, _, _, _, _, _, hpushC, hpushB, hbadC, hbadB⟩ :=
            divergence entry (top :: stack) hnodup havoid hillegal hillegalB
          right
          constructor
          · rw [hpushC]
            exact hmono _ _ (List.sublist_append_right popped _) hbadC
          · rw [hpushB]
            simpa only [List.nil_append] using hbadB
      · have hlegalB : ¬ Contains312 false true (entry :: top :: stack) :=
          fun hpattern => hillegal (hclassical false true _ hpattern)
        left
        simp only [Push, if_neg hillegal, if_neg hlegalB]
  have hprocessCouple : ∀ input stack : List ℕ, (input ++ stack).Nodup →
      ¬ Contains312 false false stack →
      Process false false input stack = Process false true input stack ∨
        Contains231 (Process false false input stack) ∧
        Contains231 (Process false true input stack) := by
    intro input
    induction input with
    | nil => intro stack hnodup havoid; exact Or.inl rfl
    | cons entry input inductionHypothesis =>
      intro stack hnodup havoid
      have hxstack : (entry :: stack).Nodup :=
        hnodup.sublist ((List.sublist_append_right input stack).cons_cons entry)
      have hdataC := push_preserves false false entry stack havoid
      have havoidB : ¬ Contains312 false true stack :=
        fun hpattern => havoid (hclassical false true stack hpattern)
      have hdataB := push_preserves false true entry stack havoidB
      rcases hpushCouple entry stack hxstack havoid with hequal | ⟨hbadC, hbadB⟩
      · have hsource : (input ++ entry :: stack).Nodup :=
          List.perm_middle.nodup_iff.mpr hnodup
        have hnext : (input ++ (Push false false entry stack).2).Nodup :=
          ((List.Perm.append_left input hdataC.2.1).nodup_iff.mpr hsource).sublist
            ((List.sublist_append_right (Push false false entry stack).1
              (Push false false entry stack).2).append_left input)
        rcases inductionHypothesis (Push false false entry stack).2 hnext hdataC.1 with
          hsame | ⟨hbadC, hbadB⟩
        · left
          simp only [Process]
          rw [← hequal, hsame]
        · right
          simp only [Process]
          rw [← hequal]
          exact ⟨hmono _ _ (List.sublist_append_right _ _) hbadC,
            hmono _ _ (List.sublist_append_right _ _) hbadB⟩
      · have hretainC :=
          (process_preserves false false input (Push false false entry stack).2 hdataC.1).2
        have hretainB :=
          (process_preserves false true input (Push false true entry stack).2 hdataB.1).2
        right
        exact ⟨hmono _ _ (hretainC.append_left _) hbadC,
          hmono _ _ (hretainB.append_left _) hbadB⟩
  have hglobalA : ∀ word : List ℕ, word.Nodup → SC false false word = SC true false word := by
    intro word hnodup
    exact hprocessA word [] (by simpa using hnodup) (hnil false false)
  have hglobalB : ∀ word : List ℕ, word.Nodup →
      SC false false word = SC false true word ∨
        Contains231 (SC false false word) ∧ Contains231 (SC false true word) := by
    intro word hnodup
    exact hprocessCouple word [] (by simpa using hnodup) (hnil false false)
  intro size hsize
  have hnd : ∀ word : List ℕ, word.Perm (List.range' 1 size) → word.Nodup := by
    intro word hperm
    exact hperm.nodup_iff.mpr List.nodup_range'
  refine ⟨?_, ?_, ?_⟩
  · apply Set.ext
    intro word
    change (word.Perm (List.range' 1 size) ∧ ¬ Contains231 (SC false false word)) ↔
      (word.Perm (List.range' 1 size) ∧ ¬ Contains231 (SC true false word))
    constructor
    · rintro ⟨hperm, havoid⟩
      exact ⟨hperm, by rwa [← hglobalA word (hnd word hperm)]⟩
    · rintro ⟨hperm, havoid⟩
      exact ⟨hperm, by rwa [hglobalA word (hnd word hperm)]⟩
  · apply Set.ext
    intro word
    change (word.Perm (List.range' 1 size) ∧ ¬ Contains231 (SC false false word)) ↔
      (word.Perm (List.range' 1 size) ∧ ¬ Contains231 (SC false true word))
    constructor
    · rintro ⟨hperm, havoid⟩
      rcases hglobalB word (hnd word hperm) with hequal | hbad
      · exact ⟨hperm, by rwa [← hequal]⟩
      · exact False.elim (havoid hbad.1)
    · rintro ⟨hperm, havoid⟩
      rcases hglobalB word (hnd word hperm) with hequal | hbad
      · exact ⟨hperm, by rwa [hequal]⟩
      · exact False.elim (havoid hbad.2)
  · intro word hmember
    obtain ⟨hperm, havoid⟩ := hmember
    refine ⟨hglobalA word (hnd word hperm), ?_⟩
    rcases hglobalB word (hnd word hperm) with hequal | hbad
    · exact hequal
    · exact False.elim (havoid hbad.1)


end D5.S3.Combinatorics.VincularStack.VincularStackThree
