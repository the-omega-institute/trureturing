/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenBTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenBTree
   mirror-E: none(waiver:classical-b-generating-tree-classification)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Maximum deletion classifies B with the increasing-piece invariant at end-active nodes. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenBTransitions
import D5.S3.Combinatorics.Fishburn.FishburnBasicClassicalParents
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenBTree

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs
open FishburnTenTenBTransitions FishburnBasicClassicalParents

inductive BType (n : ℕ) where
  | increasing
  | adjacent (cut : Fin (n - 1))
  | persistent (cut : Fin (n - 2))
  | terminal (cut : Fin (n - 1))

def BSpec (n : ℕ) (p : List ℕ) : BType n → Prop :=
  let split := fun cut =>
    (∀ first second, first < second → second < cut →
      p.getD first 0 < p.getD second 0) ∧
    (∀ first second, cut ≤ first → first < second → second < n →
      p.getD first 0 < p.getD second 0) ∧
    p.getD cut 0 < p.getD (cut - 1) 0
  fun label => match label with
  | .increasing => p = List.range' 1 n ∧ ∀ gap, gap ≤ n →
      p.insertIdx gap (n + 1) ∈
        classicalAvoiders (n + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]]
  | .adjacent cut => (cut.val + 2 = n → split (cut.val + 1)) ∧
      ∀ gap, gap ≤ n → (p.insertIdx gap (n + 1) ∈
        classicalAvoiders (n + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] ↔
          gap = cut.val + 1 ∨ gap = cut.val + 2)
  | .persistent cut => split (cut.val + 1) ∧
      ∀ gap, gap ≤ n → (p.insertIdx gap (n + 1) ∈
        classicalAvoiders (n + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] ↔
          gap = cut.val + 1 ∨ gap = n)
  | .terminal cut => ∀ gap, gap ≤ n → (p.insertIdx gap (n + 1) ∈
      classicalAvoiders (n + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] ↔
        gap = cut.val + 1)

set_option maxHeartbeats 1600000 in
theorem b_classification (n : ℕ) (p : List ℕ)
    (hmember : p ∈ classicalAvoiders n [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]]) :
    ∃ label : BType n, BSpec n p label := by
  induction n generalizing p with
  | zero =>
    have heq : p = [] := List.perm_nil.mp hmember.1
    subst p
    refine ⟨.increasing, rfl, ?_⟩
    intro gap hg
    have hz : gap = 0 := by omega
    subst gap
    refine ⟨by simp, ?_⟩
    intro pattern hp hocc
    obtain ⟨values, _, _, hsub, _⟩ := hocc
    have hl := hsub.length_le
    simp only [List.length_map, List.insertIdx_zero, List.length_cons,
      List.length_nil] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp at hl
  | succ size ih =>
    obtain ⟨entry, hentry⟩ := (classical_maximum_insertion_bijection size
      [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]]).2 ⟨p, hmember⟩
    have heq : entry.val.1.insertIdx entry.val.2 (size + 1) = p :=
      congrArg Subtype.val hentry
    rcases entry with ⟨⟨parent, site⟩, hparent, hsite, hactive⟩
    dsimp only at hparent hsite hactive heq
    subst p
    have hlen : parent.length = size := by simpa using hparent.1.length_eq
    have hsb : site ≤ size := by omega
    let child := parent.insertIdx site (size + 1)
    have hclen : child.length = size + 1 := by
      rw [List.length_insertIdx_of_le_length hsite, hlen]
    have hbound (index : ℕ) (hi : index < size) : parent.getD index 0 ≤ size := by
      have hm : parent.getD index 0 ∈ parent := by
        rw [List.getD_eq_getElem parent 0 (by omega)]
        exact List.getElem_mem _
      have hr := hparent.1.mem_iff.mp hm
      simp only [List.mem_range'_1] at hr
      omega
    have hbefore (index : ℕ) (hi : index < site) :
        child.getD index 0 = parent.getD index 0 := by
      rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
        List.getD_eq_getElem parent 0 (by omega)]
    have hat : child.getD site 0 = size + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]
      exact List.getElem_insertIdx_self _
    have hafter (index : ℕ) (hi : site < index) (hb : index < size + 1) :
        child.getD index 0 = parent.getD (index - 1) 0 := by
      rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_gt hi,
        List.getD_eq_getElem parent 0 (by omega)]
    have hinternalSplit (hi : site < size)
        (hpref : ∀ first second, first < second → second < site →
          parent.getD first 0 < parent.getD second 0)
        (hsuff : ∀ first second, site ≤ first → first < second → second < size →
          parent.getD first 0 < parent.getD second 0) :
        (∀ first second, first < second → second < site + 1 →
          child.getD first 0 < child.getD second 0) ∧
        (∀ first second, site + 1 ≤ first → first < second → second < size + 1 →
          child.getD first 0 < child.getD second 0) ∧
        child.getD (site + 1) 0 < child.getD site 0 := by
      refine ⟨?_, ?_, ?_⟩
      · intro first second hfs hs
        by_cases he : second = site
        · subst second
          rw [hbefore first hfs, hat]
          have := hbound first (by omega)
          omega
        · rw [hbefore first (by omega), hbefore second (by omega)]
          exact hpref first second hfs (by omega)
      · intro first second hf hfs hs
        rw [hafter first (by omega) (by omega), hafter second (by omega) hs]
        exact hsuff (first - 1) (second - 1) (by omega) (by omega) (by omega)
      · rw [hafter (site + 1) (by omega) (by omega), hat, Nat.add_sub_cancel]
        have := hbound site hi
        omega
    have happendSplit (he : site = size) (cut : ℕ) (hc : 0 < cut) (hcut : cut < size)
        (hsplit : (∀ first second, first < second → second < cut →
          parent.getD first 0 < parent.getD second 0) ∧
          (∀ first second, cut ≤ first → first < second → second < size →
            parent.getD first 0 < parent.getD second 0) ∧
          parent.getD cut 0 < parent.getD (cut - 1) 0) :
        ((∀ first second, first < second → second < cut →
          child.getD first 0 < child.getD second 0) ∧
          (∀ first second, cut ≤ first → first < second → second < size + 1 →
            child.getD first 0 < child.getD second 0) ∧
          child.getD cut 0 < child.getD (cut - 1) 0) ∧
        ∀ gap, gap ≤ size + 1 → (child.insertIdx gap (size + 2) ∈
          classicalAvoiders (size + 2) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] ↔
            gap = cut ∨ gap = size + 1) := by
      have hpieces (gap : ℕ) (hg : gap ≤ size) :
          ((∀ first second, first < second → second < gap →
            parent.getD first 0 < parent.getD second 0) ∧
            (∀ first second, gap ≤ first → first < second → second < size →
              parent.getD first 0 < parent.getD second 0)) ↔ gap = cut := by
        constructor
        · rintro ⟨hleft, hright⟩
          have hd := hsplit.2.2
          by_cases hl : gap < cut
          · have := hright (cut - 1) cut (by omega) (by omega) hcut
            omega
          · by_cases hr : cut < gap
            · have := hleft (cut - 1) cut (by omega) hr
              omega
            · omega
        · intro heq
          subst gap
          exact ⟨hsplit.1, hsplit.2.1⟩
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro first second hfs hs
        rw [hbefore first (by omega), hbefore second (by omega)]
        exact hsplit.1 first second hfs hs
      · intro first second hf hfs hs
        by_cases hb : second < size
        · rw [hbefore first (by omega), hbefore second (by omega)]
          exact hsplit.2.1 first second hf hfs hb
        · have hs : second = site := by omega
          subst second
          rw [hbefore first hfs, hat]
          have := hbound first (by omega)
          omega
      · rw [hbefore cut (by omega), hbefore (cut - 1) (by omega)]
        exact hsplit.2.2
      · intro gap hg
        have ht := b_append_transition size parent hparent
          (by simpa only [he] using hactive) gap hg
        change child.insertIdx gap (size + 2) ∈ _ ↔ _
        dsimp [child]
        rw [he, ht]
        constructor
        · rintro (hlast | ⟨hb, hp, hs⟩)
          · exact Or.inr hlast
          · exact Or.inl ((hpieces gap hb).mp ⟨hp, hs⟩)
        · rintro (hcutEq | hlast)
          · refine Or.inr ⟨by omega, ?_⟩
            exact (hpieces gap (by omega)).mpr hcutEq
          · exact Or.inl hlast
    obtain ⟨label, hlabel⟩ := ih parent hparent
    cases label with
    | increasing =>
      obtain ⟨hp, hsites⟩ := hlabel
      have hinc (first second : ℕ) (hfs : first < second) (hs : second < size) :
          parent.getD first 0 < parent.getD second 0 := by
        rw [hp, List.getD_eq_getElem _ 0 (by simp; omega),
          List.getD_eq_getElem _ 0 (by simp; omega),
          List.getElem_range', List.getElem_range']
        simp only [Nat.one_mul]
        omega
      by_cases he : site = size
      · refine ⟨.increasing, ?_, ?_⟩
        · rw [he, hp]
          simpa only [List.length_range', List.range'_concat, Nat.one_mul,
            Nat.add_comm] using
            (List.insertIdx_length_self (l := List.range' 1 size) (x := size + 1))
        · intro gap hg
          rw [he, b_append_transition size parent hparent
            (by simpa only [he] using hactive) gap hg]
          by_cases hl : gap = size + 1
          · exact Or.inl hl
          · exact Or.inr ⟨by omega, fun first second hfs hs =>
              hinc first second hfs (by omega), fun first second _ hfs hs =>
              hinc first second hfs hs⟩
      · have hi : site < size := by omega
        refine ⟨.adjacent ⟨site, by omega⟩, ?_, ?_⟩
        · intro _
          simpa using hinternalSplit hi
            (fun first second hfs hs => hinc first second hfs (by omega))
            (fun first second _ hfs hs => hinc first second hfs hs)
        · intro gap hg
          rw [b_internal_transition size parent hparent site hi hactive gap hg]
          simp only [hsites (site + 1) (by omega), and_true]
    | adjacent cut =>
      obtain ⟨hsplit, hsites⟩ := hlabel
      have hc := cut.is_lt
      have hslot := (hsites site hsb).mp hactive
      rcases hslot with he | he
      · have hi : site < size := by omega
        refine ⟨.adjacent ⟨site, by omega⟩, ?_, ?_⟩
        · intro hterminal
          change site + 2 = size + 1 at hterminal
          have hb : cut.val + 2 = size := by omega
          obtain ⟨hpref, hsuff, _⟩ := hsplit hb
          apply hinternalSplit hi
          · simpa only [he] using hpref
          · simpa only [he] using hsuff
        · intro gap hg
          rw [b_internal_transition size parent hparent site hi hactive gap hg]
          have hnext := (hsites (site + 1) (by omega)).mpr (Or.inr (by omega))
          simp only [hnext, and_true]
      · by_cases happ : site = size
        · refine ⟨.persistent ⟨cut.val, by omega⟩, ?_⟩
          exact happendSplit happ (cut.val + 1) (by omega) (by omega)
            (hsplit (by omega))
        · have hi : site < size := by omega
          refine ⟨.terminal ⟨site, by omega⟩, ?_⟩
          intro gap hg
          rw [b_internal_transition size parent hparent site hi hactive gap hg]
          have hnot : parent.insertIdx (site + 1) (size + 1) ∉
              classicalAvoiders (size + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] := by
            intro hh
            have := (hsites (site + 1) (by omega)).mp hh
            omega
          simp only [hnot, and_false, or_false]
    | persistent cut =>
      obtain ⟨hsplit, hsites⟩ := hlabel
      have hc := cut.is_lt
      rcases (hsites site hsb).mp hactive with he | he
      · have hi : site < size := by omega
        refine ⟨.terminal ⟨site, by omega⟩, ?_⟩
        intro gap hg
        rw [b_internal_transition size parent hparent site hi hactive gap hg]
        have hnot : parent.insertIdx (site + 1) (size + 1) ∉
            classicalAvoiders (size + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] := by
          intro hh
          have := (hsites (site + 1) (by omega)).mp hh
          omega
        simp only [hnot, and_false, or_false]
      · refine ⟨.persistent ⟨cut.val, by omega⟩, ?_⟩
        exact happendSplit he (cut.val + 1) (by omega) (by omega) hsplit
    | terminal cut =>
      have hc := cut.is_lt
      have he := (hlabel site hsb).mp hactive
      have hi : site < size := by omega
      refine ⟨.terminal ⟨site, by omega⟩, ?_⟩
      intro gap hg
      rw [b_internal_transition size parent hparent site hi hactive gap hg]
      have hnot : parent.insertIdx (site + 1) (size + 1) ∉
          classicalAvoiders (size + 1) [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]] := by
        intro hh
        have := (hlabel (site + 1) (by omega)).mp hh
        omega
      simp only [hnot, and_false, or_false]

end D5.S3.Combinatorics.Fishburn.FishburnTenTenBTree
