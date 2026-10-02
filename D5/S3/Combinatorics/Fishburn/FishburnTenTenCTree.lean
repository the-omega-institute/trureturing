/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenCTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenCTree
   mirror-E: none(waiver:classical-c-generating-tree-classification)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Maximum deletion gives the complete four-type classical C generating tree. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenCTransitions
import D5.S3.Combinatorics.Fishburn.FishburnBasicClassicalParents
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenCTree

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs
open FishburnTenTenCTransitions FishburnBasicClassicalParents

inductive CType (n : ℕ) where
  | increasing
  | persistent (cut : Fin (n - 1))
  | delayed (cut : Fin (n - 2))
  | terminal (cut : Fin n)

def CSpec (n : ℕ) (p : List ℕ) : CType n → Prop
  | .increasing => p = List.range' 1 n ∧ ∀ gap, gap ≤ n →
      p.insertIdx gap (n + 1) ∈
        classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]]
  | .persistent cut => p ≠ List.range' 1 n ∧
      (∀ first second, first < second → second < cut.val →
        p.getD first 0 < p.getD second 0) ∧
      ∀ gap, gap ≤ n → (p.insertIdx gap (n + 1) ∈
        classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] ↔
          gap = cut.val ∨ gap = n)
  | .delayed cut => p ≠ List.range' 1 n ∧ ∀ gap, gap ≤ n →
      (p.insertIdx gap (n + 1) ∈
        classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] ↔
          gap = cut.val ∨ gap = n - 1)
  | .terminal cut => ∀ gap, gap ≤ n → (p.insertIdx gap (n + 1) ∈
      classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] ↔
        gap = cut.val)

set_option maxHeartbeats 1600000 in
theorem c_classification (n : ℕ) (p : List ℕ)
    (hmember : p ∈ classicalAvoiders n [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]]) :
    ∃! label : CType n, CSpec n p label := by
  have hinc (size : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 size))
      (hprefix : ∀ first second, first < second → second < size →
        word.getD first 0 < word.getD second 0) : word = List.range' 1 size := by
    have hlen : word.length = size := by simpa using hp.length_eq
    have hsorted : word.Pairwise (· < ·) := by
      apply List.pairwise_iff_getElem.mpr
      intro first second hf hs hfs
      have hh := hprefix first second hfs (by omega)
      simpa only [List.getD_eq_getElem word 0 hf, List.getD_eq_getElem word 0 hs] using hh
    exact hp.eq_of_pairwise (by intro first second hfs hsf; omega)
      hsorted List.pairwise_lt_range'
  have hexists : ∀ size, ∀ word ∈
      classicalAvoiders size [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]],
      ∃ label : CType size, CSpec size word label := by
    intro size
    induction size with
    | zero =>
      intro word hword
      have heq : word = [] := List.perm_nil.mp hword.1
      subst word
      refine ⟨.increasing, rfl, ?_⟩
      intro gap hgap
      have hz : gap = 0 := by omega
      subst gap
      refine ⟨by simp, ?_⟩
      intro pattern hpattern hocc
      obtain ⟨values, _, _, hsub, _⟩ := hocc
      have hlength := hsub.length_le
      simp only [List.length_map, List.insertIdx_zero, List.length_cons,
        List.length_nil] at hlength
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl <;> simp at hlength
    | succ size ih =>
      intro word hword
      obtain ⟨entry, hentry⟩ := (classical_maximum_insertion_bijection size
        [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]]).2 ⟨word, hword⟩
      have heq : entry.val.1.insertIdx entry.val.2 (size + 1) = word :=
        congrArg Subtype.val hentry
      rcases entry with ⟨⟨parent, site⟩, hparent, hsite, hactive⟩
      dsimp only at hparent hsite hactive heq
      subst word
      have hlen : parent.length = size := by simpa using hparent.1.length_eq
      have hsitebound : site ≤ size := by omega
      let child := parent.insertIdx site (size + 1)
      have hchildlen : child.length = size + 1 := by
        rw [List.length_insertIdx_of_le_length hsite, hlen]
      have hbefore (index : ℕ) (hi : index < site) :
          child.getD index 0 = parent.getD index 0 := by
        rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
          List.getD_eq_getElem parent 0 (by omega)]
      have hnoninc (hi : site < size) : child ≠ List.range' 1 (size + 1) := by
        intro heq
        have hat : child.getD site 0 = size + 1 := by
          rw [List.getD_eq_getElem child 0 (by omega)]
          exact List.getElem_insertIdx_self _
        rw [heq, List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'] at hat
        simp only [Nat.one_mul] at hat
        omega
      have hnoninc_append (hp : parent ≠ List.range' 1 size) (hs : site = size) :
          child ≠ List.range' 1 (size + 1) := by
        intro heq
        apply hp
        apply hinc size parent hparent.1
        intro first second hfs hb
        have hfirst := hbefore first (by omega)
        have hsecond := hbefore second (by omega)
        rw [heq, List.getD_eq_getElem _ 0 (by simp; omega),
          List.getElem_range'] at hfirst hsecond
        simp only [Nat.one_mul] at hfirst hsecond
        omega
      have htransition (gap : ℕ) (hg : gap ≤ size + 1) :=
        c_insertion_transitions size parent hparent site hsitebound hactive gap hg
      obtain ⟨label, hlabel⟩ := ih parent hparent
      cases label with
      | increasing =>
        obtain ⟨hp, hsites⟩ := hlabel
        have hprefix : ∀ first second, first < second → second < site →
            parent.getD first 0 < parent.getD second 0 := by
          intro first second hfs hs
          rw [hp, List.getD_eq_getElem _ 0 (by simp; omega),
            List.getD_eq_getElem _ 0 (by simp; omega),
            List.getElem_range', List.getElem_range']
          simp only [Nat.one_mul]
          omega
        by_cases happend : site = size
        · refine ⟨.increasing, ?_, ?_⟩
          · rw [happend, hp]
            simpa only [List.length_range', List.range'_concat, Nat.one_mul,
              Nat.add_comm] using
              (List.insertIdx_length_self (l := List.range' 1 size) (x := size + 1))
          · intro gap hg
            apply (htransition gap hg).mpr
            by_cases hlast : gap = size + 1
            · right; right
              refine ⟨hlast, hsites size le_rfl, ?_⟩
              simpa only [happend] using hprefix
            · left
              exact ⟨happend, by omega, hsites gap (by omega)⟩
        · have hi : site < size := by omega
          refine ⟨.persistent ⟨site, by omega⟩, hnoninc hi, ?_, ?_⟩
          · intro first second hfs hs
            change second < site at hs
            rw [hbefore first (by omega), hbefore second hs]
            exact hprefix first second hfs hs
          · intro gap hg
            rw [htransition gap hg]
            constructor
            · rintro (⟨heq, _⟩ | ⟨_, heq⟩ | ⟨heq, _⟩)
              · exact False.elim (happend heq)
              · exact Or.inl heq
              · exact Or.inr heq
            · rintro (heq | heq)
              · exact Or.inr (Or.inl ⟨hi, heq⟩)
              · exact Or.inr (Or.inr ⟨heq, hsites size le_rfl, hprefix⟩)
      | persistent cut =>
        obtain ⟨hnon, hprefix, hsites⟩ := hlabel
        have hcut := cut.is_lt
        obtain hinternal | happend := (hsites site hsitebound).mp hactive
        · have hi : site < size := by omega
          refine ⟨.persistent ⟨cut.val, by omega⟩, hnoninc hi, ?_, ?_⟩
          · intro first second hfs hs
            change second < cut.val at hs
            rw [hbefore first (by omega), hbefore second (by omega)]
            exact hprefix first second hfs hs
          · intro gap hg
            rw [htransition gap hg]
            constructor
            · rintro (⟨heq, _⟩ | ⟨_, heq⟩ | ⟨heq, _⟩)
              · omega
              · exact Or.inl (heq.trans hinternal)
              · exact Or.inr heq
            · rintro (heq | heq)
              · exact Or.inr (Or.inl ⟨hi, heq.trans hinternal.symm⟩)
              · right; right
                refine ⟨heq, (hsites size le_rfl).mpr (Or.inr rfl), ?_⟩
                simpa only [hinternal] using hprefix
        · refine ⟨.delayed ⟨cut.val, by omega⟩,
            hnoninc_append hnon happend, ?_⟩
          intro gap hg
          rw [htransition gap hg]
          constructor
          · rintro (⟨_, hb, hh⟩ | ⟨hi, _⟩ | ⟨_, _, hwhole⟩)
            · simpa only [Nat.add_sub_cancel] using (hsites gap hb).mp hh
            · omega
            · have heq := hinc size parent hparent.1 (by simpa only [happend] using hwhole)
              exact False.elim (hnon heq)
          · intro hh
            have hc : gap = cut.val ∨ gap = size := by simpa using hh
            exact Or.inl ⟨happend, by omega, (hsites gap (by omega)).mpr hc⟩
      | delayed cut =>
        obtain ⟨_, hsites⟩ := hlabel
        have hcut := cut.is_lt
        have hslot : site = cut.val ∨ site = size - 1 :=
          (hsites site hsitebound).mp hactive
        have hi : site < size := by omega
        have hlastinactive : parent.insertIdx size (size + 1) ∉
            classicalAvoiders (size + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] := by
          intro hh
          have := (hsites size le_rfl).mp hh
          omega
        refine ⟨.terminal ⟨site, by omega⟩, ?_⟩
        intro gap hg
        rw [htransition gap hg]
        constructor
        · rintro (⟨heq, _⟩ | ⟨_, heq⟩ | ⟨_, hh, _⟩)
          · omega
          · exact heq
          · exact False.elim (hlastinactive hh)
        · intro heq
          exact Or.inr (Or.inl ⟨hi, heq⟩)
      | terminal cut =>
        have hsites := hlabel
        have hcut := cut.is_lt
        have hslot : site = cut.val := (hsites site hsitebound).mp hactive
        have hi : site < size := by omega
        have hlastinactive : parent.insertIdx size (size + 1) ∉
            classicalAvoiders (size + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] := by
          intro hh
          have := (hsites size le_rfl).mp hh
          omega
        refine ⟨.terminal ⟨site, by omega⟩, ?_⟩
        intro gap hg
        rw [htransition gap hg]
        constructor
        · rintro (⟨heq, _⟩ | ⟨_, heq⟩ | ⟨_, hh, _⟩)
          · omega
          · exact heq
          · exact False.elim (hlastinactive hh)
        · intro heq
          exact Or.inr (Or.inl ⟨hi, heq⟩)
  obtain ⟨label, hlabel⟩ := hexists n p hmember
  refine ⟨label, hlabel, ?_⟩
  intro other hother
  cases label with
  | increasing =>
    obtain ⟨hp, hsites⟩ := hlabel
    cases other with
    | increasing => rfl
    | persistent cut => exact False.elim (hother.1 hp)
    | delayed cut => exact False.elim (hother.1 hp)
    | terminal cut =>
      have hcut := cut.is_lt
      have hh := (hother n le_rfl).mp (hsites n le_rfl)
      omega
  | persistent cut =>
    obtain ⟨hnon, _, hsites⟩ := hlabel
    have hcut := cut.is_lt
    cases other with
    | increasing => exact False.elim (hnon hother.1)
    | persistent other =>
      have hb := other.is_lt
      have hh := (hother.2.2 cut.val (by omega)).mp
        ((hsites cut.val (by omega)).mpr (Or.inl rfl))
      have heq : other = cut := Fin.ext (by omega)
      exact congrArg CType.persistent heq
    | delayed other =>
      have hb := other.is_lt
      have hh := (hother.2 n le_rfl).mp ((hsites n le_rfl).mpr (Or.inr rfl))
      omega
    | terminal other =>
      have hb := other.is_lt
      have hh := (hother n le_rfl).mp ((hsites n le_rfl).mpr (Or.inr rfl))
      omega
  | delayed cut =>
    obtain ⟨hnon, hsites⟩ := hlabel
    have hcut := cut.is_lt
    cases other with
    | increasing => exact False.elim (hnon hother.1)
    | persistent other =>
      have hb := other.is_lt
      have hh := (hsites n le_rfl).mp ((hother.2.2 n le_rfl).mpr (Or.inr rfl))
      omega
    | delayed other =>
      have hb := other.is_lt
      have hh := (hother.2 cut.val (by omega)).mp
        ((hsites cut.val (by omega)).mpr (Or.inl rfl))
      have heq : other = cut := Fin.ext (by omega)
      exact congrArg CType.delayed heq
    | terminal other =>
      have hfirst := (hother cut.val (by omega)).mp
        ((hsites cut.val (by omega)).mpr (Or.inl rfl))
      have hlast := (hother (n - 1) (by omega)).mp
        ((hsites (n - 1) (by omega)).mpr (Or.inr rfl))
      omega
  | terminal cut =>
    have hsites := hlabel
    have hcut := cut.is_lt
    cases other with
    | increasing =>
      have hh := (hsites n le_rfl).mp (hother.2 n le_rfl)
      omega
    | persistent other =>
      have hh := (hsites n le_rfl).mp ((hother.2.2 n le_rfl).mpr (Or.inr rfl))
      omega
    | delayed other =>
      have hb := other.is_lt
      have hfirst := (hsites other.val (by omega)).mp
        ((hother.2 other.val (by omega)).mpr (Or.inl rfl))
      have hlast := (hsites (n - 1) (by omega)).mp
        ((hother.2 (n - 1) (by omega)).mpr (Or.inr rfl))
      omega
    | terminal other =>
      have hb := other.is_lt
      have hh := (hother cut.val (by omega)).mp ((hsites cut.val (by omega)).mpr rfl)
      exact congrArg CType.terminal (Fin.ext hh.symm)

end D5.S3.Combinatorics.Fishburn.FishburnTenTenCTree
