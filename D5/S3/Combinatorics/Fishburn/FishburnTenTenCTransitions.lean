/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenCTransitions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenCTransitions
   mirror-E: none(waiver:classical-c-active-slot-transition)
   anchors: []
   utility: none
   digest: Separated cuts and new 132 and 213 witnesses determine every C child active slot. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicClassicalPatterns
import D5.S3.Combinatorics.Fishburn.FishburnBasicFourPatterns
import D5.S3.Combinatorics.Fishburn.FishburnClassicalDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenCTransitions

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs
open FishburnBasicClassicalPatterns FishburnBasicFourPatterns

set_option maxHeartbeats 1600000 in
theorem c_insertion_transitions (n : ℕ) (p : List ℕ)
    (hmember : p ∈ classicalAvoiders n [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]])
    (site : ℕ) (hsite : site ≤ n)
    (hactive : p.insertIdx site (n + 1) ∈
      classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]])
    (gap : ℕ) (hgap : gap ≤ n + 1) :
    (p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
        classicalAvoiders (n + 2) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] ↔
      (site = n ∧ gap ≤ n ∧ p.insertIdx gap (n + 1) ∈
        classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]]) ∨
      (site < n ∧ gap = site) ∨
      (gap = n + 1 ∧ p.insertIdx n (n + 1) ∈
        classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] ∧
        ∀ first second, first < second → second < site →
          p.getD first 0 < p.getD second 0) := by
  have hcriteria (size : ℕ) (word : List ℕ)
      (hm : word ∈ classicalAvoiders size [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]])
      (cut : ℕ) (hc : cut ≤ word.length) :
      word.insertIdx cut (size + 1) ∈
          classicalAvoiders (size + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] ↔
        (∀ first second, first < cut → cut ≤ second → second < word.length →
          word.getD first 0 ≤ word.getD second 0) ∧
        (∀ first second third, first < second → second < third → third < cut →
          word.getD second 0 < word.getD first 0 →
          word.getD third 0 ≤ word.getD first 0) ∧
        (∀ first second third, cut ≤ first → first < second → second < third →
          third < word.length → word.getD first 0 < word.getD third 0 →
          word.getD second 0 ≤ word.getD third 0) := by
    have htests := maximum_classical_pattern_tests size word hm.1 cut hc
    have h2134 := (maximum_four_pattern_tests size word hm.1 cut hc).2.1
    have h231 := hm.2 [2, 3, 1] (by simp)
    have h4132 := hm.2 [4, 1, 3, 2] (by simp)
    have h2134old := hm.2 [2, 1, 3, 4] (by simp)
    constructor
    · intro hchild
      refine ⟨?_, ?_, ?_⟩
      · intro first second hfirst hsecond hb
        by_contra hnot
        apply hchild.2 [2, 3, 1] (by simp)
        exact htests.2.1.mpr (Or.inr ⟨first, second, hfirst, hsecond, hb, by omega⟩)
      · intro first second third hfs hst ht hlt
        by_contra hnot
        apply hchild.2 [2, 1, 3, 4] (by simp)
        exact h2134.mpr (Or.inr ⟨first, second, third, hfs, hst, ht, hlt, by omega⟩)
      · intro first second third hf hfs hst hb hlt
        by_contra hnot
        apply hchild.2 [4, 1, 3, 2] (by simp)
        exact htests.2.2.mpr (Or.inr
          ⟨first, second, third, hf, hfs, hst, hb, hlt, by omega⟩)
    · rintro ⟨hsep, hleft, hright⟩
      refine ⟨?_, ?_⟩
      · apply (List.perm_insertIdx (size + 1) word hc).trans
        apply (hm.1.cons (size + 1)).trans
        rw [List.range'_concat]
        simpa [Nat.add_comm] using
          (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
      · intro pattern hpattern hocc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl | rfl
        · rcases htests.2.1.mp hocc with hocc | ⟨first, second, hf, hs, hb, hlt⟩
          · exact h231 hocc
          · have := hsep first second hf hs hb
            omega
        · rcases htests.2.2.mp hocc with hocc |
            ⟨first, second, third, hf, hfs, hst, hb, hlt, hgt⟩
          · exact h4132 hocc
          · have := hright first second third hf hfs hst hb hlt
            omega
        · rcases h2134.mp hocc with hocc |
            ⟨first, second, third, hfs, hst, ht, hlt, hgt⟩
          · exact h2134old hocc
          · have := hleft first second third hfs hst ht hlt
            omega
  have hlen : p.length = n := by simpa using hmember.1.length_eq
  have hsitebound : site ≤ p.length := by omega
  let child := p.insertIdx site (n + 1)
  have hchildlen : child.length = n + 1 := by
    rw [List.length_insertIdx_of_le_length hsitebound, hlen]
  have hbound (index : ℕ) (hi : index < n) : p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 (by omega)]
      exact List.getElem_mem _
    have hrange := hmember.1.mem_iff.mp hm
    simp only [List.mem_range'_1] at hrange
    omega
  have hne (first second : ℕ) (hf : first < n) (hs : second < n)
      (hneq : first ≠ second) : p.getD first 0 ≠ p.getD second 0 := by
    intro heq
    exact hneq ((List.getD_inj (by omega) (by omega)
      (hmember.1.nodup_iff.mpr (List.nodup_range' 1))).mp heq)
  have hbefore (index : ℕ) (hi : index < site) :
      child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD site 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  let lower := fun index : ℕ => if index < site then index else index - 1
  let lift := fun index : ℕ => if index < site then index else index + 1
  have hlowerbound (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
      lower index < n := by dsimp [lower]; split_ifs <;> omega
  have hlowerentry (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
      child.getD index 0 = p.getD (lower index) 0 := by
    dsimp [lower]
    split_ifs with hlt
    · exact hbefore index hlt
    · rw [List.getD_eq_getElem child 0 hi, List.getElem_insertIdx_of_gt (by omega),
        List.getD_eq_getElem p 0 (by omega)]
  have hlowermono (first second : ℕ) (hlt : first < second)
      (hf : first ≠ site) (hs : second ≠ site) : lower first < lower second := by
    dsimp [lower]
    split_ifs <;> omega
  have hliftbound (index : ℕ) (hi : index < n) : lift index < child.length := by
    dsimp [lift]; split_ifs <;> omega
  have hliftentry (index : ℕ) (hi : index < n) :
      child.getD (lift index) 0 = p.getD index 0 := by
    dsimp [lift]
    split_ifs with hlt
    · exact hbefore index hlt
    · rw [List.getD_eq_getElem child 0 (by omega),
        List.getElem_insertIdx_of_gt (by omega), List.getD_eq_getElem p 0 (by omega)]
      simp only [Nat.add_sub_cancel]
  have hliftmono (first second : ℕ) (hlt : first < second) : lift first < lift second := by
    dsimp [lift]; split_ifs <;> omega
  obtain ⟨hsep, hleft, hright⟩ := (hcriteria n p hmember site hsitebound).mp hactive
  have hlast : child.insertIdx (n + 1) (n + 2) ∈
        classicalAvoiders (n + 2) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] ↔
      p.insertIdx n (n + 1) ∈
        classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] ∧
      ∀ first second, first < second → second < site →
        p.getD first 0 < p.getD second 0 := by
    rw [hcriteria (n + 1) child hactive (n + 1) (by omega),
      hcriteria n p hmember n (by omega)]
    constructor
    · rintro ⟨_, hchildleft, _⟩
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro first second hf hs hb
        omega
      · intro first second third hfs hst ht hlt
        have hh := hchildleft (lift first) (lift second) (lift third)
          (hliftmono first second hfs) (hliftmono second third hst)
          (by have := hliftbound third ht; omega)
        rw [hliftentry first (by omega), hliftentry second (by omega),
          hliftentry third ht] at hh
        exact hh hlt
      · intro first second third hf hfs hst hb
        omega
      · intro first second hfs hs
        have hfbound : first < n := by omega
        have hsbound : second < n := by omega
        have hnot := hne first second hfbound hsbound (by omega)
        by_contra hnotlt
        have hgt : p.getD second 0 < p.getD first 0 := by omega
        have hh := hchildleft first second site hfs hs (by omega)
        rw [hbefore first (by omega), hbefore second hs, hat] at hh
        have := hh hgt
        have := hbound first hfbound
        omega
    · rintro ⟨⟨_, hparentleft, _⟩, hprefix⟩
      refine ⟨?_, ?_, ?_⟩
      · intro first second hf hs hb
        omega
      · intro first second third hfs hst ht hlt
        have hthird : third < child.length := by omega
        by_cases hf : first = site
        · subst first
          rw [hat] at hlt ⊢
          have hs : second ≠ site := by omega
          rw [hlowerentry second (by omega) hs] at hlt
          have hthirdne : third ≠ site := by omega
          rw [hlowerentry third hthird hthirdne]
          have := hbound (lower third) (hlowerbound third hthird hthirdne)
          omega
        by_cases hs : second = site
        · subst second
          rw [hat, hlowerentry first (by omega) hf] at hlt
          have := hbound (lower first) (hlowerbound first (by omega) hf)
          omega
        by_cases hthirdne : third = site
        · subst third
          rw [hbefore first (by omega), hbefore second (by omega)] at hlt
          have := hprefix first second hfs (by omega)
          omega
        rw [hlowerentry second (by omega) hs, hlowerentry first (by omega) hf] at hlt
        rw [hlowerentry third hthird hthirdne, hlowerentry first (by omega) hf]
        exact hparentleft (lower first) (lower second) (lower third)
          (hlowermono first second hfs hf hs) (hlowermono second third hst hs hthirdne)
          (hlowerbound third hthird hthirdne) hlt
      · intro first second third hf hfs hst hb
        omega
  have hkept : child.insertIdx site (n + 2) ∈
      classicalAvoiders (n + 2) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] := by
    apply (hcriteria (n + 1) child hactive site (by omega)).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro first second hf hs hb
      rw [hbefore first hf]
      by_cases heq : second = site
      · subst second
        rw [hat]
        have := hbound first (by omega)
        omega
      · rw [hlowerentry second hb heq]
        apply hsep first (lower second) hf
        · dsimp [lower]; split_ifs <;> omega
        · have := hlowerbound second hb heq
          omega
    · intro first second third hfs hst ht hlt
      rw [hbefore first (by omega), hbefore second (by omega)] at hlt
      rw [hbefore third ht, hbefore first (by omega)]
      exact hleft first second third hfs hst ht hlt
    · intro first second third hf hfs hst hb hlt
      by_cases heq : first = site
      · subst first
        rw [hat, hlowerentry third hb (by omega)] at hlt
        have := hbound (lower third) (hlowerbound third hb (by omega))
        omega
      · have hs : second ≠ site := by omega
        have ht : third ≠ site := by omega
        rw [hlowerentry first (by omega) heq, hlowerentry third hb ht] at hlt
        rw [hlowerentry second (by omega) hs, hlowerentry third hb ht]
        apply hright (lower first) (lower second) (lower third)
        · dsimp [lower]; split_ifs <;> omega
        · exact hlowermono first second hfs heq hs
        · exact hlowermono second third hst hs ht
        · have := hlowerbound third hb ht
          omega
        · exact hlt
  have happend_transfer (happend : site = n) (hg : gap ≤ n) :
      child.insertIdx gap (n + 2) ∈
          classicalAvoiders (n + 2) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] ↔
        p.insertIdx gap (n + 1) ∈
          classicalAvoiders (n + 1) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] := by
    rw [hcriteria (n + 1) child hactive gap (by omega),
      hcriteria n p hmember gap (by omega)]
    constructor
    · rintro ⟨hchildsep, hchildleft, hchildright⟩
      refine ⟨?_, ?_, ?_⟩
      · intro first second hf hs hb
        have hh := hchildsep first second hf hs (by omega)
        rwa [hbefore first (by omega), hbefore second (by omega)] at hh
      · intro first second third hfs hst ht hlt
        have hh := hchildleft first second third hfs hst ht
        rw [hbefore second (by omega), hbefore first (by omega),
          hbefore third (by omega)] at hh
        exact hh hlt
      · intro first second third hf hfs hst hb hlt
        have hh := hchildright first second third hf hfs hst (by omega)
        rw [hbefore first (by omega), hbefore third (by omega),
          hbefore second (by omega)] at hh
        exact hh hlt
    · rintro ⟨hparentsep, hparentleft, hparentright⟩
      refine ⟨?_, ?_, ?_⟩
      · intro first second hf hs hb
        rw [hbefore first (by omega)]
        by_cases heq : second = site
        · subst second
          rw [hat]
          have := hbound first (by omega)
          omega
        · rw [hbefore second (by omega)]
          exact hparentsep first second hf hs (by omega)
      · intro first second third hfs hst ht hlt
        rw [hbefore second (by omega), hbefore first (by omega)] at hlt
        rw [hbefore third (by omega), hbefore first (by omega)]
        exact hparentleft first second third hfs hst ht hlt
      · intro first second third hf hfs hst hb hlt
        by_cases heq : third = site
        · subst third
          rw [hat, hbefore second (by omega)]
          have := hbound second (by omega)
          omega
        · rw [hbefore first (by omega), hbefore third (by omega)] at hlt
          rw [hbefore second (by omega), hbefore third (by omega)]
          exact hparentright first second third hf hfs hst (by omega) hlt
  change child.insertIdx gap (n + 2) ∈ _ ↔ _
  by_cases hlastgap : gap = n + 1
  · rw [hlastgap, hlast]
    constructor
    · intro hh
      exact Or.inr (Or.inr ⟨rfl, hh⟩)
    · rintro (⟨_, hb, _⟩ | ⟨_, heq⟩ | ⟨_, hh⟩)
      · omega
      · omega
      · exact hh
  have hgapold : gap ≤ n := by omega
  by_cases happend : site = n
  · rw [happend_transfer happend hgapold]
    constructor
    · intro hh
      exact Or.inl ⟨happend, hgapold, hh⟩
    · rintro (⟨_, _, hh⟩ | ⟨hsite, _⟩ | ⟨heq, _⟩)
      · exact hh
      · omega
      · omega
  have hinternal : site < n := by omega
  by_cases hsame : gap = site
  · constructor
    · intro _
      exact Or.inr (Or.inl ⟨hinternal, hsame⟩)
    · intro _
      simpa only [hsame] using hkept
  have hinactive : child.insertIdx gap (n + 2) ∉
      classicalAvoiders (n + 2) [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]] := by
    intro hchild
    obtain ⟨hchildsep, _, hchildright⟩ :=
      (hcriteria (n + 1) child hactive gap (by omega)).mp hchild
    by_cases hbeforegap : gap < site
    · have hlt : p.getD gap 0 < p.getD site 0 := by
        have := hsep gap site hbeforegap le_rfl (by omega)
        have := hne gap site (by omega) hinternal (by omega)
        omega
      have hh := hchildright gap site (site + 1) le_rfl hbeforegap (by omega)
        (by omega)
      rw [hbefore gap hbeforegap, hat,
        hlowerentry (site + 1) (by omega) (by omega)] at hh
      have hlow : lower (site + 1) = site := by simp [lower]
      rw [hlow] at hh
      have := hh hlt
      have := hbound site hinternal
      omega
    · have hh := hchildsep site gap (by omega) le_rfl (by omega)
      rw [hat, hlowerentry gap (by omega) hsame] at hh
      have := hbound (lower gap) (hlowerbound gap (by omega) hsame)
      omega
  constructor
  · intro hchild
    exact False.elim (hinactive hchild)
  · rintro (⟨heq, _⟩ | ⟨_, heq⟩ | ⟨heq, _⟩)
    · exact False.elim (happend heq)
    · exact False.elim (hsame heq)
    · exact False.elim (hlastgap heq)

end D5.S3.Combinatorics.Fishburn.FishburnTenTenCTransitions
