/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFour2143Transport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFour2143Transport
   mirror-E: none(waiver:two-maximum-2143-witness-analysis)
   anchors: []
   utility: none
   digest: Two-maximum witnesses and eligibility determine inherited and adjacent insertion cuts. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasic2143
import D5.S3.Combinatorics.Fishburn.FishburnBasicPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFour2143Transport

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasic2143 FishburnBasicInsertion
open FishburnBasicPatterns

theorem maximum_2143_transport (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (site gap : ℕ)
    (hsite : site ≤ p.length) (hgap : gap ≤ p.length) :
    (NonnestingDefs.Occurs [2, 1, 4, 3]
        ((p.insertIdx site (n + 1)).insertIdx
          (if gap ≤ site then gap else gap + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [2, 1, 4, 3] (p.insertIdx site (n + 1)) ∨
      NonnestingDefs.Occurs [2, 1, 4, 3] (p.insertIdx gap (n + 1)) ∨
      (gap ≤ site ∧ ∃ first second, first < second ∧ second < gap ∧
        p.getD second 0 < p.getD first 0)) ∧
    (0 < site → 0 < gap → IsFishburn p → IsFishburn (p.insertIdx site (n + 1)) →
      (IsFishburn ((p.insertIdx site (n + 1)).insertIdx
        (if gap ≤ site then gap else gap + 1) (n + 2)) ↔
        IsFishburn (p.insertIdx gap (n + 1)))) ∧
    (∀ patterns : List (List ℕ),
      (∀ pattern ∈ patterns, pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨
        pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3]) →
      p ∈ avoiders n patterns → 0 < site →
      p.insertIdx site (n + 1) ∈ avoiders (n + 1) patterns →
      ((p.insertIdx site (n + 1)).insertIdx (site + 1) (n + 2) ∈
        avoiders (n + 2) patterns ↔ ∃ earlier < site, p.getD earlier 0 = n)) := by
  let child := p.insertIdx site (n + 1)
  let nextgap := if gap ≤ site then gap else gap + 1
  let lift := fun index : ℕ => if index < site then index else index + 1
  let lower := fun index : ℕ => if index < site then index else index - 1
  let guard := fun (word : List ℕ) (cut : ℕ) =>
    ∃ first second third, first < second ∧ second < cut ∧ cut ≤ third ∧
      third < word.length ∧ word.getD second 0 < word.getD first 0 ∧
      word.getD first 0 < word.getD third 0
  have hlength : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hsite (n + 1)
  have hnextgap : nextgap ≤ child.length := by dsimp [nextgap]; split_ifs <;> omega
  have hchildperm : child.Perm (List.range' 1 (n + 1)) := by
    have hp := (List.perm_insertIdx (n + 1) p hsite).trans (hperm.cons (n + 1))
    rw [List.range'_concat]
    simpa only [Nat.one_mul, Nat.add_comm, List.singleton_append] using
      hp.trans (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
  have hentry (index : ℕ) (hi : index < p.length) : p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hi]
      exact List.getElem_mem hi
    have hrange := hperm.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, hvalue⟩ := hrange
    omega
  have hbefore (index : ℕ) (hi : index < site) :
      child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD site 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  have hlowerentry (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
      child.getD index 0 = p.getD (lower index) 0 := by
    dsimp [lower]
    split_ifs with hlt
    · exact hbefore index hlt
    · rw [List.getD_eq_getElem child 0 hi, List.getElem_insertIdx_of_gt (by omega),
        List.getD_eq_getElem p 0 (by omega)]
  have hbound (index : ℕ) (hi : index < child.length) : child.getD index 0 ≤ n + 1 := by
    by_cases heq : index = site
    · subst index
      omega
    · rw [hlowerentry index hi heq]
      have hb : lower index < p.length := by dsimp [lower]; split_ifs <;> omega
      exact le_trans (hentry _ hb) (by omega)
  have hliftbound (index : ℕ) (hi : index < p.length) : lift index < child.length := by
    dsimp [lift]
    split_ifs <;> omega
  have hliftentry (index : ℕ) (hi : index < p.length) :
      child.getD (lift index) 0 = p.getD index 0 := by
    dsimp [lift]
    split_ifs with hlt
    · exact hbefore index hlt
    · rw [List.getD_eq_getElem child 0 (by omega),
        List.getElem_insertIdx_of_gt (by omega), List.getD_eq_getElem p 0 (by omega)]
      simp only [Nat.add_sub_cancel]
  have hlowerbound (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
      lower index < p.length := by
    dsimp [lower]
    split_ifs <;> omega
  have hlowermono (first second : ℕ) (hlt : first < second)
      (hfirst : first ≠ site) (hsecond : second ≠ site) : lower first < lower second := by
    dsimp [lower]
    split_ifs <;> omega
  have hlowerprefix (index : ℕ) (hne : index ≠ site) (hi : index < nextgap) :
      lower index < gap := by
    by_cases hle : gap ≤ site
    · simp only [nextgap, if_pos hle] at hi
      dsimp [lower]
      split_ifs <;> omega
    · simp only [nextgap, if_neg hle] at hi
      dsimp [lower]
      split_ifs <;> omega
  have hlowersuffix (index : ℕ) (hne : index ≠ site) (hi : nextgap ≤ index) :
      gap ≤ lower index := by
    by_cases hle : gap ≤ site
    · simp only [nextgap, if_pos hle] at hi
      dsimp [lower]
      split_ifs <;> omega
    · simp only [nextgap, if_neg hle] at hi
      dsimp [lower]
      split_ifs <;> omega
  have hguard : guard child nextgap ↔ guard p gap ∨
      (gap ≤ site ∧ ∃ first second, first < second ∧ second < gap ∧
        p.getD second 0 < p.getD first 0) := by
    constructor
    · rintro ⟨first, second, third, hfs, hsecond, hthird, hthirdbound, hlow, hhigh⟩
      have hfirstbound : first < child.length := by omega
      have hsecondbound : second < child.length := by omega
      have hfirstne : first ≠ site := by
        intro heq
        rw [heq, hat] at hhigh
        have := hbound third hthirdbound
        omega
      have hsecondne : second ≠ site := by
        intro heq
        rw [heq, hat] at hlow
        have := hbound first hfirstbound
        omega
      by_cases hthirdsite : third = site
      · right
        have hle : gap ≤ site := by
          dsimp [nextgap] at hthird
          split_ifs at hthird <;> omega
        have hnext : nextgap = gap := by simp [nextgap, hle]
        rw [hnext] at hsecond
        rw [hbefore first (by omega), hbefore second (by omega)] at hlow
        exact ⟨hle, first, second, hfs, hsecond, hlow⟩
      · left
        rw [hlowerentry first hfirstbound hfirstne,
          hlowerentry second hsecondbound hsecondne] at hlow
        rw [hlowerentry first hfirstbound hfirstne,
          hlowerentry third hthirdbound hthirdsite] at hhigh
        exact ⟨lower first, lower second, lower third,
          hlowermono first second hfs hfirstne hsecondne,
          hlowerprefix second hsecondne hsecond,
          hlowersuffix third hthirdsite hthird,
          hlowerbound third hthirdbound hthirdsite, hlow, hhigh⟩
    · rintro (⟨first, second, third, hfs, hsecond, hthird, hthirdbound, hlow, hhigh⟩ |
        ⟨hle, first, second, hfs, hsecond, hlow⟩)
      · refine ⟨lift first, lift second, lift third, ?_, ?_, ?_,
          hliftbound third hthirdbound, ?_, ?_⟩
        · dsimp [lift]
          split_ifs <;> omega
        · dsimp [lift, nextgap]
          split_ifs <;> omega
        · dsimp [lift, nextgap]
          split_ifs <;> omega
        · rwa [hliftentry first (by omega), hliftentry second (by omega)]
        · rwa [hliftentry first (by omega), hliftentry third hthirdbound]
      · have hnext : nextgap = gap := by simp [nextgap, hle]
        refine ⟨first, second, site, hfs, by omega, by omega, by omega, ?_, ?_⟩
        · rwa [hbefore first (by omega), hbefore second (by omega)]
        · rw [hbefore first (by omega), hat]
          have := hentry first (by omega)
          omega
  refine ⟨?_, ?_, ?_⟩
  · have hchildtest := maximum_2143_test (n + 1) child hchildperm nextgap hnextgap
    have holdtest := maximum_2143_test n p hperm gap hgap
    have hbasetest := maximum_2143_test n p hperm site hsite
    have hbase : NonnestingDefs.Occurs [2, 1, 4, 3] p →
        NonnestingDefs.Occurs [2, 1, 4, 3] child := fun h => hbasetest.mpr (Or.inl h)
    change NonnestingDefs.Occurs [2, 1, 4, 3] (child.insertIdx nextgap (n + 2)) ↔ _
    change NonnestingDefs.Occurs [2, 1, 4, 3] (child.insertIdx nextgap (n + 1 + 1)) ↔
      NonnestingDefs.Occurs [2, 1, 4, 3] child ∨ guard child nextgap at hchildtest
    change NonnestingDefs.Occurs [2, 1, 4, 3] (p.insertIdx gap (n + 1)) ↔
      NonnestingDefs.Occurs [2, 1, 4, 3] p ∨ guard p gap at holdtest
    rw [show n + 2 = n + 1 + 1 by omega, hchildtest, hguard, holdtest]
    constructor
    · rintro (hchild | hold | hnew)
      · exact Or.inl hchild
      · exact Or.inr (Or.inl (Or.inr hold))
      · exact Or.inr (Or.inr hnew)
    · rintro (hchild | (hparent | hold) | hnew)
      · exact Or.inl hchild
      · exact Or.inl (hbase hparent)
      · exact Or.inr (Or.inl hold)
      · exact Or.inr (Or.inr hnew)
  · intro hpositive hgpositive hparentfish hchildfish

    have hnextne : nextgap ≠ site + 1 := by dsimp [nextgap]; split_ifs <;> omega
    have hmax (value : ℕ) (hm : value ∈ p) : value < n + 1 := by
      have hrange := hperm.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, hvalue⟩ := hrange
      omega
    have hmaxchild (value : ℕ) (hm : value ∈ child) : value < n + 2 := by
      have hrange := hchildperm.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, hvalue⟩ := hrange
      omega
    have heligible :
        (∀ before later, before + 1 = nextgap → nextgap ≤ later → later < child.length →
          child.getD before 0 ≠ child.getD later 0 + 1) ↔
        (∀ before later, before + 1 = gap → gap ≤ later → later < p.length →
          p.getD before 0 ≠ p.getD later 0 + 1) := by
      constructor
      · intro h before later hcross hlater hb heq
        let nextbefore := if gap ≤ site then before else before + 1
        have hnextbefore : nextbefore + 1 = nextgap := by
          dsimp [nextbefore, nextgap]
          split_ifs <;> omega
        have hnextlater : nextgap ≤ lift later := by
          dsimp [nextgap, lift]
          split_ifs <;> omega
        have hlaterbound : lift later < child.length := by dsimp [lift]; split_ifs <;> omega
        have hbottom : child.getD nextbefore 0 = p.getD before 0 := by
          dsimp [nextbefore]
          split_ifs with hle
          · exact hbefore before (by omega)
          · have he := hliftentry before (by omega)
            simpa only [lift, if_neg (by omega : ¬ before < site)] using he
        apply h nextbefore (lift later) hnextbefore hnextlater hlaterbound
        rwa [hbottom, hliftentry later hb]
      · intro h before later hcross hlater hb heq
        have hbeforene : before ≠ site := by omega
        have hbeforebound : before < child.length := by omega
        have hbeforelower : lower before + 1 = gap := by
          by_cases hle : gap ≤ site
          · simp only [nextgap, if_pos hle] at hcross
            simp only [lower, if_pos (by omega : before < site)]
            omega
          · simp only [nextgap, if_neg hle] at hcross
            simp only [lower, if_neg (by omega : ¬ before < site)]
            omega
        by_cases hlatermaximum : later = site
        · rw [hlatermaximum, hat, hlowerentry before hbeforebound hbeforene] at heq
          have hlowerbound : lower before < p.length := by dsimp [lower]; split_ifs <;> omega
          have := hentry (lower before) hlowerbound
          omega
        · have hlaterlower : gap ≤ lower later := by
            by_cases hle : gap ≤ site
            · simp only [nextgap, if_pos hle] at hlater
              dsimp [lower]
              split_ifs <;> omega
            · simp only [nextgap, if_neg hle] at hlater
              dsimp [lower]
              split_ifs <;> omega
          have hlowerbound : lower later < p.length := by dsimp [lower]; split_ifs <;> omega
          apply h (lower before) (lower later) hbeforelower hlaterlower hlowerbound
          rwa [hlowerentry before hbeforebound hbeforene,
            hlowerentry later hb hlatermaximum] at heq
    have hfishiff : IsFishburn (child.insertIdx nextgap (n + 2)) ↔
        IsFishburn (p.insertIdx gap (n + 1)) := by
      have hc := isFishburn_insertIdx_max_iff child (n + 2) nextgap hnextgap hmaxchild
      have hp := isFishburn_insertIdx_max_iff p (n + 1) gap hgap hmax
      constructor
      · intro hf
        exact hp.mpr ⟨hparentfish, heligible.mp (hc.mp hf).2⟩
      · intro hf
        exact hc.mpr ⟨hchildfish, heligible.mpr (hp.mp hf).2⟩
    exact hfishiff
  · intro patterns hpatterns hparent hpositive hactive
    let child := p.insertIdx site (n + 1)
    have hlength : child.length = p.length + 1 := by
      simp [child, List.length_insertIdx_of_le_length hsite]
    have hmaxp : ∀ value ∈ p, value < n + 1 := by
      intro value hvalue
      have hm := hparent.1.mem_iff.mp hvalue
      simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨offset, hoffset, heq⟩ := hm
      omega
    have hmaxchild : ∀ value ∈ child, value < n + 2 := by
      intro value hvalue
      have hm := hactive.1.mem_iff.mp hvalue
      simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨offset, hoffset, heq⟩ := hm
      omega
    have hbound : ∀ index, index < child.length → child.getD index 0 ≤ n + 1 := by
      intro index hindex
      rw [List.getD_eq_getElem child 0 hindex]
      have := hmaxchild _ (List.getElem_mem hindex)
      omega
    have hbefore : ∀ index, index < site →
        child.getD index 0 = p.getD index 0 := by
      intro index hindex
      rw [List.getD_eq_getElem child 0 (by omega),
        List.getElem_insertIdx_of_lt hindex, List.getD_eq_getElem p 0 (by omega)]
    have hat : child.getD site 0 = n + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]
      exact List.getElem_insertIdx_self _
    have hafter : ∀ index, site < index → index < child.length →
        child.getD index 0 = p.getD (index - 1) 0 := by
      intro index hindex hbound
      rw [List.getD_eq_getElem child 0 hbound, List.getElem_insertIdx_of_gt hindex,
        List.getD_eq_getElem p 0 (by omega)]
    have hperm : ∀ gap, gap ≤ child.length →
        (child.insertIdx gap (n + 2)).Perm (List.range' 1 (n + 2)) := by
      intro gap hgap
      apply (List.perm_insertIdx (n + 2) child hgap).trans
      apply (hactive.1.cons (n + 2)).trans
      have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
        simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
          show 1 + (n + 1) = n + 2 by omega] using
          (List.range'_concat (s := 1) (n := n + 1) (step := 1))
      rw [hrange]
      simpa using (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
    have hold := maximum_pattern_tests n p hparent.1 site hsite
    have havoids : ∀ gap, gap = site + 1 →
        ∀ pattern ∈ patterns, ¬ NonnestingDefs.Occurs pattern (child.insertIdx gap (n + 2)) := by
      intro gap hgap pattern hpattern hocc
      have hgapbound : site ≤ gap ∧ gap ≤ site + 1 := by omega
      have hnew := maximum_pattern_tests (n + 1) child hactive.1 gap (by omega)
      rcases hpatterns pattern hpattern with rfl | rfl | rfl | rfl
      · rcases hnew.1.mp hocc with hprevious | hwitness
        · exact hactive.2.2 _ hpattern hprevious
        · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hwitness
          have hthird : third < site := by
            by_contra hnot
            have heq : third = site := by omega
            rw [heq, hat] at hhigh
            have := hbound second (by omega)
            omega
          rw [hbefore first (by omega), hbefore third hthird] at hlow
          rw [hbefore third hthird, hbefore second (by omega)] at hhigh
          exact hactive.2.2 _ hpattern
            (hold.1.mpr (Or.inr ⟨first, second, third, hfs, hst, hthird, hlow, hhigh⟩))
      · rcases hnew.2.1.mp hocc with hprevious | hwitness
        · exact hactive.2.2 _ hpattern hprevious
        · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hwitness
          have hthird : third < site := by
            by_contra hnot
            have heq : third = site := by omega
            rw [heq, hat] at hhigh
            have := hbound first (by omega)
            omega
          rw [hbefore second (by omega), hbefore third hthird] at hlow
          rw [hbefore third hthird, hbefore first (by omega)] at hhigh
          exact hactive.2.2 _ hpattern
            (hold.2.1.mpr (Or.inr ⟨first, second, third, hfs, hst, hthird, hlow, hhigh⟩))
      · rcases hnew.2.2.mp hocc with hprevious | hwitness
        · exact hactive.2.2 _ hpattern hprevious
        · obtain ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩ := hwitness
          have hfirst : first < site := by
            by_contra hnot
            have heq : first = site := by omega
            rw [heq, hat] at hlow
            have := hbound second (by omega)
            omega
          have hsecond : site < second := by
            by_contra hnot
            have heq : second = site := by omega
            rw [heq, hat] at hhigh
            have := hbound third ht
            omega
          rw [hbefore first hfirst, hafter second hsecond (by omega)] at hlow
          rw [hafter second hsecond (by omega), hafter third (by omega) ht] at hhigh
          exact hactive.2.2 _ hpattern
            (hold.2.2.mpr (Or.inr ⟨first, second - 1, third - 1, hfirst, by omega,
              by omega, by omega, hlow, hhigh⟩))
      · have htest := maximum_2143_test (n + 1) child hactive.1 gap (by omega)
        rw [show n + 1 + 1 = n + 2 by omega] at htest
        rcases htest.mp hocc with hold | hnew
        · exact hactive.2.2 _ hpattern hold
        · obtain ⟨first, second, third, hfs, hs, ht, htb, hlow, hhigh⟩ := hnew
          have hsecond : second < site := by
            by_contra hnot
            have heq : second = site := by omega
            rw [heq, hat] at hlow
            have := hbound first (by omega)
            omega
          rw [hbefore first (by omega), hbefore second hsecond] at hlow
          rw [hbefore first (by omega), hafter third (by omega) htb] at hhigh
          apply hactive.2.2 _ hpattern
          apply (maximum_2143_test n p hparent.1 site hsite).mpr
          exact Or.inr ⟨first, second, third - 1, hfs, hsecond, by omega,
            by omega, hlow, hhigh⟩
    constructor
    · intro hmember
      have hnew :=
        (isFishburn_insertIdx_max_iff child (n + 2) (site + 1) (by omega) hmaxchild).mp
          hmember.2.1
      have hn : 1 ≤ n := by
        have hlen := hparent.1.length_eq
        simp only [List.length_range'] at hlen
        omega
      have hnmem : n ∈ p := by
        apply hparent.1.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨n - 1, by omega, by omega⟩
      obtain ⟨earlier, hearlier, hvalue⟩ := List.mem_iff_getElem.mp hnmem
      have hentry : p.getD earlier 0 = n := by
        rwa [List.getD_eq_getElem p 0 hearlier]
      refine ⟨earlier, ?_, hentry⟩
      by_contra hnot
      apply hnew.2 site (earlier + 1) rfl (by omega) (by omega)
      rw [hat, hafter (earlier + 1) (by omega) (by omega), Nat.add_sub_cancel, hentry]
    · rintro ⟨earlier, hearlier, hvalue⟩
      refine ⟨hperm (site + 1) (by omega), ?_, havoids (site + 1) rfl⟩
      apply (isFishburn_insertIdx_max_iff child (n + 2) (site + 1) (by omega) hmaxchild).mpr
      refine ⟨hactive.2.1, ?_⟩
      intro before later hbefore hlater hboundlater heq
      have heqbefore : before = site := by omega
      subst before
      rw [hat, hafter later (by omega) hboundlater] at heq
      have hsame : p.getD earlier 0 = p.getD (later - 1) 0 := by omega
      have hindex := (List.getD_inj (by omega) (by omega)
        (hparent.1.nodup_iff.mpr (List.nodup_range' 1))).mp hsame
      omega
end D5.S3.Combinatorics.Fishburn.FishburnTenFour2143Transport
