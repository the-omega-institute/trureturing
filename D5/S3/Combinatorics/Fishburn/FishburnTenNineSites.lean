/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenNineSites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenNineSites
   mirror-E: none(waiver:active-2143-cut-witness-evolution)
   anchors: []
   utility: none
   digest: Inherited active gaps require increasing prefixes or decreasing intervening slices. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasic2143
import D5.S3.Combinatorics.Fishburn.FishburnBasicPatternTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenNineSites

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasic2143 FishburnBasicPatternTransport

theorem active_site_evolution (n : ℕ) (p : List ℕ)
    (hpositive : 1 ≤ n)
    (hparent : p ∈ avoiders n [[2, 1, 4, 3], [3, 1, 2, 4]]) (site gap : ℕ)
    (hsite : site ≤ p.length) (hgap : gap ≤ p.length)
    (hactive : p.insertIdx site (n + 1) ∈
      avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]]) :
    ((p.insertIdx site (n + 1)).insertIdx
        (if gap ≤ site then gap else gap + 1) (n + 2) ∈
          avoiders (n + 2) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
      p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ∧
        ∀ first second, (if gap ≤ site then 0 else site) ≤ first →
          first < second → second < gap →
          if gap ≤ site then p.getD first 0 < p.getD second 0
          else p.getD second 0 < p.getD first 0) ∧
      ((p.insertIdx site (n + 1)).insertIdx (site + 1) (n + 2) ∈
        avoiders (n + 2) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
        ∃ earlier < site, p.getD earlier 0 = n) := by
  constructor
  · have hperm := hparent.1
    have h2143 : NonnestingDefs.Occurs [2, 1, 4, 3]
          ((p.insertIdx site (n + 1)).insertIdx
            (if gap ≤ site then gap else gap + 1) (n + 2)) ↔
        NonnestingDefs.Occurs [2, 1, 4, 3] (p.insertIdx site (n + 1)) ∨
        NonnestingDefs.Occurs [2, 1, 4, 3] (p.insertIdx gap (n + 1)) ∨
        ∃ first second, first < second ∧ second < gap ∧ gap ≤ site ∧
          p.getD second 0 < p.getD first 0 := by
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
      have hlowerbound (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
          lower index < p.length := by dsimp [lower]; split_ifs <;> omega
      have hbound (index : ℕ) (hi : index < child.length) : child.getD index 0 ≤ n + 1 := by
        by_cases heq : index = site
        · subst index
          omega
        · rw [hlowerentry index hi heq]
          exact le_trans (hentry _ (hlowerbound index hi heq)) (by omega)
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
      have hliftmono (first second : ℕ) (hlt : first < second) : lift first < lift second := by
        dsimp [lift]
        split_ifs <;> omega
      have hliftprefix (index : ℕ) (hi : index < gap) : lift index < nextgap := by
        dsimp [lift, nextgap]
        split_ifs <;> omega
      have hliftsuffix (index : ℕ) (hi : gap ≤ index) : nextgap ≤ lift index := by
        dsimp [lift, nextgap]
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
          ∃ first second, first < second ∧ second < gap ∧ gap ≤ site ∧
            p.getD second 0 < p.getD first 0 := by
        constructor
        · rintro ⟨first, second, third, hfs, hsecond, hthird, htb, hlow, hhigh⟩
          have hfb : first < child.length := by omega
          have hsb : second < child.length := by omega
          have hfirstne : first ≠ site := by
            intro heq
            rw [heq, hat] at hhigh
            have := hbound third htb
            omega
          have hsecondne : second ≠ site := by
            intro heq
            rw [heq, hat] at hlow
            have := hbound first hfb
            omega
          by_cases hthirdsite : third = site
          · right
            have hle : gap ≤ site := by
              dsimp [nextgap] at hthird
              split_ifs at hthird <;> omega
            have hnext : nextgap = gap := if_pos hle
            rw [hnext] at hsecond
            rw [hbefore first (by omega), hbefore second (by omega)] at hlow
            exact ⟨first, second, hfs, hsecond, hle, hlow⟩
          · left
            rw [hlowerentry first hfb hfirstne, hlowerentry second hsb hsecondne] at hlow
            rw [hlowerentry first hfb hfirstne, hlowerentry third htb hthirdsite] at hhigh
            exact ⟨lower first, lower second, lower third,
              hlowermono first second hfs hfirstne hsecondne,
              hlowerprefix second hsecondne hsecond,
              hlowersuffix third hthirdsite hthird,
              hlowerbound third htb hthirdsite, hlow, hhigh⟩
        · rintro (⟨first, second, third, hfs, hsecond, hthird, htb, hlow, hhigh⟩ |
            ⟨first, second, hfs, hsecond, hle, hlow⟩)
          · refine ⟨lift first, lift second, lift third, hliftmono first second hfs,
              hliftprefix second hsecond, hliftsuffix third hthird, hliftbound third htb,
              ?_, ?_⟩
            · rwa [hliftentry first (by omega), hliftentry second (by omega)]
            · rwa [hliftentry first (by omega), hliftentry third htb]
          · have hnext : nextgap = gap := if_pos hle
            refine ⟨first, second, site, hfs, ?_, ?_, ?_, ?_, ?_⟩
            · omega
            · omega
            · omega
            · rwa [hbefore first (by omega), hbefore second (by omega)]
            · rw [hbefore first (by omega), hat]
              have := hentry first (by omega)
              omega
      have hchildtest := maximum_2143_test (n + 1) child hchildperm nextgap hnextgap
      have hparenttest := maximum_2143_test n p hperm gap hgap
      change _ ↔ _ ∨ _ ∨ _
      rw [hchildtest]
      change _ ∨ guard child nextgap ↔ _ ∨ _ ∨ _
      rw [hguard, hparenttest]
      have hsub : p.Sublist child := List.sublist_insertIdx p site (n + 1)
      have hinherited : NonnestingDefs.Occurs [2, 1, 4, 3] p →
          NonnestingDefs.Occurs [2, 1, 4, 3] child := by
        rintro ⟨values, hstep, hmem, hindices, _⟩
        exact ⟨values, hstep, fun rank hlo hhi => hsub.subset (hmem rank hlo hhi),
          hindices.trans hsub, by simp⟩
      constructor
      · rintro (hchild | hguard | hpair)
        · exact Or.inl hchild
        · exact Or.inr (Or.inl (Or.inr hguard))
        · exact Or.inr (Or.inr hpair)
      · rintro (hchild | (hparent | hguard) | hpair)
        · exact Or.inl hchild
        · exact Or.inl (hinherited hparent)
        · exact Or.inr (Or.inl hguard)
        · exact Or.inr (Or.inr hpair)
    
    let child := p.insertIdx site (n + 1)
    let nextgap := if gap ≤ site then gap else gap + 1
    let lift := fun index : ℕ => if index < site then index else index + 1
    let lower := fun index : ℕ => if index < site then index else index - 1
    have hlength : child.length = p.length + 1 :=
      List.length_insertIdx_of_le_length hsite (n + 1)
    have hnextgap : nextgap ≤ child.length := by dsimp [nextgap]; split_ifs <;> omega
    have hmax : ∀ value ∈ p, value < n + 1 := by
      intro value hm
      have hrange := hparent.1.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, hvalue⟩ := hrange
      omega
    have hmaxchild : ∀ value ∈ child, value < n + 2 := by
      intro value hm
      have hrange := hactive.1.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, hvalue⟩ := hrange
      omega
    have hentry (index : ℕ) (hi : index < p.length) : p.getD index 0 < n + 1 := by
      rw [List.getD_eq_getElem p 0 hi]
      exact hmax _ (List.getElem_mem hi)
    have hliftbound (index : ℕ) (hi : index < p.length) : lift index < child.length := by
      dsimp [lift]; split_ifs <;> omega
    have hliftentry (index : ℕ) (hi : index < p.length) :
        child.getD (lift index) 0 = p.getD index 0 := by
      dsimp [lift]
      split_ifs with hlt
      · rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hlt,
          List.getD_eq_getElem p 0 hi]
      · rw [List.getD_eq_getElem child 0 (by omega),
          List.getElem_insertIdx_of_gt (by omega), List.getD_eq_getElem p 0 (by omega)]
        simp only [Nat.add_sub_cancel]
    have hlowerentry (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
        child.getD index 0 = p.getD (lower index) 0 := by
      dsimp [lower]
      split_ifs with hlt
      · rw [List.getD_eq_getElem child 0 hi, List.getElem_insertIdx_of_lt hlt,
          List.getD_eq_getElem p 0 (by omega)]
      · rw [List.getD_eq_getElem child 0 hi, List.getElem_insertIdx_of_gt (by omega),
          List.getD_eq_getElem p 0 (by omega)]
    have hat : child.getD site 0 = n + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]
      exact List.getElem_insertIdx_self _
    have hfish : IsFishburn (child.insertIdx nextgap (n + 2)) ↔
        IsFishburn (p.insertIdx gap (n + 1)) := by
      rw [isFishburn_insertIdx_max_iff child (n + 2) nextgap hnextgap hmaxchild,
        isFishburn_insertIdx_max_iff p (n + 1) gap hgap hmax]
      constructor
      · rintro ⟨_, htest⟩
        refine ⟨hparent.2.1, ?_⟩
        intro before later hbefore hlater hb heq
        have hliftboundary : lift before + 1 = nextgap := by
          dsimp [lift, nextgap]; split_ifs <;> omega
        have hliftsuffix : nextgap ≤ lift later := by
          dsimp [lift, nextgap]; split_ifs <;> omega
        apply htest (lift before) (lift later) hliftboundary hliftsuffix (hliftbound later hb)
        rwa [hliftentry before (by omega), hliftentry later hb]
      · rintro ⟨_, htest⟩
        refine ⟨hactive.2.1, ?_⟩
        intro before later hbefore hlater hb heq
        have hbeforene : before ≠ site := by
          dsimp [nextgap] at hbefore; split_ifs at hbefore <;> omega
        have hlowerboundary : lower before + 1 = gap := by
          dsimp [lower, nextgap] at *; split_ifs at * <;> omega
        by_cases hlatersite : later = site
        · rw [hlatersite, hat, hlowerentry before (by omega) hbeforene] at heq
          have hlowerbound : lower before < p.length := by
            dsimp [lower]; split_ifs <;> omega
          have := hentry (lower before) hlowerbound
          omega
        · have hlowerbound : lower later < p.length := by
            dsimp [lower]; split_ifs <;> omega
          have hlowersuffix : gap ≤ lower later := by
            dsimp [lower, nextgap] at *; split_ifs at * <;> omega
          apply htest (lower before) (lower later) hlowerboundary hlowersuffix hlowerbound
          rwa [hlowerentry before (by omega) hbeforene,
            hlowerentry later hb hlatersite] at heq
    have h312 := (maximum_pattern_transport n p hperm site gap hsite hgap).2.1
    have hchild2143 : ¬ NonnestingDefs.Occurs [2, 1, 4, 3] child :=
      hactive.2.2 _ (by simp)
    have hchild3124 : ¬ NonnestingDefs.Occurs [3, 1, 2, 4] child :=
      hactive.2.2 _ (by simp)
    have hinsertperm : (p.insertIdx gap (n + 1)).Perm (List.range' 1 (n + 1)) := by
      have hp := (List.perm_insertIdx (n + 1) p hgap).trans (hparent.1.cons (n + 1))
      rw [List.range'_concat]
      simpa only [Nat.one_mul, Nat.add_comm, List.singleton_append] using
        hp.trans (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
    have hnextperm : (child.insertIdx nextgap (n + 2)).Perm (List.range' 1 (n + 2)) := by
      have hp := (List.perm_insertIdx (n + 2) child hnextgap).trans (hactive.1.cons (n + 2))
      have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
        simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
          show 1 + (n + 1) = n + 2 by omega] using
          (List.range'_concat (s := 1) (n := n + 1) (step := 1))
      rw [hrange]
      simpa only [List.singleton_append] using
        hp.trans (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
    have hdecreasing :
        (¬ ∃ first second, first < second ∧ second < gap ∧ gap ≤ site ∧
          p.getD second 0 < p.getD first 0) ∧
        (¬ ∃ first second, site ≤ first ∧ first < second ∧ second < gap ∧
          p.getD first 0 < p.getD second 0) ↔
        ∀ first second, (if gap ≤ site then 0 else site) ≤ first →
          first < second → second < gap →
          if gap ≤ site then p.getD first 0 < p.getD second 0
          else p.getD second 0 < p.getD first 0 := by
      have hnodup : p.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
      constructor
      · rintro ⟨hleft, hright⟩ first second hstart hfs hb
        have hne : p.getD first 0 ≠ p.getD second 0 := by
          intro heq
          have hi := (List.getD_inj (by omega) (by omega) hnodup).mp heq
          omega
        by_cases hle : gap ≤ site
        · simp only [if_pos hle]
          by_contra hnot
          have hgt : p.getD second 0 < p.getD first 0 := by omega
          exact hleft ⟨first, second, hfs, hb, hle, hgt⟩
        · simp only [if_neg hle] at hstart ⊢
          by_contra hnot
          have hlt : p.getD first 0 < p.getD second 0 := by omega
          exact hright ⟨first, second, hstart, hfs, hb, hlt⟩
      · intro hdec
        constructor
        · rintro ⟨first, second, hfs, hb, hle, hlt⟩
          have hd := hdec first second (by simp [hle]) hfs hb
          simp only [if_pos hle] at hd
          omega
        · rintro ⟨first, second, hs, hfs, hb, hlt⟩
          have hgt : ¬ gap ≤ site := by omega
          have hd := hdec first second (by simpa [hgt] using hs) hfs hb
          simp only [if_neg hgt] at hd
          omega
    change child.insertIdx nextgap (n + 2) ∈ _ ↔ _
    change NonnestingDefs.Occurs [2, 1, 4, 3] (child.insertIdx nextgap (n + 2)) ↔
      NonnestingDefs.Occurs [2, 1, 4, 3] child ∨ _ at h2143
    change NonnestingDefs.Occurs [3, 1, 2, 4] (child.insertIdx nextgap (n + 2)) ↔
      NonnestingDefs.Occurs [3, 1, 2, 4] child ∨ _ at h312
    simp only [avoiders, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, hnextperm, hinsertperm, true_and]
    rw [hfish, h2143, h312]
    simp only [not_or, hchild2143, hchild3124, not_false_eq_true, true_and]
    constructor
    · rintro ⟨hfish, ⟨hold2143, hleft⟩, hold3124, hright⟩
      exact ⟨⟨hfish, hold2143, hold3124⟩, hdecreasing.mp ⟨hleft, hright⟩⟩
    · rintro ⟨⟨hfish, hold2143, hold3124⟩, hdec⟩
      obtain ⟨hleft, hright⟩ := hdecreasing.mpr hdec
      exact ⟨hfish, ⟨hold2143, hleft⟩, hold3124, hright⟩
  
  · let child := p.insertIdx site (n + 1)
    have hlength : child.length = p.length + 1 :=
      List.length_insertIdx_of_le_length hsite (n + 1)
    have hnewsite : site + 1 ≤ child.length := by omega
    have hmaxchild : ∀ value ∈ child, value < n + 2 := by
      intro value hm
      have hrange := hactive.1.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, hvalue⟩ := hrange
      omega
    have hentry (index : ℕ) (hi : index < p.length) : p.getD index 0 ≤ n := by
      rw [List.getD_eq_getElem p 0 hi]
      have hrange := hparent.1.mem_iff.mp (List.getElem_mem hi)
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
    have hafter (index : ℕ) (hi : site < index) (hb : index < child.length) :
        child.getD index 0 = p.getD (index - 1) 0 := by
      rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hi,
        List.getD_eq_getElem p 0 (by omega)]
    have hchildbound (index : ℕ) (hi : index < child.length) :
        child.getD index 0 ≤ n + 1 := by
      rw [List.getD_eq_getElem child 0 hi]
      have hm := hmaxchild _ (List.getElem_mem hi)
      omega
    have h2143 := maximum_2143_test (n + 1) child hactive.1 (site + 1) hnewsite
    have h312 := (FishburnBasicPatterns.maximum_pattern_tests
      (n + 1) child hactive.1 (site + 1) hnewsite).2.1
    have hno2143 : ¬ NonnestingDefs.Occurs [2, 1, 4, 3]
        (child.insertIdx (site + 1) (n + 2)) := by
      intro hocc
      rcases h2143.mp hocc with hprevious |
        ⟨first, second, third, hfs, hs, ht, htb, hlow, hhigh⟩
      · exact hactive.2.2 _ (by simp) hprevious
      · have hsecond : second < site := by
          by_contra hnot
          have heq : second = site := by omega
          rw [heq, hat] at hlow
          have := hchildbound first (by omega)
          omega
        rw [hbefore first (by omega), hbefore second hsecond] at hlow
        rw [hbefore first (by omega), hafter third (by omega) htb] at hhigh
        apply hactive.2.2 [2, 1, 4, 3] (by simp)
        apply (maximum_2143_test n p hparent.1 site hsite).mpr
        exact Or.inr ⟨first, second, third - 1, hfs, hsecond, by omega, by omega,
          hlow, hhigh⟩
    have hno3124 : ¬ NonnestingDefs.Occurs [3, 1, 2, 4]
        (child.insertIdx (site + 1) (n + 2)) := by
      intro hocc
      rcases h312.mp hocc with hprevious |
        ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩
      · exact hactive.2.2 _ (by simp) hprevious
      · have hthird : third < site := by
          by_contra hnot
          have heq : third = site := by omega
          rw [heq, hat] at hhigh
          have := hchildbound first (by omega)
          omega
        rw [hbefore second (by omega), hbefore third hthird] at hlow
        rw [hbefore third hthird, hbefore first (by omega)] at hhigh
        apply hactive.2.2 [3, 1, 2, 4] (by simp)
        apply (FishburnBasicPatterns.maximum_pattern_tests
          n p hparent.1 site hsite).2.1.mpr
        exact Or.inr ⟨first, second, third, hfs, hst, hthird, hlow, hhigh⟩
    have hperm : (child.insertIdx (site + 1) (n + 2)).Perm
        (List.range' 1 (n + 2)) := by
      have hp := (List.perm_insertIdx (n + 2) child hnewsite).trans
        (hactive.1.cons (n + 2))
      have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
        simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
          show 1 + (n + 1) = n + 2 by omega] using
          (List.range'_concat (s := 1) (n := n + 1) (step := 1))
      rw [hrange]
      simpa only [List.singleton_append] using
        hp.trans (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
    have hfish : IsFishburn (child.insertIdx (site + 1) (n + 2)) ↔
        ∃ earlier < site, p.getD earlier 0 = n := by
      rw [isFishburn_insertIdx_max_iff child (n + 2) (site + 1) hnewsite hmaxchild]
      constructor
      · rintro ⟨_, htest⟩
        have hmem : n ∈ p := hparent.1.mem_iff.mpr (by
          simp only [List.mem_range', Nat.one_mul]
          exact ⟨n - 1, by omega, by omega⟩)
        obtain ⟨earlier, hb, he⟩ := List.mem_iff_getElem.mp hmem
        have hv : p.getD earlier 0 = n := by rwa [List.getD_eq_getElem p 0 hb]
        refine ⟨earlier, ?_, hv⟩
        by_contra hnot
        apply htest site (earlier + 1) rfl (by omega) (by omega)
        rw [hat, hafter (earlier + 1) (by omega) (by omega), Nat.add_sub_cancel, hv]
      · rintro ⟨earlier, hearlier, hvalue⟩
        refine ⟨hactive.2.1, ?_⟩
        intro before later hbefore hlater hb heq
        have hbeforeeq : before = site := by omega
        rw [hbeforeeq, hat, hafter later (by omega) hb] at heq
        have hlatervalue : p.getD (later - 1) 0 = n := by omega
        have hnodup : p.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
        have hi := (List.getD_inj (by omega) (by omega) hnodup).mp
          (hvalue.trans hlatervalue.symm)
        omega
    change child.insertIdx (site + 1) (n + 2) ∈ _ ↔ _
    constructor
    · intro hmember
      exact hfish.mp hmember.2.1
    · intro hleft
      refine ⟨hperm, hfish.mpr hleft, ?_⟩
      intro pattern hpattern
      have hc : pattern = [2, 1, 4, 3] ∨ pattern = [3, 1, 2, 4] := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hpattern
      rcases hc with rfl | rfl
      · exact hno2143
      · exact hno3124

end D5.S3.Combinatorics.Fishburn.FishburnTenNineSites
