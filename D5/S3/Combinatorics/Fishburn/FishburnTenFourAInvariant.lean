/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFourAInvariant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFourAInvariant
   mirror-E: none(waiver:maximum-deletion-a-prefix-classification)
   anchors: []
   utility: none
   digest: A members have an active identity prefix or maximum-containing positive sites. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasic2143
import D5.S3.Combinatorics.Fishburn.FishburnBasicPatternTransport
import D5.S3.Combinatorics.Fishburn.FishburnBasicPrefixes
import D5.S3.Combinatorics.Fishburn.FishburnTenFour2143Transport

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFourAInvariant

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicPatterns FishburnBasic2143 FishburnBasicPrefixes


open FishburnBasicPatternTransport FishburnTenFour2143Transport

theorem all_A_site_invariant : ∀ n : ℕ, 1 ≤ n → ∀ p : List ℕ,
    p ∈ avoiders n [[1, 3, 2, 4], [2, 1, 4, 3]] →
    p = List.range' 1 n ∨ (∃ run, 0 < run ∧ run < n ∧ p.take run = List.range' 1 run ∧
        p.getD run 0 ≠ run + 1 ∧ ∀ gap, gap ≤ p.length →
          (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [2, 1, 4, 3]] ↔ gap ≤ run)) ∨
      (1 < p.getD 0 0 ∧ (∃ gap, 0 < gap ∧ gap ≤ p.length ∧
          p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [2, 1, 4, 3]]) ∧
        ∀ gap, 0 < gap → gap ≤ p.length →
          p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [2, 1, 4, 3]] →
            ∃ earlier < gap, p.getD earlier 0 = n) := by
  let family (length : ℕ) := avoiders length [[1, 3, 2, 4], [2, 1, 4, 3]]
  have prepend_inherited_sites (n : ℕ) (p : List ℕ) (hpositive : 1 ≤ n)
      (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
      (patterns : List (List ℕ))
      (hpatterns : ∀ pattern ∈ patterns, pattern = [1, 3, 2, 4] ∨
        pattern = [2, 1, 4, 3])
      (site : ℕ) (hsite : site ≤ p.length) :
      ((n + 1) :: p).insertIdx (site + 1) (n + 2) ∈ avoiders (n + 2) patterns ↔
        site ≠ 0 ∧ p.insertIdx site (n + 1) ∈ avoiders (n + 1) patterns ∧
        ([3, 1, 2, 4] ∈ patterns → ∀ first second, first < second → second < site →
          p.getD second 0 < p.getD first 0) := by
    let child := (n + 1) :: p; have hmax : ∀ value ∈ p, value < n + 1 := by
      intro value hm; have hrange := hperm.mem_iff.mp hm
      simp only [List.mem_range', Nat.one_mul] at hrange; obtain ⟨offset, hoffset, heq⟩ := hrange
      omega
    have hmaxchild : ∀ value ∈ child, value < n + 2 := by
      intro value hm; change value ∈ (n + 1) :: p at hm; rcases List.mem_cons.mp hm with rfl | hm
      · omega
      · have := hmax value hm; omega
    have hchildperm : child.Perm (List.range' 1 (n + 1)) := by
      apply (hperm.cons (n + 1)).trans; rw [List.range'_concat]
      simpa [Nat.add_comm] using (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
    have hchildfish : IsFishburn child := by
      apply (isFishburn_insertIdx_max_iff p (n + 1) 0 (by omega) hmax).mpr
      exact ⟨hfish, by intro before later heq; omega⟩
    have hchildsite : site + 1 ≤ child.length := (by simp only [child, List.length_cons]; omega)
    have hat : child.getD 0 0 = n + 1 := rfl
    have hsucc (index : ℕ) : child.getD (index + 1) 0 = p.getD index 0 := by
      simp only [child, List.getD_cons_succ]
    have htail (index : ℕ) (hi : 0 < index) : child.getD index 0 = p.getD (index - 1) 0 := by
      obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : index ≠ 0)
      simpa using hsucc previous
    have hfishshift : IsFishburn (child.insertIdx (site + 1) (n + 2)) ↔
        site ≠ 0 ∧ IsFishburn (p.insertIdx site (n + 1)) := by
      rw [isFishburn_insertIdx_max_iff child (n + 2) (site + 1) hchildsite hmaxchild,
        isFishburn_insertIdx_max_iff p (n + 1) site hsite hmax]
      constructor
      · rintro ⟨_, hsafe⟩; have hnonzero : site ≠ 0 := by
          intro hzero; have hnmem : n ∈ p := by
            apply hperm.mem_iff.mpr; simp only [List.mem_range', Nat.one_mul]
            exact ⟨n - 1, by omega, by omega⟩
          obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hnmem
          have hentry : p.getD index 0 = n := (by rwa [List.getD_eq_getElem p 0 hindex])
          have hbad := hsafe 0 (index + 1) (by omega) (by omega)
            (by simp only [child, List.length_cons]; omega)
          exact hbad (by rw [hat, hsucc, hentry])
        refine ⟨hnonzero, hfish, ?_⟩
        intro before later hbefore hlater hlaterbound heq
        apply hsafe (before + 1) (later + 1) (by omega) (by omega)
          (by simp only [child, List.length_cons]; omega)
        rwa [hsucc, hsucc]
      · rintro ⟨hnonzero, _, hsafe⟩; refine ⟨hchildfish, ?_⟩
        intro before later hbefore hlater hlaterbound heq
        rw [htail before (by omega), htail later (by omega)] at heq
        exact hsafe (before - 1) (later - 1) (by omega) (by omega)
          (by simp only [child, List.length_cons] at hlaterbound; omega) heq
    by_cases hzero : site = 0
    · constructor
      · intro hmember; exact False.elim ((hfishshift.mp hmember.2.1).1 hzero)
      · intro hmember; exact False.elim (hmember.1 hzero)
    have htransport := maximum_pattern_transport n p hperm 0 site (by omega) hsite
    have htests := maximum_pattern_tests n p hperm 0 (by omega)
    have hbase132 : NonnestingDefs.Occurs [1, 3, 2, 4] child ↔
        NonnestingDefs.Occurs [1, 3, 2, 4] p := (by simpa [child] using htests.1)
    have hsite132 := maximum_pattern_tests n p hperm site hsite
    have h132 : NonnestingDefs.Occurs [1, 3, 2, 4] (child.insertIdx (site + 1) (n + 2)) ↔
        NonnestingDefs.Occurs [1, 3, 2, 4] (p.insertIdx site (n + 1)) := by
      have hs := htransport.1
      simp only [show ¬ site ≤ 0 by omega, if_false, List.insertIdx_zero] at hs
      rw [hbase132, hsite132.1] at hs; rw [hsite132.1]; simpa [child, or_assoc] using hs
    have hbase2143 : NonnestingDefs.Occurs [2, 1, 4, 3] child ↔
        NonnestingDefs.Occurs [2, 1, 4, 3] p := by
      simpa [child] using maximum_2143_test n p hperm 0 (by omega)
    have h2143 : NonnestingDefs.Occurs [2, 1, 4, 3] (child.insertIdx (site + 1) (n + 2)) ↔
        NonnestingDefs.Occurs [2, 1, 4, 3] (p.insertIdx site (n + 1)) := by
      have shift := (maximum_2143_transport n p hperm 0 site (by omega) hsite).1
      simp only [show ¬ site ≤ 0 by omega, if_false, List.insertIdx_zero] at shift
      rw [hbase2143, maximum_2143_test n p hperm site hsite] at shift
      rw [maximum_2143_test n p hperm site hsite]
      simpa [child, or_assoc] using shift
    constructor
    · intro hmember; have hf := hfishshift.mp hmember.2.1; refine ⟨hf.1, ⟨?_, hf.2, ?_⟩, ?_⟩
      · exact (List.perm_insertIdx (n + 1) p hsite).trans hchildperm
      · intro pattern hm hocc; rcases hpatterns pattern hm with rfl | rfl
        · exact hmember.2.2 _ hm (h132.mpr hocc)
        · exact hmember.2.2 _ hm (h2143.mpr hocc)
      · intro hm; have hc := hpatterns [3, 1, 2, 4] hm; simp at hc
    · rintro ⟨hnonzero, hmember, hdecreasing⟩
      refine ⟨?_, hfishshift.mpr ⟨hnonzero, hmember.2.1⟩, ?_⟩
      · apply (List.perm_insertIdx (n + 2) child hchildsite).trans
        apply (hchildperm.cons (n + 2)).trans
        have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
          simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
            show 1 + (n + 1) = n + 2 by omega] using
            (List.range'_concat (s := 1) (n := n + 1) (step := 1))
        rw [hrange]
        simpa using (List.perm_append_comm (l₁ := [n + 2]) (l₂ := List.range' 1 (n + 1)))
      · intro pattern hm hocc; rcases hpatterns pattern hm with rfl | rfl
        · exact hmember.2.2 _ hm (h132.mp hocc)
        · exact hmember.2.2 _ hm (h2143.mp hocc)
  have identity_insertion_rules (n cut : ℕ) (hcut : cut ≤ n) :
      (List.range' 1 n).insertIdx cut (n + 1) ∈ family (n + 1) := by
    let parent := List.range' 1 n; let child := parent.insertIdx cut (n + 1)
    have hlength : parent.length = n := (by simp [parent])
    have hparentperm : parent.Perm (List.range' 1 n) := List.Perm.refl _
    have hentry (index : ℕ) (hi : index < n) : parent.getD index 0 = index + 1 := by
      rw [List.getD_eq_getElem parent 0 (by omega)]
      simp [parent, List.getElem_range', Nat.add_comm]
    have hmax : ∀ value ∈ parent, value < n + 1 := by
      intro value hm; simp only [parent, List.mem_range', Nat.one_mul] at hm
      obtain ⟨offset, hoffset, hvalue⟩ := hm; omega
    have hfish : IsFishburn parent := by
      intro before later hgap hlater hbad
      rw [hentry before (by omega), hentry later (by omega)] at hbad; omega
    have hchildfish : IsFishburn child := by
      apply (isFishburn_insertIdx_max_iff parent (n + 1) cut (by omega) hmax).mpr
      refine ⟨hfish, ?_⟩
      intro before later hcross hafter hlater heq
      rw [hentry before (by omega), hentry later (by omega)] at heq; omega
    have hchildperm : child.Perm (List.range' 1 (n + 1)) := by
      have hp := List.perm_insertIdx (n + 1) parent (by omega : cut ≤ parent.length)
      rw [List.range'_concat]
      simpa only [Nat.one_mul, Nat.add_comm, List.singleton_append, parent] using
        hp.trans (List.perm_append_comm (l₁ := [n + 1]) (l₂ := parent))
    have hparentavoid (pattern : List ℕ)
        (hpattern : pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] ∨
          pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4]) :
        ¬ NonnestingDefs.Occurs pattern parent := by
      intro hocc; have hletters : NonnestingDefs.letters pattern = 4 := by
        rcases hpattern with rfl | rfl | rfl | rfl <;> rfl
      change ArrowWilfDefs.Contains pattern [] (NonnestingDefs.letters pattern) parent at hocc
      rw [hletters] at hocc; obtain ⟨values, hstep, _, hsub, _⟩ := hocc
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      have h34 : values 3 < values 4 := hstep 3 (by omega) (by omega)
      have hpair : (pattern.map values).Pairwise (· < ·) :=
        List.Pairwise.sublist hsub (List.pairwise_lt_range' 1)
      rcases hpattern with rfl | rfl | rfl | rfl
      all_goals
        simp only [List.map_cons, List.map_nil, List.pairwise_cons,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hpair
        omega
    have htests := maximum_pattern_tests n parent hparentperm cut (by omega)
    have h2143test := maximum_2143_test n parent hparentperm cut (by omega)
    have hno132 : ¬ NonnestingDefs.Occurs [1, 3, 2, 4] child := by
      intro hocc; rcases htests.1.mp hocc with hold | hnew
      · exact hparentavoid _ (by simp) hold
      · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hnew
        rw [hentry second (by omega), hentry third (by omega)] at hhigh; omega
    have hno2143 : ¬ NonnestingDefs.Occurs [2, 1, 4, 3] child := by
      intro hocc; rcases h2143test.mp hocc with hold | hnew
      · exact hparentavoid _ (by simp) hold
      · obtain ⟨first, second, third, hfs, hs, ht, htb, hlow, hhigh⟩ := hnew
        rw [hentry first (by omega), hentry second (by omega)] at hlow; omega
    change child ∈ family (n + 1); refine ⟨hchildperm, hchildfish, ?_⟩
    intro pattern hm
    have hc : pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
    rcases hc with rfl | rfl
    · exact hno132
    · exact hno2143
  have positive_A_inherited_sites (n : ℕ) (p : List ℕ) (hparent : p ∈ family n)
      (site : ℕ) (hpositive : 0 < site) (hsite : site ≤ p.length)
      (hactive : p.insertIdx site (n + 1) ∈ family (n + 1))
      (gap : ℕ) (hgpositive : 0 < gap) (hgap : gap ≤ p.length) :
      (p.insertIdx site (n + 1)).insertIdx (if gap ≤ site then gap else gap + 1) (n + 2) ∈
        family (n + 2) ↔
      p.insertIdx gap (n + 1) ∈ family (n + 1) ∧ gap ≤ site ∧ (p.take gap).Pairwise (· < ·) := by
    let child := p.insertIdx site (n + 1); let nextgap := if gap ≤ site then gap else gap + 1
    have hlength : child.length = p.length + 1 := List.length_insertIdx_of_le_length hsite (n + 1)
    have hnextgap : nextgap ≤ child.length := (by dsimp [nextgap]; split_ifs <;> omega)
    have hnodup : p.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
    have hmax (value : ℕ) (hm : value ∈ p) : value < n + 1 := by
      have hrange := hparent.1.mem_iff.mp hm; simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, hvalue⟩ := hrange; omega
    have hentry (index : ℕ) (hi : index < p.length) : 1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
      have hm : p.getD index 0 ∈ p := by
        rw [List.getD_eq_getElem p 0 hi]; exact List.getElem_mem hi
      have hrange := hparent.1.mem_iff.mp hm; simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, hvalue⟩ := hrange; omega
    have hperm (word : List ℕ) (size cut : ℕ)
        (hp : word.Perm (List.range' 1 size)) (hc : cut ≤ word.length) :
        (word.insertIdx cut (size + 1)).Perm (List.range' 1 (size + 1)) := by
      have hp' := (List.perm_insertIdx (size + 1) word hc).trans (hp.cons (size + 1))
      rw [List.range'_concat]; simpa only [Nat.one_mul, Nat.add_comm, List.singleton_append] using
        hp'.trans (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    have hfishiff := (maximum_2143_transport n p hparent.1 site gap hsite hgap).2.1
      hpositive hgpositive hparent.2.1 hactive.2.1
    have h132 := (maximum_pattern_transport n p hparent.1 site gap hsite hgap).1
    have h2143 := (maximum_2143_transport n p hparent.1 site gap hsite hgap).1
    have hincreasing : (p.take gap).Pairwise (· < ·) ↔
        ¬ ∃ first second, first < second ∧ second < gap ∧ p.getD second 0 < p.getD first 0 := by
      constructor
      · intro hp ⟨first, second, hfs, hs, hlt⟩
        have hi := List.pairwise_iff_getElem.mp hp first second
          (by simp only [List.length_take]; omega) (by simp only [List.length_take]; omega) hfs
        rw [List.getD_eq_getElem p 0 (by omega), List.getD_eq_getElem p 0 (by omega)] at hlt
        simp only [List.getElem_take] at hi; omega
      · intro hno; apply List.pairwise_iff_getElem.mpr; intro first second hfb hsb hfs
        have hs : second < gap := (by simp only [List.length_take] at hsb; omega)
        have hfirstbound : first < p.length := (by omega)
        have hsecondbound : second < p.length := (by omega); simp only [List.getElem_take]
        rcases lt_trichotomy p[first] p[second] with hlt | heq | hgt
        · exact hlt
        · have hindex := hnodup.getElem_inj_iff.mp heq; omega
        · apply False.elim; apply hno; refine ⟨first, second, hfs, hs, ?_⟩
          rwa [List.getD_eq_getElem p 0 hsecondbound, List.getD_eq_getElem p 0 hfirstbound]
    change child.insertIdx nextgap (n + 2) ∈ avoiders (n + 2) _ ↔ _; constructor
    · intro hnew; have hold : p.insertIdx gap (n + 1) ∈ family (n + 1) := by
        refine ⟨hperm p n gap hparent.1 hgap, hfishiff.mp hnew.2.1, ?_⟩
        intro pattern hm hocc
        have hc : pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
        rcases hc with rfl | rfl
        · exact hnew.2.2 _ (by simp) (h132.mpr (Or.inr (Or.inl hocc)))
        · exact hnew.2.2 _ (by simp) (h2143.mpr (Or.inr (Or.inl hocc)))
      have hle : gap ≤ site := by
        by_contra hnot
        have hguard := (isFishburn_insertIdx_max_iff p (n + 1) site hsite hmax).mp hactive.2.1
        have hone := (eligible_prefix_structure n p hparent.1 hparent.2.1 site
          hsite hpositive hguard.2).1
        obtain ⟨one, honebound, honevalue⟩ := List.mem_iff_getElem.mp hone
        have honesite : one < site := (by simp only [List.length_take] at honebound; omega)
        have honeentry : p.getD one 0 = 1 := by
          rw [List.getD_eq_getElem p 0 (by omega)]; simpa only [List.getElem_take] using honevalue
        have hsitebound : site < p.length := (by omega); have hsitevalue : 1 < p.getD site 0 := by
          have hp := hentry site hsitebound; have hneq : p.getD site 0 ≠ 1 := by
            intro heq
            have hi := (List.getD_inj hsitebound (by omega) hnodup).mp (heq.trans honeentry.symm)
            omega
          omega
        apply hnew.2.2 [1, 3, 2, 4] (by simp); apply h132.mpr; right; right
        refine ⟨one, site, honesite, le_rfl, by omega, ?_⟩
        rwa [honeentry]
      refine ⟨hold, hle, hincreasing.mpr ?_⟩
      intro hinv; exact hnew.2.2 _ (by simp) (h2143.mpr (Or.inr (Or.inr ⟨hle, hinv⟩)))
    · rintro ⟨hold, hle, hinc⟩; have hnextperm := hperm child (n + 1) nextgap hactive.1 hnextgap
      rw [show n + 1 + 1 = n + 2 by omega] at hnextperm
      refine ⟨hnextperm, hfishiff.mpr hold.2.1, ?_⟩
      intro pattern hm hocc
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
      rcases hc with rfl | rfl
      · rcases h132.mp hocc with hchild | holdocc | ⟨first, third, hf, ht, hthird, hlt⟩
        · exact hactive.2.2 _ (by simp) hchild
        · exact hold.2.2 _ (by simp) holdocc
        · omega
      · rcases h2143.mp hocc with hchild | holdocc | ⟨_, hinv⟩
        · exact hactive.2.2 _ (by simp) hchild
        · exact hold.2.2 _ (by simp) holdocc
        · exact hincreasing.mp hinc hinv
  have maximum_insertion_bijection (n : ℕ) (patterns : List (List ℕ)) :
      Function.Bijective (fun entry : {entry : List ℕ × ℕ //
        entry.1 ∈ avoiders n patterns ∧ entry.2 ≤ entry.1.length ∧
          entry.1.insertIdx entry.2 (n + 1) ∈ avoiders (n + 1) patterns} =>
        (⟨entry.val.1.insertIdx entry.val.2 (n + 1), entry.property.2.2⟩ :
          avoiders (n + 1) patterns)) := by
    constructor
    · intro first second heq; have hchild : first.val.1.insertIdx first.val.2 (n + 1) =
          second.val.1.insertIdx second.val.2 (n + 1) := congrArg Subtype.val heq
      have hfirstlen : (first.val.1.insertIdx first.val.2 (n + 1)).length =
          first.val.1.length + 1 :=
        List.length_insertIdx_of_le_length first.property.2.1 _
      have hsecondlen : (second.val.1.insertIdx second.val.2 (n + 1)).length =
          second.val.1.length + 1 :=
        List.length_insertIdx_of_le_length second.property.2.1 _
      have hfirstbound : first.val.2 <
          (first.val.1.insertIdx first.val.2 (n + 1)).length := (by omega)
      have hsecondbound : second.val.2 <
          (first.val.1.insertIdx first.val.2 (n + 1)).length := (by rw [hchild]; omega)
      have hfirstat : (first.val.1.insertIdx first.val.2 (n + 1)).getD first.val.2 0 = n + 1 := by
        rw [List.getD_eq_getElem _ 0 hfirstbound]; exact List.getElem_insertIdx_self _
      have hsecondat : (first.val.1.insertIdx first.val.2 (n + 1)).getD second.val.2 0 = n + 1 := by
        rw [hchild, List.getD_eq_getElem _ 0 (by omega)]; exact List.getElem_insertIdx_self _
      have hnodup : (first.val.1.insertIdx first.val.2 (n + 1)).Nodup :=
        first.property.2.2.1.nodup_iff.mpr (List.nodup_range' 1)
      have hsites : first.val.2 = second.val.2 :=
        (List.getD_inj hfirstbound hsecondbound hnodup).mp (hfirstat.trans hsecondat.symm)
      have hparents : first.val.1 = second.val.1 := by
        rw [hsites] at hchild; exact List.insertIdx_injective _ _ hchild
      apply Subtype.ext; exact Prod.ext hparents hsites
    · intro child; have hlen : child.val.length = n + 1 := by
        simpa only [List.length_range'] using child.property.1.length_eq
      have hmaxmem : n + 1 ∈ child.val := by
        apply child.property.1.mem_iff.mpr; simp only [List.mem_range', Nat.one_mul]
        exact ⟨n, by omega, by omega⟩
      obtain ⟨site, hsitechild, hvalue⟩ := List.mem_iff_getElem.mp hmaxmem
      let parent := child.val.eraseIdx site
      have hinverse : parent.insertIdx site (n + 1) = child.val := by
        simpa only [parent, hvalue] using List.insertIdx_eraseIdx_getElem hsitechild
      have hparentlen : parent.length = n := by
        simp only [parent, List.length_eraseIdx_of_lt hsitechild, hlen]; omega
      have hsite : site ≤ parent.length := (by omega)
      have hparentperm : parent.Perm (List.range' 1 n) := by
        have hcons : ((n + 1) :: parent).Perm child.val := by
          simpa only [parent, hvalue] using List.getElem_cons_eraseIdx_perm hsitechild
        have hrange : (List.range' 1 (n + 1)).Perm ((n + 1) :: List.range' 1 n) := by
          rw [List.range'_concat]
          simpa [Nat.add_comm] using (List.perm_append_comm (l₁ := List.range' 1 n) (l₂ := [n + 1]))
        exact (hcons.trans (child.property.1.trans hrange)).cons_inv
      have hmaxparent : ∀ value ∈ parent, value < n + 1 := by
        intro value hvalue; have hm := hparentperm.mem_iff.mp hvalue
        simp only [List.mem_range', Nat.one_mul] at hm; obtain ⟨offset, hoffset, heq⟩ := hm; omega
      have hparentmember : parent ∈ avoiders n patterns := by
        refine ⟨hparentperm, ?_, ?_⟩
        · apply (isFishburn_insertIdx_max_iff parent (n + 1) site hsite hmaxparent).mp
            (by rw [hinverse]; exact child.property.2.1) |>.1
        · intro pattern hpattern hocc; obtain ⟨values, hstep, hmem, hsub, hrel⟩ := hocc
          apply child.property.2.2 pattern hpattern
          refine ⟨values, hstep, ?_, hsub.trans (List.eraseIdx_sublist child.val site), by simp⟩
          intro rank hlow hhigh
          exact (List.eraseIdx_sublist child.val site).subset (hmem rank hlow hhigh)
      refine ⟨⟨(parent, site), hparentmember, hsite, ?_⟩, ?_⟩
      · rw [hinverse]; exact child.property
      · exact Subtype.ext hinverse
  have after_maximum_active_iff (n : ℕ) (p : List ℕ) (patterns : List (List ℕ))
      (hpatterns : ∀ pattern ∈ patterns, pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨
        pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3])
      (hparent : p ∈ avoiders n patterns) (site : ℕ)
      (hpositive : 0 < site) (hsite : site ≤ p.length)
      (hactive : p.insertIdx site (n + 1) ∈ avoiders (n + 1) patterns) :=
    (maximum_2143_transport n p hparent.1 site 0 hsite (by omega)).2.2
      patterns hpatterns hparent hpositive hactive
  have hpatterns : ∀ pattern ∈ [[1, 3, 2, 4], [2, 1, 4, 3]],
      pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨
        pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3] := by
    intro pattern hm
    have hc : pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
    rcases hc with rfl | rfl <;> simp
  have hprependpatterns : ∀ pattern ∈ [[1, 3, 2, 4], [2, 1, 4, 3]],
      pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := by
    intro pattern hm
    have hc : pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
    rcases hc with rfl | rfl <;> simp
  have hfront (size : ℕ) (word : List ℕ) (hword : word ∈ family size) :
      word.insertIdx 0 (size + 1) ∈ family (size + 1) := by
    refine ⟨?_, ?_, ?_⟩
    · apply (List.perm_insertIdx (size + 1) word (by omega)).trans
      apply (hword.1.cons (size + 1)).trans; rw [List.range'_concat]; simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    · apply (isFishburn_insertIdx_max_iff word (size + 1) 0 (by omega) ?_).mpr
      · exact ⟨hword.2.1, by intro before later heq; omega⟩
      · intro value hm; have hrange := hword.1.mem_iff.mp hm
        simp only [List.mem_range', Nat.one_mul] at hrange; obtain ⟨offset, hoffset, heq⟩ := hrange
        omega
    · intro pattern hm hocc
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
      rcases hc with rfl | rfl
      · have ht := (maximum_pattern_tests size word hword.1 0 (by omega)).1
        exact hword.2.2 _ hm (by simpa using ht.mp hocc)
      · have ht := maximum_2143_test size word hword.1 0 (by omega)
        exact hword.2.2 _ hm (by simpa using ht.mp hocc)
  intro size; induction size with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn word hword; by_cases hid : word = List.range' 1 (n + 1)
    · exact Or.inl hid
    right
    have hnpositive : 1 ≤ n := by
      by_contra hnot
      have hnzero : n = 0 := (by omega); subst n
      have hp : word.Perm [1] := hword.1; exact hid (List.perm_singleton.mp hp)
    obtain ⟨entry, hentry⟩ := (maximum_insertion_bijection n
      [[1, 3, 2, 4], [2, 1, 4, 3]]).2 ⟨word, hword⟩
    have heq : entry.val.1.insertIdx entry.val.2 (n + 1) = word := congrArg Subtype.val hentry
    rcases entry with ⟨⟨parent, site⟩, hparent, hsite, hactive⟩
    dsimp only at hparent hsite hactive heq; subst word
    let child := parent.insertIdx site (n + 1); have hlen : child.length = n + 1 := by
      rw [List.length_insertIdx_of_le_length hsite]; simpa using hparent.1.length_eq
    have hinsertlen : (parent.insertIdx site (n + 1)).length = n + 1 := hlen
    have hparentlen : parent.length = n := (by simpa using hparent.1.length_eq)
    have hmax (value : ℕ) (hm : value ∈ parent) : value < n + 1 := by
      have hrange := hparent.1.mem_iff.mp hm; simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, heq⟩ := hrange; omega
    have hbefore (index : ℕ) (hi : index < site) : child.getD index 0 = parent.getD index 0 := by
      rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
        List.getD_eq_getElem parent 0 (by omega)]
    have hat : child.getD site 0 = n + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]; exact List.getElem_insertIdx_self _
    have hparentclass := ih hnpositive parent hparent
    have hpositiveexists : ∃ gap, 0 < gap ∧ gap ≤ parent.length ∧ parent.insertIdx gap (n + 1) ∈
          family (n + 1) := by
      rcases hparentclass with hidparent | ⟨run, hrpos, hrn, hpref, hbreak, hshape⟩ |
        ⟨hfirst, hexists, hmaxprefix⟩
      · subst parent; exact ⟨1, by omega, by simp; omega, (identity_insertion_rules n 1 (by omega))⟩
      · exact ⟨run, hrpos, by omega, (hshape run (by omega)).mpr (le_refl _)⟩
      · exact hexists
    by_cases hsitezero : site = 0
    · subst site; right; refine ⟨by change 1 < n + 1; omega, ?_, ?_⟩
      · obtain ⟨gap, hp, hb, ha⟩ := hpositiveexists; refine ⟨gap + 1, by omega, by omega, ?_⟩
        apply (prepend_inherited_sites n parent hnpositive hparent.1 hparent.2.1
          [[1, 3, 2, 4], [2, 1, 4, 3]] hprependpatterns gap hb).mpr
        exact ⟨by omega, ha, by simp⟩
      · intro gap hp hb ha; exact ⟨0, hp, rfl⟩
    · have hsitepositive : 0 < site := (by omega)
      have hraw : ∀ gap, gap ≤ child.length → (child.insertIdx gap (n + 2) ∈ family (n + 2) ↔
            gap = 0 ∨ (gap = site + 1 ∧ ∃ earlier < site, parent.getD earlier 0 = n) ∨
              ∃ oldgap, 0 < oldgap ∧ oldgap ≤ parent.length ∧ oldgap ≤ site ∧
                oldgap = gap ∧ parent.insertIdx oldgap (n + 1) ∈ family (n + 1) ∧
                (parent.take oldgap).Pairwise (· < ·)) := by
        intro gap hg; by_cases hzero : gap = 0
        · subst gap; exact iff_of_true (hfront (n + 1) child hactive) (Or.inl rfl)
        by_cases hafter : gap = site + 1
        · subst gap; have ht := after_maximum_active_iff n parent
            [[1, 3, 2, 4], [2, 1, 4, 3]] hpatterns hparent site
            hsitepositive hsite hactive
          constructor
          · intro hh; exact Or.inr (Or.inl ⟨rfl, ht.mp hh⟩)
          · rintro (hz | ⟨_, hm⟩ | ⟨oldgap, hp, hb, hle, heq, ha, hinc⟩)
            · omega
            · exact ht.mpr hm
            · omega
        let oldgap := if gap ≤ site then gap else gap - 1
        have hp : 0 < oldgap := (by dsimp [oldgap]; split_ifs <;> omega)
        have hb : oldgap ≤ parent.length := (by dsimp [oldgap]; split_ifs <;> omega)
        have hmap : (if oldgap ≤ site then oldgap else oldgap + 1) = gap := by
          dsimp [oldgap]; split_ifs <;> omega
        have ht := positive_A_inherited_sites n parent hparent site hsitepositive hsite
          hactive oldgap hp hb
        rw [hmap] at ht; constructor
        · intro hh; obtain ⟨ha, hle, hinc⟩ := ht.mp hh
          have heq : oldgap = gap := (by rw [if_pos hle] at hmap; exact hmap)
          exact Or.inr (Or.inr ⟨oldgap, hp, hb, hle, heq, ha, hinc⟩)
        · rintro (hz | ⟨heq, _⟩ | ⟨othergap, hop, hob, hle, heq, ha, hinc⟩)
          · omega
          · omega
          · have ho : othergap = oldgap := (by dsimp [oldgap]; split_ifs <;> omega)
            exact ht.mpr ⟨by simpa only [ho] using ha, by simpa only [ho] using hle,
              by simpa only [ho] using hinc⟩
      have hprefixcase : (site < n ∧ parent.take site = List.range' 1 site ∧
            ∀ gap, 0 < gap → gap ≤ site → parent.insertIdx gap (n + 1) ∈ family (n + 1)) ∨
          (1 < parent.getD 0 0 ∧ ∃ earlier < site, parent.getD earlier 0 = n) := by
        rcases hparentclass with hidparent | ⟨run, hrpos, hrn, hpref, hbreak, hshape⟩ |
          ⟨hfirst, hexists, hmaxprefix⟩
        · left
          have hsiten : site < n := by
            by_contra hnot
            have hsiteeq : site = n := (by omega); apply hid; rw [hidparent, hsiteeq]
            have he : (List.range' 1 n).insertIdx n (n + 1) = List.range' 1 n ++ [n + 1] := by
              simpa only [List.length_range'] using
                (List.insertIdx_length_self (l := List.range' 1 n) (x := n + 1))
            exact he.trans (by simpa [Nat.add_comm] using
              (List.range'_concat (s := 1) (n := n) (step := 1)).symm)
          refine ⟨hsiten, ?_, ?_⟩
          · rw [hidparent]; exact List.take_range'_of_length_ge (by omega)
          · intro gap hp hb; rw [hidparent]; exact (identity_insertion_rules n gap (by omega))
        · left
          have hsiterun := (hshape site hsite).mp hactive; refine ⟨by omega, ?_, ?_⟩
          · have ht := congrArg (List.take site) hpref
            simpa only [List.take_take, Nat.min_eq_left hsiterun,
              List.take_range'_of_length_ge hsiterun] using ht
          · intro gap hp hb; exact (hshape gap (by omega)).mpr (by omega)
        · exact Or.inr ⟨hfirst, hmaxprefix site hsitepositive hsite hactive⟩
      rcases hprefixcase with ⟨hsiten, hpref, hprefixactive⟩ | ⟨hfirst, hmaxprefix⟩
      · left
        have hchildpref : child.take site = List.range' 1 site := by
          rw [List.take_insertIdx_eq_take_of_le parent (n + 1) site site (by omega)]; exact hpref
        have hprefixinc (gap : ℕ) (hg : gap ≤ site) : (parent.take gap).Pairwise (· < ·) := by
          have ht := congrArg (List.take gap) hpref
          have he : parent.take gap = List.range' 1 gap := by
            simpa only [List.take_take, Nat.min_eq_left hg,
              List.take_range'_of_length_ge hg] using ht
          rw [he]; exact List.pairwise_lt_range' 1
        have hnomax : ¬ ∃ earlier < site, parent.getD earlier 0 = n := by
          rintro ⟨earlier, he, hv⟩
          have hi : earlier < (parent.take site).length := (by simp only [List.length_take]; omega)
          have hentry := congrArg (fun word => word.getD earlier 0) hpref
          have hh : parent.getD earlier 0 = earlier + 1 := by
            rw [List.getD_eq_getElem parent 0 (by omega)]
            have hrangebound : earlier < (List.range' 1 site).length := (by simp; omega)
            simpa only [List.getD_eq_getElem (parent.take site) 0 hi, List.getElem_take,
              List.getD_eq_getElem (List.range' 1 site) 0 hrangebound,
              List.getElem_range', Nat.one_mul, Nat.add_comm] using hentry
          omega
        refine ⟨site, hsitepositive, by omega, hchildpref, ?_, ?_⟩
        · change child.getD site 0 ≠ site + 1; rw [hat]; omega
        · intro gap hg; rw [hraw gap hg]; constructor
          · rintro (hz | ⟨_, hm⟩ | ⟨oldgap, hp, hb, hle, heq, ha, hinc⟩)
            · omega
            · exact False.elim (hnomax hm)
            · omega
          · intro hle; by_cases hz : gap = 0
            · exact Or.inl hz
            · exact Or.inr (Or.inr ⟨gap, by omega, by omega, hle, rfl,
                hprefixactive gap (by omega) hle, hprefixinc gap hle⟩)
      · right
        have hchildfirst : 1 < child.getD 0 0 := (by rw [hbefore 0 hsitepositive]; exact hfirst)
        have hnewactive : child.insertIdx (site + 1) (n + 2) ∈ family (n + 2) := by
          apply (hraw (site + 1) (by omega)).mpr; exact Or.inr (Or.inl ⟨rfl, hmaxprefix⟩)
        refine ⟨hchildfirst, ⟨site + 1, by omega, by omega, hnewactive⟩, ?_⟩
        intro gap hp hb ha; rcases (hraw gap hb).mp ha with hz | ⟨heq, _⟩ |
          ⟨oldgap, hop, hob, hle, heq, holdactive, hinc⟩
        · omega
        · exact ⟨site, by omega, hat⟩
        · have heligible := (isFishburn_insertIdx_max_iff parent (n + 1) oldgap hob hmax).mp
            holdactive.2.1 |>.2
          have hpref := (eligible_prefix_structure n parent hparent.1 hparent.2.1
            oldgap hob hop heligible).2 hinc
          have hi : 0 < (parent.take oldgap).length := (by simp only [List.length_take]; omega)
          have hv := congrArg (fun word => word.getD 0 0) hpref
          have hfirstone : parent.getD 0 0 = 1 := by
            rw [List.getD_eq_getElem parent 0 (by omega)]
            have hrangebound : 0 < (List.range' 1 oldgap).length := (by simp; omega)
            simpa only [List.getD_eq_getElem (parent.take oldgap) 0 hi, List.getElem_take,
              List.getD_eq_getElem (List.range' 1 oldgap) 0 hrangebound,
              List.getElem_range', Nat.one_mul, Nat.add_zero] using hv
          omega

end D5.S3.Combinatorics.Fishburn.FishburnTenFourAInvariant
