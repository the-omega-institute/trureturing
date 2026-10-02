/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFourBCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFourBCount
   mirror-E: none(waiver:b-weighted-tree-counting)
   anchors: []
   utility: none
   digest: Maximum-deletion induction transfers the B path count to actual permutations. -/
import D5.S3.Combinatorics.Fishburn.FishburnTenFourBChildren
import D5.S3.Combinatorics.Fishburn.FishburnBasicPatternTransport
import D5.S3.Combinatorics.Fishburn.FishburnTenFour2143Transport
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Fishburn.FishburnTenFourBCount
open D5.S3.Combinatorics FishburnDefs FishburnTenFourBTree FishburnTenFourBChildren
open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicPatterns FishburnBasic2143
open FishburnTenFourBInvariant FishburnTenFourBTree
open FishburnBasicPatternTransport FishburnBasicPrefixes FishburnTenFour2143Transport
set_option maxHeartbeats 1600000 in
theorem B_count (size : ℕ) (hsize : 1 ≤ size) : (avoiders size [[1, 4, 2, 3], [2, 1, 4, 3]]).ncard =
      (size - 1) * 2 ^ (size - 2) + 1 := by
  let rec pathsFintype (depth : ℕ) (mark : Label) : Fintype (Paths depth mark) :=
    match depth, mark with
    | 0, _ => inferInstanceAs (Fintype Unit)
    | depth + 1, mark =>
      letI : ∀ mark, Fintype (Paths depth mark) := pathsFintype depth
      by cases mark <;> dsimp [Paths] <;> infer_instance
  letI (depth : ℕ) (mark : Label) : Fintype (Paths depth mark) := pathsFintype depth mark
  have hpathcount (depth : ℕ) :
      Nat.card (Paths depth .X ⊕ Paths depth .I) = (depth + 1) * 2 ^ depth + 1 := by
    have hcounts : ∀ count,
        Nat.card (Paths count .X) = 2 ^ count ∧
        Nat.card (Paths (count + 1) .Y) = (count + 3) * 2 ^ count ∧
        Nat.card (Paths (count + 1) .I) = (count + 1) * 2 ^ (count + 1) + 1 := by
      intro count; induction count with
      | zero => simp [Paths, Nat.card_eq_fintype_card]
      | succ count ih =>
        have hX : Nat.card (Paths (count + 1) .X) = 2 ^ (count + 1) := by
          rw [Paths, Nat.card_sum, ih.1, Nat.pow_succ]; omega
        refine ⟨hX, ?_, ?_⟩
        · rw [Paths, Nat.card_sum, Nat.card_sum, ih.2.1, hX, Nat.pow_succ]; ring
        · rw [Paths, Nat.card_sum, Nat.card_sum, ih.2.1, ih.2.2, Nat.pow_succ, Nat.pow_succ]
          ring
    cases depth with
    | zero => simp [Paths, Nat.card_eq_fintype_card]
    | succ count => rw [Nat.card_sum, (hcounts (count + 1)).1, (hcounts count).2.2]; ring
  let family (length : ℕ) := avoiders length [[1, 4, 2, 3], [2, 1, 4, 3]]
  have prepend_inherited_sites (n : ℕ) (p : List ℕ) (hpositive : 1 ≤ n)
      (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
      (patterns : List (List ℕ))
      (hpatterns : ∀ pattern ∈ patterns, pattern = [2, 1, 4, 3] ∨ pattern = [1, 4, 2, 3])
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
    have hbase142 : NonnestingDefs.Occurs [1, 4, 2, 3] child ↔
        NonnestingDefs.Occurs [1, 4, 2, 3] p := (by simpa [child] using htests.2.2)
    have hsite132 := maximum_pattern_tests n p hperm site hsite
    have h142 : NonnestingDefs.Occurs [1, 4, 2, 3] (child.insertIdx (site + 1) (n + 2)) ↔
        NonnestingDefs.Occurs [1, 4, 2, 3] (p.insertIdx site (n + 1)) := by
      have hs := htransport.2.2
      simp only [show ¬ site ≤ 0 by omega, if_false, List.insertIdx_zero] at hs
      rw [hbase142, hsite132.2.2] at hs; rw [hsite132.2.2]; simpa [child, or_assoc] using hs
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
        · exact hmember.2.2 _ hm (h2143.mpr hocc)
        · exact hmember.2.2 _ hm (h142.mpr hocc)
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
        · exact hmember.2.2 _ hm (h2143.mp hocc)
        · exact hmember.2.2 _ hm (h142.mp hocc)
  have identity_insertion_rules (n cut : ℕ) (hcut : cut ≤ n) :
      (List.range' 1 n).insertIdx cut (n + 1) ∈ family (n + 1) ↔ cut = 0 ∨ n ≤ cut + 1 := by
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
    have hno2143 : ¬ NonnestingDefs.Occurs [2, 1, 4, 3] child := by
      intro hocc; rcases h2143test.mp hocc with hold | hnew
      · exact hparentavoid _ (by simp) hold
      · obtain ⟨first, second, third, hfs, hs, ht, htb, hlow, hhigh⟩ := hnew
        rw [hentry first (by omega), hentry second (by omega)] at hlow; omega
    have h142rule : ¬ NonnestingDefs.Occurs [1, 4, 2, 3] child ↔ cut = 0 ∨ n ≤ cut + 1 := by
      constructor
      · intro havoid; by_cases hzero : cut = 0
        · exact Or.inl hzero
        · right
          by_contra hnot
          apply havoid; apply htests.2.2.mpr; right
          refine ⟨0, cut, cut + 1, by omega, by omega, by omega, by omega, ?_, ?_⟩
          · rw [hentry 0 (by omega), hentry cut (by omega)]; omega
          · rw [hentry cut (by omega), hentry (cut + 1) (by omega)]; omega
      · intro hcuts hocc; rcases htests.2.2.mp hocc with hold | hnew
        · exact hparentavoid _ (by simp) hold
        · obtain ⟨first, second, third, hf, hs, hst, htb, _, _⟩ := hnew
          rcases hcuts with hzero | hend <;> omega
    change child ∈ family (n + 1) ↔ _; constructor
    · intro hmember; exact h142rule.mp (hmember.2.2 _ (by simp))
    · intro hcuts; refine ⟨hchildperm, hchildfish, ?_⟩
      intro pattern hm
      have hc : pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
      rcases hc with rfl | rfl
      · exact h142rule.mpr hcuts
      · exact hno2143
  have positive_B_inherited_sites (n : ℕ) (p : List ℕ) (hparent : p ∈ family n)
      (site : ℕ) (hpositive : 0 < site) (hsite : site ≤ p.length)
      (hactive : p.insertIdx site (n + 1) ∈ family (n + 1))
      (gap : ℕ) (hgpositive : 0 < gap) (hgap : gap ≤ p.length) :
      (p.insertIdx site (n + 1)).insertIdx (if gap ≤ site then gap else gap + 1) (n + 2) ∈
        family (n + 2) ↔
      p.insertIdx gap (n + 1) ∈ family (n + 1) ∧
        ((gap = site ∧ (p.take gap).Pairwise (· < ·)) ∨ site < gap) := by
    let child := p.insertIdx site (n + 1); let nextgap := if gap ≤ site then gap else gap + 1
    have hlength : child.length = p.length + 1 := List.length_insertIdx_of_le_length hsite (n + 1)
    have hnextgap : nextgap ≤ child.length := (by dsimp [nextgap]; split_ifs <;> omega)
    have hnodup : p.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
    have hmax (value : ℕ) (hm : value ∈ p) : value < n + 1 := by
      have hrange := hparent.1.mem_iff.mp hm; simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, hvalue⟩ := hrange; omega
    have hentry (index : ℕ) (hi : index < p.length) : 1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
      have hm : p.getD index 0 ∈ p := by rw [List.getD_eq_getElem p 0 hi]; exact List.getElem_mem hi
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
    have h142 := (maximum_pattern_transport n p hparent.1 site gap hsite hgap).2.2
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
        have hc : pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
        rcases hc with rfl | rfl
        · exact hnew.2.2 _ (by simp) (h142.mpr (Or.inr (Or.inl hocc)))
        · exact hnew.2.2 _ (by simp) (h2143.mpr (Or.inr (Or.inl hocc)))
      refine ⟨hold, ?_⟩
      by_cases hle : gap ≤ site
      · have hinc : (p.take gap).Pairwise (· < ·) := by
          apply hincreasing.mpr; intro hinv
          exact hnew.2.2 _ (by simp) (h2143.mpr (Or.inr (Or.inr ⟨hle, hinv⟩)))
        have heq : gap = site := by
          by_contra hne
          have hguard := (isFishburn_insertIdx_max_iff p (n + 1) gap hgap hmax).mp hold.2.1
          have hone := (eligible_prefix_structure n p hparent.1 hparent.2.1 gap
            hgap hgpositive hguard.2).1
          obtain ⟨one, honebound, honevalue⟩ := List.mem_iff_getElem.mp hone
          have honegap : one < gap := (by simp only [List.length_take] at honebound; omega)
          have honeentry : p.getD one 0 = 1 := by
            rw [List.getD_eq_getElem p 0 (by omega)]; simpa only [List.getElem_take] using honevalue
          have hgapbound : gap < p.length := (by omega); have hgapvalue : 1 < p.getD gap 0 := by
            have hp := hentry gap hgapbound; have hneq : p.getD gap 0 ≠ 1 := by
              intro heq
              have hi := (List.getD_inj hgapbound (by omega) hnodup).mp (heq.trans honeentry.symm)
              omega
            omega
          apply hnew.2.2 [1, 4, 2, 3] (by simp); apply h142.mpr; right; right
          refine ⟨one, gap, honegap, le_rfl, by omega, ?_⟩
          rwa [honeentry]
        exact Or.inl ⟨heq, hinc⟩
      · exact Or.inr (by omega)
    · rintro ⟨hold, hcuts⟩; have hnextperm := hperm child (n + 1) nextgap hactive.1 hnextgap
      rw [show n + 1 + 1 = n + 2 by omega] at hnextperm
      refine ⟨hnextperm, hfishiff.mpr hold.2.1, ?_⟩
      intro pattern hm hocc
      have hc : pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
      rcases hc with rfl | rfl
      · rcases h142.mp hocc with hchild | holdocc | ⟨first, second, hf, hs, hsecond, hlt⟩
        · exact hactive.2.2 _ (by simp) hchild
        · exact hold.2.2 _ (by simp) holdocc
        · rcases hcuts with ⟨heq, _⟩ | hgt <;> omega
      · rcases h2143.mp hocc with hchild | holdocc | ⟨hle, hinv⟩
        · exact hactive.2.2 _ (by simp) hchild
        · exact hold.2.2 _ (by simp) holdocc
        · rcases hcuts with ⟨_, hinc⟩ | hgt
          · exact hincreasing.mp hinc hinv
          · omega
  have after_maximum_active_iff (n : ℕ) (p : List ℕ) (patterns : List (List ℕ))
      (hpatterns : ∀ pattern ∈ patterns, pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨
        pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3])
      (hparent : p ∈ avoiders n patterns) (site : ℕ)
      (hpositive : 0 < site) (hsite : site ≤ p.length)
      (hactive : p.insertIdx site (n + 1) ∈ avoiders (n + 1) patterns) :=
    (maximum_2143_transport n p hparent.1 site 0 hsite (by omega)).2.2
      patterns hpatterns hparent hpositive hactive
  have B_ordered_children (n : ℕ) (p : List ℕ) (hn : 2 ≤ n) (hparent : p ∈ family n) :
      ∃ correspondence : Paths 1 (label n p) ≃ {cut : ℕ // cut ≤ p.length ∧
        p.insertIdx cut (n + 1) ∈ family (n + 1)},
        ∀ edge, label (n + 1) (p.insertIdx (correspondence edge).val (n + 1)) =
          nextLabel (label n p) edge := by
    classical
    have hlen : p.length = n := (by simpa using hparent.1.length_eq)
    have hpatterns : ∀ pattern ∈ [[1, 4, 2, 3], [2, 1, 4, 3]],
        pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨
          pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3] := by
      intro pattern hm
      have hc : pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
      rcases hc with rfl | rfl <;> simp
    have hprependpatterns : ∀ pattern ∈ [[1, 4, 2, 3], [2, 1, 4, 3]],
        pattern = [2, 1, 4, 3] ∨ pattern = [1, 4, 2, 3] := by
      intro pattern hm
      have hc : pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
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
          simp only [List.mem_range', Nat.one_mul] at hrange
          obtain ⟨offset, hoffset, heq⟩ := hrange; omega
      · intro pattern hm hocc
        have hc : pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
        rcases hc with rfl | rfl
        · exact hword.2.2 _ hm (by simpa using
            (maximum_pattern_tests size word hword.1 0 (by omega)).2.2.mp hocc)
        · exact hword.2.2 _ hm (by simpa using
            (maximum_2143_test size word hword.1 0 (by omega)).mp hocc)
    have hidentity (site : ℕ) (hb : site ≤ p.length) :
        p.insertIdx site (n + 1) = List.range' 1 (n + 1) ↔ p = List.range' 1 n ∧ site = n := by
      have hc : (p.insertIdx site (n + 1)).length = n + 1 := by
        rw [List.length_insertIdx_of_le_length hb, hlen]
      constructor
      · intro heq; have hat : (p.insertIdx site (n + 1)).getD site 0 = n + 1 := by
          rw [List.getD_eq_getElem _ 0 (by omega)]; exact List.getElem_insertIdx_self _
        rw [heq, List.getD_eq_getElem _ 0 (by simp; omega)] at hat
        simp only [List.getElem_range', Nat.one_mul] at hat; have hs : site = n := (by omega)
        refine ⟨?_, hs⟩
        have ht := congrArg (List.take n) heq
        rw [List.take_insertIdx_eq_take_of_le p (n + 1) n site (by omega)] at ht
        rw [List.range'_concat] at ht; simpa [← hlen, List.take_append] using ht
      · rintro ⟨heq, hs⟩; rw [heq, hs]
        have ht : (List.range' 1 n).insertIdx n (n + 1) = List.range' 1 n ++ [n + 1] := by
          simpa only [List.length_range'] using
            (List.insertIdx_length_self (l := List.range' 1 n) (x := n + 1))
        exact ht.trans (by simpa [Nat.add_comm] using
          (List.range'_concat (s := 1) (n := n) (step := 1)).symm)
    have hclassify (word : List ℕ) (hnot : word ≠ List.range' 1 (n + 1))
        (middle : ℕ) (hm : middle < n + 1)
        (hshape : ∀ gap, gap ≤ word.length → (word.insertIdx gap (n + 2) ∈ family (n + 2) ↔
            gap = 0 ∨ (0 < middle ∧ gap = middle) ∨ gap = n + 1))
        (hwordlen : word.length = n + 1) :
        label (n + 1) word = if middle = 0 then .X else .Y := by
      have hinterior : (∃ cut, 0 < cut ∧ cut < n + 1 ∧ word.insertIdx cut (n + 2) ∈
          family (n + 2)) ↔ middle ≠ 0 := by
        constructor
        · rintro ⟨cut, hp, hb, ha⟩ hz; have hc := (hshape cut (by omega)).mp ha; omega
        · intro hnonzero
          exact ⟨middle, by omega, hm,
            (hshape middle (by omega)).mpr (Or.inr (Or.inl ⟨by omega, rfl⟩))⟩
      dsimp only [family] at hinterior
      simp only [label, if_neg hnot, hinterior]; by_cases hz : middle = 0 <;> simp [hz]
    have hmaxbefore (site : ℕ) (hb : site ≤ p.length) :
        (∃ earlier < site, p.getD earlier 0 = n) ↔ n ∈ p.take site := by
      constructor
      · rintro ⟨index, hi, hv⟩; apply List.mem_iff_getElem.mpr
        refine ⟨index, by simp only [List.length_take]; omega, ?_⟩
        rw [List.getD_eq_getElem p 0 (by omega)] at hv; simpa only [List.getElem_take] using hv
      · intro hm; obtain ⟨index, hib, hiv⟩ := List.mem_iff_getElem.mp hm
        have hi : index < p.length := (by simp only [List.length_take] at hib; omega)
        refine ⟨index, by simp only [List.length_take] at hib; omega, ?_⟩
        rw [List.getD_eq_getElem p 0 hi]; simpa only [List.getElem_take] using hiv
    have hraw (site : ℕ) (hp : 0 < site) (hb : site ≤ p.length) (ha : p.insertIdx site (n + 1) ∈
          family (n + 1)) :
        ∀ gap, gap ≤ (p.insertIdx site (n + 1)).length →
          ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈ family (n + 2) ↔
          gap = 0 ∨ (gap = site + 1 ∧ n ∈ p.take site) ∨ ∃ oldgap, 0 < oldgap ∧ oldgap ≤ p.length ∧
              (if oldgap ≤ site then oldgap else oldgap + 1) = gap ∧
              p.insertIdx oldgap (n + 1) ∈ family (n + 1) ∧
              ((oldgap = site ∧ (p.take oldgap).Pairwise (· < ·)) ∨ site < oldgap)) := by
      intro gap hg; have hc : (p.insertIdx site (n + 1)).length = n + 1 := by
        rw [List.length_insertIdx_of_le_length hb, hlen]
      by_cases hz : gap = 0
      · subst gap; exact iff_of_true (hfront (n + 1) _ ha) (Or.inl rfl)
      by_cases haf : gap = site + 1
      · subst gap; have ht := after_maximum_active_iff n p _ hpatterns hparent site hp hb ha
        rw [hmaxbefore site hb] at ht; constructor
        · intro hh; exact Or.inr (Or.inl ⟨rfl, ht.mp hh⟩)
        · rintro (hz | ⟨_, hm⟩ | ⟨oldgap, ho, hob, heq, _, hd⟩)
          · omega
          · exact ht.mpr hm
          · split_ifs at heq <;> omega
      let oldgap := if gap ≤ site then gap else gap - 1
      have ho : 0 < oldgap := (by dsimp [oldgap]; split_ifs <;> omega)
      have hob : oldgap ≤ p.length := (by dsimp [oldgap]; split_ifs <;> omega)
      have hmap : (if oldgap ≤ site then oldgap else oldgap + 1) = gap := by
        dsimp [oldgap]; split_ifs <;> omega
      have ht := positive_B_inherited_sites n p hparent site hp hb ha oldgap ho hob; rw [hmap] at ht
      constructor
      · intro hh; exact Or.inr (Or.inr ⟨oldgap, ho, hob, hmap, (ht.mp hh).1, (ht.mp hh).2⟩)
      · rintro (hzero | ⟨heq, _⟩ | ⟨other, hop, hobb, hshift, hold, hd⟩)
        · omega
        · omega
        · have heq : other = oldgap := by
            dsimp [oldgap]; split_ifs at hshift ⊢ <;> omega
          subst other; exact ht.mpr ⟨hold, hd⟩
    obtain ⟨middle, hm, hshape, hguard, hmark⟩ : ∃ middle, middle < n ∧
          (∀ gap, gap ≤ p.length → (p.insertIdx gap (n + 1) ∈ family (n + 1) ↔
              gap = 0 ∨ (0 < middle ∧ gap = middle) ∨ gap = n)) ∧
          (0 < middle → ((p.take middle).Pairwise (· < ·) ∧ n ∉ p.take middle ∨
            ¬ (p.take middle).Pairwise (· < ·) ∧ n ∈ p.take middle)) ∧
          label n p = if p = List.range' 1 n then .I else if middle = 0 then .X else .Y := by
      rcases all_B_site_invariant n (by omega) p hparent with hid | ⟨hnot, hx | hy⟩
      · subst p; refine ⟨n - 1, by omega, ?_, ?_, ?_⟩
        · intro gap hb; have hr := (identity_insertion_rules n gap (by simpa using hb))
          exact hr.trans (by constructor <;> intro hh <;> omega)
        · intro _; left
          refine ⟨List.Pairwise.sublist (List.take_sublist _ _) (List.pairwise_lt_range' 1), ?_⟩
          intro hnmem; obtain ⟨index, hib, hiv⟩ := List.mem_iff_getElem.mp hnmem
          simp only [List.length_take, List.length_range'] at hib; have hv : index + 1 = n := by
            simpa [List.getElem_take, List.getElem_range', Nat.add_comm] using hiv
          omega
        · simp [label]
      · refine ⟨0, by omega, ?_, by intro hh; omega, ?_⟩
        · intro gap hb; simpa using hx gap hb
        · have hnone : ¬ ∃ cut, 0 < cut ∧ cut < n ∧ p.insertIdx cut (n + 1) ∈
              family (n + 1) := by
            rintro ⟨cut, hp, hb, ha⟩; have hc := (hx cut (by omega)).mp ha; omega
          dsimp only [family] at hnone; simp [label, hnot, hnone]
      · obtain ⟨middle, hp, hb, hg, hs⟩ := hy; refine ⟨middle, hb, ?_, by intro _; exact hg, ?_⟩
        · intro gap hgb; simpa only [show 0 < middle from hp, true_and] using hs gap hgb
        · have hex : ∃ cut, 0 < cut ∧ cut < n ∧ p.insertIdx cut (n + 1) ∈
              family (n + 1) :=
            ⟨middle, hp, hb, (hs middle (by omega)).mpr (Or.inr (Or.inl rfl))⟩
          dsimp only [family] at hex; simp [label, hnot, hex, show middle ≠ 0 by omega]
    have hfrontlabel : label (n + 1) (p.insertIdx 0 (n + 1)) = if middle = 0 then .X else .Y := by
      have hc : (p.insertIdx 0 (n + 1)).length = n + 1 := (by simp [hlen])
      apply hclassify _ (by intro heq; have ht := (hidentity 0 (by omega)).mp heq; omega)
        (if middle = 0 then 0 else middle + 1) (by split_ifs <;> omega) ?_ hc |>.trans ?_
      · intro gap hb; by_cases hz : gap = 0
        · subst gap; exact iff_of_true (hfront (n + 1) _ (hfront n p hparent)) (Or.inl rfl)
        obtain ⟨oldgap, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
        have hob : oldgap ≤ p.length := (by omega)
        have ht := prepend_inherited_sites n p (by omega) hparent.1 hparent.2.1
          [[1, 4, 2, 3], [2, 1, 4, 3]] hprependpatterns oldgap hob
        simp only [show [3, 1, 2, 4] ∉ [[1, 4, 2, 3], [2, 1, 4, 3]] by decide,
          false_implies, and_true] at ht
        rw [hshape oldgap hob] at ht; rw [List.insertIdx_zero]
        exact ht.trans (by
          split_ifs with hzero
          · constructor
            · intro hh; omega
            · rintro (hf | ⟨_, hf⟩ | he)
              · exact False.elim hf
              · exact False.elim hf
              · exact ⟨by omega, Or.inr (Or.inr (by omega))⟩
          · constructor
            · intro hh; omega
            · rintro (hf | ⟨_, he⟩ | he)
              · exact False.elim hf
              · exact ⟨by omega, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
              · exact ⟨by omega, Or.inr (Or.inr (by omega))⟩)
      · split_ifs <;> simp_all
    have hendlabel : label (n + 1) (p.insertIdx n (n + 1)) =
        if p = List.range' 1 n then .I else .X := by
      by_cases hid : p = List.range' 1 n
      · have hc := (hidentity n (by omega)).mpr ⟨hid, rfl⟩; rw [hc]
        simp only [label, ite_true, if_pos hid]
      have hnotinc : ¬ (p.take n).Pairwise (· < ·) := by
        intro hi; have hpinc : p.Pairwise (· < ·) := (by simpa [← hlen] using hi)
        exact hid (List.Perm.eq_of_pairwise (by intro first second _ _ hfs hsf; omega)
          hpinc (List.pairwise_lt_range' 1) hparent.1)
      have hnmem : n ∈ p.take n := by
        rw [← hlen, List.take_length]; apply hparent.1.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]; exact ⟨n - 1, by omega, by omega⟩
      have ha := (hshape n (by omega)).mpr (Or.inr (Or.inr rfl))
      have hc : (p.insertIdx n (n + 1)).length = n + 1 := by
        rw [List.length_insertIdx_of_le_length (by omega), hlen]
      rw [if_neg hid]
      apply hclassify _ (by intro heq; exact hid ((hidentity n (by omega)).mp heq).1)
        0 (by omega) ?_ hc
      intro gap hb; rw [hraw n (by omega) (by omega) ha gap hb]; constructor
      · rintro (hz | ⟨heq, _⟩ | ⟨oldgap, hp, hob, heq, hold, hd⟩)
        · exact Or.inl hz
        · exact Or.inr (Or.inr heq)
        · rcases hd with ⟨rfl, hi⟩ | hlt
          · exact False.elim (hnotinc hi)
          · omega
      · rintro (hz | ⟨hp, _⟩ | heq)
        · exact Or.inl hz
        · omega
        · exact Or.inr (Or.inl ⟨heq, hnmem⟩)
    have hmiddlelabel (hp : 0 < middle) : label (n + 1) (p.insertIdx middle (n + 1)) = .Y := by
      have ha := (hshape middle (by omega)).mpr (Or.inr (Or.inl ⟨hp, rfl⟩))
      have hc : (p.insertIdx middle (n + 1)).length = n + 1 := by
        rw [List.length_insertIdx_of_le_length (by omega), hlen]
      have hnot : p.insertIdx middle (n + 1) ≠ List.range' 1 (n + 1) := by
        intro heq; have := ((hidentity middle (by omega)).mp heq).2; omega
      rcases hguard hp with ⟨hi, hnm⟩ | ⟨hni, hnm⟩
      · have hs : label (n + 1) (p.insertIdx middle (n + 1)) =
            if middle = 0 then .X else .Y := by
          apply hclassify _ hnot middle (by omega) ?_ hc
          intro gap hb; rw [hraw middle hp (by omega) ha gap hb]; constructor
          · rintro (hz | ⟨_, hm⟩ | ⟨oldgap, hop, hob, heq, hold, hd⟩)
            · exact Or.inl hz
            · exact False.elim (hnm hm)
            · have holdshape := (hshape oldgap hob).mp hold
              split_ifs at heq <;> rcases holdshape with hz | ⟨_, he⟩ | he <;> omega
          · rintro (hz | ⟨_, heq⟩ | heq)
            · exact Or.inl hz
            · exact Or.inr (Or.inr ⟨middle, hp, by omega,
                by simpa using heq.symm, ha, Or.inl ⟨rfl, hi⟩⟩)
            · exact Or.inr (Or.inr ⟨n, by omega, by omega,
                by simpa [show ¬ n ≤ middle by omega] using heq.symm,
                (hshape n (by omega)).mpr (Or.inr (Or.inr rfl)), Or.inr (by omega)⟩)
        simpa [show middle ≠ 0 by omega] using hs
      · have hs : label (n + 1) (p.insertIdx middle (n + 1)) =
            if middle + 1 = 0 then .X else .Y := by
          apply hclassify _ hnot (middle + 1) (by omega) ?_ hc
          intro gap hb; rw [hraw middle hp (by omega) ha gap hb]; constructor
          · rintro (hz | ⟨heq, _⟩ | ⟨oldgap, hop, hob, heq, hold, hd⟩)
            · exact Or.inl hz
            · exact Or.inr (Or.inl ⟨by omega, heq⟩)
            · have holdshape := (hshape oldgap hob).mp hold; rcases hd with ⟨rfl, hi⟩ | hlt
              · exact False.elim (hni hi)
              · split_ifs at heq <;> rcases holdshape with hz | ⟨_, he⟩ | he <;> omega
          · rintro (hz | ⟨_, heq⟩ | heq)
            · exact Or.inl hz
            · exact Or.inr (Or.inl ⟨heq, hnm⟩)
            · exact Or.inr (Or.inr ⟨n, by omega, by omega,
                by simpa [show ¬ n ≤ middle by omega] using heq.symm,
                (hshape n (by omega)).mpr (Or.inr (Or.inr rfl)), Or.inr (by omega)⟩)
        simpa using hs
    let active := {cut : ℕ // cut ≤ p.length ∧ p.insertIdx cut (n + 1) ∈ family (n + 1)}
    by_cases hmzero : middle = 0
    · have hidnot : p ≠ List.range' 1 n := by
        intro hid; have ha := (identity_insertion_rules n (n - 1) (by omega)).mpr (by omega)
        rw [← hid] at ha; have hs := (hshape (n - 1) (by omega)).mp ha; omega
      have hlabel : label n p = .X := (by simpa [hidnot, hmzero] using hmark)
      let correspondence : Unit ⊕ Unit ≃ active :=
        { toFun := fun edge => match edge with
            | .inl _ => ⟨0, by omega, (hshape 0 (by omega)).mpr (Or.inl rfl)⟩
            | .inr _ => ⟨n, by omega, (hshape n (by omega)).mpr (Or.inr (Or.inr rfl))⟩
          invFun := fun cut => if cut.val = 0 then .inl () else .inr ()
          left_inv := by
            intro edge; rcases edge with token | token <;> cases token <;>
              simp [show n ≠ 0 by omega]
          right_inv := by
            intro cut; apply Subtype.ext
            have hs := (hshape cut.val cut.property.1).mp cut.property.2; dsimp only
            split_ifs <;> simp only <;> omega }
      rw [hlabel]; refine ⟨correspondence, ?_⟩; intro edge; rcases edge with token | token
      · change label (n + 1) (p.insertIdx 0 (n + 1)) = .X; simpa [hmzero] using hfrontlabel
      · change label (n + 1) (p.insertIdx n (n + 1)) = .X; simpa [hidnot] using hendlabel
    · have hp : 0 < middle := (by omega)
      let correspondence : (Unit ⊕ Unit) ⊕ Unit ≃ active :=
        { toFun := fun edge => match edge with
            | .inl (.inl _) => ⟨0, by omega, (hshape 0 (by omega)).mpr (Or.inl rfl)⟩
            | .inl (.inr _) => ⟨middle, by omega,
                (hshape middle (by omega)).mpr (Or.inr (Or.inl ⟨hp, rfl⟩))⟩
            | .inr _ => ⟨n, by omega, (hshape n (by omega)).mpr (Or.inr (Or.inr rfl))⟩
          invFun := fun cut => if cut.val = 0 then .inl (.inl ())
            else if cut.val = middle then .inl (.inr ()) else .inr ()
          left_inv := by
            intro edge; rcases edge with (token | token) | token <;> cases token
            · simp
            · simp [hmzero]
            · simp [show n ≠ 0 by omega, show n ≠ middle by omega]
          right_inv := by
            intro cut; apply Subtype.ext
            have hs := (hshape cut.val cut.property.1).mp cut.property.2; dsimp only
            split_ifs <;> simp only <;> omega }
      by_cases hid : p = List.range' 1 n
      · have hlabel : label n p = .I := (by simpa [hid] using hmark); rw [hlabel]
        refine ⟨correspondence, ?_⟩
        intro edge; rcases edge with (token | token) | token
        · change label (n + 1) (p.insertIdx 0 (n + 1)) = .Y; simpa [hmzero] using hfrontlabel
        · change label (n + 1) (p.insertIdx middle (n + 1)) = .Y; exact hmiddlelabel hp
        · change label (n + 1) (p.insertIdx n (n + 1)) = .I; simpa [hid] using hendlabel
      · have hlabel : label n p = .Y := (by simpa [hid, hmzero] using hmark); rw [hlabel]
        refine ⟨correspondence, ?_⟩
        intro edge; rcases edge with (token | token) | token
        · change label (n + 1) (p.insertIdx 0 (n + 1)) = .Y; simpa [hmzero] using hfrontlabel
        · change label (n + 1) (p.insertIdx middle (n + 1)) = .Y; exact hmiddlelabel hp
        · change label (n + 1) (p.insertIdx n (n + 1)) = .X; simpa [hid] using hendlabel
  classical
  have hfinite (n : ℕ) : (family n).Finite := by
    apply (List.finite_toSet (List.range' 1 n).permutations).subset; intro p hp
    exact List.mem_permutations.mpr hp.1
  let (n : ℕ) : Fintype (family n) := (hfinite n).fintype; let active (n : ℕ) (parent : family n) :=
    {cut : ℕ // cut ≤ parent.val.length ∧ parent.val.insertIdx cut (n + 1) ∈ family (n + 1)}
  let edgeMap (n : ℕ) (hn : 2 ≤ n) (parent : family n) :
      Paths 1 (label n parent.val) ≃ active n parent :=
    Classical.choose (B_ordered_children n parent.val hn parent.property)
  have hedgeLabel (n : ℕ) (hn : 2 ≤ n) (parent : family n) (edge : Paths 1 (label n parent.val)) :
      label (n + 1) (parent.val.insertIdx (edgeMap n hn parent edge).val (n + 1)) =
        nextLabel (label n parent.val) edge :=
    Classical.choose_spec (B_ordered_children n parent.val hn parent.property) edge
  let weighted (n depth : ℕ) := ∑ parent : family n, Nat.card (Paths depth (label n parent.val))
  have hbranches (mark : Label) (depth : ℕ) :
      (∑ edge : Paths 1 mark, Nat.card (Paths depth (nextLabel mark edge))) =
        Nat.card (Paths (depth + 1) mark) := by
    cases mark with
    | I =>
      have transfer : (∑ edge : (Unit ⊕ Unit) ⊕ Unit, Nat.card (Paths depth (nextLabel .I edge))) =
          Nat.card (Paths (depth + 1) .I) := by simp [nextLabel, Fintype.sum_sum_type, Paths]
      convert transfer using 1
      apply Finset.sum_congr
      · exact congrArg (fun finiteType : Fintype (Paths 1 .I) => finiteType.elems)
          (Subsingleton.elim _ _)
      · intro edge _; rfl
    | X =>
      have transfer : (∑ edge : Unit ⊕ Unit, Nat.card (Paths depth (nextLabel .X edge))) =
          Nat.card (Paths (depth + 1) .X) := by simp [nextLabel, Paths, two_mul]
      convert transfer using 1
      apply Finset.sum_congr
      · exact congrArg (fun finiteType : Fintype (Paths 1 .X) => finiteType.elems)
          (Subsingleton.elim _ _)
      · intro edge _; rfl
    | Y =>
      have transfer : (∑ edge : (Unit ⊕ Unit) ⊕ Unit, Nat.card (Paths depth (nextLabel .Y edge))) =
          Nat.card (Paths (depth + 1) .Y) := by simp [nextLabel, Fintype.sum_sum_type, Paths]
      convert transfer using 1
      apply Finset.sum_congr
      · exact congrArg (fun finiteType : Fintype (Paths 1 .Y) => finiteType.elems)
          (Subsingleton.elim _ _)
      · intro edge _; rfl
  have hstep (n : ℕ) (hn : 2 ≤ n) (depth : ℕ) :
      weighted (n + 1) depth = weighted n (depth + 1) := by
    let (parent : family n) : Fintype (active n parent) :=
      Fintype.ofEquiv (Paths 1 (label n parent.val)) (edgeMap n hn parent)
    let insertion : (Σ parent : family n, active n parent) → family (n + 1) := fun entry =>
      ⟨entry.1.val.insertIdx entry.2.val (n + 1), entry.2.property.2⟩
    have hbijective : Function.Bijective insertion := by
      constructor
      · intro first second heq; have hfirstsite := first.2.property.1
        have hsecondsite := second.2.property.1
        have hchild : first.1.val.insertIdx first.2.val (n + 1) =
            second.1.val.insertIdx second.2.val (n + 1) := congrArg Subtype.val heq
        have hfirstlen : (first.1.val.insertIdx first.2.val (n + 1)).length =
            first.1.val.length + 1 :=
          List.length_insertIdx_of_le_length first.2.property.1 _
        have hsecondlen : (second.1.val.insertIdx second.2.val (n + 1)).length =
            second.1.val.length + 1 :=
          List.length_insertIdx_of_le_length second.2.property.1 _
        have hfirstbound : first.2.val <
            (first.1.val.insertIdx first.2.val (n + 1)).length := (by omega)
        have hsecondbound : second.2.val <
            (first.1.val.insertIdx first.2.val (n + 1)).length := (by rw [hchild]; omega)
        have hfirstat : (first.1.val.insertIdx first.2.val (n + 1)).getD first.2.val 0 = n + 1 := by
          rw [List.getD_eq_getElem _ 0 hfirstbound]; exact List.getElem_insertIdx_self _
        have hsecondat : (first.1.val.insertIdx first.2.val (n + 1)).getD second.2.val 0 =
            n + 1 := by
          rw [hchild, List.getD_eq_getElem _ 0 (by omega)]; exact List.getElem_insertIdx_self _
        have hnodup : (first.1.val.insertIdx first.2.val (n + 1)).Nodup :=
          first.2.property.2.1.nodup_iff.mpr (List.nodup_range' 1)
        have hsites : first.2.val = second.2.val :=
          (List.getD_inj hfirstbound hsecondbound hnodup).mp (hfirstat.trans hsecondat.symm)
        have hparents : first.1.val = second.1.val := by
          rw [hsites] at hchild; exact List.insertIdx_injective _ _ hchild
        rcases first with ⟨parent, cut⟩; rcases second with ⟨other, othercut⟩
        have hp : parent = other := Subtype.ext hparents; subst other
        exact congrArg (Sigma.mk parent) (Subtype.ext hsites)
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
            rw [List.range'_concat]; simpa [Nat.add_comm] using
              (List.perm_append_comm (l₁ := List.range' 1 n) (l₂ := [n + 1]))
          exact (hcons.trans (child.property.1.trans hrange)).cons_inv
        have hmaxparent : ∀ value ∈ parent, value < n + 1 := by
          intro value hvalue; have hm := hparentperm.mem_iff.mp hvalue
          simp only [List.mem_range', Nat.one_mul] at hm; obtain ⟨offset, hoffset, heq⟩ := hm; omega
        have hparentmember : parent ∈ family n := by
          refine ⟨hparentperm, ?_, ?_⟩
          · apply (isFishburn_insertIdx_max_iff parent (n + 1) site hsite hmaxparent).mp
              (by rw [hinverse]; exact child.property.2.1) |>.1
          · intro pattern hpattern hocc; obtain ⟨values, hstep, hmem, hsub, hrel⟩ := hocc
            apply child.property.2.2 pattern hpattern
            refine ⟨values, hstep, ?_, hsub.trans (List.eraseIdx_sublist child.val site), by simp⟩
            intro rank hlow hhigh
            exact (List.eraseIdx_sublist child.val site).subset (hmem rank hlow hhigh)
        refine ⟨⟨⟨parent, hparentmember⟩, ⟨site, hsite, ?_⟩⟩, ?_⟩
        · rw [hinverse]; exact child.property
        · exact Subtype.ext hinverse
    let parentMap := Equiv.ofBijective insertion hbijective
    calc
      weighted (n + 1) depth =
          ∑ entry : (Σ parent : family n, active n parent), Nat.card (Paths depth
              (label (n + 1) (entry.1.val.insertIdx entry.2.val (n + 1)))) := by
        exact (parentMap.sum_comp (fun child =>
          Nat.card (Paths depth (label (n + 1) child.val)))).symm
      _ = ∑ parent : family n, ∑ cut : active n parent,
            Nat.card (Paths depth (label (n + 1) (parent.val.insertIdx cut.val (n + 1)))) := by
        rw [Fintype.sum_sigma]
      _ = weighted n (depth + 1) := by
        apply Finset.sum_congr rfl; intro parent _
        rw [← (edgeMap n hn parent).sum_comp (fun cut =>
          Nat.card (Paths depth (label (n + 1) (parent.val.insertIdx cut.val (n + 1)))))]
        calc
          _ = ∑ edge : Paths 1 (label n parent.val),
                Nat.card (Paths depth (nextLabel (label n parent.val) edge)) := by
            apply Finset.sum_congr rfl; intro edge _; rw [hedgeLabel n hn parent edge]
          _ = _ := hbranches (label n parent.val) depth
  have h12 : [1, 2] ∈ family 2 := by
    simpa using (identity_insertion_rules 1 1 (by omega)).mpr (Or.inr (by omega))
  have h21 : [2, 1] ∈ family 2 := by
    simpa using (identity_insertion_rules 1 0 (by omega)).mpr (Or.inl rfl)
  let ascending : family 2 := ⟨[1, 2], h12⟩; let descending : family 2 := ⟨[2, 1], h21⟩
  have h12label : label 2 ascending.val = .I := (by simp [ascending, label, List.range'])
  have h21label : label 2 descending.val = .X := by
    have hnone : ¬ ∃ cut, 0 < cut ∧ cut < 2 ∧ ([2, 1] : List ℕ).insertIdx cut 3 ∈ family 3 := by
      rintro ⟨cut, hp, hb, ha⟩; have heq : cut = 1 := (by omega)
      subst cut; have hf := ha.2.1 0 2 (by decide) (by decide); exact hf ⟨rfl, by decide⟩
    have hnot : ([2, 1] : List ℕ) ≠ List.range' 1 2 := (by decide); dsimp only [family] at hnone
    simp only [descending, label, if_neg hnot, if_neg hnone]
  have hbase (depth : ℕ) : weighted 2 depth = Nat.card (Paths depth .X ⊕ Paths depth .I) := by
    let correspondence : Unit ⊕ Unit ≃ family 2 :=
      { toFun := fun edge => match edge with
          | .inl _ => descending
          | .inr _ => ascending
        invFun := fun parent => if parent.val = [2, 1] then .inl () else .inr ()
        left_inv := by
          intro edge
          rcases edge with token | token <;> cases token <;> simp [ascending, descending]
        right_inv := by
          intro parent; apply Subtype.ext; have hp : parent.val.Perm [1, 2] := parent.property.1
          rcases List.perm_pair.mp hp with heq | heq <;> simp [heq, ascending, descending] }
    change (∑ parent : family 2, Nat.card (Paths depth (label 2 parent.val))) = _
    rw [← correspondence.sum_comp (fun parent => Nat.card (Paths depth (label 2 parent.val)))]
    change (∑ edge : Unit ⊕ Unit, Nat.card (Paths depth (label 2 (correspondence edge).val))) = _
    simp [Fintype.sum_sum_type, correspondence, h21label, h12label]
  have htransfer : ∀ n : ℕ, 2 ≤ n → ∀ depth,
      weighted n depth = Nat.card (Paths (depth + n - 2) .X ⊕ Paths (depth + n - 2) .I) := by
    intro n; induction n with
    | zero => intro hn; omega
    | succ n ih =>
      intro hn depth; by_cases heq : n = 1
      · subst n; simpa using hbase depth
      · rw [hstep n (by omega) depth, ih (by omega) (depth + 1)]; congr 3 <;> omega
  have hweightzero (n : ℕ) : weighted n 0 = Nat.card (family n) := by
    have hunit (mark : Label) : Nat.card (Paths 0 mark) = 1 := (by change Nat.card Unit = 1; simp)
    change (∑ parent : family n, Nat.card (Paths 0 (label n parent.val))) = _
    simp only [hunit, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Nat.card_eq_fintype_card, Nat.cast_id]
  by_cases hone : size = 1
  · subst size; have hroot : [1] ∈ family 1 := by
      simpa using (identity_insertion_rules 0 0 (by omega)).mpr (Or.inl rfl)
    have hall : family 1 = {([1] : List ℕ)} := by
      ext word
      constructor
      · intro hw; exact List.perm_singleton.mp hw.1
      · intro hw; have heq : word = [1] := hw; simpa only [heq] using hroot
    dsimp only [family] at hall; simp [hall]
  · have hcard : Nat.card (family size) =
        (size - 1) * 2 ^ (size - 2) + 1 := by
      rw [← hweightzero size, htransfer size (by omega) 0, hpathcount]
      simp only [Nat.zero_add]; congr 2; omega
    simpa only [Nat.card_coe_set_eq] using hcard
end D5.S3.Combinatorics.Fishburn.FishburnTenFourBCount
