/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFour
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFour
   mirror-E: none(waiver:three-fishburn-pair-enumerations)
   anchors: []
   utility: none
   digest: Weighted maximum-deletion induction proves all three counts in Conjecture 10.4. -/
import D5.S3.Combinatorics.Fishburn.FishburnTenFourAChildren
import D5.S3.Combinatorics.Fishburn.FishburnTenFourBCount
import D5.S3.Combinatorics.Fishburn.FishburnTenFourCLabels
import D5.S3.Combinatorics.Fishburn.FishburnBasicPatternTransport
import D5.S3.Combinatorics.Fishburn.FishburnTenFour2143Transport
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Fishburn.FishburnTenFour
open D5.S3.Combinatorics FishburnDefs FishburnTenFourAChildren
open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicPatterns FishburnBasic2143 FishburnBasicPrefixes
open FishburnTenFourAInvariant
open FishburnBasicPatternTransport FishburnTenFour2143Transport
set_option maxHeartbeats 1600000 in
theorem result : FishburnDefs.claim104 := by
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
  have after_maximum_active_iff (n : ℕ) (p : List ℕ) (patterns : List (List ℕ))
      (hpatterns : ∀ pattern ∈ patterns, pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨
        pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3])
      (hparent : p ∈ avoiders n patterns) (site : ℕ)
      (hpositive : 0 < site) (hsite : site ≤ p.length)
      (hactive : p.insertIdx site (n + 1) ∈ avoiders (n + 1) patterns) :=
    (maximum_2143_transport n p hparent.1 site 0 hsite (by omega)).2.2
      patterns hpatterns hparent hpositive hactive
  have A_children (n : ℕ) (p : List ℕ) (hn : 1 ≤ n) (hparent : p ∈ family n) (weight : Label → ℕ) :
      let cuts := {cut : ℕ // cut ≤ p.length ∧ p.insertIdx cut (n + 1) ∈ family (n + 1)}
      ∃ _ : Fintype cuts, (∑ cut : cuts, weight (label (n + 1) (p.insertIdx cut.val (n + 1)))) =
        match label n p with
        | .I => weight (.Q n) + (∑ index : Fin (n - 1), weight (.P (index.val + 1))) + weight .I
        | .P run => weight (.Q run) + ∑ index : Fin run, weight (.P (index.val + 1))
        | .Q sites => weight (.Q sites) + sites * weight (.Q 1) := by
    classical
    let positive (size : ℕ) (word : List ℕ) := {cut : ℕ // 0 < cut ∧ cut ≤ word.length ∧
      word.insertIdx cut (size + 1) ∈ family (size + 1)}
    let active (size : ℕ) (word : List ℕ) := {cut : ℕ // cut ≤ word.length ∧
      word.insertIdx cut (size + 1) ∈ family (size + 1)}
    have hfinitepos (size : ℕ) (word : List ℕ) : Finite (positive size word) :=
      (Set.finite_Iic word.length).subset (fun _ entry => entry.2.1)
    have hfiniteactive (size : ℕ) (word : List ℕ) : Finite (active size word) :=
      (Set.finite_Iic word.length).subset (fun _ entry => entry.1)
    let (size : ℕ) (word : List ℕ) : Fintype (positive size word) :=
      @Fintype.ofFinite _ (hfinitepos size word)
    let (size : ℕ) (word : List ℕ) : Fintype (active size word) :=
      @Fintype.ofFinite _ (hfiniteactive size word)
    refine ⟨inferInstanceAs (Fintype (active n p)), ?_⟩
    have hlen : p.length = n := (by simpa using hparent.1.length_eq)
    have hmax (value : ℕ) (hm : value ∈ p) : value < n + 1 := by
      have hrange := hparent.1.mem_iff.mp hm; simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, heq⟩ := hrange; omega
    have hpatterns : ∀ pattern ∈ [[1, 3, 2, 4], [2, 1, 4, 3]],
        pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] ∨
          pattern = [1, 4, 2, 3] ∨ pattern = [2, 1, 4, 3] := by
      intro pattern hm
      have hc : pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
      rcases hc with rfl | rfl <;> simp
    have hprependpatterns : ∀ pattern ∈ [[1, 3, 2, 4], [2, 1, 4, 3]],
        pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := by simpa
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
        have hc : pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] := (by simpa using hm)
        rcases hc with rfl | rfl
        · exact hword.2.2 _ hm (by simpa using
            (maximum_pattern_tests size word hword.1 0 (by omega)).1.mp hocc)
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
    have hinterval (size : ℕ) (word : List ℕ) (run : ℕ) (hr : run ≤ word.length)
        (hshape : ∀ gap, gap ≤ word.length → (word.insertIdx gap (size + 1) ∈
            family (size + 1) ↔ gap ≤ run)) :
        ∃ correspondence : Fin run ≃ positive size word,
          ∀ index, (correspondence index).val = index.val + 1 := by
      let correspondence : Fin run ≃ positive size word :=
        { toFun := fun index => ⟨index.val + 1, by omega, by omega,
            (hshape (index.val + 1) (by omega)).mpr (by omega)⟩
          invFun := fun cut => ⟨cut.val - 1, by
            have hp := cut.property.1
            have hs := (hshape cut.val cut.property.2.1).mp cut.property.2.2
            omega⟩
          left_inv := (by intro index; apply Fin.ext; simp)
          right_inv := by
            intro cut; apply Subtype.ext
            have := cut.property.1; dsimp only; omega }
      exact ⟨correspondence, by intro index; rfl⟩
    have hcardinterval (size : ℕ) (word : List ℕ) (run : ℕ) (hr : run ≤ word.length)
        (hshape : ∀ gap, gap ≤ word.length → (word.insertIdx gap (size + 1) ∈
            family (size + 1) ↔ gap ≤ run)) :
        Nat.card (positive size word) = run := by
      obtain ⟨correspondence, _⟩ := hinterval size word run hr hshape
      rw [← Nat.card_congr correspondence]; simp
    have hfrontlabel : label (n + 1) (p.insertIdx 0 (n + 1)) = .Q (Nat.card (positive n p)) := by
      have hshift (gap : ℕ) (hb : gap ≤ p.length) : ((n + 1) :: p).insertIdx (gap + 1) (n + 2) ∈
            family (n + 2) ↔
          gap ≠ 0 ∧ p.insertIdx gap (n + 1) ∈ family (n + 1) := by
        simpa using prepend_inherited_sites n p hn hparent.1 hparent.2.1
          [[1, 3, 2, 4], [2, 1, 4, 3]] hprependpatterns gap hb
      let correspondence : positive n p ≃ positive (n + 1) ((n + 1) :: p) :=
        { toFun := fun cut => ⟨cut.val + 1, by omega,
            by simp only [List.length_cons]; have := cut.property.2.1; omega,
            (hshift cut.val cut.property.2.1).mpr ⟨by have := cut.property.1; omega,
              cut.property.2.2⟩⟩
          invFun := fun cut => by
            have hp := cut.property.1; have hb := cut.property.2.1
            simp only [List.length_cons] at hb; have hsub : cut.val - 1 + 1 = cut.val := (by omega)
            have ht := (hshift (cut.val - 1) (by omega)).mp
              (by simpa only [hsub] using cut.property.2.2)
            exact ⟨cut.val - 1, by omega, by omega, ht.2⟩
          left_inv := (by intro cut; apply Subtype.ext; simp)
          right_inv := by intro cut; apply Subtype.ext; have := cut.property.1; dsimp; omega }
      have hnot : p.insertIdx 0 (n + 1) ≠ List.range' 1 (n + 1) := by
        intro heq; have := ((hidentity 0 (by omega)).mp heq).2; omega
      have hhead : (p.insertIdx 0 (n + 1)).getD 0 0 ≠ 1 := (by change n + 1 ≠ 1; omega)
      simp only [label, if_neg hnot, if_neg hhead]
      congr 1; simpa only [List.insertIdx_zero] using (Nat.card_congr correspondence).symm
    have hraw (site : ℕ) (hp : 0 < site) (hb : site ≤ p.length) (ha : p.insertIdx site (n + 1) ∈
          family (n + 1)) :
        ∀ gap, gap ≤ (p.insertIdx site (n + 1)).length →
          ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈ family (n + 2) ↔
          gap = 0 ∨ (gap = site + 1 ∧ ∃ earlier < site, p.getD earlier 0 = n) ∨
            ∃ oldgap, 0 < oldgap ∧ oldgap ≤ p.length ∧ oldgap ≤ site ∧
              oldgap = gap ∧ p.insertIdx oldgap (n + 1) ∈ family (n + 1) ∧
              (p.take oldgap).Pairwise (· < ·)) := by
      intro gap hg; have hc : (p.insertIdx site (n + 1)).length = n + 1 := by
        rw [List.length_insertIdx_of_le_length hb, hlen]
      by_cases hz : gap = 0
      · subst gap; exact iff_of_true (hfront (n + 1) _ ha) (Or.inl rfl)
      by_cases haf : gap = site + 1
      · subst gap; have ht := after_maximum_active_iff n p _ hpatterns hparent site hp hb ha
        constructor
        · intro hh; exact Or.inr (Or.inl ⟨rfl, ht.mp hh⟩)
        · rintro (hzero | ⟨_, hm⟩ | ⟨oldgap, ho, hob, hle, heq, _, _⟩)
          · omega
          · exact ht.mpr hm
          · omega
      let oldgap := if gap ≤ site then gap else gap - 1
      have ho : 0 < oldgap := (by dsimp [oldgap]; split_ifs <;> omega)
      have hob : oldgap ≤ p.length := (by dsimp [oldgap]; split_ifs <;> omega)
      have hmap : (if oldgap ≤ site then oldgap else oldgap + 1) = gap := by
        dsimp [oldgap]; split_ifs <;> omega
      have ht := positive_A_inherited_sites n p hparent site hp hb ha oldgap ho hob; rw [hmap] at ht
      constructor
      · intro hh; obtain ⟨hold, hle, hi⟩ := ht.mp hh
        have heq : oldgap = gap := (by rw [if_pos hle] at hmap; exact hmap)
        exact Or.inr (Or.inr ⟨oldgap, ho, hob, hle, heq, hold, hi⟩)
      · rintro (hzero | ⟨heq, _⟩ | ⟨other, hop, hobb, hle, heq, hold, hi⟩)
        · omega
        · omega
        · have he : other = oldgap := (by dsimp [oldgap]; split_ifs <;> omega)
          exact ht.mpr ⟨by simpa only [he] using hold, by simpa only [he] using hle,
            by simpa only [he] using hi⟩
    have hprefixchild (site : ℕ) (hp : 0 < site) (hs : site < n)
        (hpref : p.take site = List.range' 1 site)
        (hactive : ∀ gap, 0 < gap → gap ≤ site → p.insertIdx gap (n + 1) ∈ family (n + 1)) :
        label (n + 1) (p.insertIdx site (n + 1)) = .P site := by
      have hb : site ≤ p.length := (by omega); have ha := hactive site hp (le_refl _)
      have hc : (p.insertIdx site (n + 1)).length = n + 1 := by
        rw [List.length_insertIdx_of_le_length hb, hlen]
      have hnot : p.insertIdx site (n + 1) ≠ List.range' 1 (n + 1) := by
        intro heq; have := ((hidentity site hb).mp heq).2; omega
      have hshape : ∀ gap, gap ≤ (p.insertIdx site (n + 1)).length →
          ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈ family (n + 2) ↔ gap ≤ site) := by
        intro gap hg; rw [hraw site hp hb ha gap hg]; constructor
        · rintro (hz | ⟨_, earlier, he, hv⟩ | ⟨oldgap, _, _, hle, heq, _, _⟩)
          · omega
          · have ht : (p.take site).getD earlier 0 = p.getD earlier 0 := by
              rw [List.getD_eq_getElem _ 0 (by simp only [List.length_take]; omega),
                List.getElem_take, List.getD_eq_getElem p 0 (by omega)]
            rw [← ht, hpref, List.getD_eq_getElem _ 0 (by simp; omega)] at hv
            simp only [List.getElem_range', Nat.one_mul] at hv; omega
          · omega
        · intro hle; by_cases hz : gap = 0
          · exact Or.inl hz
          right
          right
          have ht := congrArg (List.take gap) hpref
          have hprefix : p.take gap = List.range' 1 gap := by
            simpa only [List.take_take, Nat.min_eq_left hle,
              List.take_range'_of_length_ge hle] using ht
          exact ⟨gap, by omega, by omega, hle, rfl,
            hactive gap (by omega) hle, hprefix ▸ List.pairwise_lt_range' 1⟩
      have hhead : (p.insertIdx site (n + 1)).getD 0 0 = 1 := by
        rw [List.getD_eq_getElem _ 0 (by omega), List.getElem_insertIdx_of_lt hp]
        have ht := congrArg (fun word : List ℕ => word.getD 0 0) hpref
        rw [List.getD_eq_getElem (p.take site) 0
            (by simp only [List.length_take]; omega), List.getElem_take,
          List.getD_eq_getElem (List.range' 1 site) 0 (by simp; omega)] at ht
        simpa only [List.getElem_range', Nat.one_mul, Nat.add_zero] using ht
      simp only [label, if_neg hnot, if_pos hhead]
      congr 1; exact hcardinterval (n + 1) _ site (by omega) hshape
    have hQchild (hfirst : 1 < p.getD 0 0)
        (hguard : ∀ gap, 0 < gap → gap ≤ p.length → p.insertIdx gap (n + 1) ∈ family (n + 1) →
          ∃ earlier < gap, p.getD earlier 0 = n)
        (cut : positive n p) : label (n + 1) (p.insertIdx cut.val (n + 1)) = .Q 1 := by
      have hp := cut.property.1; have hb := cut.property.2.1
      have ha := cut.property.2.2; have hc : (p.insertIdx cut.val (n + 1)).length = n + 1 := by
        rw [List.length_insertIdx_of_le_length hb, hlen]
      have hnot : p.insertIdx cut.val (n + 1) ≠ List.range' 1 (n + 1) := by
        intro heq; have hid := ((hidentity cut.val hb).mp heq).1
        rw [hid] at hfirst; have ht : (List.range' 1 n).getD 0 0 = 1 := by
          rw [List.getD_eq_getElem _ 0 (by simp; omega)]; simp
        omega
      have hhead : (p.insertIdx cut.val (n + 1)).getD 0 0 ≠ 1 := by
        rw [List.getD_eq_getElem _ 0 (by omega), List.getElem_insertIdx_of_lt hp,
          ← List.getD_eq_getElem p 0 (by omega)]
        omega
      have hshape : ∀ gap, gap ≤ (p.insertIdx cut.val (n + 1)).length →
          ((p.insertIdx cut.val (n + 1)).insertIdx gap (n + 2) ∈
            family (n + 2) ↔ gap = 0 ∨ gap = cut.val + 1) := by
        intro gap hg; rw [hraw cut.val hp hb ha gap hg]; constructor
        · rintro (hz | ⟨heq, _⟩ | ⟨oldgap, ho, hob, _, _, hold, hi⟩)
          · exact Or.inl hz
          · exact Or.inr heq
          · have heligible :=
              (isFishburn_insertIdx_max_iff p (n + 1) oldgap hob hmax).mp hold.2.1 |>.2
            have ht := (eligible_prefix_structure n p hparent.1 hparent.2.1
              oldgap hob ho heligible).2 hi
            have hh := congrArg (fun word : List ℕ => word.getD 0 0) ht
            have hone : p.getD 0 0 = 1 := by
              rw [List.getD_eq_getElem (p.take oldgap) 0
                  (by simp only [List.length_take]; omega), List.getElem_take,
                List.getD_eq_getElem (List.range' 1 oldgap) 0 (by simp; omega)] at hh
              rw [List.getD_eq_getElem p 0 (by omega)]
              simpa only [List.getElem_range', Nat.one_mul, Nat.add_zero] using hh
            omega
        · rintro (hz | heq)
          · exact Or.inl hz
          · exact Or.inr (Or.inl ⟨heq, hguard cut.val hp hb ha⟩)
      let correspondence : Unit ≃ positive (n + 1) (p.insertIdx cut.val (n + 1)) :=
        { toFun := fun _ => ⟨cut.val + 1, by omega, by omega,
            (hshape (cut.val + 1) (by omega)).mpr (Or.inr rfl)⟩
          invFun := fun _ => ()
          left_inv := (by intro token; cases token; rfl)
          right_inv := by
            intro other; apply Subtype.ext; have ho := other.property.1
            have hs := (hshape other.val other.property.2.1).mp other.property.2.2
            dsimp only; omega }
      simp only [label, if_neg hnot, if_neg hhead]; congr 1; rw [← Nat.card_congr correspondence]
      simp
    let splitCuts : Unit ⊕ positive n p ≃ active n p :=
      { toFun := fun edge => match edge with
          | .inl _ => ⟨0, by omega, hfront n p hparent⟩
          | .inr cut => ⟨cut.val, cut.property.2.1, cut.property.2.2⟩
        invFun := fun cut => if hz : cut.val = 0 then .inl ()
          else .inr ⟨cut.val, by omega, cut.property.1, cut.property.2⟩
        left_inv := by
          intro edge; rcases edge with token | cut
          · cases token
            simp
          · simp [show cut.val ≠ 0 by have := cut.property.1; omega]
        right_inv := by
          intro cut
          apply Subtype.ext; dsimp only; split_ifs <;> simp_all }
    have hsplit : (∑ cut : active n p, weight (label (n + 1) (p.insertIdx cut.val (n + 1)))) =
        weight (.Q (Nat.card (positive n p))) +
          ∑ cut : positive n p, weight (label (n + 1) (p.insertIdx cut.val (n + 1))) := by
      rw [← splitCuts.sum_comp (fun cut =>
        weight (label (n + 1) (p.insertIdx cut.val (n + 1))))]
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, splitCuts, Equiv.coe_fn_mk, hfrontlabel]
    change (∑ cut : active n p, weight (label (n + 1) (p.insertIdx cut.val (n + 1)))) = _
    rw [hsplit]
    rcases all_A_site_invariant n hn p hparent with hid | ⟨run, hr, hrn, hpref, _, hs⟩ |
      ⟨hfirst, _, hguard⟩
    · have hshape : ∀ gap, gap ≤ p.length →
          (p.insertIdx gap (n + 1) ∈ family (n + 1) ↔ gap ≤ n) := by
        intro gap hb
        exact iff_of_true (by rw [hid]; exact (identity_insertion_rules n gap (by omega)))
          (by omega)
      obtain ⟨correspondence, hvalues⟩ := hinterval n p n (by omega) hshape
      have hcard := hcardinterval n p n (by omega) hshape
      have hlabel : label n p = .I := (by simp only [label, if_pos hid])
      rw [hlabel, hcard]; rw [Nat.add_assoc]; apply congrArg (fun total => weight (.Q n) + total)
      rw [← correspondence.sum_comp (fun cut =>
        weight (label (n + 1) (p.insertIdx cut.val (n + 1))))]
      have hvalueschild : ∀ index : Fin n,
          label (n + 1) (p.insertIdx (correspondence index).val (n + 1)) =
            if index.val + 1 = n then .I else .P (index.val + 1) := by
        intro index; rw [hvalues]; by_cases heq : index.val + 1 = n
        · rw [if_pos heq, heq, (hidentity n (by omega)).mpr ⟨hid, rfl⟩]; simp only [label, ite_true]
        · rw [if_neg heq]; refine hprefixchild (index.val + 1) (by omega) (by omega) ?_ ?_
          · rw [hid]; exact List.take_range'_of_length_ge (by omega)
          · intro gap hp hb; exact (hshape gap (by omega)).mpr (by omega)
      simp_rw [hvalueschild]
      obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last, Nat.succ_eq_add_one]
      congr 1
      apply Finset.sum_congr rfl; intro index _; rw [if_neg (by have := index.isLt; omega)]
    · have hhead : p.getD 0 0 = 1 := by
        have ht := congrArg (fun word : List ℕ => word.getD 0 0) hpref
        rw [List.getD_eq_getElem (p.take run) 0
            (by simp only [List.length_take]; omega), List.getElem_take,
          List.getD_eq_getElem (List.range' 1 run) 0 (by simp; omega)] at ht
        rw [List.getD_eq_getElem p 0 (by omega)]
        simpa only [List.getElem_range', Nat.one_mul, Nat.add_zero] using ht
      have hnot : p ≠ List.range' 1 n := by
        intro hid; have ha := (identity_insertion_rules n n (by omega))
        rw [← hid] at ha; have := (hs n (by omega)).mp ha; omega
      have hcard := hcardinterval n p run (by omega) hs; have hlabel : label n p = .P run := by
        simp only [label, if_neg hnot, if_pos hhead]; exact congrArg Label.P hcard
      rw [hlabel, hcard]; congr 1
      obtain ⟨correspondence, hvalues⟩ := hinterval n p run (by omega) hs
      rw [← correspondence.sum_comp (fun cut =>
        weight (label (n + 1) (p.insertIdx cut.val (n + 1))))]
      apply Finset.sum_congr rfl; intro index _; rw [hvalues]; congr 1
      refine hprefixchild (index.val + 1) (by omega) (by have := index.isLt; omega) ?_ ?_
      · have ht := congrArg (List.take (index.val + 1)) hpref
        simpa only [List.take_take, Nat.min_eq_left (by omega : index.val + 1 ≤ run),
          List.take_range'_of_length_ge (by omega : index.val + 1 ≤ run)] using ht
      · intro gap hp hb; exact (hs gap (by omega)).mpr (by have := index.isLt; omega)
    · have hnot : p ≠ List.range' 1 n := by
        intro hid; rw [hid, List.getD_eq_getElem _ 0 (by simp; omega)] at hfirst
        simp only [List.getElem_range', Nat.one_mul, Nat.add_zero] at hfirst; omega
      have hhead : p.getD 0 0 ≠ 1 := (by omega)
      have hlabel : label n p = .Q (Nat.card (positive n p)) := by
        simp only [label, positive, family, if_neg hnot, if_neg hhead]
      rw [hlabel]; congr 1
      have hconstant : ∀ cut : positive n p, label (n + 1) (p.insertIdx cut.val (n + 1)) = .Q 1 :=
        hQchild hfirst hguard
      simp only [hconstant, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Nat.card_eq_fintype_card, Nat.cast_id]
  classical
  have hfinite (n : ℕ) : (family n).Finite := by
    apply (List.finite_toSet (List.range' 1 n).permutations).subset
    intro p hp; exact List.mem_permutations.mpr hp.1
  let (n : ℕ) : Fintype (family n) := (hfinite n).fintype; let active (n : ℕ) (parent : family n) :=
    {cut : ℕ // cut ≤ parent.val.length ∧ parent.val.insertIdx cut (n + 1) ∈ family (n + 1)}
  let partialSum (count : ℕ) (values : ℕ → ℕ) := ∑ index : Fin count, values (index.val + 1)
  let forest (count : ℕ) (values : ℕ → ℕ) :=
    ∑ index : Fin count, 2 ^ (count - 1 - index.val) * values (index.val + 1)
  let production (n : ℕ) (weight : Label → ℕ) : Label → ℕ
    | .I => weight (.Q n) + partialSum (n - 1) (fun run => weight (.P run)) + weight .I
    | .P run => weight (.Q run) + partialSum run (fun index => weight (.P index))
    | .Q sites => weight (.Q sites) + sites * weight (.Q 1)
  let weighted (n : ℕ) (weight : Label → ℕ) := ∑ parent : family n, weight (label n parent.val)
  have hstep (n : ℕ) (hn : 1 ≤ n) (weight : Label → ℕ) :
      weighted (n + 1) weight = weighted n (production n weight) := by
    let (parent : family n) : Fintype (active n parent) :=
      Classical.choose (A_children n parent.val hn parent.property weight)
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
        rcases first with ⟨parent, cut⟩
        rcases second with ⟨other, othercut⟩
        have hp : parent = other := Subtype.ext hparents
        subst other; exact congrArg (Sigma.mk parent) (Subtype.ext hsites)
      · intro child; have hlen : child.val.length = n + 1 := by
          simpa only [List.length_range'] using child.property.1.length_eq
        have hmaxmem : n + 1 ∈ child.val := by
          apply child.property.1.mem_iff.mpr
          simp only [List.mem_range', Nat.one_mul]; exact ⟨n, by omega, by omega⟩
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
      weighted (n + 1) weight = ∑ entry : (Σ parent : family n, active n parent),
            weight (label (n + 1) (entry.1.val.insertIdx entry.2.val (n + 1))) := by
        exact (parentMap.sum_comp (fun child => weight (label (n + 1) child.val))).symm
      _ = ∑ parent : family n, ∑ cut : active n parent,
            weight (label (n + 1) (parent.val.insertIdx cut.val (n + 1))) := by
        rw [Fintype.sum_sigma]
      _ = weighted n (production n weight) := by
        apply Finset.sum_congr rfl; intro parent _
        exact Classical.choose_spec (A_children n parent.val hn parent.property weight)
  have hroot : [1] ∈ family 1 := (by simpa using (identity_insertion_rules 0 0 (by omega)))
  let root : family 1 := ⟨[1], hroot⟩
  have hrootlabel : label 1 root.val = .I := (by simp [root, label, List.range'])
  have hrootweight (weight : Label → ℕ) : weighted 1 weight = weight .I := by
    have hall (parent : family 1) : parent = root := by
      apply Subtype.ext; have hp : parent.val.Perm [1] := parent.property.1
      exact List.perm_singleton.mp hp
    calc
      weighted 1 weight = weight (label 1 root.val) := by
        apply Finset.sum_eq_single root
        · intro other _ hne; exact False.elim (hne (hall other))
        · intro hnot; exact False.elim (hnot (Finset.mem_univ root))
      _ = _ := (by rw [hrootlabel])
  have hsizeTwo (weight : Label → ℕ) : weighted 2 weight = weight (.Q 1) + weight .I := by
    rw [hstep 1 (by omega), hrootweight]; simp [production, partialSum]
  have hprefixsucc (count : ℕ) (values : ℕ → ℕ) :
      partialSum (count + 1) values = partialSum count values + values (count + 1) := by
    dsimp only [partialSum]; rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
  have hforestsucc (count : ℕ) (values : ℕ → ℕ) :
      forest (count + 1) values = 2 * forest count values + values (count + 1) := by
    dsimp only [forest]; rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    congr 1; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro index _
    have he : count - index.val = count - 1 - index.val + 1 := (by have := index.isLt; omega)
    rw [he, Nat.pow_succ]; ring
  have hforestadd (count : ℕ) (first second : ℕ → ℕ) :
      forest count (fun run => first run + second run) =
        forest count first + forest count second := by
    dsimp only [forest]; simp only [mul_add, Finset.sum_add_distrib]
  have hforestscale (count : ℕ) (factor : ℕ) :
      forest count (fun run => run * factor) = forest count id * factor := by
    dsimp only [forest]; simp only [← mul_assoc, Finset.sum_mul, id_eq]
  have hprefixforest : ∀ count : ℕ, ∀ values : ℕ → ℕ,
      forest count (fun run => partialSum run values) + partialSum count values =
        2 * forest count values := by
    intro count; induction count with
    | zero => intro values; simp [forest, partialSum]
    | succ count ih =>
      intro values; rw [hforestsucc count (fun run => partialSum run values),
        hprefixsucc count values, hforestsucc count values]
      have ht := ih values; omega
  have hforestindex : ∀ count : ℕ, forest count id + count + 2 = 2 ^ (count + 1) := by
    intro count; induction count with
    | zero => simp [forest]
    | succ count ih =>
      rw [hforestsucc]; simp only [id_eq]
      rw [show count + 1 + 1 = (count + 1) + 1 by rfl, Nat.pow_succ]; omega
  have hforestconstant : ∀ count : ℕ, forest count (fun _ => 1) + 1 = 2 ^ count := by
    intro count; induction count with
    | zero => simp [forest]
    | succ count ih => rw [hforestsucc count (fun _ => 1), Nat.pow_succ]; omega
  have hdistribution : ∀ depth : ℕ, ∀ weight : Label → ℕ, weighted (depth + 3) weight =
        weight .I + (depth * 2 ^ (depth + 1) + 1) * weight (.Q 1) + weight (.Q (depth + 2)) +
          forest (depth + 1) (fun run => weight (.P run)) +
          forest (depth + 1) (fun sites => weight (.Q sites)) := by
    intro depth; induction depth with
    | zero =>
      intro weight; rw [show 0 + 3 = 2 + 1 by rfl, hstep 2 (by omega), hsizeTwo]
      simp [production, forest, partialSum]; ring
    | succ depth ih =>
      intro weight
      rw [show depth + 1 + 3 = (depth + 3) + 1 by omega, hstep (depth + 3) (by omega), ih]
      have hP : forest (depth + 1) (fun run => production (depth + 3) weight (.P run)) =
          forest (depth + 1) (fun run => weight (.Q run)) +
            forest (depth + 1) (fun run => partialSum run (fun index => weight (.P index))) := by
        exact hforestadd (depth + 1) (fun run => weight (.Q run))
          (fun run => partialSum run (fun index => weight (.P index)))
      have hQ : forest (depth + 1) (fun run => production (depth + 3) weight (.Q run)) =
          forest (depth + 1) (fun run => weight (.Q run)) +
            forest (depth + 1) id * weight (.Q 1) := by
        rw [show (fun run => production (depth + 3) weight (.Q run)) =
          (fun run => weight (.Q run) + run * weight (.Q 1)) from rfl,
          hforestadd (depth + 1) (fun run => weight (.Q run))
            (fun run => run * weight (.Q 1)), hforestscale (depth + 1) (weight (.Q 1))]
      rw [hP, hQ]; have hp := hprefixforest (depth + 1) (fun run => weight (.P run))
      have hi := hforestindex (depth + 1)
      have hcoefficient : (depth + 1) * 2 ^ (depth + 1 + 1) + 1 =
          2 * (depth * 2 ^ (depth + 1) + 1) + (depth + 2) + forest (depth + 1) id := by
        rw [Nat.pow_succ] at hi ⊢; nlinarith
      simp only [production]
      rw [hcoefficient, hforestsucc (depth + 1) (fun run => weight (.P run)),
        hforestsucc (depth + 1) (fun run => weight (.Q run))]
      have he : depth + 3 - 1 = (depth + 1) + 1 := (by omega)
      rw [he, hprefixsucc (depth + 1) (fun run => weight (.P run)),
        show depth + 1 + 2 = depth + 3 by omega]
      ring_nf at hp ⊢; omega
  have hweightone (n : ℕ) : weighted n (fun _ => 1) = Nat.card (family n) := by
    dsimp only [weighted]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
      Nat.card_eq_fintype_card, Nat.cast_id]
  intro size hsize
  refine ⟨?_, FishburnTenFourBCount.B_count size hsize, FishburnTenFourCLabels.C_count size hsize⟩
  have hcard : Nat.card (family size) = (size - 1) * 2 ^ (size - 2) + 1 := by
    rw [← hweightone]; by_cases hone : size = 1
    · subst size; rw [hrootweight (fun _ => 1)]; norm_num
    by_cases htwo : size = 2
    · subst size; rw [hsizeTwo (fun _ => 1)]; norm_num
    obtain ⟨depth, heq⟩ : ∃ depth, size = depth + 3 := ⟨size - 3, by omega⟩; subst size
    rw [hdistribution depth (fun _ => 1)]
    rw [show depth + 3 - 1 = depth + 2 by omega, show depth + 3 - 2 = depth + 1 by omega]
    simp only [mul_one]; have ht := hforestconstant (depth + 1); nlinarith
  simpa only [Nat.card_coe_set_eq] using hcard
end D5.S3.Combinatorics.Fishburn.FishburnTenFour
