/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicPatternTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicPatternTransport
   mirror-E: none(waiver:two-maximum-pattern-witness-analysis)
   anchors: []
   utility: none
   digest: Inherited cuts acquire exactly the cross-pair and interval two-maximum obstructions. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicPatternTransport

open D5.S3.Combinatorics Nonnesting FishburnBasicPatterns

theorem maximum_pattern_transport (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (site gap : ℕ)
    (hsite : site ≤ p.length) (hgap : gap ≤ p.length) :
    (NonnestingDefs.Occurs [1, 3, 2, 4]
        ((p.insertIdx site (n + 1)).insertIdx
          (if gap ≤ site then gap else gap + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [1, 3, 2, 4] (p.insertIdx site (n + 1)) ∨
      NonnestingDefs.Occurs [1, 3, 2, 4] (p.insertIdx gap (n + 1)) ∨
      ∃ first third, first < site ∧ site ≤ third ∧ third < gap ∧
        p.getD first 0 < p.getD third 0) ∧
    (NonnestingDefs.Occurs [3, 1, 2, 4]
        ((p.insertIdx site (n + 1)).insertIdx
          (if gap ≤ site then gap else gap + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [3, 1, 2, 4] (p.insertIdx site (n + 1)) ∨
      NonnestingDefs.Occurs [3, 1, 2, 4] (p.insertIdx gap (n + 1)) ∨
      ∃ second third, site ≤ second ∧ second < third ∧ third < gap ∧
        p.getD second 0 < p.getD third 0) ∧
    (NonnestingDefs.Occurs [1, 4, 2, 3]
        ((p.insertIdx site (n + 1)).insertIdx
          (if gap ≤ site then gap else gap + 1) (n + 2)) ↔
      NonnestingDefs.Occurs [1, 4, 2, 3] (p.insertIdx site (n + 1)) ∨
      NonnestingDefs.Occurs [1, 4, 2, 3] (p.insertIdx gap (n + 1)) ∨
      ∃ first second, first < gap ∧ gap ≤ second ∧ second < site ∧
        p.getD first 0 < p.getD second 0) := by
  let child := p.insertIdx site (n + 1)
  let nextgap := if gap ≤ site then gap else gap + 1
  let lift := fun index : ℕ => if index < site then index else index + 1
  let lower := fun index : ℕ => if index < site then index else index - 1
  let guard132 := fun (word : List ℕ) (cut : ℕ) =>
    ∃ first second third, first < second ∧ second < third ∧ third < cut ∧
      word.getD first 0 < word.getD third 0 ∧ word.getD third 0 < word.getD second 0
  let guard312 := fun (word : List ℕ) (cut : ℕ) =>
    ∃ first second third, first < second ∧ second < third ∧ third < cut ∧
      word.getD second 0 < word.getD third 0 ∧ word.getD third 0 < word.getD first 0
  let guard142 := fun (word : List ℕ) (cut : ℕ) =>
    ∃ first second third, first < cut ∧ cut ≤ second ∧ second < third ∧
      third < word.length ∧ word.getD first 0 < word.getD second 0 ∧
      word.getD second 0 < word.getD third 0
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
  have hguard132 : guard132 child nextgap ↔ guard132 p gap ∨
      ∃ first third, first < site ∧ site ≤ third ∧ third < gap ∧
        p.getD first 0 < p.getD third 0 := by
    constructor
    · rintro ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩
      have htb : third < child.length := by omega
      have hfb : first < child.length := by omega
      have hsb : second < child.length := by omega
      have hfirstne : first ≠ site := by
        intro heq
        rw [heq, hat] at hlow
        have := hbound third htb
        omega
      have hthirdne : third ≠ site := by
        intro heq
        rw [heq, hat] at hhigh
        have := hbound second hsb
        omega
      by_cases hsecondsite : second = site
      · right
        have hgt : site < gap := by
          dsimp [nextgap] at ht
          split_ifs at ht <;> omega
        have hnext : nextgap = gap + 1 := if_neg (by omega)
        rw [hnext] at ht
        rw [hbefore first (by omega), hlowerentry third htb hthirdne] at hlow
        have hlower : lower third = third - 1 := if_neg (by omega)
        rw [hlower] at hlow
        exact ⟨first, third - 1, by omega, by omega, by omega, hlow⟩
      · left
        rw [hlowerentry first hfb hfirstne, hlowerentry third htb hthirdne] at hlow
        rw [hlowerentry third htb hthirdne, hlowerentry second hsb hsecondsite] at hhigh
        exact ⟨lower first, lower second, lower third,
          hlowermono first second hfs hfirstne hsecondsite,
          hlowermono second third hst hsecondsite hthirdne,
          hlowerprefix third hthirdne ht, hlow, hhigh⟩
    · rintro (⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ |
        ⟨first, third, hfirst, hthird, ht, hlow⟩)
      · refine ⟨lift first, lift second, lift third, hliftmono first second hfs,
          hliftmono second third hst, hliftprefix third ht, ?_, ?_⟩
        · rwa [hliftentry first (by omega), hliftentry third (by omega)]
        · rwa [hliftentry third (by omega), hliftentry second (by omega)]
      · have hnext : nextgap = gap + 1 := if_neg (by omega)
        refine ⟨first, site, third + 1, hfirst, by omega, by omega, ?_, ?_⟩
        · rw [hbefore first hfirst]
          have he := hliftentry third (by omega)
          simp only [lift, if_neg (by omega : ¬ third < site)] at he
          rwa [he]
        · rw [hat]
          have he := hliftentry third (by omega)
          simp only [lift, if_neg (by omega : ¬ third < site)] at he
          rw [he]
          have := hentry third (by omega)
          omega
  have hguard312 : guard312 child nextgap ↔ guard312 p gap ∨
      ∃ second third, site ≤ second ∧ second < third ∧ third < gap ∧
        p.getD second 0 < p.getD third 0 := by
    constructor
    · rintro ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩
      have htb : third < child.length := by omega
      have hfb : first < child.length := by omega
      have hsb : second < child.length := by omega
      have hsecondne : second ≠ site := by
        intro heq
        rw [heq, hat] at hlow
        have := hbound third htb
        omega
      have hthirdne : third ≠ site := by
        intro heq
        rw [heq, hat] at hhigh
        have := hbound first hfb
        omega
      by_cases hfirstsite : first = site
      · right
        have hgt : site < gap := by
          dsimp [nextgap] at ht
          split_ifs at ht <;> omega
        have hnext : nextgap = gap + 1 := if_neg (by omega)
        rw [hnext] at ht
        rw [hlowerentry second hsb hsecondne, hlowerentry third htb hthirdne] at hlow
        have hls : lower second = second - 1 := if_neg (by omega)
        have hlt : lower third = third - 1 := if_neg (by omega)
        rw [hls, hlt] at hlow
        exact ⟨second - 1, third - 1, by omega, by omega, by omega, hlow⟩
      · left
        rw [hlowerentry second hsb hsecondne, hlowerentry third htb hthirdne] at hlow
        rw [hlowerentry third htb hthirdne, hlowerentry first hfb hfirstsite] at hhigh
        exact ⟨lower first, lower second, lower third,
          hlowermono first second hfs hfirstsite hsecondne,
          hlowermono second third hst hsecondne hthirdne,
          hlowerprefix third hthirdne ht, hlow, hhigh⟩
    · rintro (⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ |
        ⟨second, third, hsecond, hst, ht, hlow⟩)
      · refine ⟨lift first, lift second, lift third, hliftmono first second hfs,
          hliftmono second third hst, hliftprefix third ht, ?_, ?_⟩
        · rwa [hliftentry second (by omega), hliftentry third (by omega)]
        · rwa [hliftentry third (by omega), hliftentry first (by omega)]
      · have hnext : nextgap = gap + 1 := if_neg (by omega)
        have hs := hliftentry second (by omega)
        have ht' := hliftentry third (by omega)
        simp only [lift, if_neg (by omega : ¬ second < site)] at hs
        simp only [lift, if_neg (by omega : ¬ third < site)] at ht'
        refine ⟨site, second + 1, third + 1, by omega, by omega, by omega, ?_, ?_⟩
        · rwa [hs, ht']
        · rw [ht', hat]
          have := hentry third (by omega)
          omega
  have hguard142 : guard142 child nextgap ↔ guard142 p gap ∨
      ∃ first second, first < gap ∧ gap ≤ second ∧ second < site ∧
        p.getD first 0 < p.getD second 0 := by
    constructor
    · rintro ⟨first, second, third, hf, hs, hst, htb, hlow, hhigh⟩
      have hfb : first < child.length := by omega
      have hsb : second < child.length := by omega
      have hfirstne : first ≠ site := by
        intro heq
        rw [heq, hat] at hlow
        have := hbound second hsb
        omega
      have hsecondne : second ≠ site := by
        intro heq
        rw [heq, hat] at hhigh
        have := hbound third htb
        omega
      by_cases hthirdsite : third = site
      · right
        have hle : gap ≤ site := by
          dsimp [nextgap] at hs
          split_ifs at hs <;> omega
        have hnext : nextgap = gap := by simp [nextgap, hle]
        rw [hnext] at hf hs
        rw [hbefore first (by omega), hbefore second (by omega)] at hlow
        exact ⟨first, second, hf, hs, by omega, hlow⟩
      · left
        rw [hlowerentry first hfb hfirstne, hlowerentry second hsb hsecondne] at hlow
        rw [hlowerentry second hsb hsecondne, hlowerentry third htb hthirdsite] at hhigh
        exact ⟨lower first, lower second, lower third, hlowerprefix first hfirstne hf,
          hlowersuffix second hsecondne hs,
          hlowermono second third hst hsecondne hthirdsite,
          hlowerbound third htb hthirdsite, hlow, hhigh⟩
    · rintro (⟨first, second, third, hf, hs, hst, htb, hlow, hhigh⟩ |
        ⟨first, second, hf, hs, hsecond, hlow⟩)
      · refine ⟨lift first, lift second, lift third, hliftprefix first hf,
          hliftsuffix second hs, hliftmono second third hst, hliftbound third htb, ?_, ?_⟩
        · rwa [hliftentry first (by omega), hliftentry second (by omega)]
        · rwa [hliftentry second (by omega), hliftentry third htb]
      · have hnext : nextgap = gap := if_pos (by omega)
        refine ⟨first, second, site, by omega, by omega, hsecond, by omega, ?_, ?_⟩
        · rwa [hbefore first (by omega), hbefore second hsecond]
        · rw [hbefore second hsecond, hat]
          have := hentry second (by omega)
          omega
  have hpackage (pattern : List ℕ) (oldguard childguard extra : Prop)
      (hchildtest : NonnestingDefs.Occurs pattern (child.insertIdx nextgap (n + 2)) ↔
        NonnestingDefs.Occurs pattern child ∨ childguard)
      (holdtest : NonnestingDefs.Occurs pattern (p.insertIdx gap (n + 1)) ↔
        NonnestingDefs.Occurs pattern p ∨ oldguard)
      (hbase : NonnestingDefs.Occurs pattern p → NonnestingDefs.Occurs pattern child)
      (hguard : childguard ↔ oldguard ∨ extra) :
      NonnestingDefs.Occurs pattern (child.insertIdx nextgap (n + 2)) ↔
        NonnestingDefs.Occurs pattern child ∨
        NonnestingDefs.Occurs pattern (p.insertIdx gap (n + 1)) ∨ extra := by
    rw [hchildtest, hguard, holdtest]
    constructor
    · rintro (hc | ho | he)
      · exact Or.inl hc
      · exact Or.inr (Or.inl (Or.inr ho))
      · exact Or.inr (Or.inr he)
    · rintro (hc | (hp | ho) | he)
      · exact Or.inl hc
      · exact Or.inl (hbase hp)
      · exact Or.inr (Or.inl ho)
      · exact Or.inr (Or.inr he)
  have hchildtests := maximum_pattern_tests (n + 1) child hchildperm nextgap hnextgap
  have holdtests := maximum_pattern_tests n p hperm gap hgap
  have hbasetests := maximum_pattern_tests n p hperm site hsite
  have hnextsize : n + 1 + 1 = n + 2 := by omega
  rw [hnextsize] at hchildtests
  exact ⟨hpackage _ _ _ _ hchildtests.1 holdtests.1
      (fun h => hbasetests.1.mpr (Or.inl h)) hguard132,
    hpackage _ _ _ _ hchildtests.2.1 holdtests.2.1
      (fun h => hbasetests.2.1.mpr (Or.inl h)) hguard312,
    hpackage _ _ _ _ hchildtests.2.2 holdtests.2.2
      (fun h => hbasetests.2.2.mpr (Or.inl h)) hguard142⟩

end D5.S3.Combinatorics.Fishburn.FishburnBasicPatternTransport
