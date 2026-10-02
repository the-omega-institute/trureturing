/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBUpdates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBUpdates
   mirror-E: none(waiver:two-pattern-active-site-update)
   anchors: []
   utility: none
   digest: Class B old cuts survive precisely when the additional crossing pairs are absent. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicTenThirteenPatterns
import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponentCuts

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBUpdates

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicFourPatterns FishburnBasicTenThirteenPatterns
open FishburnBasicComponents FishburnBasicComponentCuts
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

theorem crossing_site_updates (n : ℕ) (p : List ℕ) (hn : 0 < n)
    (hparent : p ∈ avoiders n [[2, 4, 3, 1], [3, 2, 4, 1]])
    (site : ℕ) (hsite : site ≤ p.length)
    (hchild : p.insertIdx site (n + 1) ∈
      avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]]) :
    (∀ gap, gap ≤ site →
      ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
          avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
          ∀ before later, before < gap → site ≤ later → later < p.length →
            p.getD before 0 < p.getD later 0)) ∧
    (∀ gap, site < gap → gap ≤ p.length →
      ((p.insertIdx site (n + 1)).insertIdx (gap + 1) (n + 2) ∈
          avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
          ∀ middle later, site ≤ middle → middle < gap → gap ≤ later →
            later < p.length →
            p.getD middle 0 < p.getD later 0)) ∧
    ((p.insertIdx site (n + 1)).insertIdx (site + 1) (n + 2) ∈
        avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔ n ∈ p.take site)∧
   (site = 0 → ∀ parts : List (List ℕ),
     (∀ block ∈ parts, block ≠ [] ∧
       block.Perm (List.range' 1 block.length) ∧ sumIndecomposable block) →
     assemble parts = p →
     let cuts := @Finset.filter ℕ (fun gap =>
       (p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
         avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]])
       (fun _ => Classical.propDecidable _)
       (Finset.range ((p.insertIdx site (n + 1)).length + 1))
     cuts.card = parts.length + 1) := by
  let eligible (word : List ℕ) (gap : ℕ) : Prop :=
    ∀ before later, before + 1 = gap → gap ≤ later → later < word.length →
      word.getD before 0 ≠ word.getD later 0 + 1
  let guard243 (word : List ℕ) (gap : ℕ) : Prop :=
    ∃ first second third, first < gap ∧ gap ≤ second ∧ second < third ∧
      third < word.length ∧ word.getD third 0 < word.getD first 0 ∧
      word.getD first 0 < word.getD second 0
  let guard324 (word : List ℕ) (gap : ℕ) : Prop :=
    ∃ first second third, first < second ∧ second < gap ∧ gap ≤ third ∧
      third < word.length ∧ word.getD third 0 < word.getD second 0 ∧
      word.getD second 0 < word.getD first 0
  have htest (size : ℕ) (word : List ℕ)
      (hp : word ∈ avoiders size [[2, 4, 3, 1], [3, 2, 4, 1]])
      (gap : ℕ) (hg : gap ≤ word.length) :
      word.insertIdx gap (size + 1) ∈
          avoiders (size + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔
        eligible word gap ∧ ¬ guard243 word gap ∧ ¬ guard324 word gap := by
    have hmax : ∀ value ∈ word, value < size + 1 := by
      intro value hv
      have hm := hp.1.mem_iff.mp hv
      simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨index, hi, heq⟩ := hm
      omega
    have h243 := (maximum_crossing_pattern_tests size word hp.1 gap hg).2
    have h324 := (maximum_four_pattern_tests size word hp.1 gap hg).2.2
    have hperm : (word.insertIdx gap (size + 1)).Perm (List.range' 1 (size + 1)) := by
      apply (List.perm_insertIdx (size + 1) word hg).trans
      apply (hp.1.cons (size + 1)).trans
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    constructor
    · intro hc
      refine ⟨(isFishburn_insertIdx_max_iff word (size + 1) gap hg hmax).mp hc.2.1 |>.2,
        ?_, ?_⟩
      · intro hbad
        exact hc.2.2 _ (by simp) (h243.mpr (Or.inr hbad))
      · intro hbad
        exact hc.2.2 _ (by simp) (h324.mpr (Or.inr hbad))
    · rintro ⟨he, hno243, hno324⟩
      refine ⟨hperm,
        (isFishburn_insertIdx_max_iff word (size + 1) gap hg hmax).mpr ⟨hp.2.1, he⟩, ?_⟩
      intro pattern hpattern hbad
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl
      · exact (h243.mp hbad).elim (hp.2.2 _ (by simp)) hno243
      · exact (h324.mp hbad).elim (hp.2.2 _ (by simp)) hno324
  let child := p.insertIdx site (n + 1)
  let lift : ℕ → ℕ := fun index => if index < site then index else index + 1
  let lower : ℕ → ℕ := fun index => if index < site then index else index - 1
  have hlength : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hsite _
  have hentry (index : ℕ) (hi : index < p.length) : p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hi]
      exact List.getElem_mem hi
    have hr := hparent.1.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, hoffset, heq⟩ := hr
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
  have hchildbound (index : ℕ) (hi : index < child.length) : child.getD index 0 ≤ n + 1 := by
    rcases lt_trichotomy index site with hlt | heq | hgt
    · rw [hbefore index hlt]
      exact Nat.le_trans (hentry index (by omega)) (by omega)
    · subst index
      exact Nat.le_of_eq hat
    · rw [hafter index hgt hi]
      exact Nat.le_trans (hentry (index - 1) (by omega)) (by omega)
  have hliftbound (index : ℕ) (hi : index < p.length) : lift index < child.length := by
    dsimp [lift]
    split_ifs <;> omega
  have hliftmono : StrictMono lift := by
    intro first second hs
    dsimp [lift]
    split_ifs <;> omega
  have hliftentry (index : ℕ) (hi : index < p.length) :
      child.getD (lift index) 0 = p.getD index 0 := by
    dsimp [lift]
    split_ifs with hlt
    · exact hbefore index hlt
    · simpa only [Nat.add_sub_cancel] using hafter (index + 1) (by omega) (by omega)
  have hlowerbound (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
      lower index < p.length := by
    dsimp [lower]
    split_ifs <;> omega
  have hlowermono (first second : ℕ) (hf : first ≠ site) (hs : second ≠ site)
      (horder : first < second) : lower first < lower second := by
    dsimp [lower]
    split_ifs <;> omega
  have hlowerentry (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
      child.getD index 0 = p.getD (lower index) 0 := by
    dsimp [lower]
    split_ifs with hlt
    · exact hbefore index hlt
    · exact hafter index (by omega) hi
  have htransport (gap : ℕ) (hgap : gap ≤ p.length) :
      let nextgap := if gap ≤ site then gap else gap + 1
      (eligible child nextgap ↔ eligible p gap) ∧
      (guard243 child nextgap ↔ guard243 p gap ∨
        (gap ≤ site ∧ ∃ before later, before < gap ∧ site ≤ later ∧ later < p.length ∧
          p.getD later 0 < p.getD before 0)) ∧
      (guard324 child nextgap ↔ guard324 p gap ∨
        (site < gap ∧ ∃ middle later, site ≤ middle ∧ middle < gap ∧ gap ≤ later ∧
          later < p.length ∧ p.getD later 0 < p.getD middle 0)) := by
    let nextgap := if gap ≤ site then gap else gap + 1
    have hnextbound : nextgap ≤ child.length := by
      dsimp [nextgap]
      split_ifs <;> omega
    have hliftprefix (index : ℕ) (hi : index < gap) : lift index < nextgap := by
      dsimp [lift, nextgap]
      split_ifs <;> omega
    have hliftsuffix (index : ℕ) (hi : gap ≤ index) : nextgap ≤ lift index := by
      dsimp [lift, nextgap]
      split_ifs <;> omega
    have hlowerprefix (index : ℕ) (hi : index < nextgap) (hne : index ≠ site) :
        lower index < gap := by
      dsimp [lower, nextgap] at *
      split_ifs at * <;> omega
    have hlowersuffix (index : ℕ) (hi : nextgap ≤ index) (hne : index ≠ site) :
        gap ≤ lower index := by
      dsimp [lower, nextgap] at *
      split_ifs at * <;> omega
    change (eligible child nextgap ↔ _) ∧ (guard243 child nextgap ↔ _) ∧
      (guard324 child nextgap ↔ _)
    constructor
    · by_cases hg : gap ≤ site
      · have hnext : nextgap = gap := if_pos hg
        rw [hnext]
        constructor
        · intro he before later hb hl hbound hbad
          apply he before (lift later) hb
            (by simpa only [hnext] using hliftsuffix later hl) (hliftbound later hbound)
          rwa [hbefore before (by omega), hliftentry later hbound]
        · intro he before later hb hl hbound hbad
          rw [hbefore before (by omega)] at hbad
          rcases lt_trichotomy later site with hlt | heq | hgt
          · apply he before later hb hl (by omega)
            rwa [hbefore later hlt] at hbad
          · subst later
            rw [hat] at hbad
            have := hentry before (by omega)
            omega
          · apply he before (later - 1) hb (by omega) (by omega)
            rwa [hafter later hgt hbound] at hbad
      · have hnext : nextgap = gap + 1 := if_neg hg
        rw [hnext]
        constructor
        · intro he before later hb hl hbound hbad
          apply he (before + 1) (later + 1) (by omega) (by omega) (by omega)
          rwa [hafter (before + 1) (by omega) (by omega),
            hafter (later + 1) (by omega) (by omega), Nat.add_sub_cancel]
        · intro he before later hb hl hbound hbad
          apply he (before - 1) (later - 1) (by omega) (by omega) (by omega)
          rwa [hafter before (by omega) (by omega), hafter later (by omega) hbound] at hbad
    constructor
    · constructor
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlo, hhi⟩
        have hfirstne : first ≠ site := by
          intro heq
          subst first
          rw [hat] at hhi
          have := hchildbound second (by omega)
          omega
        have hthirdne : third ≠ site := by
          intro heq
          subst third
          rw [hat] at hlo
          have := hchildbound first (by omega)
          omega
        by_cases hsecond : second = site
        · subst second
          right
          have hgapsite : gap ≤ site := by
            dsimp [nextgap] at hs
            split_ifs at hs <;> omega
          refine ⟨hgapsite, lower first, lower third, hlowerprefix first hf hfirstne,
            ?_, hlowerbound third ht hthirdne, ?_⟩
          · dsimp [lower]
            split_ifs <;> omega
          · rwa [hlowerentry first (by omega) hfirstne, hlowerentry third ht hthirdne] at hlo
        · left
          refine ⟨lower first, lower second, lower third, hlowerprefix first hf hfirstne,
            hlowersuffix second hs hsecond, hlowermono second third hsecond hthirdne hst,
            hlowerbound third ht hthirdne, ?_, ?_⟩
          · rwa [hlowerentry first (by omega) hfirstne, hlowerentry third ht hthirdne] at hlo
          · rwa [hlowerentry first (by omega) hfirstne,
              hlowerentry second (by omega) hsecond] at hhi
      · rintro (⟨first, second, third, hf, hs, hst, ht, hlo, hhi⟩ |
          ⟨hg, before, later, hb, hl, hbound, hbad⟩)
        · refine ⟨lift first, lift second, lift third, hliftprefix first hf,
            hliftsuffix second hs, hliftmono hst, hliftbound third ht, ?_, ?_⟩
          · rwa [hliftentry first (by omega), hliftentry third ht]
          · rwa [hliftentry first (by omega), hliftentry second (by omega)]
        · have hnext : nextgap = gap := if_pos hg
          refine ⟨lift before, site, lift later, hliftprefix before hb, by omega,
            ?_, hliftbound later hbound, ?_, ?_⟩
          · dsimp [lift]
            split_ifs <;> omega
          · rwa [hliftentry before (by omega), hliftentry later hbound]
          · rw [hliftentry before (by omega), hat]
            have := hentry before (by omega)
            omega
    · constructor
      · rintro ⟨first, second, third, hfs, hs, ht, hbound, hlo, hhi⟩
        have hsecondne : second ≠ site := by
          intro heq
          subst second
          rw [hat] at hhi
          have := hchildbound first (by omega)
          omega
        have hthirdne : third ≠ site := by
          intro heq
          subst third
          rw [hat] at hlo
          have := hchildbound second (by omega)
          omega
        by_cases hfirst : first = site
        · subst first
          right
          have hgapsite : site < gap := by
            dsimp [nextgap] at hs
            split_ifs at hs <;> omega
          refine ⟨hgapsite, lower second, lower third, ?_,
            hlowerprefix second hs hsecondne, hlowersuffix third ht hthirdne,
            hlowerbound third hbound hthirdne, ?_⟩
          · dsimp [lower]
            split_ifs <;> omega
          · rwa [hlowerentry second (by omega) hsecondne,
              hlowerentry third hbound hthirdne] at hlo
        · left
          refine ⟨lower first, lower second, lower third,
            hlowermono first second hfirst hsecondne hfs,
            hlowerprefix second hs hsecondne, hlowersuffix third ht hthirdne,
            hlowerbound third hbound hthirdne, ?_, ?_⟩
          · rwa [hlowerentry second (by omega) hsecondne,
              hlowerentry third hbound hthirdne] at hlo
          · rwa [hlowerentry first (by omega) hfirst,
              hlowerentry second (by omega) hsecondne] at hhi
      · rintro (⟨first, second, third, hfs, hs, ht, hbound, hlo, hhi⟩ |
          ⟨hg, middle, later, hm, hmg, hl, hbound, hbad⟩)
        · refine ⟨lift first, lift second, lift third, hliftmono hfs,
            hliftprefix second hs, hliftsuffix third ht, hliftbound third hbound, ?_, ?_⟩
          · rwa [hliftentry second (by omega), hliftentry third hbound]
          · rwa [hliftentry first (by omega), hliftentry second (by omega)]
        · refine ⟨site, lift middle, lift later, ?_, hliftprefix middle hmg,
            hliftsuffix later hl, hliftbound later hbound, ?_, ?_⟩
          · dsimp [lift]
            split_ifs <;> omega
          · rwa [hliftentry middle (by omega), hliftentry later hbound]
          · rw [hat, hliftentry middle (by omega)]
            have := hentry middle (by omega)
            omega
  have hnd : p.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
  have hneq (first later : ℕ) (hf : first < later) (hl : later < p.length) :
      p.getD first 0 ≠ p.getD later 0 := by
    intro heq
    have := (List.getD_inj (by omega) hl hnd).mp heq
    omega
  have hsize : n + 1 + 1 = n + 2 := by omega
  have hupdates :
    (∀ gap, gap ≤ site →
      ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
          avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
          ∀ before later, before < gap → site ≤ later → later < p.length →
            p.getD before 0 < p.getD later 0)) ∧
    (∀ gap, site < gap → gap ≤ p.length →
      ((p.insertIdx site (n + 1)).insertIdx (gap + 1) (n + 2) ∈
          avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 3, 1], [3, 2, 4, 1]] ∧
          ∀ middle later, site ≤ middle → middle < gap → gap ≤ later →
            later < p.length →
            p.getD middle 0 < p.getD later 0)) ∧
    ((p.insertIdx site (n + 1)).insertIdx (site + 1) (n + 2) ∈
        avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔ n ∈ p.take site) := by
    constructor
    · intro gap hg
      have ht := htransport gap (by omega)
      dsimp only at ht
      rw [if_pos hg] at ht
      have hnew := htest (n + 1) child hchild gap (by omega)
      have hold := htest n p hparent gap (by omega)
      rw [hsize] at hnew
      have hsep : (¬ ∃ before later, before < gap ∧ site ≤ later ∧ later < p.length ∧
          p.getD later 0 < p.getD before 0) ↔
          ∀ before later, before < gap → site ≤ later → later < p.length →
            p.getD before 0 < p.getD later 0 := by
        constructor
        · intro hno before later hb hl hbound
          have hne := hneq before later (by omega) hbound
          by_contra hnot
          exact hno ⟨before, later, hb, hl, hbound, by omega⟩
        · intro hs hbad
          obtain ⟨before, later, hb, hl, hbound, hbad⟩ := hbad
          have := hs before later hb hl hbound
          omega
      change child.insertIdx gap (n + 2) ∈ _ ↔ _
      rw [hnew, hold, ht.1, ht.2.1, ht.2.2]
      simp only [hg, true_and, Nat.not_lt.mpr hg, false_and, or_false, not_or]
      constructor
      · rintro ⟨he, ⟨hno243, hnoextra⟩, hno324⟩
        exact ⟨⟨he, hno243, hno324⟩, hsep.mp hnoextra⟩
      · rintro ⟨⟨he, hno243, hno324⟩, hseparated⟩
        exact ⟨he, ⟨hno243, hsep.mpr hseparated⟩, hno324⟩
    constructor
    · intro gap hg hgap
      have ht := htransport gap hgap
      dsimp only at ht
      rw [if_neg (by omega : ¬ gap ≤ site)] at ht
      have hnew := htest (n + 1) child hchild (gap + 1) (by omega)
      have hold := htest n p hparent gap hgap
      rw [hsize] at hnew
      have hsep : (¬ ∃ middle later, site ≤ middle ∧ middle < gap ∧ gap ≤ later ∧
          later < p.length ∧ p.getD later 0 < p.getD middle 0) ↔
          ∀ middle later, site ≤ middle → middle < gap → gap ≤ later →
            later < p.length →
            p.getD middle 0 < p.getD later 0 := by
        constructor
        · intro hno middle later hm hmg hl hbound
          have hne := hneq middle later (by omega) hbound
          by_contra hnot
          exact hno ⟨middle, later, hm, hmg, hl, hbound, by omega⟩
        · intro hs hbad
          obtain ⟨middle, later, hm, hmg, hl, hbound, hbad⟩ := hbad
          have := hs middle later hm hmg hl hbound
          omega
      change child.insertIdx (gap + 1) (n + 2) ∈ _ ↔ _
      rw [hnew, hold, ht.1, ht.2.1, ht.2.2]
      simp only [Nat.not_le.mpr hg, false_and, or_false, hg, true_and, not_or]
      constructor
      · rintro ⟨he, hno243, ⟨hno324, hnoextra⟩⟩
        exact ⟨⟨he, hno243, hno324⟩, hsep.mp hnoextra⟩
      · rintro ⟨⟨he, hno243, hno324⟩, hseparated⟩
        exact ⟨he, hno243, ⟨hno324, hsep.mpr hseparated⟩⟩
    · have hold := (htest n p hparent site hsite).mp hchild
      have hnew := htest (n + 1) child hchild (site + 1) (by omega)
      rw [hsize] at hnew
      have hno243 : ¬ guard243 child (site + 1) := by
        rintro ⟨first, second, third, hf, hs, hst, ht, hlo, hhi⟩
        have hfirst : first < site := by
          by_contra hnot
          have heq : first = site := by omega
          subst first
          rw [hat] at hhi
          have := hchildbound second (by omega)
          omega
        apply hold.2.1
        refine ⟨first, second - 1, third - 1, hfirst, by omega, by omega, by omega, ?_, ?_⟩
        · rwa [hbefore first hfirst, hafter third (by omega) ht] at hlo
        · rwa [hbefore first hfirst, hafter second (by omega) (by omega)] at hhi
      have hno324 : ¬ guard324 child (site + 1) := by
        rintro ⟨first, second, third, hfs, hs, ht, hbound, hlo, hhi⟩
        have hsecond : second < site := by
          by_contra hnot
          have heq : second = site := by omega
          subst second
          rw [hat] at hhi
          have := hchildbound first (by omega)
          omega
        apply hold.2.2
        refine ⟨first, second, third - 1, hfs, hsecond, by omega, by omega, ?_, ?_⟩
        · rwa [hbefore second hsecond, hafter third (by omega) hbound] at hlo
        · rwa [hbefore first (by omega), hbefore second hsecond] at hhi
      rw [hnew]
      constructor
      · rintro ⟨he, _, _⟩
        have hnmem : n ∈ p := by
          apply hparent.1.mem_iff.mpr
          simp only [List.mem_range', Nat.one_mul]
          exact ⟨n - 1, by omega, by omega⟩
        have hnapp : n ∈ p.take site ++ p.drop site := by simpa using hnmem
        rcases List.mem_append.mp hnapp with hnleft | hnright
        · exact hnleft
        · obtain ⟨index, hi, heq⟩ := List.mem_drop_iff_getElem.mp hnright
          apply False.elim
          apply he site (site + index + 1) rfl (by omega) (by omega)
          rw [hat, hafter (site + index + 1) (by omega) (by omega), Nat.add_sub_cancel]
          rw [List.getD_eq_getElem p 0 (by omega), heq]
      · intro hnleft
        refine ⟨?_, hno243, hno324⟩
        intro before later hb hl hbound heq
        have hbeforeeq : before = site := by omega
        subst before
        rw [hat, hafter later (by omega) hbound] at heq
        have hvalue : p.getD (later - 1) 0 = n := by omega
        obtain ⟨index, hi, hindex⟩ := List.mem_take_iff_getElem.mp hnleft
        have hget : p.getD index 0 = n := (List.getD_eq_getElem p 0 (by omega)).trans hindex
        have hindexeq := (List.getD_inj (by omega) (by omega) hnd).mp (hget.trans hvalue.symm)
        omega
  refine ⟨hupdates.1, hupdates.2.1, hupdates.2.2, ?_⟩
  intro hz parts hparts heq
  classical
  dsimp only
  let boundaries := @Finset.filter ℕ (fun gap =>
    ∀ before ∈ p.take gap, ∀ later ∈ p.drop gap, before < later)
    (fun _ => Classical.propDecidable _) (Finset.range (p.length + 1))
  let cuts := (Finset.range (child.length + 1)).filter fun gap =>
    child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]]
  change cuts.card = parts.length + 1
  have hboundaryCount : boundaries.card = parts.length + 1 := by
    dsimp only [boundaries]
    rw [← heq]
    exact component_boundary_count parts hparts
  have hboundary (gap : ℕ) : gap ∈ boundaries ↔ gap ≤ p.length ∧
      ∀ before ∈ p.take gap, ∀ later ∈ p.drop gap, before < later := by
    simp only [boundaries, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hcut (gap : ℕ) : gap ∈ cuts ↔ gap ≤ child.length ∧
      child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] := by
    simp only [cuts, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hseparated (gap : ℕ) (hb : gap ≤ p.length) :
      (∀ before ∈ p.take gap, ∀ later ∈ p.drop gap, before < later) ↔
        ∀ before later, before < gap → gap ≤ later → later < p.length →
          p.getD before 0 < p.getD later 0 := by
    constructor
    · intro hsep before later hbefore hlater hbound
      apply hsep
      · apply List.mem_take_iff_getElem.mpr
        exact ⟨before, by omega, (List.getD_eq_getElem p 0 (by omega)).symm⟩
      · apply List.mem_drop_iff_getElem.mpr
        refine ⟨later - gap, by omega, ?_⟩
        have heq : gap + (later - gap) = later := by omega
        simpa only [heq] using (List.getD_eq_getElem p 0 hbound).symm
    · intro hsep before hbefore later hlater
      obtain ⟨first, hf, heqFirst⟩ := List.mem_take_iff_getElem.mp hbefore
      obtain ⟨second, hs, heqSecond⟩ := List.mem_drop_iff_getElem.mp hlater
      have hless := hsep first (gap + second) (by omega) (by omega) (by omega)
      simpa only [List.getD_eq_getElem p 0 (by omega : first < p.length),
        List.getD_eq_getElem p 0 (by omega : gap + second < p.length),
        heqFirst, heqSecond] using hless
  have hfrontSite (gap : ℕ) (hp : 0 < gap) (hb : gap ≤ p.length) :
      child.insertIdx (gap + 1) (n + 2) ∈
          avoiders (n + 2) [[2, 4, 3, 1], [3, 2, 4, 1]] ↔
        ∀ before ∈ p.take gap, ∀ later ∈ p.drop gap, before < later := by
    rw [hupdates.2.1 gap (by omega) hb]
    constructor
    · rintro ⟨_, hsep⟩
      apply (hseparated gap hb).mpr
      intro before later hbefore hlater hbound
      exact hsep before later (by omega) hbefore hlater hbound
    · intro hsep
      have hs := (hseparated gap hb).mp hsep
      refine ⟨(htest n p hparent gap hb).mpr ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · intro before later hbefore hlater hbound heqValue
          have := hs before later (by omega) hlater hbound
          omega
        · rintro ⟨first, second, third, hf, hsuffix, hst, ht, hlo, hhi⟩
          have := hs first third hf (by omega) ht
          omega
        · rintro ⟨first, second, third, hfs, hsbound, ht, hb, hlo, hhi⟩
          have := hs second third hsbound ht hb
          omega
      · intro before later hbefore hbeforeGap hlater hbound
        exact hs before later hbeforeGap hlater hbound
  have hzero : 0 ∈ cuts := by
    apply (hcut 0).mpr
    refine ⟨Nat.zero_le _, (hupdates.1 0 (Nat.zero_le _)).mpr ?_⟩
    exact ⟨by simpa only [hz] using hchild, by intros; omega⟩
  have hone : 1 ∉ cuts := by
    intro hmem
    have ha := ((hcut 1).mp hmem).2
    have hmax : n ∈ p.take site := hupdates.2.2.mp
      (by simpa only [child, hz, Nat.zero_add] using ha)
    simp only [hz, List.take_zero, List.not_mem_nil] at hmax
  have hdecomp : cuts = {0} ∪ (boundaries.erase 0).image (· + 1) := by
    ext gap
    constructor
    · intro hg
      obtain ⟨hb, ha⟩ := (hcut gap).mp hg
      by_cases hzGap : gap = 0
      · simp [hzGap]
      have hnotOne : gap ≠ 1 := fun h => hone (by simpa only [h] using hg)
      have hprevPositive : 0 < gap - 1 := by omega
      have hprevBound : gap - 1 ≤ p.length := by omega
      have hsep := (hfrontSite (gap - 1) hprevPositive hprevBound).mp
        (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ gap)] using ha)
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨gap - 1, Finset.mem_erase.mpr
        ⟨by omega, (hboundary _).mpr ⟨hprevBound, hsep⟩⟩, by omega⟩
    · intro hg
      rcases Finset.mem_union.mp hg with hzGap | him
      · simpa only [Finset.mem_singleton.mp hzGap] using hzero
      · obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp him
        obtain ⟨hne, hold⟩ := Finset.mem_erase.mp hold
        obtain ⟨hb, hsep⟩ := (hboundary old).mp hold
        exact (hcut _).mpr ⟨by omega, (hfrontSite old (by omega) hb).mpr hsep⟩
  have hdisjoint : Disjoint ({0} : Finset ℕ) ((boundaries.erase 0).image (· + 1)) := by
    apply Finset.disjoint_left.mpr
    intro gap hgap him
    obtain ⟨old, _, heq⟩ := Finset.mem_image.mp him
    simp only [Finset.mem_singleton] at hgap
    omega
  have himage : ((boundaries.erase 0).image (· + 1)).card =
      (boundaries.erase 0).card :=
    Finset.card_image_of_injective _ (fun _ _ heq => Nat.add_right_cancel heq)
  have hboundaryZero : 0 ∈ boundaries := by simp [boundaries]
  have herase := Finset.card_erase_add_one hboundaryZero
  rw [hdecomp, Finset.card_union_of_disjoint hdisjoint, Finset.card_singleton, himage]
  omega

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenBUpdates
