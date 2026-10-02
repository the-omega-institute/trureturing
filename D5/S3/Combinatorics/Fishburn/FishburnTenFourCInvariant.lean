/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFourCInvariant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFourCInvariant
   mirror-E: none(waiver:maximum-deletion-c-site-classification)
   anchors: []
   utility: none
   digest: Maximum-deletion induction classifies C sites and their decreasing maximum interval. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicPatternTransport
import D5.S3.Combinatorics.Fishburn.FishburnBasicPrefixes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFourCInvariant

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicPatterns FishburnBasicPrefixes
open FishburnBasicPatternTransport

theorem all_C_site_invariant : ∀ n : ℕ, 1 ≤ n → ∀ p : List ℕ,
    p ∈ avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]] →
    ∃ one, one < p.length ∧ p.getD one 0 = 1 ∧ ((p.getD 0 0 = n ∧ ∀ gap, gap ≤ p.length →
        (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔
          gap = 0 ∨ gap = one + 1 ∧
            ∀ earlier later, one < earlier → earlier < later → later < p.length →
              p.getD later 0 < p.getD earlier 0)) ∨
      ∃ first last, 0 < first ∧ first < last ∧ last ≤ p.length ∧ p.getD first 0 = n ∧
        ((∀ earlier later, one < earlier → earlier < later → later < p.length →
          p.getD later 0 < p.getD earlier 0) → first = one + 1) ∧
        (∀ earlier later, first ≤ earlier → earlier < later → later < last →
          p.getD later 0 < p.getD earlier 0) ∧
        ∀ gap, gap ≤ p.length →
          (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔
            gap = 0 ∨ gap = first ∨ gap = last)) := by
  have prefix_through_one_decreasing (n : ℕ) (p : List ℕ)
      (hperm : p.Perm (List.range' 1 n)) (hfish : IsFishburn p)
      (one : ℕ) (honebound : one < p.length) (hone : p.getD one 0 = 1) :
      ∀ earlier later, earlier < later → later ≤ one → p.getD later 0 < p.getD earlier 0 := by
    have isFishburn_iff_ascent_predecessor (n : ℕ) (p : List ℕ) (hperm : p.Perm (List.range' 1 n)) :
        IsFishburn p ↔ ∀ index, index + 1 < p.length → p.getD index 0 < p.getD (index + 1) 0 →
            p.getD index 0 = 1 ∨
              ∃ earlier, earlier < index ∧ p.getD earlier 0 + 1 = p.getD index 0 := by
      have hvalues (index : ℕ) (hi : index < p.length) :
          1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
        have hm : p.getD index 0 ∈ p := by
          rw [List.getD_eq_getElem p 0 hi]; exact List.getElem_mem hi
        have hrange := hperm.mem_iff.mp hm; simp only [List.mem_range', Nat.one_mul] at hrange
        obtain ⟨offset, hoffset, hvalue⟩ := hrange; omega
      have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1); constructor
      · intro h index hi hascent; by_cases hone : p.getD index 0 = 1
        · exact Or.inl hone
        · right
          have hbottom := hvalues index (by omega); have hpredmem : p.getD index 0 - 1 ∈ p := by
            apply hperm.mem_iff.mpr; simp only [List.mem_range', Nat.one_mul]
            refine ⟨p.getD index 0 - 2, by omega, by omega⟩
          obtain ⟨earlier, hearlier, hvalue⟩ := List.mem_iff_getElem.mp hpredmem
          have hpred : p.getD earlier 0 + 1 = p.getD index 0 := by
            rw [List.getD_eq_getElem p 0 hearlier, hvalue]; omega
          have hleft : earlier < index := by
            by_contra hnot
            by_cases heq : earlier = index
            · subst earlier; omega
            by_cases hnext : earlier = index + 1
            · subst earlier; omega
            exact h index earlier (by omega) hearlier ⟨hpred.symm, by omega⟩
          exact ⟨earlier, hleft, hpred⟩
      · intro h before later hgap hlater hbad; have ha := h before (by omega) (by omega)
        rcases ha with hone | ⟨earlier, hearlier, hpred⟩
        · have hpositive := (hvalues later hlater).1; omega
        · have heq : p.getD earlier 0 = p.getD later 0 := (by omega)
          have hindex := (List.getD_inj (by omega) hlater hnodup).mp heq; omega
    have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hascents := (isFishburn_iff_ascent_predecessor n p hperm).mp hfish
    have hdec : ∀ later, later ≤ one → ∀ earlier, earlier < later →
        p.getD later 0 < p.getD earlier 0 := by
      intro later; induction later using Nat.strong_induction_on with
      | h later ih =>
        intro hlater earlier hearlier; cases later with
        | zero => omega
        | succ previous =>
          have hstep : p.getD (previous + 1) 0 < p.getD previous 0 := by
            rcases lt_trichotomy (p.getD (previous + 1) 0) (p.getD previous 0) with
              hlt | heq | hascent
            · exact hlt
            · have hindex := (List.getD_inj (by omega) (by omega) hnodup).mp heq; omega
            · rcases hascents previous (by omega) hascent with hbottom | hpred
              · have hindex : previous = one :=
                  (List.getD_inj (by omega) honebound hnodup).mp (hbottom.trans hone.symm)
                omega
              · obtain ⟨pred, hpred, hvalue⟩ := hpred
                have hdecrease := ih previous (by omega) (by omega) pred hpred; omega
          by_cases heq : earlier = previous
          · subst earlier; exact hstep
          · exact lt_trans hstep (ih previous (by omega) (by omega) earlier (by omega))
    intro earlier later hearlier hlater; exact hdec later hlater earlier hearlier
  have hperm (word : List ℕ) (size cut : ℕ)
      (hp : word.Perm (List.range' 1 size)) (hc : cut ≤ word.length) :
      (word.insertIdx cut (size + 1)).Perm (List.range' 1 (size + 1)) := by
    have hp' := (List.perm_insertIdx (size + 1) word hc).trans (hp.cons (size + 1))
    rw [List.range'_concat]; simpa only [Nat.one_mul, Nat.add_comm, List.singleton_append] using
      hp'.trans (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
  have hmax (size : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 size))
      (value : ℕ) (hm : value ∈ word) : value < size + 1 := by
    have hrange := hp.mem_iff.mp hm; simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, hvalue⟩ := hrange; omega
  have hentry (size : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 size))
      (index : ℕ) (hi : index < word.length) : 1 ≤ word.getD index 0 := by
    have hm := hp.mem_iff.mp (List.getElem_mem hi); simp only [List.mem_range', Nat.one_mul] at hm
    rw [List.getD_eq_getElem word 0 hi]; obtain ⟨offset, hoffset, hvalue⟩ := hm; omega
  have hfront (size : ℕ) (word : List ℕ) (hp : word ∈ avoiders size [[1, 4, 2, 3], [3, 1, 2, 4]]) :
      word.insertIdx 0 (size + 1) ∈ avoiders (size + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] := by
    refine ⟨hperm word size 0 hp.1 (by omega), ?_, ?_⟩
    · exact (isFishburn_insertIdx_max_iff word (size + 1) 0 (by omega)
        (hmax size word hp.1)).mpr ⟨hp.2.1, by intro before later heq; omega⟩
    · have ht := maximum_pattern_tests size word hp.1 0 (by omega); intro pattern hm hocc
      have hc : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := (by simpa using hm)
      rcases hc with rfl | rfl
      · exact hp.2.2 _ hm (by simpa using ht.2.2.mp hocc)
      · exact hp.2.2 _ hm (by simpa using ht.2.1.mp hocc)
  have honebefore (n : ℕ) (p : List ℕ) (hp : p ∈ avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]])
      (one : ℕ) (hb : one < p.length) (hv : p.getD one 0 = 1)
      (cut : ℕ) (hc : cut ≤ p.length) (hpos : 0 < cut)
      (ha : p.insertIdx cut (n + 1) ∈
        avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]]) : one < cut := by
    have hg := (isFishburn_insertIdx_max_iff p (n + 1) cut hc (hmax n p hp.1)).mp ha.2.1
    have hm := (eligible_prefix_structure n p hp.1 hp.2.1 cut hc hpos hg.2).1
    obtain ⟨index, hib, hiv⟩ := List.mem_iff_getElem.mp hm
    have hi : index < p.length := (by simp only [List.length_take] at hib; omega)
    have he : p.getD index 0 = 1 := by
      rw [List.getD_eq_getElem p 0 hi]; simpa only [List.getElem_take] using hiv
    have heq := (List.getD_inj hi hb (hp.1.nodup_iff.mpr (List.nodup_range' 1))).mp
      (he.trans hv.symm)
    simp only [List.length_take] at hib; omega
  have parent_exists (n : ℕ) (word : List ℕ)
      (hw : word ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]]) :
      ∃ parent site, parent ∈ avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]] ∧
        site ≤ parent.length ∧ parent.insertIdx site (n + 1) = word := by
    have hlen : word.length = n + 1 := (by simpa using hw.1.length_eq)
    have hm : n + 1 ∈ word := hw.1.mem_iff.mpr (by
      simp only [List.mem_range', Nat.one_mul]; exact ⟨n, by omega, by omega⟩)
    obtain ⟨site, hs, hv⟩ := List.mem_iff_getElem.mp hm; let parent := word.eraseIdx site
    have hinverse : parent.insertIdx site (n + 1) = word := by
      simpa only [parent, hv] using List.insertIdx_eraseIdx_getElem hs
    have hparentlen : parent.length = n := by
      simp only [parent, List.length_eraseIdx_of_lt hs, hlen]; omega
    have hsite : site ≤ parent.length := (by omega); have hp : parent.Perm (List.range' 1 n) := by
      have hc : ((n + 1) :: parent).Perm word := by
        simpa only [parent, hv] using List.getElem_cons_eraseIdx_perm hs
      have hr : (List.range' 1 (n + 1)).Perm ((n + 1) :: List.range' 1 n) := by
        rw [List.range'_concat]
        simpa [Nat.add_comm] using (List.perm_append_comm (l₁ := List.range' 1 n) (l₂ := [n + 1]))
      exact (hc.trans (hw.1.trans hr)).cons_inv
    refine ⟨parent, site, ⟨hp, ?_, ?_⟩, hsite, hinverse⟩
    · exact ((isFishburn_insertIdx_max_iff parent (n + 1) site hsite
        (hmax n parent hp)).mp (by rw [hinverse]; exact hw.2.1)).1
    · intro pattern hm hocc; obtain ⟨values, hstep, hmem, hsub, hrel⟩ := hocc
      apply hw.2.2 pattern hm
      refine ⟨values, hstep, ?_, hsub.trans (List.eraseIdx_sublist word site), by simp⟩
      intro rank hlow hhigh; exact (List.eraseIdx_sublist word site).subset (hmem rank hlow hhigh)
  have after_maximum_active_iff (n : ℕ) (p : List ℕ)
      (hp : p ∈ avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]]) (site : ℕ)
      (hpos : 0 < site) (hs : site ≤ p.length)
      (ha : p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]]) :
      (p.insertIdx site (n + 1)).insertIdx (site + 1) (n + 2) ∈
        avoiders (n + 2) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔
        ∃ earlier < site, p.getD earlier 0 = n := by
    let child := p.insertIdx site (n + 1)
    have hlen : child.length = p.length + 1 := List.length_insertIdx_of_le_length hs _
    have hat : child.getD site 0 = n + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]; exact List.getElem_insertIdx_self _
    have hbefore (index : ℕ) (hi : index < site) : child.getD index 0 = p.getD index 0 := by
      rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
        List.getD_eq_getElem p 0 (by omega)]
    have hafter (index : ℕ) (hi : site < index) (hb : index < child.length) :
        child.getD index 0 = p.getD (index - 1) 0 := by
      rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hi,
        List.getD_eq_getElem p 0 (by omega)]
    have hbound (index : ℕ) (hi : index < child.length) : child.getD index 0 ≤ n + 1 := by
      rw [List.getD_eq_getElem child 0 hi]
      have := hmax (n + 1) child ha.1 _ (List.getElem_mem hi); omega
    have hsafe : ∀ pattern ∈ [[1, 4, 2, 3], [3, 1, 2, 4]],
        ¬ NonnestingDefs.Occurs pattern (child.insertIdx (site + 1) (n + 2)) := by
      have ht := maximum_pattern_tests (n + 1) child ha.1 (site + 1) (by omega)
      have ho := maximum_pattern_tests n p hp.1 site hs; intro pattern hm hocc
      have hc : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := (by simpa using hm)
      rcases hc with rfl | rfl
      · rcases ht.2.2.mp hocc with hold | ⟨first, second, third, hf, hsuf, hst, hb, hl, hh⟩
        · exact ha.2.2 _ hm hold
        · have hfirst : first < site := by
            by_contra hnot
            have heq : first = site := (by omega)
            rw [heq, hat] at hl; have := hbound second (by omega); omega
          rw [hbefore first hfirst, hafter second (by omega) (by omega)] at hl
          rw [hafter second (by omega) (by omega), hafter third (by omega) hb] at hh
          exact ha.2.2 _ hm (ho.2.2.mpr (Or.inr
            ⟨first, second - 1, third - 1, hfirst, by omega, by omega, by omega, hl, hh⟩))
      · rcases ht.2.1.mp hocc with hold | ⟨first, second, third, hfs, hst, ht, hl, hh⟩
        · exact ha.2.2 _ hm hold
        · have hthird : third < site := by
            by_contra hnot
            have heq : third = site := (by omega)
            rw [heq, hat] at hh; have := hbound first (by omega); omega
          rw [hbefore second (by omega), hbefore third hthird] at hl
          rw [hbefore third hthird, hbefore first (by omega)] at hh
          exact ha.2.2 _ hm (ho.2.1.mpr (Or.inr ⟨first, second, third, hfs, hst, hthird, hl, hh⟩))
    constructor
    · intro hn
      have hg := (isFishburn_insertIdx_max_iff child (n + 2) (site + 1) (by omega)
        (hmax (n + 1) child ha.1)).mp hn.2.1
      have hsize : 1 ≤ n := by
        have hlength := hp.1.length_eq; simp only [List.length_range'] at hlength; omega
      have hm : n ∈ p := hp.1.mem_iff.mpr (by
        simp only [List.mem_range', Nat.one_mul]; exact ⟨n - 1, by omega, by omega⟩)
      obtain ⟨earlier, hb, hv⟩ := List.mem_iff_getElem.mp hm
      have he : p.getD earlier 0 = n := (by rwa [List.getD_eq_getElem p 0 hb])
      refine ⟨earlier, ?_, he⟩
      by_contra hnot
      apply hg.2 site (earlier + 1) rfl (by omega) (by omega)
      rw [hat, hafter (earlier + 1) (by omega) (by omega), Nat.add_sub_cancel, he]
    · rintro ⟨earlier, hb, hv⟩; refine ⟨hperm child (n + 1) (site + 1) ha.1 (by omega), ?_, hsafe⟩
      apply (isFishburn_insertIdx_max_iff child (n + 2) (site + 1) (by omega)
        (hmax (n + 1) child ha.1)).mpr
      refine ⟨ha.2.1, ?_⟩
      intro before later hc hl hboundlater heq; have heqbefore : before = site := (by omega)
      subst before; rw [hat, hafter later (by omega) hboundlater] at heq
      have hsame : p.getD earlier 0 = p.getD (later - 1) 0 := (by omega)
      have hi := (List.getD_inj (by omega) (by omega)
        (hp.1.nodup_iff.mpr (List.nodup_range' 1))).mp hsame
      omega
  have positive_C_inherited_sites (n : ℕ) (p : List ℕ)
      (hparent : p ∈ avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]])
      (site : ℕ) (hpositive : 0 < site) (hsite : site ≤ p.length)
      (hactive : p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]])
      (gap : ℕ) (hgpositive : 0 < gap) (hgap : gap ≤ p.length) :
      (p.insertIdx site (n + 1)).insertIdx (if gap ≤ site then gap else gap + 1) (n + 2) ∈
        avoiders (n + 2) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔
      p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] ∧
        site ≤ gap ∧ ∀ earlier later, site ≤ earlier → earlier < later → later < gap →
          p.getD later 0 < p.getD earlier 0 := by
    let child := p.insertIdx site (n + 1); let nextgap := if gap ≤ site then gap else gap + 1
    let lift := fun index : ℕ => if index < site then index else index + 1
    let lower := fun index : ℕ => if index < site then index else index - 1
    have hlength : child.length = p.length + 1 := List.length_insertIdx_of_le_length hsite (n + 1)
    have hnextgap : nextgap ≤ child.length := (by dsimp [nextgap]; split_ifs <;> omega)
    have hnextpositive : 0 < nextgap := (by dsimp [nextgap]; split_ifs <;> omega)
    have hnextne : nextgap ≠ site + 1 := (by dsimp [nextgap]; split_ifs <;> omega)
    have hnodup : p.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
    have hmaxp := hmax n p hparent.1; have hmaxchild := hmax (n + 1) child hactive.1
    have hentry (index : ℕ) (hi : index < p.length) : 1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
      refine ⟨hentry n p hparent.1 index hi, ?_⟩
      rw [List.getD_eq_getElem p 0 hi]; have := hmax n p hparent.1 _ (List.getElem_mem hi); omega
    have hbefore (index : ℕ) (hi : index < site) : child.getD index 0 = p.getD index 0 := by
      rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
        List.getD_eq_getElem p 0 (by omega)]
    have hat : child.getD site 0 = n + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]; exact List.getElem_insertIdx_self _
    have hlowerentry (index : ℕ) (hi : index < child.length) (hne : index ≠ site) :
        child.getD index 0 = p.getD (lower index) 0 := by
      dsimp [lower]; split_ifs with hlt
      · exact hbefore index hlt
      · rw [List.getD_eq_getElem child 0 hi, List.getElem_insertIdx_of_gt (by omega),
          List.getD_eq_getElem p 0 (by omega)]
    have hliftentry (index : ℕ) (hi : index < p.length) :
        child.getD (lift index) 0 = p.getD index 0 := by
      dsimp [lift]; split_ifs with hlt
      · exact hbefore index hlt
      · rw [List.getD_eq_getElem child 0 (by omega),
          List.getElem_insertIdx_of_gt (by omega), List.getD_eq_getElem p 0 (by omega)]
        simp only [Nat.add_sub_cancel]
    have heligible :
        (∀ before later, before + 1 = nextgap → nextgap ≤ later → later < child.length →
          child.getD before 0 ≠ child.getD later 0 + 1) ↔
        (∀ before later, before + 1 = gap → gap ≤ later → later < p.length →
          p.getD before 0 ≠ p.getD later 0 + 1) := by
      constructor
      · intro h before later hcross hlater hb heq
        let nextbefore := if gap ≤ site then before else before + 1
        have hnextbefore : nextbefore + 1 = nextgap := by
          dsimp [nextbefore, nextgap]; split_ifs <;> omega
        have hnextlater : nextgap ≤ lift later := (by dsimp [nextgap, lift]; split_ifs <;> omega)
        have hlaterbound : lift later < child.length := (by dsimp [lift]; split_ifs <;> omega)
        have hbottom : child.getD nextbefore 0 = p.getD before 0 := by
          dsimp [nextbefore]; split_ifs with hle
          · exact hbefore before (by omega)
          · have he := hliftentry before (by omega)
            simpa only [lift, if_neg (by omega : ¬ before < site)] using he
        apply h nextbefore (lift later) hnextbefore hnextlater hlaterbound
        rwa [hbottom, hliftentry later hb]
      · intro h before later hcross hlater hb heq; have hbeforene : before ≠ site := (by omega)
        have hbeforebound : before < child.length := (by omega)
        have hbeforelower : lower before + 1 = gap := by
          by_cases hle : gap ≤ site
          · simp only [nextgap, if_pos hle] at hcross
            simp only [lower, if_pos (by omega : before < site)]; omega
          · simp only [nextgap, if_neg hle] at hcross
            simp only [lower, if_neg (by omega : ¬ before < site)]; omega
        by_cases hlatermaximum : later = site
        · rw [hlatermaximum, hat, hlowerentry before hbeforebound hbeforene] at heq
          have hlowerbound : lower before < p.length := (by dsimp [lower]; split_ifs <;> omega)
          have := hentry (lower before) hlowerbound; omega
        · have hlaterlower : gap ≤ lower later := by
            by_cases hle : gap ≤ site
            · simp only [nextgap, if_pos hle] at hlater; dsimp [lower]; split_ifs <;> omega
            · simp only [nextgap, if_neg hle] at hlater; dsimp [lower]; split_ifs <;> omega
          have hlowerbound : lower later < p.length := (by dsimp [lower]; split_ifs <;> omega)
          apply h (lower before) (lower later) hbeforelower hlaterlower hlowerbound
          rwa [hlowerentry before hbeforebound hbeforene, hlowerentry later hb hlatermaximum] at heq
    have hfishiff : IsFishburn (child.insertIdx nextgap (n + 2)) ↔
        IsFishburn (p.insertIdx gap (n + 1)) := by
      have hc := isFishburn_insertIdx_max_iff child (n + 2) nextgap hnextgap hmaxchild
      have hp := isFishburn_insertIdx_max_iff p (n + 1) gap hgap hmaxp; constructor
      · intro hf; exact hp.mpr ⟨hparent.2.1, heligible.mp (hc.mp hf).2⟩
      · intro hf; exact hc.mpr ⟨hactive.2.1, heligible.mpr (hp.mp hf).2⟩
    have ht := maximum_pattern_transport n p hparent.1 site gap hsite hgap
    change child.insertIdx nextgap (n + 2) ∈ avoiders (n + 2) _ ↔ _; constructor
    · intro hn
      have hold : p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] := by
        refine ⟨hperm p n gap hparent.1 hgap, hfishiff.mp hn.2.1, ?_⟩
        intro pattern hm hocc
        have hc : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := (by simpa using hm)
        rcases hc with rfl | rfl
        · exact hn.2.2 _ hm (ht.2.2.mpr (Or.inr (Or.inl hocc)))
        · exact hn.2.2 _ hm (ht.2.1.mpr (Or.inr (Or.inl hocc)))
      have hle : site ≤ gap := by
        by_contra hnot
        have hg := (isFishburn_insertIdx_max_iff p (n + 1) gap hgap hmaxp).mp hold.2.1
        have hm := (eligible_prefix_structure n p hparent.1 hparent.2.1 gap hgap hgpositive hg.2).1
        obtain ⟨one, hb, hv⟩ := List.mem_iff_getElem.mp hm
        have ho : one < gap := (by simp only [List.length_take] at hb; omega)
        have he : p.getD one 0 = 1 := by
          rw [List.getD_eq_getElem p 0 (by omega)]; simpa only [List.getElem_take] using hv
        have hneq : p.getD gap 0 ≠ 1 := by
          intro hh; have hi := (List.getD_inj (by omega) (by omega) hnodup).mp (hh.trans he.symm)
          omega
        have hb := hentry gap (by omega); apply hn.2.2 [1, 4, 2, 3] (by simp); apply ht.2.2.mpr
        exact Or.inr (Or.inr ⟨one, gap, ho, le_refl _, by omega, by rw [he]; omega⟩)
      refine ⟨hold, hle, ?_⟩
      intro earlier later hs hl hb; have hneq : p.getD later 0 ≠ p.getD earlier 0 := by
        intro he; have hi := (List.getD_inj (by omega) (by omega) hnodup).mp he; omega
      have hno : ¬ p.getD earlier 0 < p.getD later 0 := by
        intro hh
        exact hn.2.2 _ (by simp) (ht.2.1.mpr (Or.inr (Or.inr ⟨earlier, later, hs, hl, hb, hh⟩)))
      omega
    · rintro ⟨hold, hle, hdec⟩
      refine ⟨hperm child (n + 1) nextgap hactive.1 hnextgap, hfishiff.mpr hold.2.1, ?_⟩
      intro pattern hm hocc
      have hc : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := (by simpa using hm)
      rcases hc with rfl | rfl
      · rcases ht.2.2.mp hocc with hc | ho | ⟨first, second, hf, hs, hb, hh⟩
        · exact hactive.2.2 _ hm hc
        · exact hold.2.2 _ hm ho
        · omega
      · rcases ht.2.1.mp hocc with hc | ho | ⟨earlier, later, hs, hl, hb, hh⟩
        · exact hactive.2.2 _ hm hc
        · exact hold.2.2 _ hm ho
        · have := hdec earlier later hs hl hb; omega
  have cut_after_one_active_iff_valley (n : ℕ) (p : List ℕ)
      (hparent : p ∈ avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]])
      (one : ℕ) (honebound : one < p.length) (hone : p.getD one 0 = 1) :
      p.insertIdx (one + 1) (n + 1) ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔
        ∀ earlier later, one < earlier → earlier < later → later < p.length →
          p.getD later 0 < p.getD earlier 0 := by
    have hmaxp := hmax n p hparent.1; have hpositive := hentry n p hparent.1
    have hnodup : p.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
    have hprefix := prefix_through_one_decreasing n p hparent.1 hparent.2.1 one honebound hone
    have htests := maximum_pattern_tests n p hparent.1 (one + 1) (by omega)
    have hno312 : ¬ NonnestingDefs.Occurs [3, 1, 2, 4] (p.insertIdx (one + 1) (n + 1)) := by
      intro hocc; rcases htests.2.1.mp hocc with hold | hnew
      · exact hparent.2.2 _ (by simp) hold
      · obtain ⟨first, second, third, hfs, hst, ht, hlow, hhigh⟩ := hnew
        have hdec := hprefix second third hst (by omega); omega
    constructor
    · intro hactive earlier later honeearlier hearlierlater hlaterbound
      have hearlierbound : earlier < p.length := (by omega)
      rcases lt_trichotomy (p.getD later 0) (p.getD earlier 0) with hlt | heq | hgt
      · exact hlt
      · have hi := (List.getD_inj hlaterbound hearlierbound hnodup).mp heq; omega
      · have haboveone : 1 < p.getD earlier 0 := by
          have hp := hpositive earlier hearlierbound; have hne : p.getD earlier 0 ≠ 1 := by
            intro heq
            have hi := (List.getD_inj hearlierbound honebound hnodup).mp (heq.trans hone.symm)
            omega
          omega
        apply False.elim; apply hactive.2.2 [1, 4, 2, 3] (by simp); apply htests.2.2.mpr; right
        refine ⟨one, earlier, later, by omega, by omega, hearlierlater, hlaterbound, ?_, hgt⟩
        rwa [hone]
    · intro hvalley; refine ⟨?_, ?_, ?_⟩
      · exact hperm p n (one + 1) hparent.1 (by omega)
      · apply (isFishburn_insertIdx_max_iff p (n + 1) (one + 1) (by omega) hmaxp).mpr
        refine ⟨hparent.2.1, ?_⟩
        intro before later hcross hlater hlaterbound heq; have hbefore : before = one := (by omega)
        rw [hbefore, hone] at heq; have hp := hpositive later hlaterbound; omega
      · intro pattern hm hocc
        have hc : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := (by simpa using hm)
        rcases hc with rfl | rfl
        · rcases htests.2.2.mp hocc with hold | hnew
          · exact hparent.2.2 _ (by simp) hold
          · obtain ⟨first, second, third, hf, hs, hst, htb, hlow, hhigh⟩ := hnew
            have hdec := hvalley second third (by omega) hst htb; omega
        · exact hno312 hocc
  have prepend_C_sites (n : ℕ) (p : List ℕ) (hp : p ∈ avoiders n [[1, 4, 2, 3], [3, 1, 2, 4]])
      (one : ℕ) (hb : one < p.length) (hv : p.getD one 0 = 1)
      (cut : ℕ) (hc : cut ≤ p.length + 1) :
      ((n + 1) :: p).insertIdx cut (n + 2) ∈ avoiders (n + 2) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔
        cut = 0 ∨ cut = one + 2 ∧ ∀ earlier later,
          one < earlier → earlier < later → later < p.length →
            p.getD later 0 < p.getD earlier 0 := by
    have hbase := hfront n p hp; by_cases hz : cut = 0
    · subst cut; exact iff_of_true (hfront (n + 1) ((n + 1) :: p) hbase) (Or.inl rfl)
    obtain ⟨site, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz; have hs : site ≤ p.length := (by omega)
    let child := (n + 1) :: p; have hlen : child.length = p.length + 1 := rfl
    have htail (index : ℕ) (hi : 0 < index) : child.getD index 0 = p.getD (index - 1) 0 := by
      obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : index ≠ 0); simp [child]
    have ht := maximum_pattern_transport n p hp.1 0 site (by omega) hs
    have hfish : IsFishburn (child.insertIdx (site + 1) (n + 2)) ↔
        site ≠ 0 ∧ IsFishburn (p.insertIdx site (n + 1)) := by
      rw [isFishburn_insertIdx_max_iff child (n + 2) (site + 1) (by omega)
        (hmax (n + 1) child hbase.1),
        isFishburn_insertIdx_max_iff p (n + 1) site hs (hmax n p hp.1)]
      constructor
      · rintro ⟨_, hg⟩; have hnonzero : site ≠ 0 := by
          intro heq; have hn : 1 ≤ n := by
            have hlength := hp.1.length_eq; simp only [List.length_range'] at hlength; omega
          have hm : n ∈ p := hp.1.mem_iff.mpr (by
            simp only [List.mem_range', Nat.one_mul]; exact ⟨n - 1, by omega, by omega⟩)
          obtain ⟨index, hi, he⟩ := List.mem_iff_getElem.mp hm
          apply hg 0 (index + 1) (by omega) (by omega) (by omega)
          simpa only [child, List.getD_cons_zero, List.getD_cons_succ,
            List.getD_eq_getElem p 0 hi, he] using (show n + 1 = n + 1 from rfl)
        refine ⟨hnonzero, hp.2.1, ?_⟩
        intro before later he hl hlb heq
        apply hg (before + 1) (later + 1) (by omega) (by omega) (by omega)
        simpa only [child, List.getD_cons_succ] using heq
      · rintro ⟨hnonzero, _, hg⟩; refine ⟨hbase.2.1, ?_⟩
        intro before later he hl hlb heq
        rw [htail before (by omega), htail later (by omega)] at heq
        exact hg (before - 1) (later - 1) (by omega) (by omega) (by omega) heq
    constructor
    · intro ha; have hf := hfish.mp ha.2.1; have hpositive : 0 < site := (by omega)
      have hmap : (if site ≤ 0 then site else site + 1) = site + 1 := if_neg (by omega)
      rw [hmap, List.insertIdx_zero] at ht
      have hold : p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] := by
        refine ⟨hperm p n site hp.1 hs, hf.2, ?_⟩
        intro pattern hm ho
        have hcases : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := (by simpa using hm)
        rcases hcases with rfl | rfl
        · exact ha.2.2 _ hm (ht.2.2.mpr (Or.inr (Or.inl ho)))
        · exact ha.2.2 _ hm (ht.2.1.mpr (Or.inr (Or.inl ho)))
      have honecut := honebefore n p hp one hb hv site hs hpositive hold
      have hsiteone : site = one + 1 := by
        by_contra hnot
        have hvalue := hentry n p hp.1 (one + 1) (by omega)
        have hneq : p.getD (one + 1) 0 ≠ 1 := by
          intro he
          have hi := (List.getD_inj (by omega) hb
            (hp.1.nodup_iff.mpr (List.nodup_range' 1))).mp (he.trans hv.symm); omega
        apply ha.2.2 [3, 1, 2, 4] (by simp)
        exact ht.2.1.mpr (Or.inr (Or.inr
          ⟨one, one + 1, by omega, by omega, by omega, by rw [hv]; omega⟩))
      exact Or.inr ⟨by omega, (cut_after_one_active_iff_valley n p hp one hb hv).mp
        (by simpa only [hsiteone] using hold)⟩
    · rintro (hzero | ⟨heq, hdec⟩)
      · omega
      have hsone : site = one + 1 := (by omega)
      have hmap : (if site ≤ 0 then site else site + 1) = site + 1 := if_neg (by omega)
      rw [hmap, List.insertIdx_zero] at ht
      have hold := (cut_after_one_active_iff_valley n p hp one hb hv).mpr hdec; rw [← hsone] at hold
      refine ⟨hperm child (n + 1) (site + 1) hbase.1 (by omega), hfish.mpr ⟨by omega, hold.2.1⟩, ?_⟩
      intro pattern hm hocc
      have hcases : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := (by simpa using hm)
      rcases hcases with rfl | rfl
      · have ho := ht.2.2.mp hocc; rcases ho with hc | ho | ⟨first, second, hf, hs, ht, hh⟩
        · exact hbase.2.2 _ hm hc
        · exact hold.2.2 _ hm ho
        · omega
      · have ho := ht.2.1.mp hocc; rcases ho with hc | ho | ⟨earlier, later, hs, hl, ht, hh⟩
        · exact hbase.2.2 _ hm hc
        · exact hold.2.2 _ hm ho
        · have hd := prefix_through_one_decreasing n p hp.1 hp.2.1 one hb hv
            earlier later hl (by omega)
          omega
  intro size; induction size with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn word hword; by_cases hzero : n = 0
    · subst n; have hrootperm : word.Perm [1] := hword.1
      have heq := List.perm_singleton.mp hrootperm; subst word
      refine ⟨0, by decide, rfl, Or.inl ⟨rfl, ?_⟩⟩
      intro gap hgap; have hg : gap ≤ 1 := hgap
      have hactive : [1].insertIdx gap 2 ∈ avoiders 2 [[1, 4, 2, 3], [3, 1, 2, 4]] := by
        refine ⟨hperm [1] 1 gap (List.Perm.refl _) hgap, ?_, ?_⟩
        · apply (isFishburn_insertIdx_max_iff [1] 2 gap hgap (by simp)).mpr; constructor
          · intro before later he hl; change later < 1 at hl; omega
          · intro before later he hl hb heq; change later < 1 at hb
            have hbefore : before = 0 := (by omega); have hlater : later = 0 := (by omega)
            subst before; subst later; simp at heq
        · intro pattern hm hocc
          have hc : pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := (by simpa using hm)
          rcases hc with rfl | rfl <;> obtain ⟨values, _, _, hsub, _⟩ := hocc <;>
            have hb := hsub.length_le <;> simp only [List.length_map] at hb
          all_goals
            have hlen := List.length_insertIdx_of_le_length hgap 2
            change 4 ≤ ([1].insertIdx gap 2).length at hb
            simp only [List.length_cons, List.length_nil] at hlen; omega
      constructor
      · intro _; have hc : gap = 0 ∨ gap = 1 := (by omega); rcases hc with hgapzero | hgapone
        · exact Or.inl hgapzero
        · refine Or.inr ⟨hgapone, ?_⟩
          intro earlier later he hl hb; change later < 1 at hb; omega
      · intro _; exact hactive
    · have hnpositive : 1 ≤ n := (by omega)
      obtain ⟨parent, site, hparent, hsite, rfl⟩ := parent_exists n word hword
      have hactive := hword; let child := parent.insertIdx site (n + 1)
      have hlen : child.length = parent.length + 1 := List.length_insertIdx_of_le_length hsite _
      have hinsertlen : (parent.insertIdx site (n + 1)).length = parent.length + 1 := hlen
      have hparentlen : parent.length = n := (by simpa using hparent.1.length_eq)
      obtain ⟨one, honebound, hone, hcase⟩ := ih hnpositive parent hparent
      have hmax (value : ℕ) (hm : value ∈ parent) : value < n + 1 := by
        have hrange := hparent.1.mem_iff.mp hm; simp only [List.mem_range', Nat.one_mul] at hrange
        obtain ⟨offset, hoffset, heq⟩ := hrange; omega
      have hbound (index : ℕ) (hi : index < parent.length) : parent.getD index 0 < n + 1 := by
        rw [List.getD_eq_getElem parent 0 hi]; exact hmax _ (List.getElem_mem hi)
      have hbefore (index : ℕ) (hi : index < site) : child.getD index 0 = parent.getD index 0 := by
        rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
          List.getD_eq_getElem parent 0 (by omega)]
      have hat : child.getD site 0 = n + 1 := by
        rw [List.getD_eq_getElem child 0 (by omega)]; exact List.getElem_insertIdx_self _
      have hafter (index : ℕ) (hi : site < index) (hb : index < child.length) :
          child.getD index 0 = parent.getD (index - 1) 0 := by
        rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hi,
          List.getD_eq_getElem parent 0 (by omega)]
      by_cases hsitezero : site = 0
      · subst site; have hchild : child = (n + 1) :: parent := rfl
        refine ⟨one + 1, by omega, ?_, Or.inl ⟨rfl, ?_⟩⟩
        · simpa only [List.insertIdx_zero, List.getD_cons_succ] using hone
        · intro gap hgap
          have hsites := prepend_C_sites n parent hparent one honebound hone gap (by omega)
          have hvalley : (∀ earlier later, one < earlier → earlier < later → later < parent.length →
                parent.getD later 0 < parent.getD earlier 0) ↔
              ∀ earlier later, one + 1 < earlier → earlier < later →
                later < child.length → child.getD later 0 < child.getD earlier 0 := by
            constructor
            · intro hv earlier later he hl hb
              rw [hafter later (by omega) hb, hafter earlier (by omega) (by omega)]
              exact hv (earlier - 1) (later - 1) (by omega) (by omega) (by omega)
            · intro hv earlier later he hl hb
              have hh := hv (earlier + 1) (later + 1) (by omega) (by omega) (by omega)
              simpa only [child, List.insertIdx_zero, List.getD_cons_succ] using hh
          simpa only [child, List.insertIdx_zero, Nat.add_assoc, Nat.reduceAdd,
            hvalley] using hsites
      · have hsitepositive : 0 < site := (by omega)
        have hnodup : parent.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
        have honecut := honebefore n parent hparent one honebound hone
          site hsite hsitepositive hactive
        have hchildadj : (∀ earlier later, one < earlier → earlier < later → later < child.length →
              child.getD later 0 < child.getD earlier 0) → site = one + 1 := by
          intro hv; by_contra hnot; have hh := hv (one + 1) site (by omega) (by omega) (by omega)
          rw [hat, hbefore (one + 1) (by omega)] at hh; have hb := hbound (one + 1) (by omega)
          omega
        have hchildshape (last : ℕ) (hafterrule :
            (∃ earlier < site, parent.getD earlier 0 = n) ↔ last = site + 1)
            (hinherited : ∀ oldgap, 0 < oldgap → oldgap ≤ parent.length →
              ((parent.insertIdx oldgap (n + 1) ∈
                  avoiders (n + 1) [[1, 4, 2, 3], [3, 1, 2, 4]] ∧ site ≤ oldgap ∧
                ∀ earlier later, site ≤ earlier → earlier < later → later < oldgap →
                  parent.getD later 0 < parent.getD earlier 0) ↔
                (if oldgap ≤ site then oldgap else oldgap + 1) = site ∨
                (if oldgap ≤ site then oldgap else oldgap + 1) = last)) :
            ∀ gap, gap ≤ child.length → (child.insertIdx gap (n + 2) ∈
                avoiders (n + 2) [[1, 4, 2, 3], [3, 1, 2, 4]] ↔
                gap = 0 ∨ gap = site ∨ gap = last) := by
          intro gap hgap; by_cases hgapzero : gap = 0
          · subst gap; exact iff_of_true (hfront (n + 1) child hactive) (Or.inl rfl)
          by_cases hgapafter : gap = site + 1
          · subst gap
            have hrule := after_maximum_active_iff n parent hparent site hsitepositive hsite hactive
            rw [hafterrule] at hrule; simpa [child, eq_comm] using hrule
          let oldgap := if gap ≤ site then gap else gap - 1
          have holdpositive : 0 < oldgap := (by dsimp [oldgap]; split_ifs <;> omega)
          have holdbound : oldgap ≤ parent.length := (by dsimp [oldgap]; split_ifs <;> omega)
          have htransport : (if oldgap ≤ site then oldgap else oldgap + 1) = gap := by
            dsimp [oldgap]; split_ifs <;> omega
          have hrule := positive_C_inherited_sites n parent hparent site hsitepositive
            hsite hactive oldgap holdpositive holdbound
          rw [hinherited oldgap holdpositive holdbound, htransport] at hrule
          simpa only [child, hgapzero, false_or] using hrule
        refine ⟨one, by omega, by rw [hbefore one honecut, hone], Or.inr ?_⟩
        rcases hcase with ⟨hfirstmax, hshape⟩ | ⟨first, last, hfirstpos, hfirstlast,
          hlastbound, hfirstmax, _, hdecreasing, hshape⟩
        · have hsiteclass := (hshape site hsite).mp hactive
          have hsiteone : site = one + 1 := (by rcases hsiteclass with hz | ⟨heq, _⟩ <;> omega)
          refine ⟨site, site + 1, hsitepositive, by omega, by omega, hat, hchildadj, ?_, ?_⟩
          · intro earlier later he hl hb; omega
          · refine hchildshape (site + 1) ?_ ?_
            · constructor
              · intro _; rfl
              · intro _; exact ⟨0, hsitepositive, hfirstmax⟩
            · intro oldgap hp hb; rw [hshape oldgap hb]; constructor
              · rintro ⟨hclass, hge, hdec⟩; rcases hclass with hz | ⟨heq, _⟩
                · omega
                · left
                  have heqsite : oldgap = site := (by omega); simp only [heqsite, le_refl, if_true]
              · intro hclass; have heq : oldgap = site := (by split_ifs at hclass <;> omega)
                subst oldgap; refine ⟨(hshape site hsite).mp hactive, le_refl _, ?_⟩
                intro earlier later he hl hb; omega
        · have hsiteclass := (hshape site hsite).mp hactive
          have hcases : site = first ∨ site = last := by
            rcases hsiteclass with hz | hh
            · omega
            · exact hh
          have hmaxbefore : (∃ earlier < site, parent.getD earlier 0 = n) ↔ first < site := by
            constructor
            · rintro ⟨earlier, he, hv⟩
              have hi := (List.getD_inj (by omega) (by omega) hnodup).mp (hv.trans hfirstmax.symm)
              omega
            · intro he; exact ⟨first, he, hfirstmax⟩
          rcases hcases with hsitefirst | hsitelast
          · subst site
            refine ⟨first, last + 1, hfirstpos, by omega, by omega, hat, hchildadj, ?_, ?_⟩
            · intro earlier later he hl hb; by_cases heq : earlier = first
              · subst earlier; rw [hat, hafter later (by omega) (by omega)]
                exact hbound (later - 1) (by omega)
              · rw [hafter later (by omega) (by omega), hafter earlier (by omega) (by omega)]
                exact hdecreasing (earlier - 1) (later - 1) (by omega) (by omega) (by omega)
            · refine hchildshape (last + 1) ?_ ?_
              · rw [hmaxbefore]; omega
              · intro oldgap hp hb; rw [hshape oldgap hb]; constructor
                · rintro ⟨hclass, hge, hdec⟩; rcases hclass with hz | heq | heq
                  · omega
                  · subst oldgap; simp
                  · subst oldgap; simp only [show ¬ last ≤ first by omega, if_false, or_true]
                · intro hclass
                  have hc : oldgap = first ∨ oldgap = last := (by split_ifs at hclass <;> omega)
                  rcases hc with rfl | rfl
                  · refine ⟨Or.inr (Or.inl rfl), le_refl _, ?_⟩
                    intro earlier later he hl hb; omega
                  · exact ⟨Or.inr (Or.inr rfl), by omega, hdecreasing⟩
          · subst site
            refine ⟨last, last + 1, by omega, by omega, by omega, hat, hchildadj, ?_, ?_⟩
            · intro earlier later he hl hb; omega
            · refine hchildshape (last + 1) ?_ ?_
              · rw [hmaxbefore]; exact iff_of_true hfirstlast rfl
              · intro oldgap hp hb; rw [hshape oldgap hb]; constructor
                · rintro ⟨hclass, hge, hdec⟩
                  have heq : oldgap = last := (by rcases hclass with hz | heq | heq <;> omega)
                  subst oldgap; simp
                · intro hclass; have heq : oldgap = last := (by split_ifs at hclass <;> omega)
                  subst oldgap; refine ⟨Or.inr (Or.inr rfl), le_refl _, ?_⟩
                  intro earlier later he hl hb; omega

end D5.S3.Combinatorics.Fishburn.FishburnTenFourCInvariant
