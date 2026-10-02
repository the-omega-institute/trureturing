/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenElevenSites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenElevenSites
   mirror-E: none(waiver:fishburn-active-site-classification)
   anchors: []
   utility: none
   digest: The Fishburn 1243 and 2134 class has left, after-one and eligible end sites. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicFourPatterns
import D5.S3.Combinatorics.Fishburn.FishburnBasicSmallValues
import D5.S3.Combinatorics.Fishburn.FishburnBasicDecreasingPrefixes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenElevenSites

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicFourPatterns FishburnBasicSmallValues FishburnBasicPrefixes

theorem fishburn_active_sites (n : ℕ) (p : List ℕ)
    (hparent : p ∈ avoiders n [[1, 2, 4, 3], [2, 1, 3, 4]])
    (site : ℕ) (hsite : site ≤ p.length) :
    p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[1, 2, 4, 3], [2, 1, 3, 4]] ↔
      site = 0 ∨
      (∃ one, one < p.length ∧ p.getD one 0 = 1 ∧ site = one + 1) ∨
      (site = p.length ∧ ¬ NonnestingDefs.Occurs [2, 1, 3] p) := by
  have hperm := hparent.1
  have hfish := hparent.2.1
  have h124 : ¬ NonnestingDefs.Occurs [1, 2, 4, 3] p := hparent.2.2 _ (by simp)
  have h2134 : ¬ NonnestingDefs.Occurs [2, 1, 3, 4] p := hparent.2.2 _ (by simp)
  have hlength : p.length = n := by simpa using hperm.length_eq
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hvalues (index : ℕ) (hi : index < p.length) :
      1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hi]
      exact List.getElem_mem hi
    have hr := hperm.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, ho, hv⟩ := hr
    omega
  have hmax : ∀ value ∈ p, value < n + 1 := by
    intro value hv
    have hr := hperm.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, ho, he⟩ := hr
    omega
  have hchildperm : (p.insertIdx site (n + 1)).Perm (List.range' 1 (n + 1)) := by
    apply (List.perm_insertIdx (n + 1) p hsite).trans
    apply (hperm.cons (n + 1)).trans
    rw [List.range'_concat]
    simpa [Nat.add_comm] using
      (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
  have htake (index : ℕ) (hi : index < site) :
      (p.take site).getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem _ 0 (by simp only [List.length_take]; omega),
      List.getElem_take, List.getD_eq_getElem p 0 (by omega)]
  have hselected : ∀ (positions : List ℕ), positions.Pairwise (· < ·) →
      (∀ index ∈ positions, index < site) →
      (positions.map (fun index => p.getD index 0)).Sublist (p.take site) := by
    intro positions ho hb
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    let select : Fin (positions.map (fun index => p.getD index 0)).length →
        Fin (p.take site).length := fun index =>
      ⟨positions[index.val]'(by simpa using index.is_lt),
        by have := hb _ (List.getElem_mem (by simpa using index.is_lt))
           simp only [List.length_take]; omega⟩
    have hmono : StrictMono select := by
      intro first second hlt
      exact List.pairwise_iff_getElem.mp ho first.val second.val
        (by simpa using first.is_lt) (by simpa using second.is_lt) hlt
    refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
    intro index
    simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono,
      List.getElem_take]
    exact List.getD_eq_getElem p 0 _
  have h213 : NonnestingDefs.Occurs [2, 1, 3] (p.take site) ↔
      ∃ first second third, first < second ∧ second < third ∧ third < site ∧
        p.getD second 0 < p.getD first 0 ∧ p.getD first 0 < p.getD third 0 := by
    change ArrowWilfDefs.Contains [2, 1, 3] [] 3 (p.take site) ↔ _
    constructor
    · rintro ⟨values, hstep, _, hsub, _⟩
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      obtain ⟨positions, hp⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let first := positions ⟨0, by simp⟩
      let second := positions ⟨1, by simp⟩
      let third := positions ⟨2, by simp⟩
      have hf : first.val < site := by have := first.is_lt; simp only [List.length_take]
                                                      at this; omega
      have hs : second.val < site := by have := second.is_lt; simp only [List.length_take]
                                                        at this; omega
      have ht : third.val < site := by have := third.is_lt; simp only [List.length_take]
                                                      at this; omega
      have hfirst : p.getD first.val 0 = values 2 := by
        rw [← htake first.val hf, List.getD_eq_get]
        simpa [first] using (hp ⟨0, by simp⟩).symm
      have hsecond : p.getD second.val 0 = values 1 := by
        rw [← htake second.val hs, List.getD_eq_get]
        simpa [second] using (hp ⟨1, by simp⟩).symm
      have hthird : p.getD third.val 0 = values 3 := by
        rw [← htake third.val ht, List.getD_eq_get]
        simpa [third] using (hp ⟨2, by simp⟩).symm
      refine ⟨first.val, second.val, third.val, ?_, ?_, ht, by omega, by omega⟩
      · exact positions.strictMono (by change (0 : ℕ) < 1; omega)
      · exact positions.strictMono (by change (1 : ℕ) < 2; omega)
    · rintro ⟨first, second, third, hfs, hst, ht, hlo, hhi⟩
      let values : ℕ → ℕ := fun rank => if rank = 1 then p.getD second 0
        else if rank = 2 then p.getD first 0 else p.getD third 0
      have hs := hselected [first, second, third]
        (by simp [List.pairwise_cons]; omega) (by
          intro index hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> omega)
      simp only [List.map_cons, List.map_nil] at hs
      refine ⟨values, ?_, ?_, ?_, by simp⟩
      · intro rank hl hh
        have hc : rank = 1 ∨ rank = 2 := by omega
        rcases hc with rfl | rfl <;>
          simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
      · intro rank hl hh
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hc with rfl | rfl | rfl <;> apply hs.subset <;> simp [values]
      · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
          Nat.reduceEqDiff] using hs
  have htests := maximum_four_pattern_tests n p hperm site hsite
  have hcriteria :
      p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[1, 2, 4, 3], [2, 1, 3, 4]] ↔
      (∀ before later, before + 1 = site → site ≤ later → later < p.length →
        p.getD before 0 ≠ p.getD later 0 + 1) ∧
      (¬ ∃ first second third, first < second ∧ second < site ∧ site ≤ third ∧
        third < p.length ∧ p.getD first 0 < p.getD second 0 ∧
        p.getD second 0 < p.getD third 0) ∧
      ¬ NonnestingDefs.Occurs [2, 1, 3] (p.take site) := by
    constructor
    · intro hc
      refine ⟨((isFishburn_insertIdx_max_iff p (n + 1) site hsite hmax).mp hc.2.1).2,
        ?_, ?_⟩
      · intro hw
        exact hc.2.2 _ (by simp) (htests.1.mpr (Or.inr hw))
      · intro hw
        exact hc.2.2 _ (by simp) (htests.2.1.mpr (Or.inr (h213.mp hw)))
    · rintro ⟨heligible, hcross, hprefix⟩
      refine ⟨hchildperm,
        (isFishburn_insertIdx_max_iff p (n + 1) site hsite hmax).mpr ⟨hfish, heligible⟩,
        ?_⟩
      intro pattern hp ho
      have hc : pattern = [1, 2, 4, 3] ∨ pattern = [2, 1, 3, 4] := by simpa using hp
      rcases hc with rfl | rfl
      · exact (htests.1.mp ho).elim h124 hcross
      · exact (htests.2.1.mp ho).elim h2134 (fun hw => hprefix (h213.mpr hw))
  rw [hcriteria]
  constructor
  · rintro ⟨heligible, hcross, hprefix⟩
    by_cases hzero : site = 0
    · exact Or.inl hzero
    have hlast : site - 1 < p.length := by omega
    by_cases hone : p.getD (site - 1) 0 = 1
    · exact Or.inr (Or.inl ⟨site - 1, hlast, hone, by omega⟩)
    by_cases hend : site = p.length
    · exact Or.inr (Or.inr ⟨hend, by simpa [hend] using hprefix⟩)
    have hpred : ∀ earlier, earlier < p.length →
        p.getD earlier 0 + 1 = p.getD (site - 1) 0 → earlier < site - 1 := by
      intro earlier hearlier hv
      by_contra hnot
      by_cases heq : earlier = site - 1
      · subst earlier
        omega
      exact heligible (site - 1) earlier (by omega) (by omega) hearlier hv.symm
    have hsmall := small_value_chain n p hperm hfish (site - 1) hlast
      (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ site)] using hprefix) hpred
    have hsuffix : p.getD (site - 1) 0 < p.getD site 0 := by
      by_contra hnot
      have := hsmall.1 site (by omega) (by omega)
      omega
    have honemem : 1 ∈ p := by
      apply hperm.mem_iff.mpr
      simp only [List.mem_range', Nat.one_mul]
      exact ⟨0, by omega, by omega⟩
    obtain ⟨one, hob, hov⟩ := List.mem_iff_getElem.mp honemem
    have ho : p.getD one 0 = 1 := by rw [List.getD_eq_getElem p 0 hob, hov]
    have hbottom := (hvalues (site - 1) hlast).1
    have hbefore := hsmall.2 one (site - 1) hob hlast (by omega) le_rfl
    exact False.elim (hcross ⟨one, site - 1, site, hbefore, by omega,
      le_rfl, by omega, by omega, hsuffix⟩)
  · rintro (hzero | ⟨one, hob, ho, hsiteone⟩ | ⟨hend, havoid⟩)
    · subst site
      refine ⟨?_, ?_, ?_⟩
      · intro before later hb
        omega
      · rintro ⟨first, second, third, _, hs, _⟩
        omega
      · intro hw
        obtain ⟨first, second, third, _, _, ht, _⟩ := h213.mp hw
        omega
    · have hdec := prefix_through_one_decreasing n p hperm hfish one hob ho
      refine ⟨?_, ?_, ?_⟩
      · intro before later hb hl hlen heq
        have hbefore : before = one := by omega
        rw [hbefore, ho] at heq
        have := (hvalues later hlen).1
        omega
      · rintro ⟨first, second, third, hfs, hs, _, _, hlt, _⟩
        have := hdec first second hfs (by omega)
        omega
      · intro hw
        obtain ⟨first, second, third, hfs, hst, ht, _, hlt⟩ := h213.mp hw
        have := hdec first third (by omega) (by omega)
        omega
    · refine ⟨?_, ?_, by simpa [hend] using havoid⟩
      · intro before later _ hl hb
        omega
      · rintro ⟨first, second, third, _, _, ht, hb, _⟩
        omega

end D5.S3.Combinatorics.Fishburn.FishburnTenElevenSites
