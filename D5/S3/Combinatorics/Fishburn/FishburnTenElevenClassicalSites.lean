/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenElevenClassicalSites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenElevenClassicalSites
   mirror-E: none(waiver:classical-active-site-classification)
   anchors: []
   utility: none
   digest: The classical 123 and 3241 active cuts are determined by their decreasing prefixes. -/

import D5.S3.Combinatorics.Fishburn.FishburnClassicalDefs
import D5.S3.Combinatorics.Fishburn.FishburnBasicFourPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenElevenClassicalSites

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs FishburnBasicFourPatterns

theorem classical_active_sites (n : ℕ) (p : List ℕ)
    (hparent : p ∈ classicalAvoiders n [[1, 2, 3], [3, 2, 4, 1]])
    (site : ℕ) (hsite : site ≤ p.length) :
    p.insertIdx site (n + 1) ∈ classicalAvoiders (n + 1) [[1, 2, 3], [3, 2, 4, 1]] ↔
      site ≤ 1 ∨
      ((p.take site).Pairwise (· > ·) ∧
        ∀ later, site ≤ later → later < p.length → p.getD 1 0 < p.getD later 0) := by
  have hperm := hparent.1
  have h123 : ¬ NonnestingDefs.Occurs [1, 2, 3] p := hparent.2 _ (by simp)
  have h3241 : ¬ NonnestingDefs.Occurs [3, 2, 4, 1] p := hparent.2 _ (by simp)
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
  have hbound : ∀ value ∈ p, value ≤ n := by
    intro value hv
    have hr := hperm.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨offset, ho, he⟩ := hr
    omega
  have hentry (index : ℕ) (hi : index < p.length) : p.getD index 0 ≤ n := by
    rw [List.getD_eq_getElem p 0 hi]
    exact hbound _ (List.getElem_mem hi)
  let child := p.insertIdx site (n + 1)
  have hlength : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hsite _
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
  have hmaxpos (index : ℕ) (hb : index < child.length)
      (hv : child.getD index 0 = n + 1) : index = site := by
    rcases lt_trichotomy index site with hlt | heq | hgt
    · rw [hbefore index hlt] at hv
      have := hentry index (by omega)
      omega
    · exact heq
    · rw [hafter index hgt hb] at hv
      have := hentry (index - 1) (by omega)
      omega
  have hfilter : ∀ (word : List ℕ) (gap : ℕ), gap ≤ word.length →
      (∀ value ∈ word, value ≠ n + 1) →
      (word.insertIdx gap (n + 1)).filter (· != n + 1) = word := by
    intro word gap
    induction gap generalizing word with
    | zero =>
      intro _ hw
      simp only [List.insertIdx_zero, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte]
      apply List.filter_eq_self.mpr
      intro value hv
      simpa using hw value hv
    | succ gap ih =>
      cases word with
      | nil => simp
      | cons head tail =>
        intro hg hw
        have hhead := hw head (by simp)
        have htail : ∀ value ∈ tail, value ≠ n + 1 := by
          intro value hv
          exact hw value (by simp [hv])
        simpa [List.insertIdx_succ_cons, hhead] using
          congrArg (head :: ·) (ih tail (by simpa using hg) htail)
  have hfiltered : child.filter (· != n + 1) = p :=
    hfilter p site hsite (fun value hv => by have := hbound value hv; omega)
  have hselected : ∀ (positions : List ℕ), positions.Pairwise (· < ·) →
      (∀ index ∈ positions, index < child.length) →
      (positions.map (fun index => child.getD index 0)).Sublist child := by
    intro positions ho hb
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    let select : Fin (positions.map (fun index => child.getD index 0)).length →
        Fin child.length := fun index =>
      ⟨positions[index.val]'(by simpa using index.is_lt),
        hb _ (List.getElem_mem (by simpa using index.is_lt))⟩
    have hmono : StrictMono select := by
      intro first second hlt
      exact List.pairwise_iff_getElem.mp ho first.val second.val
        (by simpa using first.is_lt) (by simpa using second.is_lt) hlt
    refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
    intro index
    simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
    exact List.getD_eq_getElem child 0 _
  have hnew123 : NonnestingDefs.Occurs [1, 2, 3] child ↔
      ∃ first second, first < second ∧ second < site ∧
        p.getD first 0 < p.getD second 0 := by
    change ArrowWilfDefs.Contains [1, 2, 3] [] 3 child ↔ _
    constructor
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      by_cases htop : values 3 = n + 1
      · obtain ⟨positions, hp⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
        let first := positions ⟨0, by simp⟩
        let second := positions ⟨1, by simp⟩
        let third := positions ⟨2, by simp⟩
        have hfs : first.val < second.val :=
          positions.strictMono (by change (0 : ℕ) < 1; omega)
        have hst : second.val < third.val :=
          positions.strictMono (by change (1 : ℕ) < 2; omega)
        have hthird : child.getD third.val 0 = values 3 := by
          rw [List.getD_eq_get]
          simpa [third] using (hp ⟨2, by simp⟩).symm
        have hsiteat : third.val = site := hmaxpos third.val third.is_lt
          (hthird.trans htop)
        have hfirst : p.getD first.val 0 = values 1 := by
          rw [← hbefore first.val (by omega), List.getD_eq_get]
          simpa [first] using (hp ⟨0, by simp⟩).symm
        have hsecond : p.getD second.val 0 = values 2 := by
          rw [← hbefore second.val (by omega), List.getD_eq_get]
          simpa [second] using (hp ⟨1, by simp⟩).symm
        exact ⟨first.val, second.val, hfs, by omega, by omega⟩
      · have htopmem : values 3 ∈ p :=
          (List.eq_or_mem_of_mem_insertIdx (hmem 3 (by omega) (by omega))).resolve_left htop
        have htopbound := hbound _ htopmem
        have hsmall : ∀ rank, 1 ≤ rank → rank ≤ 3 → values rank ≠ n + 1 := by
          intro rank hl hh
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> omega
        apply False.elim
        apply h123
        refine ⟨values, hstep, ?_, ?_, by simp⟩
        · intro rank hl hh
          exact (List.eq_or_mem_of_mem_insertIdx (hmem rank hl hh)).resolve_left
            (hsmall rank hl hh)
        · have hs := hsub.filter (· != n + 1)
          rw [hfiltered] at hs
          have heq : ([1, 2, 3].map values).filter (· != n + 1) = [1, 2, 3].map values := by
            apply List.filter_eq_self.mpr
            intro value hv
            obtain ⟨rank, hr, rfl⟩ := List.mem_map.mp hv
            have hb : 1 ≤ rank ∧ rank ≤ 3 := by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              omega
            simpa using hsmall rank hb.1 hb.2
          rwa [heq] at hs
    · rintro ⟨first, second, hfs, hs, hlt⟩
      let values : ℕ → ℕ := fun rank => if rank = 1 then p.getD first 0
        else if rank = 2 then p.getD second 0 else n + 1
      have hsub := hselected [first, second, site]
        (by simp [List.pairwise_cons]; omega) (by
          intro index hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl <;> omega)
      rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil,
        hbefore first (by omega), hbefore second hs, hat] at hsub
      refine ⟨values, ?_, ?_, ?_, by simp⟩
      · intro rank hl hh
        have hc : rank = 1 ∨ rank = 2 := by omega
        have := hentry second (by omega)
        rcases hc with rfl | rfl <;>
          simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
      · intro rank hl hh
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases hc with rfl | rfl | rfl <;> apply hsub.subset <;> simp [values]
      · simpa only [List.map_cons, List.map_nil, values, ↓reduceIte,
          Nat.reduceEqDiff] using hsub
  have hdecreasing : (p.take site).Pairwise (· > ·) ↔
      ∀ first second, first < second → second < site →
        p.getD second 0 < p.getD first 0 := by
    rw [List.pairwise_iff_getElem]
    constructor
    · intro ho first second hfs hs
      have hp := ho first second (by simp only [List.length_take]; omega)
        (by simp only [List.length_take]; omega) hfs
      simpa only [List.getElem_take, List.getD_eq_getElem p 0 (by omega : first < p.length),
        List.getD_eq_getElem p 0 (by omega : second < p.length)] using hp
    · intro ho first second hf hs hfs
      have hsecond : second < site := by simp only [List.length_take] at hs; omega
      have hp := ho first second hfs hsecond
      rw [List.getD_eq_getElem p 0 (by omega), List.getD_eq_getElem p 0 (by omega)] at hp
      simpa only [List.getElem_take] using hp
  have htests := (maximum_four_pattern_tests n p hperm site hsite).2.2
  have hchildperm : child.Perm (List.range' 1 (n + 1)) := by
    apply (List.perm_insertIdx (n + 1) p hsite).trans
    apply (hperm.cons (n + 1)).trans
    rw [List.range'_concat]
    simpa [Nat.add_comm] using
      (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
  constructor
  · intro hc
    by_cases hsmall : site ≤ 1
    · exact Or.inl hsmall
    have hdec : ∀ first second, first < second → second < site →
        p.getD second 0 < p.getD first 0 := by
      intro first second hfs hs
      rcases lt_trichotomy (p.getD second 0) (p.getD first 0) with hlt | heq | hgt
      · exact hlt
      · have := (List.getD_inj (by omega) (by omega) hnodup).mp heq
        omega
      · exact False.elim (hc.2 _ (by simp) (hnew123.mpr ⟨first, second, hfs, hs, hgt⟩))
    refine Or.inr ⟨hdecreasing.mpr hdec, ?_⟩
    intro later hl hb
    rcases lt_trichotomy (p.getD 1 0) (p.getD later 0) with hlt | heq | hgt
    · exact hlt
    · have := (List.getD_inj (by omega) hb hnodup).mp heq
      omega
    · apply False.elim
      apply hc.2 [3, 2, 4, 1] (by simp)
      exact htests.mpr (Or.inr ⟨0, 1, later, by omega, by omega, hl, hb, hgt,
        hdec 0 1 (by omega) (by omega)⟩)
  · intro hcriterion
    refine ⟨hchildperm, ?_⟩
    intro pattern hp ho
    have hc : pattern = [1, 2, 3] ∨ pattern = [3, 2, 4, 1] := by simpa using hp
    rcases hc with rfl | rfl
    · obtain ⟨first, second, hfs, hs, hlt⟩ := hnew123.mp ho
      rcases hcriterion with hsmall | ⟨hdec, _⟩
      · omega
      · have := hdecreasing.mp hdec first second hfs hs
        omega
    · rcases htests.mp ho with hold | ⟨first, second, third, hfs, hs, ht, hb, hlo, _⟩
      · exact h3241 hold
      · rcases hcriterion with hsmall | ⟨hdec, htail⟩
        · omega
        · have hsecond : p.getD second 0 ≤ p.getD 1 0 := by
            by_cases heq : second = 1
            · subst second
              exact le_rfl
            · have := hdecreasing.mp hdec 1 second (by omega) hs
              omega
          have := htail third ht hb
          omega

end D5.S3.Combinatorics.Fishburn.FishburnTenElevenClassicalSites
