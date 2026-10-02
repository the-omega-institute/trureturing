/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTwelveSuccession
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTwelveSuccession
   mirror-E: none(waiver:ordered-four-state-generating-tree)
   anchors: []
   utility: none
   digest: Maximum insertion realizes the complete ordered four-state succession table. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTwelveStructure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTwelveSuccession

open D5.S3.Combinatorics FishburnDefs FishburnBasicPrefixes
open FishburnTenTwelveSites FishburnTenTwelveStructure

inductive Label
  | A | B | C | D
  deriving DecidableEq

noncomputable def label (n : ℕ) (p : List ℕ) (first extra : ℕ) : Label := by
  classical
  exact if first < extra then
    if ∀ earlier later, first ≤ earlier → earlier < later → later < extra →
        p.getD later 0 < p.getD earlier 0 then .C else .D
    else if ∃ maximum < first, p.getD maximum 0 = n then .A else .B

theorem full_succession (n : ℕ) (p : List ℕ) (hpositive : 1 ≤ n)
    (hparent : p ∈ avoiders n [[1, 2, 4, 3], [3, 1, 2, 4]])
    (first extra : ℕ) (hfirst : 0 < first) (hfe : first ≤ extra)
    (hextent : extra ≤ p.length) (hone : p.getD (first - 1) 0 = 1)
    (hcuts : ∀ gap, gap ≤ p.length →
      (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]] ↔
        gap = 0 ∨ gap = first ∨ first < extra ∧ gap = extra))
    (hmaximum : first < extra → ∃ maximum, first ≤ maximum ∧ maximum < extra ∧
      p.getD maximum 0 = n) :
    (∃ nextfirst nextextra, 0 < nextfirst ∧ nextfirst ≤ nextextra ∧
      nextextra ≤ (p.insertIdx 0 (n + 1)).length ∧
      (p.insertIdx 0 (n + 1)).getD (nextfirst - 1) 0 = 1 ∧
      (∀ gap, gap ≤ (p.insertIdx 0 (n + 1)).length →
        ((p.insertIdx 0 (n + 1)).insertIdx gap (n + 2) ∈
            avoiders (n + 2) [[1, 2, 4, 3], [3, 1, 2, 4]] ↔
          gap = 0 ∨ gap = nextfirst ∨ nextfirst < nextextra ∧ gap = nextextra)) ∧
      (nextfirst < nextextra → ∃ maximum, nextfirst ≤ maximum ∧ maximum < nextextra ∧
        (p.insertIdx 0 (n + 1)).getD maximum 0 = n + 1) ∧
      nextfirst = first + 1 ∧ nextextra = first + 1 ∧
      label (n + 1) (p.insertIdx 0 (n + 1)) nextfirst nextextra = .A) ∧
    (∃ nextfirst nextextra, 0 < nextfirst ∧ nextfirst ≤ nextextra ∧
      nextextra ≤ (p.insertIdx first (n + 1)).length ∧
      (p.insertIdx first (n + 1)).getD (nextfirst - 1) 0 = 1 ∧
      (∀ gap, gap ≤ (p.insertIdx first (n + 1)).length →
        ((p.insertIdx first (n + 1)).insertIdx gap (n + 2) ∈
            avoiders (n + 2) [[1, 2, 4, 3], [3, 1, 2, 4]] ↔
          gap = 0 ∨ gap = nextfirst ∨ nextfirst < nextextra ∧ gap = nextextra)) ∧
      (nextfirst < nextextra → ∃ maximum, nextfirst ≤ maximum ∧ maximum < nextextra ∧
        (p.insertIdx first (n + 1)).getD maximum 0 = n + 1) ∧
      nextfirst = first ∧
      label (n + 1) (p.insertIdx first (n + 1)) nextfirst nextextra =
        if label n p first extra = .A ∨ label n p first extra = .C then .C else .B) ∧
    (first < extra →
      ∃ nextfirst nextextra, 0 < nextfirst ∧ nextfirst ≤ nextextra ∧
        nextextra ≤ (p.insertIdx extra (n + 1)).length ∧
        (p.insertIdx extra (n + 1)).getD (nextfirst - 1) 0 = 1 ∧
        (∀ gap, gap ≤ (p.insertIdx extra (n + 1)).length →
          ((p.insertIdx extra (n + 1)).insertIdx gap (n + 2) ∈
              avoiders (n + 2) [[1, 2, 4, 3], [3, 1, 2, 4]] ↔
            gap = 0 ∨ gap = nextfirst ∨ nextfirst < nextextra ∧ gap = nextextra)) ∧
        (nextfirst < nextextra → ∃ maximum, nextfirst ≤ maximum ∧ maximum < nextextra ∧
          (p.insertIdx extra (n + 1)).getD maximum 0 = n + 1) ∧
        nextfirst = first ∧ nextextra = extra + 1 ∧
        label (n + 1) (p.insertIdx extra (n + 1)) nextfirst nextextra = .D) := by
  classical
  have hprefix := prefix_through_one_decreasing n p hparent.1 hparent.2.1
    (first - 1) (by omega) hone
  have hentry (index : ℕ) (hi : index < p.length) :
      1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hi]
      exact List.getElem_mem hi
    have hrange := hparent.1.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, hvalue⟩ := hrange
    omega
  have hnotprefix (hlt : first < extra) :
      ¬ ∀ earlier later, 0 ≤ earlier → earlier < later → later < extra →
        p.getD later 0 < p.getD earlier 0 := by
    intro hdec
    have hh := hdec (first - 1) first (by omega) (by omega) hlt
    have hbound := hentry first (by omega)
    rw [hone] at hh
    omega
  have hmaxright (hlt : first < extra) :
      ¬ ∃ maximum < first, p.getD maximum 0 = n := by
    rintro ⟨left, hleft, hvalue⟩
    obtain ⟨right, hright, hrange, hrightvalue⟩ := hmaximum hlt
    have hnodup : p.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
    have heq := (List.getD_inj (by omega) (by omega) hnodup).mp
      (hvalue.trans hrightvalue.symm)
    omega
  have hchilddata (site : ℕ) (hsite : site ≤ p.length)
      (hactive : p.insertIdx site (n + 1) ∈
        avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]]) :
      ∃ nextfirst nextextra, 0 < nextfirst ∧ nextfirst ≤ nextextra ∧
        nextextra ≤ (p.insertIdx site (n + 1)).length ∧
        (p.insertIdx site (n + 1)).getD (nextfirst - 1) 0 = 1 ∧
        (∀ gap, gap ≤ (p.insertIdx site (n + 1)).length →
          ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
              avoiders (n + 2) [[1, 2, 4, 3], [3, 1, 2, 4]] ↔
            gap = 0 ∨ gap = nextfirst ∨ nextfirst < nextextra ∧ gap = nextextra)) ∧
        (nextfirst < nextextra → ∃ maximum, nextfirst ≤ maximum ∧ maximum < nextextra ∧
          (p.insertIdx site (n + 1)).getD maximum 0 = n + 1) ∧
        (site = 0 → nextfirst = first + 1) ∧
        (first ≤ site → nextfirst = first) := by
    obtain ⟨nextfirst, nextextra, hnf, hnfe, hnb, hnone, hncut, hnmax⟩ :=
      four_state_structure (n + 1) (by omega) _ hactive
    have hnodup : (p.insertIdx site (n + 1)).Nodup :=
      hactive.1.nodup_iff.mpr (List.nodup_range' 1)
    have hlen := List.length_insertIdx_of_le_length hsite (n + 1)
    refine ⟨nextfirst, nextextra, hnf, hnfe, hnb, hnone, hncut, hnmax, ?_, ?_⟩
    · intro hzero
      subst site
      have hnext : (p.insertIdx 0 (n + 1)).getD first 0 = 1 := by
        rw [List.getD_eq_getElem _ 0 (by omega), List.getElem_insertIdx_of_gt hfirst,
          ← List.getD_eq_getElem p 0 (by omega)]
        exact hone
      have heq := (List.getD_inj (by omega) (by omega) hnodup).mp
        (hnone.trans hnext.symm)
      omega
    · intro hleft
      have hnext : (p.insertIdx site (n + 1)).getD (first - 1) 0 = 1 := by
        rw [List.getD_eq_getElem _ 0 (by omega),
          List.getElem_insertIdx_of_lt (by omega),
          ← List.getD_eq_getElem p 0 (by omega)]
        exact hone
      have heq := (List.getD_inj (by omega) (by omega) hnodup).mp
        (hnone.trans hnext.symm)
      omega
  constructor
  · have hactive := (hcuts 0 (by omega)).mpr (Or.inl rfl)
    obtain ⟨nextfirst, nextextra, hnf, hnfe, hnb, hnone, hncut, hnmax, hzero, _⟩ :=
      hchilddata 0 (by omega) hactive
    have hnfirst := hzero rfl
    subst nextfirst
    have hnextra : nextextra = first + 1 := by
      by_contra hne
      have hlt : first + 1 < nextextra := by omega
      have hactiveextra := (hncut nextextra hnb).mpr (Or.inr (Or.inr ⟨hlt, rfl⟩))
      have hlen := List.length_insertIdx_of_le_length (by omega : 0 ≤ p.length) (n + 1)
      have hgap : nextextra - 1 ≤ p.length := by omega
      have ht := (active_site_evolution n p hpositive hparent 0 (nextextra - 1)
        (by omega) hgap hactive).1
      have hinherited : (if nextextra - 1 ≤ 0 then nextextra - 1
        else nextextra - 1 + 1) = nextextra := by split_ifs <;> omega
      rw [hinherited] at ht
      obtain ⟨hold, hdec⟩ := ht.mp hactiveextra
      have hcases := (hcuts (nextextra - 1) hgap).mp hold
      rcases hcases with hzero | hfirsteq | ⟨hfe', heq⟩
      · omega
      · omega
      · subst extra
        exact hnotprefix (by omega) (by simpa only [ite_self] using hdec)
    subst nextextra
    refine ⟨first + 1, first + 1, hnf, hnfe, hnb, hnone, hncut, hnmax, rfl, rfl, ?_⟩
    have hmax : ∃ maximum < first + 1, (p.insertIdx 0 (n + 1)).getD maximum 0 =
        n + 1 := ⟨0, by omega, by simp⟩
    simp only [label, if_neg (lt_irrefl (first + 1)), if_pos hmax]
  constructor
  · have hsite : first ≤ p.length := by omega
    have hactive := (hcuts first hsite).mpr (Or.inr (Or.inl rfl))
    obtain ⟨nextfirst, nextextra, hnf, hnfe, hnb, hnone, hncut, hnmaxslice, _, hleft⟩ :=
      hchilddata first hsite hactive
    have hnfirst := hleft (by omega)
    subst nextfirst
    let child := p.insertIdx first (n + 1)
    have hlen : child.length = p.length + 1 :=
      List.length_insertIdx_of_le_length hsite (n + 1)
    have hrawlen : (p.insertIdx first (n + 1)).length = p.length + 1 := hlen
    have hat : child.getD first 0 = n + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]
      exact List.getElem_insertIdx_self _
    have hbefore (index : ℕ) (hi : index < first) :
        child.getD index 0 = p.getD index 0 := by
      rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
        List.getD_eq_getElem p 0 (by omega)]
    have hafter (index : ℕ) (hi : first < index) (hb : index < child.length) :
        child.getD index 0 = p.getD (index - 1) 0 := by
      rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hi,
        List.getD_eq_getElem p 0 (by omega)]
    have hnmax : ¬ ∃ maximum < first, child.getD maximum 0 = n + 1 := by
      rintro ⟨maximum, hm, hv⟩
      rw [hbefore maximum hm] at hv
      have hb := hentry maximum (by omega)
      omega
    have hnew := (active_site_evolution n p hpositive hparent first 0 hsite
      (by omega) hactive).2
    have hextracases : nextextra = first ∨ nextextra = first + 1 ∨
        first < extra ∧ nextextra = extra + 1 := by
      by_cases heq : nextextra = first
      · exact Or.inl heq
      by_cases hnewgap : nextextra = first + 1
      · exact Or.inr (Or.inl hnewgap)
      have hnactive := (hncut nextextra hnb).mpr
        (Or.inr (Or.inr ⟨by omega, rfl⟩))
      have hgap : nextextra - 1 ≤ p.length := by omega
      have ht := (active_site_evolution n p hpositive hparent first (nextextra - 1)
        hsite hgap hactive).1
      have hinherited : (if nextextra - 1 ≤ first then nextextra - 1
        else nextextra - 1 + 1) = nextextra := by split_ifs <;> omega
      rw [hinherited] at ht
      have hc := (hcuts (nextextra - 1) hgap).mp (ht.mp hnactive).1
      rcases hc with hz | hf | ⟨hlt, hb⟩
      · omega
      · omega
      · exact Or.inr (Or.inr ⟨hlt, by omega⟩)
    have hslice : first < extra →
        ((∀ earlier later, first ≤ earlier → earlier < later → later < extra →
          p.getD later 0 < p.getD earlier 0) ↔ nextextra = extra + 1) := by
      intro hlt
      have htest := (active_site_evolution n p hpositive hparent first extra hsite
        hextent hactive).1
      have hold := (hcuts extra hextent).mpr (Or.inr (Or.inr ⟨hlt, rfl⟩))
      simp only [if_neg (by omega : ¬ extra ≤ first), hold, true_and] at htest
      rw [hncut (extra + 1) (by omega)] at htest
      constructor
      · intro hdec
        have hh := htest.mpr hdec
        rcases hh with hz | hf | ⟨_, heq⟩ <;> omega
      · intro heq
        exact htest.mp (Or.inr (Or.inr ⟨by omega, heq.symm⟩))
    have hnewextra : (∃ maximum < first, p.getD maximum 0 = n) ↔
        nextextra = first + 1 := by
      rw [← hnew, hncut (first + 1) (by omega)]
      constructor
      · rintro (hz | hf | ⟨_, heq⟩) <;> omega
      · intro heq
        exact Or.inr (Or.inr ⟨by omega, heq.symm⟩)
    refine ⟨first, nextextra, hnf, hnfe, hnb, hnone, hncut, hnmaxslice, rfl, ?_⟩
    change label (n + 1) child first nextextra = _
    by_cases hlt : first < extra
    · have hmax := hmaxright hlt
      have hnnew : nextextra ≠ first + 1 := by
        intro heq
        exact hmax (hnewextra.mpr heq)
      by_cases hdec : ∀ earlier later, first ≤ earlier → earlier < later → later < extra →
          p.getD later 0 < p.getD earlier 0
      · have heq := (hslice hlt).mp hdec
        subst nextextra
        have hnchild : ∀ earlier later, first ≤ earlier → earlier < later →
            later < extra + 1 → child.getD later 0 < child.getD earlier 0 := by
          intro earlier later hearlier horder hlater
          by_cases heq : earlier = first
          · subst earlier
            rw [hat, hafter later (by omega) (by omega)]
            have hb := hentry (later - 1) (by omega)
            omega
          · rw [hafter earlier (by omega) (by omega),
              hafter later (by omega) (by omega)]
            exact hdec (earlier - 1) (later - 1) (by omega) (by omega) (by omega)
        simp only [label, if_pos hlt, if_pos hdec, if_pos hnchild,
          if_pos (by omega : first < extra + 1)]
        decide
      · have hnextra : nextextra = first := by
          rcases hextracases with heq | heq | ⟨_, heq⟩
          · exact heq
          · exact False.elim (hnnew heq)
          · exact False.elim (hdec ((hslice hlt).mpr heq))
        subst nextextra
        simp only [label, if_pos hlt, if_neg hdec, if_neg (lt_irrefl first), if_neg hnmax]
        decide
    · have heq : extra = first := by omega
      subst extra
      by_cases hmax : ∃ maximum < first, p.getD maximum 0 = n
      · have hnextra := hnewextra.mp hmax
        subst nextextra
        have hnchild : ∀ earlier later, first ≤ earlier → earlier < later →
            later < first + 1 → child.getD later 0 < child.getD earlier 0 := by
          intro earlier later hearlier horder hlater
          omega
        simp only [label, if_neg (lt_irrefl first), if_pos hmax, if_pos hnchild,
          if_pos (by omega : first < first + 1)]
        decide
      · have hnextra : nextextra = first := by
          rcases hextracases with heq | heq | ⟨hlt, _⟩
          · exact heq
          · exact False.elim (hmax (hnewextra.mpr heq))
          · omega
        subst nextextra
        simp only [label, if_neg (lt_irrefl first), if_neg hmax, if_neg hnmax]
        decide
  · intro hlt
    have hactive := (hcuts extra hextent).mpr (Or.inr (Or.inr ⟨hlt, rfl⟩))
    obtain ⟨nextfirst, nextextra, hnf, hnfe, hnb, hnone, hncut, hnmaxslice, _, hleft⟩ :=
      hchilddata extra hextent hactive
    have hnfirst := hleft hfe
    subst nextfirst
    have hlen := List.length_insertIdx_of_le_length hextent (n + 1)
    obtain ⟨maximum, hmfirst, hmextra, hmvalue⟩ := hmaximum hlt
    have hnew := (active_site_evolution n p hpositive hparent extra 0 hextent
      (by omega) hactive).2
    have hnewactive := hnew.mpr ⟨maximum, hmextra, hmvalue⟩
    have hextracases : extra + 1 = 0 ∨ extra + 1 = first ∨
        first < nextextra ∧ extra + 1 = nextextra :=
      (hncut (extra + 1) (by omega)).mp hnewactive
    have hnextra : nextextra = extra + 1 := by
      rcases hextracases with hz | hf | ⟨_, heq⟩ <;> omega
    subst nextextra
    refine ⟨first, extra + 1, hnf, hnfe, hnb, hnone, hncut, hnmaxslice, rfl, rfl, ?_⟩
    have hnchild : ¬ ∀ earlier later, first ≤ earlier → earlier < later →
        later < extra + 1 → (p.insertIdx extra (n + 1)).getD later 0 <
          (p.insertIdx extra (n + 1)).getD earlier 0 := by
      intro hdec
      have hh := hdec maximum extra hmfirst hmextra (by omega)
      have hat : (p.insertIdx extra (n + 1)).getD extra 0 = n + 1 := by
        rw [List.getD_eq_getElem _ 0 (by omega)]
        exact List.getElem_insertIdx_self _
      have hbefore : (p.insertIdx extra (n + 1)).getD maximum 0 = n := by
        rw [List.getD_eq_getElem _ 0 (by omega), List.getElem_insertIdx_of_lt hmextra,
          ← List.getD_eq_getElem p 0 (by omega)]
        exact hmvalue
      rw [hat, hbefore] at hh
      omega
    simp only [label, if_neg hnchild, if_pos (by omega : first < extra + 1)]

end D5.S3.Combinatorics.Fishburn.FishburnTenTwelveSuccession
