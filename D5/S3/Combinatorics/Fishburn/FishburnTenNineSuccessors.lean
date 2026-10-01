/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenNineSuccessors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenNineSuccessors
   mirror-E: none(waiver:labelled-maximum-insertion-rules)
   anchors: []
   utility: none
   digest: Maximum insertion determines all four labelled active-site successor rules. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenNineStructure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenNineSuccessors

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicPrefixes FishburnTenNineSites

theorem labelled_successors (n initial extra site nextInitial nextExtra : ℕ) (p : List ℕ)
    (hparent : p ∈ avoiders n [[2, 1, 4, 3], [3, 1, 2, 4]])
    (hie : initial ≤ extra) (hen : extra ≤ n)
    (hprefix : p.take initial = List.range' 1 initial)
    (hbreak : initial < n → p.getD initial 0 ≠ initial + 1)
    (hcuts : ∀ gap, gap ≤ p.length →
      (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
        gap ≤ initial ∨ initial < extra ∧ gap = extra))
    (hmaximum : initial < extra → ∃ maximum, initial ≤ maximum ∧ maximum < extra ∧
      p.getD maximum 0 = n)
    (hsite : site ≤ p.length)
    (hactive : p.insertIdx site (n + 1) ∈
      avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]])
    (hnie : nextInitial ≤ nextExtra) (hnen : nextExtra ≤ n + 1)
    (hnextPrefix : (p.insertIdx site (n + 1)).take nextInitial =
      List.range' 1 nextInitial)
    (hnextBreak : nextInitial < n + 1 →
      (p.insertIdx site (n + 1)).getD nextInitial 0 ≠ nextInitial + 1)
    (hnextCuts : ∀ gap, gap ≤ (p.insertIdx site (n + 1)).length →
      ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
        avoiders (n + 2) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
          gap ≤ nextInitial ∨ nextInitial < nextExtra ∧ gap = nextExtra)) :
    nextInitial = (if site < initial then site else
      if initial = n then n + 1 else initial) ∧
    nextExtra = (if site < initial then site + 2 else
      if initial = n then n + 1 else
      if initial < extra ∧ (site = extra ∨ p.getD initial 0 = n)
        then extra + 1 else initial) ∧
    (nextInitial < nextExtra →
      ((p.insertIdx site (n + 1)).getD nextInitial 0 = n + 1 ↔ site ≤ initial)) := by
  let child := p.insertIdx site (n + 1)
  have hlen : p.length = n := by simpa using hparent.1.length_eq
  have hchildLen : child.length = n + 1 := by
    rw [List.length_insertIdx_of_le_length hsite, hlen]
  have hrawLen : (p.insertIdx site (n + 1)).length = n + 1 := hchildLen
  have hnodup : p.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
  have hvalue (index : ℕ) (hi : index < n) :
      1 ≤ p.getD index 0 ∧ p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 (by omega)]
      exact List.getElem_mem _
    have hr := hparent.1.mem_iff.mp hm
    simp only [List.mem_range'_1] at hr
    omega
  have hidentity (index : ℕ) (hi : index < initial) : p.getD index 0 = index + 1 := by
    have heq := congrArg (fun word : List ℕ => word.getD index 0) hprefix
    rw [List.getD_eq_getElem (p.take initial) 0 (by simp; omega), List.getElem_take,
      List.getD_eq_getElem (List.range' 1 initial) 0 (by simp; omega),
      List.getElem_range', ← List.getD_eq_getElem p 0 (by omega)] at heq
    simpa [Nat.add_comm] using heq
  have hnext (hi : initial < n) : initial + 1 < p.getD initial 0 := by
    have hb := hvalue initial hi
    have hgt : initial < p.getD initial 0 := by
      by_contra hnot
      let index := p.getD initial 0 - 1
      have hindex : index < initial := by dsimp [index]; omega
      have heq : p.getD index 0 = p.getD initial 0 := by
        rw [hidentity index hindex]
        dsimp [index]
        omega
      have hx := (List.getD_inj (by omega) (by omega) hnodup).mp heq
      omega
    have hne := hbreak hi
    omega
  have hbefore (index : ℕ) (hi : index < site) :
      child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD site 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  have hinitialUnique (count : ℕ) (hc : count ≤ n + 1)
      (hp : child.take count = List.range' 1 count)
      (hb : count < n + 1 → child.getD count 0 ≠ count + 1) : nextInitial = count := by
    have hentry (bound index : ℕ) (hbound : bound ≤ n + 1)
        (hpref : child.take bound = List.range' 1 bound) (hi : index < bound) :
        child.getD index 0 = index + 1 := by
      have heq := congrArg (fun word : List ℕ => word.getD index 0) hpref
      rw [List.getD_eq_getElem (child.take bound) 0 (by simp; omega),
        List.getElem_take, List.getD_eq_getElem (List.range' 1 bound) 0 (by simp; omega),
        List.getElem_range', ← List.getD_eq_getElem child 0 (by omega)] at heq
      simpa [Nat.add_comm] using heq
    rcases lt_trichotomy nextInitial count with hlt | heq | hgt
    · exact (hnextBreak (by omega) (hentry count nextInitial hc hp hlt)).elim
    · exact heq
    · exact (hb (by omega) (hentry nextInitial count (by omega) hnextPrefix hgt)).elim
  have hextraUnique (count : ℕ) (hc : nextInitial ≤ count) (hb : count ≤ n + 1)
      (hclass : ∀ gap, gap ≤ child.length →
        (child.insertIdx gap (n + 2) ∈
          avoiders (n + 2) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
            gap ≤ nextInitial ∨ nextInitial < count ∧ gap = count)) : nextExtra = count := by
    by_cases heq : count = nextInitial
    · have htest := (hclass nextExtra (by omega)).mp
        ((hnextCuts nextExtra (by omega)).mpr (by omega))
      omega
    · have htest := (hnextCuts count (by omega)).mp
        ((hclass count (by omega)).mpr (by omega))
      omega
  have hprefixChild (count : ℕ) (hc : count ≤ site) :
      child.take count = p.take count := List.take_insertIdx_eq_take_of_le _ _ _ _ hc
  have hsiteCases := (hcuts site hsite).mp hactive
  by_cases hnzero : n = 0
  · have hi : initial = 0 := by omega
    have he : extra = 0 := by omega
    have hs : site = 0 := by omega
    have hp : p = [] := List.perm_nil.mp (by simpa [hnzero] using hparent.1)
    subst n initial extra site p
    have hni : nextInitial = 1 := hinitialUnique 1 (by omega) (by simp [child]) (by omega)
    have hne : nextExtra = 1 := by omega
    simp [hni, hne]
  have hn : 1 ≤ n := by omega
  have hincreasing (gap : ℕ) (hg : gap ≤ n) :
      (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ∧
        ∀ first second, 0 ≤ first → first < second → second < gap →
          p.getD first 0 < p.getD second 0) ↔ gap ≤ initial := by
    constructor
    · rintro ⟨hgapActive, hinc⟩
      by_contra hnot
      have hincList : (p.take gap).Pairwise (· < ·) := by
        apply List.pairwise_iff_getElem.mpr
        intro first second hf hs hfs
        simp only [List.length_take, hlen] at hf hs
        have hpinc := hinc first second (by omega) hfs
          (by omega)
        rw [List.getElem_take, List.getElem_take]
        rwa [List.getD_eq_getElem p 0 (by omega : first < p.length),
          List.getD_eq_getElem p 0 (by omega : second < p.length)] at hpinc
      have heligible := (FishburnBasicInsertion.isFishburn_insertIdx_max_iff
        p (n + 1) gap (by omega) (by
          intro value hm
          have hr := hparent.1.mem_iff.mp hm
          simp only [List.mem_range'_1] at hr
          omega)).mp hgapActive.2.1 |>.2
      have heq := (eligible_prefix_structure n p hparent.1 hparent.2.1
        gap (by omega) (by omega) heligible).2 hincList
      have hi := congrArg (fun word : List ℕ => word.getD initial 0) heq
      rw [List.getD_eq_getElem (p.take gap) 0 (by simp; omega), List.getElem_take,
        List.getD_eq_getElem (List.range' 1 gap) 0 (by simp; omega),
        List.getElem_range', ← List.getD_eq_getElem p 0 (by omega)] at hi
      exact hbreak (by omega) (by simpa [Nat.add_comm] using hi)
    · intro hgi
      refine ⟨(hcuts gap (by omega)).mpr (Or.inl hgi), ?_⟩
      intro first second _ hfs hs
      rw [hidentity first (by omega), hidentity second (by omega)]
      omega
  let descending := fun gap => ∀ first second, site ≤ first → first < second →
    second < gap → p.getD second 0 < p.getD first 0
  have hinherited (gap : ℕ) (hg : gap ≤ n) :
      (child.insertIdx (if gap ≤ site then gap else gap + 1) (n + 2) ∈
        avoiders (n + 2) [[2, 1, 4, 3], [3, 1, 2, 4]]) ↔
      if gap ≤ site then gap ≤ initial else
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ∧
          descending gap := by
    rw [(active_site_evolution n p hn hparent site gap hsite (by omega) hactive).1]
    by_cases hle : gap ≤ site
    · simp only [if_pos hle]
      exact hincreasing gap hg
    · simp only [if_neg hle]
      rfl
  have hnew := (active_site_evolution n p hn hparent site 0 hsite
    (by omega) hactive).2
  have hclassify (count : ℕ)
      (hnewRule : (∃ earlier < site, p.getD earlier 0 = n) ↔
        site + 1 ≤ nextInitial ∨ nextInitial < count ∧ site + 1 = count)
      (hleft : ∀ gap, gap ≤ site →
        (gap ≤ initial ↔ gap ≤ nextInitial ∨ nextInitial < count ∧ gap = count))
      (hright : ∀ gap, site < gap → gap ≤ n →
        (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ∧
          descending gap ↔
            gap + 1 ≤ nextInitial ∨ nextInitial < count ∧ gap + 1 = count)) :
      ∀ gap, gap ≤ child.length →
        (child.insertIdx gap (n + 2) ∈
          avoiders (n + 2) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
            gap ≤ nextInitial ∨ nextInitial < count ∧ gap = count) := by
    intro gap hg
    by_cases hle : gap ≤ site
    · have hh := hinherited gap (by omega)
      simp only [if_pos hle] at hh
      exact hh.trans (hleft gap hle)
    by_cases heq : gap = site + 1
    · subst gap
      exact hnew.trans hnewRule
    · have hgt : site < gap - 1 := by omega
      have hh := hinherited (gap - 1) (by omega)
      simp only [if_neg (by omega : ¬ gap - 1 ≤ site),
        Nat.sub_add_cancel (by omega : 1 ≤ gap)] at hh
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ gap)] using
        hh.trans (hright (gap - 1) hgt (by omega))
  by_cases hsmall : site < initial
  · have hni : nextInitial = site := by
      apply hinitialUnique site (by omega)
      · rw [hprefixChild site le_rfl]
        have ht := congrArg (List.take site) hprefix
        simpa [List.take_take, Nat.min_eq_left (by omega : site ≤ initial),
          List.take_range'_of_length_ge (by omega : initial ≥ site)] using ht
      · intro _ heq
        rw [hat] at heq
        omega
    have hdescRule (gap : ℕ) (hg : gap ≤ n) :
        (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ∧
          descending gap) ↔ gap ≤ site + 1 := by
      constructor
      · rintro ⟨_, hdesc⟩
        by_contra hnot
        have hlt : p.getD site 0 < p.getD (site + 1) 0 := by
          rw [hidentity site hsmall]
          by_cases hsi : site + 1 < initial
          · rw [hidentity (site + 1) hsi]; omega
          · have heq : site + 1 = initial := by omega
            rw [heq]
            have hnv := hnext (by omega)
            omega
        have hd := hdesc site (site + 1) le_rfl (by omega) (by omega)
        omega
      · intro hgapSmall
        refine ⟨(hcuts gap (by omega)).mpr (Or.inl (by omega)), ?_⟩
        intro first second hs hfs hb
        omega
    have hnewFalse : ¬ ∃ earlier < site, p.getD earlier 0 = n := by
      rintro ⟨earlier, he, hv⟩
      rw [hidentity earlier (by omega)] at hv
      omega
    have hne : nextExtra = site + 2 := by
      apply hextraUnique (site + 2) (by omega) (by omega)
      refine hclassify (site + 2) ?_ ?_ ?_
      · rw [hni]
        constructor
        · intro hh; exact (hnewFalse hh).elim
        · intro hh; omega
      · intro gap hg; rw [hni]; omega
      · intro gap hgt hg
        rw [hdescRule gap hg, hni]
        omega
    refine ⟨by simp [hsmall, hni], by simp [hsmall, hne], ?_⟩
    intro _
    rw [hni]
    exact ⟨fun _ => by omega, fun _ => hat⟩
  have hremaining : site = initial ∨ initial < extra ∧ site = extra := by
    rcases hsiteCases with hs | hh
    · exact Or.inl (Nat.le_antisymm hs (Nat.le_of_not_gt hsmall))
    · exact Or.inr hh
  rcases hremaining with hsInitial | ⟨hieStrict, hsExtra⟩
  · subst site
    by_cases hid : initial = n
    · have hpIdentity : p = List.range' 1 n := by
        simpa only [hid, List.take_of_length_le (by omega : p.length ≤ n)] using hprefix
      have hpChild : child = List.range' 1 (n + 1) := by
        dsimp [child]
        rw [hid, hpIdentity]
        have hinsert : (List.range' 1 n).insertIdx n (n + 1) =
            List.range' 1 n ++ [n + 1] := by
          simpa only [List.length_range'] using
            (List.insertIdx_length_self (l := List.range' 1 n) (x := n + 1))
        rw [hinsert]
        simpa [Nat.add_comm] using
          (List.range'_concat (s := 1) (n := n) (step := 1)).symm
      have hni : nextInitial = n + 1 :=
        hinitialUnique (n + 1) le_rfl (by rw [hpChild]; simp) (by omega)
      have hne : nextExtra = n + 1 := by omega
      simp [hni, hne, hid]
    have hi : initial < n := by omega
    have hni : nextInitial = initial := by
      apply hinitialUnique initial (by omega)
      · rw [hprefixChild initial le_rfl]; exact hprefix
      · intro _ heq
        rw [hat] at heq
        omega
    have hnewFalse : ¬ ∃ earlier < initial, p.getD earlier 0 = n := by
      rintro ⟨earlier, he, hv⟩
      rw [hidentity earlier he] at hv
      omega
    have hdescExtra (he : initial < extra) : descending extra ↔ p.getD initial 0 = n := by
      constructor
      · intro hd
        obtain ⟨maximum, hmlo, hmhi, hmv⟩ := hmaximum he
        by_cases hm : maximum = initial
        · simpa [hm] using hmv
        · have hh := hd initial maximum le_rfl (by omega) hmhi
          have hb := hvalue initial hi
          omega
      · intro hfirst first second hlo hfs hb
        have hfirstBound := hvalue first (by omega)
        have hsecondBound := hvalue second (by omega)
        have hne : p.getD first 0 ≠ p.getD second 0 := by
          intro heq
          have hx := (List.getD_inj (by omega) (by omega) hnodup).mp heq
          omega
        by_contra hnot
        have hrise : p.getD first 0 < p.getD second 0 := by omega
        have hfirstIndex : initial < first := by
          by_contra hnotIndex
          have heq : first = initial := by omega
          rw [heq, hfirst] at hrise
          omega
        have hsecondNe : p.getD second 0 ≠ n := by
          intro heq
          have hx := (List.getD_inj (by omega) (by omega) hnodup).mp
            (hfirst.trans heq.symm)
          omega
        have hactiveExtra := (hcuts extra (by omega)).mpr (Or.inr ⟨he, rfl⟩)
        apply hactiveExtra.2.2 [3, 1, 2, 4] (by simp)
        apply (FishburnBasicPatterns.maximum_pattern_tests n p hparent.1
          extra (by omega)).2.1.mpr
        exact Or.inr ⟨initial, first, second, hfirstIndex, hfs, hb, hrise, by omega⟩
    by_cases hblock : initial < extra ∧ p.getD initial 0 = n
    · have hne : nextExtra = extra + 1 := by
        apply hextraUnique (extra + 1) (by omega) (by omega)
        refine hclassify (extra + 1) ?_ ?_ ?_
        · rw [hni]
          constructor
          · intro hh; exact (hnewFalse hh).elim
          · intro hh; omega
        · intro gap hg; rw [hni]; omega
        · intro gap hgt hg
          rw [hcuts gap (by omega), hni]
          constructor
          · rintro ⟨hgap, _⟩
            rcases hgap with hgi | ⟨_, rfl⟩ <;> omega
          · intro hh
            have hge : gap = extra := by omega
            subst gap
            exact ⟨Or.inr ⟨hblock.1, rfl⟩, (hdescExtra hblock.1).mpr hblock.2⟩
      refine ⟨by simp [hni, hid], ?_, ?_⟩
      · have hc : initial < extra ∧ (initial = extra ∨ p.getD initial 0 = n) :=
          ⟨hblock.1, Or.inr hblock.2⟩
        simpa only [if_neg (Nat.lt_irrefl initial), if_neg hid, if_pos hc] using hne
      · intro _
        rw [hni]
        exact ⟨fun _ => le_rfl, fun _ => hat⟩
    · have hne : nextExtra = initial := by
        apply hextraUnique initial (by omega) (by omega)
        refine hclassify initial ?_ ?_ ?_
        · rw [hni]
          constructor
          · intro hh; exact (hnewFalse hh).elim
          · intro hh; omega
        · intro gap hg; rw [hni]; omega
        · intro gap hgt hg
          rw [hcuts gap (by omega), hni]
          constructor
          · rintro ⟨hgap, hd⟩
            rcases hgap with hgi | ⟨he, rfl⟩
            · omega
            · exact (hblock ⟨he, (hdescExtra he).mp hd⟩).elim
          · intro hh; omega
      have hcond : ¬ (initial < extra ∧
          (initial = extra ∨ p.getD initial 0 = n)) := by
        rintro ⟨he, heq | hv⟩
        · omega
        · exact hblock ⟨he, hv⟩
      refine ⟨by simp [hni, hid], ?_, ?_⟩
      · simpa only [if_neg (Nat.lt_irrefl initial), if_neg hid, if_neg hcond] using hne
      · intro hh
        omega
  · subst site
    have hni : nextInitial = initial := by
      apply hinitialUnique initial (by omega)
      · rw [hprefixChild initial (by omega)]; exact hprefix
      · intro _ heq
        rw [hbefore initial hieStrict] at heq
        exact hbreak (by omega) heq
    have hnewTrue : ∃ earlier < extra, p.getD earlier 0 = n := by
      obtain ⟨maximum, _, hmhi, hmv⟩ := hmaximum hieStrict
      exact ⟨maximum, hmhi, hmv⟩
    have hne : nextExtra = extra + 1 := by
      apply hextraUnique (extra + 1) (by omega) (by omega)
      refine hclassify (extra + 1) ?_ ?_ ?_
      · rw [hni]
        exact ⟨fun _ => by omega, fun _ => hnewTrue⟩
      · intro gap hg; rw [hni]; omega
      · intro gap hgt hg
        rw [hcuts gap (by omega), hni]
        constructor
        · rintro ⟨hc, _⟩; omega
        · intro hc; omega
    refine ⟨by simp [hni, hsmall, show initial ≠ n by omega], ?_, ?_⟩
    · simp [hne, hsmall, hieStrict, show initial ≠ n by omega]
    · intro _
      rw [hni, hbefore initial hieStrict]
      have hb := hvalue initial (by omega)
      omega

end D5.S3.Combinatorics.Fishburn.FishburnTenNineSuccessors
