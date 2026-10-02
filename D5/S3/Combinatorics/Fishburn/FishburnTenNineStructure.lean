/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenNineStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenNineStructure
   mirror-E: none(waiver:initial-run-and-exceptional-cut-induction)
   anchors: []
   utility: none
   digest: Each 2143 and 3124 Fishburn avoider has an initial run and at most one extra cut. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenNineSites
import D5.S3.Combinatorics.Fishburn.FishburnBasicPrefixes
import D5.S3.Combinatorics.Fishburn.FishburnBasicParents

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenNineStructure

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicParents
open FishburnBasicPrefixes FishburnTenNineSites

theorem active_sites_structure (size : ℕ) (p : List ℕ)
    (hmember : p ∈ avoiders size [[2, 1, 4, 3], [3, 1, 2, 4]]) :
    ∃ initial extra, initial ≤ extra ∧ extra ≤ size ∧
      p.take initial = List.range' 1 initial ∧
      (initial < size → p.getD initial 0 ≠ initial + 1) ∧
      (∀ gap, gap ≤ p.length →
        (p.insertIdx gap (size + 1) ∈ avoiders (size + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
          gap ≤ initial ∨ initial < extra ∧ gap = extra)) ∧
      (initial < extra → ∃ maximum, initial ≤ maximum ∧ maximum < extra ∧
        p.getD maximum 0 = size) := by
  induction size generalizing p with
  | zero =>
    have hp : p = [] := List.perm_nil.mp hmember.1
    subst p
    refine ⟨0, 0, le_rfl, le_rfl, rfl, by omega, ?_, by omega⟩
    intro gap hgap
    have hg : gap = 0 := by simpa using hgap
    subst gap
    simp only [List.insertIdx_zero, zero_add]
    constructor
    · intro _; exact Or.inl le_rfl
    · intro _
      refine ⟨by simp, ?_, ?_⟩
      · intro first last horder hlast; simp only [List.length_cons, List.length_nil] at hlast
        omega
      · intro pattern hpattern hocc
        have hp : pattern = [2, 1, 4, 3] ∨ pattern = [3, 1, 2, 4] := by
          simpa using hpattern
        obtain ⟨values, _, _, hsub, _⟩ := hocc
        have hl := hsub.length_le
        rcases hp with rfl | rfl <;> simp at hl
  | succ n ih =>
    by_cases hnzero : n = 0
    · subst n
      have hp : p = [1] := List.perm_singleton.mp hmember.1
      subst p
      refine ⟨1, 1, le_rfl, le_rfl, by simp, by omega, ?_, by omega⟩
      intro gap hgap
      have hc : gap = 0 ∨ gap = 1 := by
        simp only [List.length_cons, List.length_nil] at hgap
        omega
      constructor
      · intro _; exact Or.inl (by omega)
      · intro _
        rcases hc with rfl | rfl
        all_goals
          refine ⟨by decide, ?_, ?_⟩
          · intro first last horder hlast
            simp only [List.insertIdx_zero, List.insertIdx_succ_cons,
              List.length_cons, List.length_nil] at hlast
            omega
          · intro pattern hpattern hocc
            have hp : pattern = [2, 1, 4, 3] ∨ pattern = [3, 1, 2, 4] := by
              simpa using hpattern
            obtain ⟨values, _, _, hsub, _⟩ := hocc
            have hl := hsub.length_le
            rcases hp with rfl | rfl
            all_goals
              simp only [List.length_map, List.length_cons, List.length_nil,
                List.insertIdx_zero, List.insertIdx_succ_cons] at hl
              omega
    have hn : 1 ≤ n := by omega
    obtain ⟨entry, hentry⟩ :=
      (maximum_insertion_bijection n [[2, 1, 4, 3], [3, 1, 2, 4]]).2 ⟨p, hmember⟩
    have hp : entry.val.1.insertIdx entry.val.2 (n + 1) = p := congrArg Subtype.val hentry
    rcases entry with ⟨⟨parent, site⟩, hparent, hsite, hactive⟩
    dsimp only at hparent hsite hactive hp
    subst p
    obtain ⟨initial, extra, hie, hen, hprefix, hbreak, hcuts, hmaximum⟩ :=
      ih parent hparent
    let child := parent.insertIdx site (n + 1)
    have hlen : parent.length = n := by simpa using hparent.1.length_eq
    have hchildLen : child.length = n + 1 := by
      rw [List.length_insertIdx_of_le_length hsite, hlen]
    have hnodup : parent.Nodup := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
    have hvalue (index : ℕ) (hi : index < n) :
        1 ≤ parent.getD index 0 ∧ parent.getD index 0 ≤ n := by
      have hm : parent.getD index 0 ∈ parent := by
        rw [List.getD_eq_getElem parent 0 (by omega)]
        exact List.getElem_mem _
      have hr := hparent.1.mem_iff.mp hm
      simp only [List.mem_range'_1] at hr
      omega
    have hidentity (index : ℕ) (hi : index < initial) : parent.getD index 0 = index + 1 := by
      have heq := congrArg (fun word : List ℕ => word.getD index 0) hprefix
      rw [List.getD_eq_getElem (parent.take initial) 0 (by simp; omega),
        List.getElem_take, List.getD_eq_getElem (List.range' 1 initial) 0 (by simp; omega),
        List.getElem_range', ← List.getD_eq_getElem parent 0 (by omega)] at heq
      simpa [Nat.add_comm] using heq
    have hnext (hi : initial < n) : initial + 1 < parent.getD initial 0 := by
      have hb := hvalue initial hi
      have hgt : initial < parent.getD initial 0 := by
        by_contra hnot
        let index := parent.getD initial 0 - 1
        have hindex : index < initial := by dsimp [index]; omega
        have heq : parent.getD index 0 = parent.getD initial 0 := by
          rw [hidentity index hindex]
          dsimp [index]
          omega
        have hx := (List.getD_inj (by omega) (by omega) hnodup).mp heq
        omega
      have hne := hbreak hi
      omega
    have hbefore (index : ℕ) (hi : index < site) :
        child.getD index 0 = parent.getD index 0 := by
      rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
        List.getD_eq_getElem parent 0 (by omega)]
    have hat : child.getD site 0 = n + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]
      exact List.getElem_insertIdx_self _
    have hincreasing (gap : ℕ) (hg : gap ≤ n) :
        (parent.insertIdx gap (n + 1) ∈
          avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ∧
          ∀ first second, 0 ≤ first → first < second → second < gap →
            parent.getD first 0 < parent.getD second 0) ↔ gap ≤ initial := by
      constructor
      · rintro ⟨hgapActive, hinc⟩
        by_contra hnot
        have hgpos : 0 < gap := by omega
        have hincList : (parent.take gap).Pairwise (· < ·) := by
          apply List.pairwise_iff_getElem.mpr
          intro first second hf hs hfs
          have hs' : second < gap := by simp only [List.length_take, hlen] at hs; omega
          have hpinc := hinc first second (by omega) hfs hs'
          rw [List.getElem_take, List.getElem_take]
          rwa [List.getD_eq_getElem parent 0 (by omega : first < parent.length),
            List.getD_eq_getElem parent 0 (by omega : second < parent.length)] at hpinc
        have heligible := (FishburnBasicInsertion.isFishburn_insertIdx_max_iff
          parent (n + 1) gap (by omega) (by
            intro value hm
            have hr := hparent.1.mem_iff.mp hm
            simp only [List.mem_range'_1] at hr
            omega)).mp hgapActive.2.1 |>.2
        have heq := (eligible_prefix_structure n parent hparent.1 hparent.2.1
          gap (by omega) hgpos heligible).2 hincList
        have hi := congrArg (fun word : List ℕ => word.getD initial 0) heq
        rw [List.getD_eq_getElem (parent.take gap) 0 (by simp; omega),
          List.getElem_take, List.getD_eq_getElem (List.range' 1 gap) 0 (by simp; omega),
          List.getElem_range', ← List.getD_eq_getElem parent 0 (by omega)] at hi
        exact hbreak (by omega) (by simpa [Nat.add_comm] using hi)
      · intro hgi
        refine ⟨(hcuts gap (by omega)).mpr (Or.inl hgi), ?_⟩
        intro first second _ hfs hs
        rw [hidentity first (by omega), hidentity second (by omega)]
        omega
    let descending := fun gap => ∀ first second, site ≤ first → first < second →
      second < gap → parent.getD second 0 < parent.getD first 0
    have hinherited (gap : ℕ) (hg : gap ≤ n) :
        (child.insertIdx (if gap ≤ site then gap else gap + 1) (n + 2) ∈
          avoiders (n + 2) [[2, 1, 4, 3], [3, 1, 2, 4]]) ↔
        if gap ≤ site then gap ≤ initial else
          parent.insertIdx gap (n + 1) ∈
            avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ∧ descending gap := by
      rw [(active_site_evolution n parent hn hparent site gap hsite (by omega) hactive).1]
      by_cases hle : gap ≤ site
      · simp only [if_pos hle]
        exact hincreasing gap hg
      · simp only [if_neg hle]
        rfl
    have hnew := (active_site_evolution n parent hn hparent site 0 hsite
      (by omega) hactive).2
    change child.insertIdx (site + 1) (n + 2) ∈ _ ↔ _ at hnew
    have hclassify (nextInitial nextExtra : ℕ)
        (hnewRule : (∃ earlier < site, parent.getD earlier 0 = n) ↔
          site + 1 ≤ nextInitial ∨ nextInitial < nextExtra ∧ site + 1 = nextExtra)
        (hleft : ∀ gap, gap ≤ site →
          (gap ≤ initial ↔ gap ≤ nextInitial ∨ nextInitial < nextExtra ∧ gap = nextExtra))
        (hright : ∀ gap, site < gap → gap ≤ n →
          (parent.insertIdx gap (n + 1) ∈
            avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ∧ descending gap ↔
            gap + 1 ≤ nextInitial ∨ nextInitial < nextExtra ∧ gap + 1 = nextExtra)) :
        ∀ gap, gap ≤ child.length →
          (child.insertIdx gap (n + 2) ∈
            avoiders (n + 2) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
            gap ≤ nextInitial ∨ nextInitial < nextExtra ∧ gap = nextExtra) := by
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
    have hprefixChild (count : ℕ) (hc : count ≤ site) :
        child.take count = parent.take count := by
      apply List.ext_getElem
      · simp only [List.length_take, hchildLen, hlen]
        omega
      · intro index hi hj
        have hib : index < count := by simp only [List.length_take, hchildLen] at hi; omega
        rw [List.getElem_take, List.getElem_take, List.getElem_insertIdx_of_lt (by omega)]
    have hsiteCases : site ≤ initial ∨ initial < extra ∧ site = extra :=
      (hcuts site hsite).mp hactive
    change ∃ nextInitial nextExtra, nextInitial ≤ nextExtra ∧ nextExtra ≤ n + 1 ∧
      child.take nextInitial = List.range' 1 nextInitial ∧
      (nextInitial < n + 1 → child.getD nextInitial 0 ≠ nextInitial + 1) ∧
      (∀ gap, gap ≤ child.length → (child.insertIdx gap (n + 2) ∈
        avoiders (n + 2) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
        gap ≤ nextInitial ∨ nextInitial < nextExtra ∧ gap = nextExtra)) ∧
      (nextInitial < nextExtra → ∃ maximum, nextInitial ≤ maximum ∧
        maximum < nextExtra ∧ child.getD maximum 0 = n + 1)
    by_cases hsmall : site < initial
    · have hdescRule (gap : ℕ) (hg : gap ≤ n) :
          (parent.insertIdx gap (n + 1) ∈
            avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ∧ descending gap) ↔
          gap ≤ site + 1 := by
        constructor
        · rintro ⟨_, hdesc⟩
          by_contra hnot
          have hlt : parent.getD site 0 < parent.getD (site + 1) 0 := by
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
      have hnewRule : ¬ ∃ earlier < site, parent.getD earlier 0 = n := by
        rintro ⟨earlier, he, hv⟩
        rw [hidentity earlier (by omega)] at hv
        omega
      refine ⟨site, site + 2, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · rw [hprefixChild site le_rfl]
        have ht := congrArg (List.take site) hprefix
        simpa [List.take_take, Nat.min_eq_left (by omega : site ≤ initial),
          List.take_range'_of_length_ge (by omega : initial ≥ site)] using ht
      · intro _ heq
        rw [hat] at heq
        omega
      · refine hclassify site (site + 2) ?_ ?_ ?_
        · constructor
          · intro hh; exact (hnewRule hh).elim
          · intro hh; omega
        · intro gap hg; omega
        · intro gap hgt hg
          rw [hdescRule gap hg]
          omega
      · intro _
        exact ⟨site, le_rfl, by omega, hat⟩
    · have hsiteRemaining : site = initial ∨ initial < extra ∧ site = extra := by
        omega
      rcases hsiteRemaining with hsiteInitial | ⟨hieStrict, hsiteExtra⟩
      · subst site
        by_cases hid : initial = n
        · have hpIdentity : parent = List.range' 1 n := by
            simpa only [hid, List.take_of_length_le (by omega : parent.length ≤ n)]
              using hprefix
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
          refine ⟨n + 1, n + 1, le_rfl, le_rfl, ?_, by omega, ?_, by omega⟩
          · rw [hpChild]; simp
          · refine hclassify (n + 1) (n + 1) ?_ ?_ ?_
            · constructor
              · intro _; exact Or.inl (by omega)
              · intro _
                refine ⟨n - 1, by omega, ?_⟩
                rw [hidentity (n - 1) (by omega)]
                omega
            · intro gap hg; omega
            · intro gap hgt hg; omega
        · have hi : initial < n := by omega
          have hnewRule : ¬ ∃ earlier < initial, parent.getD earlier 0 = n := by
            rintro ⟨earlier, he, hv⟩
            rw [hidentity earlier he] at hv
            omega
          have hdescExtra (he : initial < extra) :
              descending extra ↔ parent.getD initial 0 = n := by
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
              have hne : parent.getD first 0 ≠ parent.getD second 0 := by
                intro heq
                have hx := (List.getD_inj (by omega) (by omega) hnodup).mp heq
                omega
              by_contra hnot
              have hrise : parent.getD first 0 < parent.getD second 0 := by omega
              have hfirstIndex : initial < first := by
                by_contra hnotIndex
                have heq : first = initial := by omega
                rw [heq, hfirst] at hrise
                omega
              have hsecondNe : parent.getD second 0 ≠ n := by
                intro heq
                have hx := (List.getD_inj (by omega) (by omega) hnodup).mp
                  (hfirst.trans heq.symm)
                omega
              have hactiveExtra := (hcuts extra (by omega)).mpr (Or.inr ⟨he, rfl⟩)
              apply hactiveExtra.2.2 [3, 1, 2, 4] (by simp)
              apply (FishburnBasicPatterns.maximum_pattern_tests n parent hparent.1
                extra (by omega)).2.1.mpr
              exact Or.inr ⟨initial, first, second, hfirstIndex, hfs, hb, hrise, by omega⟩
          by_cases hblock : initial < extra ∧ parent.getD initial 0 = n
          · refine ⟨initial, extra + 1, by omega, by omega, ?_, ?_, ?_, ?_⟩
            · rw [hprefixChild initial le_rfl]; exact hprefix
            · intro _ heq
              rw [hat] at heq
              omega
            · refine hclassify initial (extra + 1) ?_ ?_ ?_
              · constructor
                · intro hh; exact (hnewRule hh).elim
                · intro hh; omega
              · intro gap hg; omega
              · intro gap hgt hg
                rw [hcuts gap (by omega)]
                constructor
                · rintro ⟨hgap, hd⟩
                  rcases hgap with hgi | ⟨_, rfl⟩
                  · omega
                  · exact Or.inr ⟨by omega, rfl⟩
                · intro hh
                  have hge : gap = extra := by omega
                  subst gap
                  exact ⟨Or.inr ⟨hblock.1, rfl⟩, (hdescExtra hblock.1).mpr hblock.2⟩
            · intro _
              exact ⟨initial, le_rfl, by omega, hat⟩
          · refine ⟨initial, initial, le_rfl, by omega, ?_, ?_, ?_, by omega⟩
            · rw [hprefixChild initial le_rfl]; exact hprefix
            · intro _ heq
              rw [hat] at heq
              omega
            · refine hclassify initial initial ?_ ?_ ?_
              · constructor
                · intro hh; exact (hnewRule hh).elim
                · intro hh; omega
              · intro gap hg; omega
              · intro gap hgt hg
                rw [hcuts gap (by omega)]
                constructor
                · rintro ⟨hgap, hd⟩
                  rcases hgap with hgi | ⟨he, rfl⟩
                  · omega
                  · exact (hblock ⟨he, (hdescExtra he).mp hd⟩).elim
                · intro hh; omega
      · subst site
        have hnewRule : ∃ earlier < extra, parent.getD earlier 0 = n := by
          obtain ⟨maximum, _, hmhi, hmv⟩ := hmaximum hieStrict
          exact ⟨maximum, hmhi, hmv⟩
        refine ⟨initial, extra + 1, by omega, by omega, ?_, ?_, ?_, ?_⟩
        · rw [hprefixChild initial (by omega)]; exact hprefix
        · intro hi heq
          rw [hbefore initial hieStrict] at heq
          exact hbreak (by omega) heq
        · refine hclassify initial (extra + 1) ?_ ?_ ?_
          · constructor
            · intro _; exact Or.inr ⟨by omega, rfl⟩
            · intro _; exact hnewRule
          · intro gap hg; omega
          · intro gap hgt hg
            rw [hcuts gap (by omega)]
            constructor
            · rintro ⟨hc, _⟩; omega
            · intro hc; omega
        · intro _
          exact ⟨extra, by omega, by omega, hat⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenNineStructure
