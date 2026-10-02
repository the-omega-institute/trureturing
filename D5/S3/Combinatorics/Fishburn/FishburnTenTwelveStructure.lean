/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTwelveStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTwelveStructure
   mirror-E: none(waiver:four-state-maximum-induction)
   anchors: []
   utility: none
   digest: Maximum deletion and exact site evolution classify every nonempty Fishburn avoider. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTwelveSites
import D5.S3.Combinatorics.Fishburn.FishburnBasicParents
import D5.S3.Combinatorics.Fishburn.FishburnBasicDecreasingPrefixes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTwelveStructure

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasic1243 FishburnBasicParents FishburnBasicPrefixes FishburnTenTwelveSites

theorem four_state_structure : ∀ n : ℕ, 1 ≤ n → ∀ p : List ℕ,
    p ∈ avoiders n [[1, 2, 4, 3], [3, 1, 2, 4]] →
    ∃ first extra, 0 < first ∧ first ≤ extra ∧ extra ≤ p.length ∧
      p.getD (first - 1) 0 = 1 ∧
      (∀ gap, gap ≤ p.length →
        (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 2, 4, 3], [3, 1, 2, 4]] ↔
          gap = 0 ∨ gap = first ∨ first < extra ∧ gap = extra)) ∧
      (first < extra → ∃ maximum, first ≤ maximum ∧ maximum < extra ∧
        p.getD maximum 0 = n) := by
  intro size
  induction size with
  | zero => intro hpositive; omega
  | succ n ih =>
    intro hn word hword
    by_cases hnzero : n = 0
    · subst n
      have hsingle : word = [1] := List.perm_singleton.mp hword.1
      subst word
      refine ⟨1, 1, by omega, by omega, by simp, by simp, ?_, ?_⟩
      · intro gap hgap
        have hc : gap = 0 ∨ gap = 1 := by
          simp only [List.length_cons, List.length_nil] at hgap
          omega
        constructor
        · intro _
          rcases hc with rfl | rfl <;> simp
        · intro _
          rcases hc with rfl | rfl
          all_goals
            refine ⟨by decide, ?_, ?_⟩
            · intro first later horder hbound
              simp only [List.insertIdx_zero, List.insertIdx_succ_cons,
                List.length_cons, List.length_nil] at hbound
              omega
            · intro pattern hpattern hocc
              have hp : pattern = [1, 2, 4, 3] ∨ pattern = [3, 1, 2, 4] := by
                simpa using hpattern
              rcases hp with rfl | rfl
              all_goals
                obtain ⟨values, _, _, hsub, _⟩ := hocc
                have hlen := hsub.length_le
                simp only [List.length_map, List.length_cons, List.length_nil,
                  List.insertIdx_zero, List.insertIdx_succ_cons] at hlen
                omega
      · intro hlt; omega
    have hpositive : 1 ≤ n := by omega
    obtain ⟨entry, hentry⟩ := (maximum_insertion_bijection n
      [[1, 2, 4, 3], [3, 1, 2, 4]]).2 ⟨word, hword⟩
    have heq : entry.val.1.insertIdx entry.val.2 (n + 1) = word :=
      congrArg Subtype.val hentry
    rcases entry with ⟨⟨parent, site⟩, hparent, hsite, hactive⟩
    dsimp only at hparent hsite hactive heq
    subst word
    obtain ⟨first, extra, hfirst, hfe, hextent, hone, hcuts, hmaximum⟩ :=
      ih hpositive parent hparent
    let child := parent.insertIdx site (n + 1)
    change ∃ first extra, 0 < first ∧ first ≤ extra ∧ extra ≤ child.length ∧
      child.getD (first - 1) 0 = 1 ∧
      (∀ gap, gap ≤ child.length →
        (child.insertIdx gap (n + 2) ∈ avoiders (n + 2) [[1, 2, 4, 3], [3, 1, 2, 4]] ↔
          gap = 0 ∨ gap = first ∨ first < extra ∧ gap = extra)) ∧
      (first < extra → ∃ maximum, first ≤ maximum ∧ maximum < extra ∧
        child.getD maximum 0 = n + 1)
    let inherited := fun gap : ℕ => if gap ≤ site then gap else gap + 1
    let decreasing := fun gap : ℕ => ∀ earlier later,
      (if gap ≤ site then 0 else site) ≤ earlier → earlier < later → later < gap →
        parent.getD later 0 < parent.getD earlier 0
    have hlength : child.length = parent.length + 1 :=
      List.length_insertIdx_of_le_length hsite (n + 1)
    have hsitecases : site = 0 ∨ site = first ∨ first < extra ∧ site = extra :=
      (hcuts site hsite).mp hactive
    have hprefix := prefix_through_one_decreasing n parent hparent.1 hparent.2.1
      (first - 1) (by omega) hone
    have hdecfirst : decreasing first := by
      intro earlier later _ horder hb
      exact hprefix earlier later horder (by omega)
    have hdeczero : decreasing 0 := by intro earlier later _ _ hb; omega
    have hnotprefix (hlt : first < extra) :
        ¬ ∀ earlier later, 0 ≤ earlier → earlier < later → later < extra →
          parent.getD later 0 < parent.getD earlier 0 := by
      intro hdec
      have hh := hdec (first - 1) first (by omega) (by omega) hlt
      rw [hone] at hh
      have hmem : parent.getD first 0 ∈ parent := by
        rw [List.getD_eq_getElem parent 0 (by omega)]
        exact List.getElem_mem (by omega)
      have hrange := hparent.1.mem_iff.mp hmem
      simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, hoffset, hvalue⟩ := hrange
      omega
    have hbefore (index : ℕ) (hi : index < site) :
        child.getD index 0 = parent.getD index 0 := by
      rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
        List.getD_eq_getElem parent 0 (by omega)]
    have hat : child.getD site 0 = n + 1 := by
      rw [List.getD_eq_getElem child 0 (by omega)]
      exact List.getElem_insertIdx_self _
    have hafter (index : ℕ) (hi : site < index) (hb : index < child.length) :
        child.getD index 0 = parent.getD (index - 1) 0 := by
      rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hi,
        List.getD_eq_getElem parent 0 (by omega)]
    have hnewgap := (active_site_evolution n parent hpositive hparent site 0
      hsite (by omega) hactive).2
    change child.insertIdx (site + 1) (n + 2) ∈ _ ↔ _ at hnewgap
    have hclassification (nextfirst nextextra : ℕ)
        (hnew : (∃ earlier < site, parent.getD earlier 0 = n) ↔
          site + 1 = 0 ∨ site + 1 = nextfirst ∨
            nextfirst < nextextra ∧ site + 1 = nextextra)
        (hold : ∀ gap, gap ≤ parent.length →
          ((gap = 0 ∨ gap = first ∨ first < extra ∧ gap = extra) ∧ decreasing gap ↔
            inherited gap = 0 ∨ inherited gap = nextfirst ∨
              nextfirst < nextextra ∧ inherited gap = nextextra)) :
        ∀ gap, gap ≤ child.length →
          (child.insertIdx gap (n + 2) ∈
              avoiders (n + 2) [[1, 2, 4, 3], [3, 1, 2, 4]] ↔
            gap = 0 ∨ gap = nextfirst ∨ nextfirst < nextextra ∧ gap = nextextra) := by
      intro gap hb
      by_cases hgap : gap = site + 1
      · subst gap
        exact hnewgap.trans hnew
      · let oldgap := if gap ≤ site then gap else gap - 1
        have holdbound : oldgap ≤ parent.length := by
          dsimp [oldgap]; split_ifs <;> omega
        have hinherited : inherited oldgap = gap := by
          dsimp [inherited, oldgap]; split_ifs <;> omega
        have ht := (active_site_evolution n parent hpositive hparent site oldgap
          hsite holdbound hactive).1
        change child.insertIdx (inherited oldgap) (n + 2) ∈ _ ↔
          parent.insertIdx oldgap (n + 1) ∈ _ ∧ decreasing oldgap at ht
        rw [hinherited, hcuts oldgap holdbound] at ht
        have hh := hold oldgap holdbound
        rw [hinherited] at hh
        exact ht.trans hh
    have htest (nextfirst nextextra : ℕ)
        (hzero : (inherited 0 = 0 ∨ inherited 0 = nextfirst ∨
          nextfirst < nextextra ∧ inherited 0 = nextextra))
        (hfirstcut : (inherited first = 0 ∨ inherited first = nextfirst ∨
          nextfirst < nextextra ∧ inherited first = nextextra))
        (hextracut : first < extra →
          (decreasing extra ↔ inherited extra = 0 ∨ inherited extra = nextfirst ∨
            nextfirst < nextextra ∧ inherited extra = nextextra))
        (hback : ∀ gap, gap ≤ parent.length →
          (inherited gap = 0 ∨ inherited gap = nextfirst ∨
            nextfirst < nextextra ∧ inherited gap = nextextra) →
          gap = 0 ∨ gap = first ∨ first < extra ∧ gap = extra) :
        ∀ gap, gap ≤ parent.length →
          ((gap = 0 ∨ gap = first ∨ first < extra ∧ gap = extra) ∧ decreasing gap ↔
            inherited gap = 0 ∨ inherited gap = nextfirst ∨
              nextfirst < nextextra ∧ inherited gap = nextextra) := by
      intro gap hb
      constructor
      · rintro ⟨hlabel, hdec⟩
        rcases hlabel with rfl | rfl | ⟨hlt, rfl⟩
        · exact hzero
        · exact hfirstcut
        · exact (hextracut hlt).mp hdec
      · intro hlabel
        have holdlabel := hback gap hb hlabel
        refine ⟨holdlabel, ?_⟩
        rcases holdlabel with rfl | rfl | ⟨hlt, rfl⟩
        · exact hdeczero
        · exact hdecfirst
        · exact (hextracut hlt).mpr hlabel
    rcases hsitecases with hzero | hfirstsite | ⟨hextra, hextrasite⟩
    · subst site
      have honechild : child.getD first 0 = 1 := by
        rw [hafter first (by omega) (by omega)]
        exact hone
      refine ⟨first + 1, first + 1, by omega, by omega, by omega, ?_, ?_, ?_⟩
      · simpa using honechild
      · apply hclassification (first + 1) (first + 1)
        · constructor
          · rintro ⟨earlier, he, _⟩; omega
          · intro hh; omega
        · apply htest (first + 1) (first + 1)
          · simp [inherited]
          · exact Or.inr (Or.inl (by
              simp only [inherited, if_neg (by omega : ¬ first ≤ 0)]))
          · intro hlt
            have hd : ¬ decreasing extra := by
              simpa only [decreasing, if_neg (by omega : ¬ extra ≤ 0)] using hnotprefix hlt
            simp only [hd, inherited, if_neg (by omega : ¬ extra ≤ 0), false_iff,
              lt_self_iff_false, false_and, or_false]
            omega
          · intro gap _ hh
            dsimp [inherited] at hh
            rcases hh with hh | hh | ⟨horder, hh⟩
            all_goals (try split_ifs at hh) <;> omega
      · intro hh; omega
    · subst site
      by_cases hextra : first < extra
      · by_cases hdec : decreasing extra
        · refine ⟨first, extra + 1, hfirst, by omega, by omega, ?_, ?_, ?_⟩
          · rw [hbefore (first - 1) (by omega)]
            exact hone
          · apply hclassification first (extra + 1)
            · constructor
              · rintro ⟨earlier, he, hv⟩
                obtain ⟨maximum, hmfirst, hmextra, hmvalue⟩ := hmaximum hextra
                have hnodup : parent.Nodup :=
                  hparent.1.nodup_iff.mpr (List.nodup_range' 1)
                have hi := (List.getD_inj (by omega) (by omega) hnodup).mp
                  (hv.trans hmvalue.symm)
                omega
              · intro hh; omega
            · apply htest first (extra + 1)
              · exact Or.inl (by simp [inherited])
              · exact Or.inr (Or.inl (by simp [inherited]))
              · intro _
                simp only [hdec, inherited, if_neg (by omega : ¬ extra ≤ first),
                  true_iff]
                exact Or.inr (Or.inr ⟨by omega, trivial⟩)
              · intro gap _ hh
                dsimp [inherited] at hh
                rcases hh with hh | hh | ⟨horder, hh⟩
                all_goals (try split_ifs at hh) <;> omega
          · intro _
            exact ⟨first, by omega, by omega, hat⟩
        · refine ⟨first, first, hfirst, by omega, by omega, ?_, ?_, ?_⟩
          · rw [hbefore (first - 1) (by omega)]
            exact hone
          · apply hclassification first first
            · constructor
              · rintro ⟨earlier, he, hv⟩
                obtain ⟨maximum, hmfirst, hmextra, hmvalue⟩ := hmaximum hextra
                have hnodup : parent.Nodup :=
                  hparent.1.nodup_iff.mpr (List.nodup_range' 1)
                have hi := (List.getD_inj (by omega) (by omega) hnodup).mp
                  (hv.trans hmvalue.symm)
                omega
              · intro hh; omega
            · apply htest first first
              · exact Or.inl (by simp [inherited])
              · exact Or.inr (Or.inl (by simp [inherited]))
              · intro _
                simp only [hdec, inherited, if_neg (by omega : ¬ extra ≤ first),
                  false_iff, lt_self_iff_false, false_and, or_false]
                omega
              · intro gap _ hh
                dsimp [inherited] at hh
                rcases hh with hh | hh | ⟨horder, hh⟩
                all_goals (try split_ifs at hh) <;> omega
          · intro hh; omega
      · have hextraeq : extra = first := by omega
        subst extra
        by_cases hmaxleft : ∃ earlier < first, parent.getD earlier 0 = n
        · refine ⟨first, first + 1, hfirst, by omega, by omega, ?_, ?_, ?_⟩
          · rw [hbefore (first - 1) (by omega)]
            exact hone
          · apply hclassification first (first + 1)
            · constructor
              · intro _; exact Or.inr (Or.inr ⟨by omega, rfl⟩)
              · intro _; exact hmaxleft
            · apply htest first (first + 1)
              · exact Or.inl (by simp [inherited])
              · exact Or.inr (Or.inl (by simp [inherited]))
              · intro hh; omega
              · intro gap _ hh
                dsimp [inherited] at hh
                rcases hh with hh | hh | ⟨horder, hh⟩
                all_goals (try split_ifs at hh) <;> omega
          · intro _
            exact ⟨first, by omega, by omega, hat⟩
        · refine ⟨first, first, hfirst, by omega, by omega, ?_, ?_, ?_⟩
          · rw [hbefore (first - 1) (by omega)]
            exact hone
          · apply hclassification first first
            · simp only [hmaxleft, lt_self_iff_false, false_and, or_false, false_iff]
              omega
            · apply htest first first
              · exact Or.inl (by simp [inherited])
              · exact Or.inr (Or.inl (by simp [inherited]))
              · intro hh; omega
              · intro gap _ hh
                dsimp [inherited] at hh
                rcases hh with hh | hh | ⟨horder, hh⟩
                all_goals (try split_ifs at hh) <;> omega
          · intro hh; omega
    · subst site
      refine ⟨first, extra + 1, hfirst, by omega, by omega, ?_, ?_, ?_⟩
      · rw [hbefore (first - 1) (by omega)]
        exact hone
      · apply hclassification first (extra + 1)
        · have hmaxleft : ∃ earlier < extra, parent.getD earlier 0 = n := by
            obtain ⟨maximum, _, hmextra, hmvalue⟩ := hmaximum hextra
            exact ⟨maximum, hmextra, hmvalue⟩
          constructor
          · intro _; exact Or.inr (Or.inr ⟨by omega, rfl⟩)
          · intro _; exact hmaxleft
        · apply htest first (extra + 1)
          · exact Or.inl (by simp [inherited])
          · exact Or.inr (Or.inl (by simp [inherited, show first ≤ extra by omega]))
          · intro hlt
            have hd : ¬ decreasing extra := by
              simpa only [decreasing, if_pos (by omega : extra ≤ extra)] using hnotprefix hlt
            simp only [hd, inherited, if_pos (by omega : extra ≤ extra), false_iff]
            omega
          · intro gap _ hh
            dsimp [inherited] at hh
            rcases hh with hh | hh | ⟨horder, hh⟩
            all_goals (try split_ifs at hh) <;> omega
      · intro _
        exact ⟨extra, by omega, by omega, hat⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenTwelveStructure
