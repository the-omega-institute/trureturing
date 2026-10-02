/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenCCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenCCount
   mirror-E: none(waiver:classical-c-descendant-counting)
   anchors: [mathlib/module/Mathlib.Data.List.Lemmas, mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: An invertible partition by the first child counts all C permutations at every size. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenCTree
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenCCount

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs
open FishburnBasicClassicalParents FishburnTenTenCTransitions FishburnTenTenCTree

set_option maxHeartbeats 2400000 in
theorem c_enumeration (size : ℕ) :
    (classicalAvoiders size [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]]).ncard =
      if size = 0 then 1 else size + 2 * size.choose 3 := by
  classical
  let family := fun n => classicalAvoiders n [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]]
  let weight := fun (height n : ℕ) (label : CType n) =>
    match label with
    | .increasing => if height = 0 then 1
        else n * (1 + 2 * height.choose 2) + height + 2 * height.choose 3
    | .persistent _ => if height = 0 then 1 else 2 * height
    | .delayed _ => if height = 0 then 1 else 2
    | .terminal _ => 1
  have hfinite (n : ℕ) : (family n).Finite := by
    apply (List.finite_toSet (List.range' 1 n).permutations).subset
    intro word hw
    exact List.mem_permutations.mpr hw.1
  letI (n : ℕ) : Finite (family n) := (hfinite n).to_subtype
  have hfilterSelf (n : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 n)) :
      word.filter (fun value => value ≤ n) = word := by
    apply List.filter_eq_self.mpr
    intro value hm
    have hr := hp.mem_iff.mp hm
    simp only [List.mem_range'_1] at hr
    simpa using (show value ≤ n by omega)
  have hfilterTwice (n : ℕ) (word : List ℕ) :
      (word.filter (fun value => value ≤ n + 1)).filter (fun value => value ≤ n) =
        word.filter (fun value => value ≤ n) := by
    rw [List.filter_filter]
    congr 1
    funext value
    by_cases hv : value ≤ n
    · simp [hv, show value ≤ n + 1 by omega]
    · simp [hv]
  have hfilterInsert (bound : ℕ) (word : List ℕ) (site value : ℕ)
      (hs : site ≤ word.length) (hv : bound < value) :
      (word.insertIdx site value).filter (fun entry => entry ≤ bound) =
        word.filter (fun entry => entry ≤ bound) := by
    induction word generalizing site with
    | nil =>
      have hz : site = 0 := by simpa using hs
      subst site
      simp [show ¬ value ≤ bound by omega]
    | cons head tail ih =>
      cases site with
      | zero => simp [show ¬ value ≤ bound by omega]
      | succ site =>
        simp only [List.insertIdx_succ_cons, List.filter_cons]
        rw [ih site (by simp only [List.length_cons] at hs; omega)]
  have hinitial (n : ℕ) (word : List ℕ) (hm : word ∈ family n)
      (cut : ℕ) (hc : cut ≤ n) :
      word.filter (fun value => value ≤ cut) ∈ family cut := by
    induction n generalizing word cut with
    | zero =>
      have hz : cut = 0 := by omega
      have hw : word = [] := List.perm_nil.mp hm.1
      simpa only [hw, hz, List.filter_nil] using hm
    | succ n ih =>
      by_cases heq : cut = n + 1
      · subst cut
        simpa only [hfilterSelf (n + 1) word hm.1] using hm
      · obtain ⟨entry, heq⟩ := (classical_maximum_insertion_bijection n
          [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]]).2 ⟨word, hm⟩
        have hw : entry.val.1.insertIdx entry.val.2 (n + 1) = word :=
          congrArg Subtype.val heq
        rw [← hw, hfilterInsert cut entry.val.1 entry.val.2 (n + 1)
          entry.property.2.1 (by omega)]
        exact ih entry.val.1 entry.property.1 cut (by omega)
  have hinc (n : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 n))
      (hprefix : ∀ first second, first < second → second < n →
        word.getD first 0 < word.getD second 0) : word = List.range' 1 n := by
    have hlen : word.length = n := by simpa using hp.length_eq
    have hsorted : word.Pairwise (· < ·) := by
      apply List.pairwise_iff_getElem.mpr
      intro first second hf hs hfs
      have hh := hprefix first second hfs (by omega)
      simpa only [List.getD_eq_getElem word 0 hf, List.getD_eq_getElem word 0 hs] using hh
    exact hp.eq_of_pairwise (by intro first second hfs hsf; omega)
      hsorted List.pairwise_lt_range'
  have hdescendants (height n : ℕ) (p : List ℕ) (hm : p ∈ family n)
      (label : CType n) (hspec : CSpec n p label) :
      Nat.card {q : family (n + height) // q.val.filter (fun value => value ≤ n) = p} =
        weight height n label := by
    induction height generalizing n p label with
    | zero =>
      have hcard : Nat.card {q : family n // q.val.filter (fun value => value ≤ n) = p} =
          1 := by
        apply Nat.card_eq_one_iff_exists.mpr
        refine ⟨⟨⟨p, hm⟩, hfilterSelf n p hm.1⟩, ?_⟩
        intro q
        apply Subtype.ext
        apply Subtype.ext
        have hq := q.property
        rw [hfilterSelf n q.val.val q.val.property.1] at hq
        exact hq
      cases label <;> simpa [weight] using hcard
    | succ height ih =>
      have hlen : p.length = n := by simpa using hm.1.length_eq
      let degree : ℕ := match label with
        | .increasing => n + 1
        | .persistent _ => 2
        | .delayed _ => 2
        | .terminal _ => 1
      let Choices := Fin degree
      let site : Choices → ℕ := fun ordinal => match label with
        | .increasing => ordinal.val
        | .persistent cut => if ordinal.val = 0 then cut.val else n
        | .delayed cut => if ordinal.val = 0 then cut.val else n - 1
        | .terminal cut => cut.val
      let child : Choices → List ℕ := fun ordinal => p.insertIdx (site ordinal) (n + 1)
      have hsite (ordinal : Choices) : site ordinal ≤ p.length := by
        have hb := ordinal.is_lt
        cases label with
        | increasing => dsimp [site, Choices, degree] at *; omega
        | persistent cut =>
          have hc := cut.is_lt
          dsimp [site]; split_ifs <;> omega
        | delayed cut =>
          have hc := cut.is_lt
          dsimp [site]; split_ifs <;> omega
        | terminal cut =>
          have hc := cut.is_lt
          dsimp [site]; omega
      have hchild (ordinal : Choices) : child ordinal ∈ family (n + 1) := by
        cases label with
        | increasing => exact hspec.2 (site ordinal) (by have := hsite ordinal; omega)
        | persistent cut =>
          apply (hspec.2.2 (site ordinal) (by have := hsite ordinal; omega)).mpr
          dsimp [site]; split_ifs <;> simp
        | delayed cut =>
          apply (hspec.2 (site ordinal) (by have := hsite ordinal; omega)).mpr
          dsimp [site]; split_ifs <;> simp
        | terminal cut =>
          apply (hspec (site ordinal) (by have := hsite ordinal; omega)).mpr
          rfl
      have hsiteInjective : Function.Injective site := by
        intro first second heq
        apply Fin.ext
        have hf := first.is_lt
        have hs := second.is_lt
        cases label with
        | increasing => exact heq
        | persistent cut =>
          have hc := cut.is_lt
          dsimp [Choices, degree] at hf hs
          dsimp [site] at heq
          split_ifs at heq <;> omega
        | delayed cut =>
          have hc := cut.is_lt
          dsimp [Choices, degree] at hf hs
          dsimp [site] at heq
          split_ifs at heq <;> omega
        | terminal cut => dsimp [Choices, degree] at hf hs; omega
      have hcoverage (gap : ℕ) (hg : gap ≤ p.length)
          (ha : p.insertIdx gap (n + 1) ∈ family (n + 1)) :
          ∃ ordinal : Choices, site ordinal = gap := by
        cases label with
        | increasing => exact ⟨⟨gap, by dsimp [Choices, degree]; omega⟩, rfl⟩
        | persistent cut =>
          rcases (hspec.2.2 gap (by omega)).mp ha with heq | heq
          · exact ⟨⟨0, by simp [Choices, degree]⟩, by simp [site, heq]⟩
          · exact ⟨⟨1, by simp [Choices, degree]⟩, by simp [site, heq]⟩
        | delayed cut =>
          rcases (hspec.2 gap (by omega)).mp ha with heq | heq
          · exact ⟨⟨0, by simp [Choices, degree]⟩, by simp [site, heq]⟩
          · exact ⟨⟨1, by simp [Choices, degree]⟩, by simp [site, heq]⟩
        | terminal cut =>
          have heq := (hspec gap (by omega)).mp ha
          exact ⟨⟨0, by simp [Choices, degree]⟩, by simp [site, heq]⟩
      let Branches := Σ ordinal : Choices,
        {q : family (n + 1 + height) //
          q.val.filter (fun value => value ≤ n + 1) = child ordinal}
      let Future := {q : family (n + 1 + height) //
        q.val.filter (fun value => value ≤ n) = p}
      let assemble : Branches → Future := fun entry => ⟨entry.2.val, by
        rw [← hfilterTwice n, entry.2.property]
        dsimp [child]
        rw [hfilterInsert n p (site entry.1) (n + 1) (hsite entry.1) (by omega),
          hfilterSelf n p hm.1]⟩
      have hbijective : Function.Bijective assemble := by
        constructor
        · intro first second heq
          have hq : first.2.val = second.2.val := congrArg Subtype.val heq
          have hc : child first.1 = child second.1 := by
            rw [← first.2.property, ← second.2.property, hq]
          have hnot : n + 1 ∉ p := by
            intro hmem
            have hrange := hm.1.mem_iff.mp hmem
            simp only [List.mem_range'_1] at hrange
            omega
          have hsites : site first.1 = site second.1 :=
            List.injOn_insertIdx_index_of_notMem p (n + 1) hnot
              (hsite first.1) (hsite second.1) hc
          have ho := hsiteInjective hsites
          cases first with
          | mk firstOrdinal firstWord =>
            cases second with
            | mk secondOrdinal secondWord =>
              dsimp only at ho hq
              subst secondOrdinal
              have hw : firstWord = secondWord := Subtype.ext hq
              subst secondWord
              rfl
        · intro q
          have hfiltered := hinitial (n + 1 + height) q.val.val q.val.property
            (n + 1) (by omega)
          obtain ⟨entry, heq⟩ := (classical_maximum_insertion_bijection n
            [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]]).2
              ⟨q.val.val.filter (fun value => value ≤ n + 1), hfiltered⟩
          have hw : entry.val.1.insertIdx entry.val.2 (n + 1) =
              q.val.val.filter (fun value => value ≤ n + 1) := congrArg Subtype.val heq
          have hp : entry.val.1 = p := by
            have hf := congrArg (fun word : List ℕ =>
              word.filter (fun value => value ≤ n)) hw
            rw [hfilterInsert n entry.val.1 entry.val.2 (n + 1)
              entry.property.2.1 (by omega), hfilterSelf n entry.val.1 entry.property.1.1,
              hfilterTwice n] at hf
            exact hf.trans q.property
          have hg : entry.val.2 ≤ p.length := by simpa only [hp] using entry.property.2.1
          have ha : p.insertIdx entry.val.2 (n + 1) ∈ family (n + 1) := by
            simpa only [hp] using entry.property.2.2
          obtain ⟨ordinal, ho⟩ := hcoverage entry.val.2 hg ha
          have hc : q.val.val.filter (fun value => value ≤ n + 1) = child ordinal := by
            dsimp [child]
            rw [ho]
            simpa only [hp] using hw.symm
          exact ⟨⟨ordinal, ⟨q.val, hc⟩⟩, Subtype.ext rfl⟩
      have hsum : Nat.card Future = ∑ ordinal : Choices,
          Nat.card {q : family (n + 1 + height) //
            q.val.filter (fun value => value ≤ n + 1) = child ordinal} := by
        rw [← Nat.card_congr (Equiv.ofBijective assemble hbijective)]
        exact Nat.card_sigma
      let branchWeight : Choices → ℕ := fun ordinal => match label with
        | .increasing => if ordinal.val = n then
            weight height (n + 1) .increasing else if height = 0 then 1 else 2 * height
        | .persistent _ => if ordinal.val = 0 then
            (if height = 0 then 1 else 2 * height) else (if height = 0 then 1 else 2)
        | .delayed _ => 1
        | .terminal _ => 1
      have hbranch (ordinal : Choices) :
          Nat.card {q : family (n + 1 + height) //
            q.val.filter (fun value => value ≤ n + 1) = child ordinal} =
            branchWeight ordinal := by
        obtain ⟨next, hnext, _⟩ := c_classification (n + 1) (child ordinal) (hchild ordinal)
        rw [ih (n + 1) (child ordinal) (hchild ordinal) next hnext]
        have hs := hsite ordinal
        have hb := ordinal.is_lt
        have htransition (gap : ℕ) (hg : gap ≤ n + 1) :=
          c_insertion_transitions n p hm (site ordinal) (by omega) (hchild ordinal) gap hg
        have hbefore (index : ℕ) (hi : index < site ordinal) :
            (child ordinal).getD index 0 = p.getD index 0 := by
          rw [List.getD_eq_getElem _ 0 (by
              rw [List.length_insertIdx_of_le_length hs]; omega),
            List.getElem_insertIdx_of_lt hi, List.getD_eq_getElem p 0 (by omega)]
        have hnoninc (hi : site ordinal < n) : child ordinal ≠ List.range' 1 (n + 1) := by
          intro heq
          have hat : (child ordinal).getD (site ordinal) 0 = n + 1 := by
            rw [List.getD_eq_getElem _ 0 (by
              rw [List.length_insertIdx_of_le_length hs]; omega)]
            exact List.getElem_insertIdx_self _
          rw [heq, List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range'] at hat
          simp only [Nat.one_mul] at hat
          omega
        have hpersistent (cut : ℕ) (hc : cut < n)
            (hnon : child ordinal ≠ List.range' 1 (n + 1))
            (hcuts : ∀ gap, gap ≤ n + 1 → ((child ordinal).insertIdx gap (n + 2) ∈
              family (n + 2) ↔ gap = cut ∨ gap = n + 1)) :
            weight height (n + 1) next = if height = 0 then 1 else 2 * height := by
          cases next with
          | increasing => exact False.elim (hnon hnext.1)
          | persistent nextcut => rfl
          | delayed nextcut =>
            have hnc := nextcut.is_lt
            have hh := (hnext.2 (n + 1) le_rfl).mp
              ((hcuts (n + 1) le_rfl).mpr (Or.inr rfl))
            omega
          | terminal nextcut =>
            have hnc := nextcut.is_lt
            have hh := (hnext (n + 1) le_rfl).mp
              ((hcuts (n + 1) le_rfl).mpr (Or.inr rfl))
            omega
        have hdelayed (cut : ℕ) (hc : cut < n)
            (hcuts : ∀ gap, gap ≤ n + 1 → ((child ordinal).insertIdx gap (n + 2) ∈
              family (n + 2) ↔ gap = cut ∨ gap = n)) :
            weight height (n + 1) next = if height = 0 then 1 else 2 := by
          cases next with
          | increasing =>
            have hh := (hcuts (n + 1) le_rfl).mp (hnext.2 (n + 1) le_rfl)
            omega
          | persistent nextcut =>
            have hh := (hcuts (n + 1) le_rfl).mp
              ((hnext.2.2 (n + 1) le_rfl).mpr (Or.inr rfl))
            omega
          | delayed nextcut => rfl
          | terminal nextcut =>
            have hfirst := (hnext cut (by omega)).mp
              ((hcuts cut (by omega)).mpr (Or.inl rfl))
            have hlast := (hnext n (by omega)).mp ((hcuts n (by omega)).mpr (Or.inr rfl))
            omega
        have hterminal (cut : ℕ) (hc : cut < n + 1)
            (hcuts : ∀ gap, gap ≤ n + 1 → ((child ordinal).insertIdx gap (n + 2) ∈
              family (n + 2) ↔ gap = cut)) : weight height (n + 1) next = 1 := by
          cases next with
          | increasing =>
            have hh := (hcuts (n + 1) le_rfl).mp (hnext.2 (n + 1) le_rfl)
            omega
          | persistent nextcut =>
            have hh := (hcuts (n + 1) le_rfl).mp
              ((hnext.2.2 (n + 1) le_rfl).mpr (Or.inr rfl))
            omega
          | delayed nextcut =>
            have hnc := nextcut.is_lt
            have hfirst := (hcuts nextcut.val (by omega)).mp
              ((hnext.2 nextcut.val (by omega)).mpr (Or.inl rfl))
            have hlast := (hcuts n (by omega)).mp
              ((hnext.2 n (by omega)).mpr (Or.inr (by omega)))
            omega
          | terminal nextcut => rfl
        cases label with
        | increasing =>
          obtain ⟨hp, hcuts⟩ := hspec
          have hprefix : ∀ first second, first < second → second < site ordinal →
              p.getD first 0 < p.getD second 0 := by
            intro first second hfs hb
            rw [hp, List.getD_eq_getElem _ 0 (by simp; omega),
              List.getD_eq_getElem _ 0 (by simp; omega),
              List.getElem_range', List.getElem_range']
            simp only [Nat.one_mul]
            omega
          dsimp [branchWeight]
          by_cases happend : ordinal.val = n
          · rw [if_pos happend]
            have hidentity : child ordinal = List.range' 1 (n + 1) := by
              dsimp [child, site]
              rw [happend, hp]
              simpa only [List.length_range', List.range'_concat, Nat.one_mul,
                Nat.add_comm] using
                (List.insertIdx_length_self (l := List.range' 1 n) (x := n + 1))
            cases next with
            | increasing => rfl
            | persistent nextcut => exact False.elim (hnext.1 hidentity)
            | delayed nextcut => exact False.elim (hnext.1 hidentity)
            | terminal nextcut =>
              have hnc := nextcut.is_lt
              have ha : (child ordinal).insertIdx (n + 1) (n + 2) ∈ family (n + 2) := by
                apply (htransition (n + 1) le_rfl).mpr
                right; right
                exact ⟨rfl, hcuts n le_rfl, hprefix⟩
              have hh := (hnext (n + 1) le_rfl).mp ha
              omega
          · rw [if_neg happend]
            have hi : site ordinal < n := by dsimp [site, Choices, degree] at *; omega
            apply hpersistent (site ordinal) hi (hnoninc hi)
            intro gap hg
            rw [htransition gap hg]
            constructor
            · rintro (⟨heq, _⟩ | ⟨_, heq⟩ | ⟨heq, _⟩)
              · omega
              · exact Or.inl heq
              · exact Or.inr heq
            · rintro (heq | heq)
              · exact Or.inr (Or.inl ⟨hi, heq⟩)
              · exact Or.inr (Or.inr ⟨heq, hcuts n le_rfl, hprefix⟩)
        | persistent cut =>
          obtain ⟨hnon, hprefix, hcuts⟩ := hspec
          have hc := cut.is_lt
          dsimp [branchWeight]
          by_cases hfirst : ordinal.val = 0
          · rw [if_pos hfirst]
            have hs : site ordinal = cut.val := by
              dsimp only [site]
              rw [if_pos hfirst]
            have hi : site ordinal < n := by omega
            apply hpersistent cut.val (by omega) (hnoninc hi)
            intro gap hg
            rw [htransition gap hg]
            constructor
            · rintro (⟨heq, _⟩ | ⟨_, heq⟩ | ⟨heq, _⟩)
              · omega
              · exact Or.inl (heq.trans hs)
              · exact Or.inr heq
            · rintro (heq | heq)
              · exact Or.inr (Or.inl ⟨hi, heq.trans hs.symm⟩)
              · right; right
                exact ⟨heq, (hcuts n le_rfl).mpr (Or.inr rfl),
                  by simpa only [hs] using hprefix⟩
          · rw [if_neg hfirst]
            have hs : site ordinal = n := by
              dsimp only [site]
              rw [if_neg hfirst]
            apply hdelayed cut.val (by omega)
            intro gap hg
            rw [htransition gap hg]
            constructor
            · rintro (⟨_, hb, hh⟩ | ⟨hi, _⟩ | ⟨_, _, hwhole⟩)
              · exact (hcuts gap hb).mp hh
              · omega
              · exact False.elim (hnon (hinc n p hm.1 (by simpa only [hs] using hwhole)))
            · intro hh
              exact Or.inl ⟨hs, by omega, (hcuts gap (by omega)).mpr hh⟩
        | delayed cut =>
          have hc := cut.is_lt
          have hi : site ordinal < n := by dsimp [site]; split_ifs <;> omega
          have hlast : p.insertIdx n (n + 1) ∉ family (n + 1) := by
            intro hh
            have := (hspec.2 n le_rfl).mp hh
            omega
          apply hterminal (site ordinal) (by omega)
          intro gap hg
          rw [htransition gap hg]
          constructor
          · rintro (⟨heq, _⟩ | ⟨_, heq⟩ | ⟨_, hh, _⟩)
            · omega
            · exact heq
            · exact False.elim (hlast hh)
          · intro heq
            exact Or.inr (Or.inl ⟨hi, heq⟩)
        | terminal cut =>
          have hc := cut.is_lt
          have hi : site ordinal < n := by dsimp [site]; omega
          have hlast : p.insertIdx n (n + 1) ∉ family (n + 1) := by
            intro hh
            have := (hspec n le_rfl).mp hh
            omega
          apply hterminal (site ordinal) (by omega)
          intro gap hg
          rw [htransition gap hg]
          constructor
          · rintro (⟨heq, _⟩ | ⟨_, heq⟩ | ⟨_, hh, _⟩)
            · omega
            · exact heq
            · exact False.elim (hlast hh)
          · intro heq
            exact Or.inr (Or.inl ⟨hi, heq⟩)
      have hsize : n + (height + 1) = n + 1 + height := by omega
      rw [hsize]
      change Nat.card Future = _
      rw [hsum]
      simp_rw [hbranch]
      cases label with
      | increasing =>
        change (∑ ordinal : Fin (n + 1),
          if ordinal.val = n then weight height (n + 1) .increasing
          else if height = 0 then 1 else 2 * height) = weight (height + 1) n .increasing
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_last, ↓reduceIte, Fin.val_castSucc]
        have hsumconstant : (∑ ordinal : Fin n, if ordinal.val = n then
            weight height (n + 1) .increasing else if height = 0 then 1 else 2 * height) =
            n * (if height = 0 then 1 else 2 * height) := by
          simp [show ∀ ordinal : Fin n, ordinal.val ≠ n from fun ordinal =>
            Nat.ne_of_lt ordinal.is_lt]
        rw [hsumconstant]
        cases height with
        | zero => norm_num [weight, Nat.choose]
        | succ height =>
          simp only [weight, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
            ↓reduceIte, Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
          ring
      | persistent cut =>
        change (∑ ordinal : Fin 2, if ordinal.val = 0 then
          (if height = 0 then 1 else 2 * height) else (if height = 0 then 1 else 2)) =
          weight (height + 1) n (.persistent cut)
        rw [Fin.sum_univ_two]
        cases height <;> simp [weight] <;> omega
      | delayed cut =>
        change (∑ _ordinal : Fin 2, 1) = weight (height + 1) n (.delayed cut)
        simp [weight]
      | terminal cut =>
        change (∑ _ordinal : Fin 1, 1) = weight (height + 1) n (.terminal cut)
        simp [weight]
  have hroot : [] ∈ family 0 := by
    refine ⟨by simp, ?_⟩
    intro pattern hpattern hocc
    obtain ⟨values, _, _, hsub, _⟩ := hocc
    have hl := hsub.length_le
    simp only [List.length_map, List.length_nil] at hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
    rcases hpattern with rfl | rfl | rfl <;> simp at hl
  obtain ⟨rootLabel, hrootSpec, _⟩ := c_classification 0 [] hroot
  have hlabel : rootLabel = .increasing := by
    cases rootLabel with
    | increasing => rfl
    | persistent cut => exact Fin.elim0 cut
    | delayed cut => exact Fin.elim0 cut
    | terminal cut => exact Fin.elim0 cut
  have hcount := hdescendants size 0 [] hroot rootLabel hrootSpec
  rw [hlabel, Nat.zero_add] at hcount
  let forget : {q : family size // q.val.filter (fun value => value ≤ 0) = []} →
      family size := fun q => q.val
  have hforget : Function.Bijective forget := by
    constructor
    · intro first second heq
      exact Subtype.ext heq
    · intro q
      refine ⟨⟨q, ?_⟩, rfl⟩
      apply List.filter_eq_nil_iff.mpr
      intro value hm
      have hr := q.property.1.mem_iff.mp hm
      simp only [List.mem_range'_1] at hr
      simpa using (show ¬ value ≤ 0 by omega)
  have hcard : Nat.card (family size) = weight size 0 .increasing := by
    rw [← Nat.card_congr (Equiv.ofBijective forget hforget)]
    exact hcount
  rw [← Nat.card_coe_set_eq]
  simpa [family, weight] using hcard

end D5.S3.Combinatorics.Fishburn.FishburnTenTenCCount
