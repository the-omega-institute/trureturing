/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTen
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTen
   mirror-E: none(waiver:classical-triple-fishburn-resolution)
   anchors: [mathlib/module/Mathlib.Data.List.Lemmas, mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: Maximum-insertion descendant counts prove the three Conjecture 10.10 cardinalities. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenBTree
import D5.S3.Combinatorics.Fishburn.FishburnTenTenAEnumeration
import D5.S3.Combinatorics.Fishburn.FishburnTenTenCCount
import D5.S3.Combinatorics.Fishburn.FishburnTripleClassicalDefs
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTen

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs
open FishburnBasicClassicalParents FishburnTenTenBTransitions FishburnTenTenBTree

set_option maxHeartbeats 2400000 in
theorem result : FishburnTripleClassicalDefs.claim1010 := by
  have b_enumeration (size : ℕ) :
      (classicalAvoiders size [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]]).ncard =
        if size = 0 then 1 else size + 2 * size.choose 3 := by
    classical
    let family := fun n => classicalAvoiders n [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]]
    let weight := fun (height n : ℕ) (label : BType n) =>
      match label with
      | .increasing => 1 + n * (height + 1).choose 2 + height.choose 2 +
          2 * height.choose 3
      | .adjacent cut => if cut.val + 2 = n then 1 + (height + 1).choose 2
          else height + 1
      | .persistent _ => height + 1
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
            [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]]).2 ⟨word, hm⟩
          have hw : entry.val.1.insertIdx entry.val.2 (n + 1) = word :=
            congrArg Subtype.val heq
          rw [← hw, hfilterInsert cut entry.val.1 entry.val.2 (n + 1)
            entry.property.2.1 (by omega)]
          exact ih entry.val.1 entry.property.1 cut (by omega)
    have hdescendants (height n : ℕ) (hn : 0 < n) (p : List ℕ) (hm : p ∈ family n)
        (label : BType n) (hspec : BSpec n p label) :
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
        cases label <;> simpa [weight, Nat.choose, apply_ite] using hcard
      | succ height ih =>
        have hlen : p.length = n := by simpa using hm.1.length_eq
        let degree : ℕ := match label with
          | .increasing => n + 1
          | .persistent _ => 2
          | .adjacent _ => 2
          | .terminal _ => 1
        let Choices := Fin degree
        let site : Choices → ℕ := fun ordinal => match label with
          | .increasing => ordinal.val
          | .persistent cut => if ordinal.val = 0 then cut.val + 1 else n
          | .adjacent cut => if ordinal.val = 0 then cut.val + 1 else cut.val + 2
          | .terminal cut => cut.val + 1
        let child : Choices → List ℕ := fun ordinal => p.insertIdx (site ordinal) (n + 1)
        have hsite (ordinal : Choices) : site ordinal ≤ p.length := by
          have hb := ordinal.is_lt
          cases label with
          | increasing => dsimp [site, Choices, degree] at *; omega
          | persistent cut =>
            have hc := cut.is_lt
            dsimp [site]; split_ifs <;> omega
          | adjacent cut =>
            have hc := cut.is_lt
            dsimp [site]; split_ifs <;> omega
          | terminal cut =>
            have hc := cut.is_lt
            dsimp [site]; omega
        have hchild (ordinal : Choices) : child ordinal ∈ family (n + 1) := by
          cases label with
          | increasing => exact hspec.2 (site ordinal) (by have := hsite ordinal; omega)
          | persistent cut =>
            apply (hspec.2 (site ordinal) (by have := hsite ordinal; omega)).mpr
            dsimp [site]; split_ifs <;> simp
          | adjacent cut =>
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
          | adjacent cut =>
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
            rcases (hspec.2 gap (by omega)).mp ha with heq | heq
            · exact ⟨⟨0, by simp [Choices, degree]⟩, by simp [site, heq]⟩
            · exact ⟨⟨1, by simp [Choices, degree]⟩, by simp [site, heq]⟩
          | adjacent cut =>
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
              [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]]).2
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
          | .increasing => if ordinal.val = n then weight height (n + 1) .increasing
              else if ordinal.val + 1 = n then 1 + (height + 1).choose 2 else height + 1
          | .adjacent cut => if ordinal.val = 0 then
              (if cut.val + 2 = n then 1 + (height + 1).choose 2 else height + 1)
              else if cut.val + 2 = n then height + 1 else 1
          | .persistent _ => if ordinal.val = 0 then 1 else height + 1
          | .terminal _ => 1
        have hbranch (ordinal : Choices) :
            Nat.card {q : family (n + 1 + height) //
              q.val.filter (fun value => value ≤ n + 1) = child ordinal} =
              branchWeight ordinal := by
          obtain ⟨next, hnext⟩ := b_classification (n + 1) (child ordinal) (hchild ordinal)
          rw [ih (n + 1) (by omega) (child ordinal) (hchild ordinal) next hnext]
          have hs := hsite ordinal
          have hb := ordinal.is_lt
          have hadjacent (cut : ℕ) (hc : 0 < cut) (hcut : cut ≤ n)
              (hcuts : ∀ gap, gap ≤ n + 1 → ((child ordinal).insertIdx gap (n + 2) ∈
                family (n + 2) ↔ gap = cut ∨ gap = cut + 1)) :
              weight height (n + 1) next =
                if cut + 1 = n + 1 then 1 + (height + 1).choose 2 else height + 1 := by
            cases next with
            | increasing =>
              have hh := (hcuts 0 (by omega)).mp (hnext.2 0 (by omega))
              omega
            | adjacent nextcut =>
              have hnc := nextcut.is_lt
              have hfirst := (hcuts (nextcut.val + 1) (by omega)).mp
                ((hnext.2 (nextcut.val + 1) (by omega)).mpr (Or.inl rfl))
              have hlast := (hcuts (nextcut.val + 2) (by omega)).mp
                ((hnext.2 (nextcut.val + 2) (by omega)).mpr (Or.inr rfl))
              have heq : nextcut.val + 2 = cut + 1 := by omega
              simp only [weight, heq]
            | persistent nextcut =>
              have hnc := nextcut.is_lt
              have hfirst := (hcuts (nextcut.val + 1) (by omega)).mp
                ((hnext.2 (nextcut.val + 1) (by omega)).mpr (Or.inl rfl))
              have hlast := (hcuts (n + 1) (by omega)).mp
                ((hnext.2 (n + 1) (by omega)).mpr (Or.inr rfl))
              omega
            | terminal nextcut =>
              have hfirst := (hnext cut (by omega)).mp
                ((hcuts cut (by omega)).mpr (Or.inl rfl))
              have hlast := (hnext (cut + 1) (by omega)).mp
                ((hcuts (cut + 1) (by omega)).mpr (Or.inr rfl))
              omega
          have hpersistent (cut : ℕ) (hc : 0 < cut) (hcut : cut < n)
              (hcuts : ∀ gap, gap ≤ n + 1 → ((child ordinal).insertIdx gap (n + 2) ∈
                family (n + 2) ↔ gap = cut ∨ gap = n + 1)) :
              weight height (n + 1) next = height + 1 := by
            cases next with
            | increasing =>
              have hh := (hcuts 0 (by omega)).mp (hnext.2 0 (by omega))
              omega
            | adjacent nextcut =>
              have hnc := nextcut.is_lt
              have hfirst := (hcuts (nextcut.val + 1) (by omega)).mp
                ((hnext.2 (nextcut.val + 1) (by omega)).mpr (Or.inl rfl))
              have hlast := (hcuts (nextcut.val + 2) (by omega)).mp
                ((hnext.2 (nextcut.val + 2) (by omega)).mpr (Or.inr rfl))
              omega
            | persistent nextcut => rfl
            | terminal nextcut =>
              have hfirst := (hnext cut (by omega)).mp
                ((hcuts cut (by omega)).mpr (Or.inl rfl))
              have hlast := (hnext (n + 1) (by omega)).mp
                ((hcuts (n + 1) (by omega)).mpr (Or.inr rfl))
              omega
          have hterminal (cut : ℕ) (hc : 0 < cut) (hcut : cut ≤ n)
              (hcuts : ∀ gap, gap ≤ n + 1 → ((child ordinal).insertIdx gap (n + 2) ∈
                family (n + 2) ↔ gap = cut)) : weight height (n + 1) next = 1 := by
            cases next with
            | increasing =>
              have hh := (hcuts 0 (by omega)).mp (hnext.2 0 (by omega))
              omega
            | adjacent nextcut =>
              have hnc := nextcut.is_lt
              have hfirst := (hcuts (nextcut.val + 1) (by omega)).mp
                ((hnext.2 (nextcut.val + 1) (by omega)).mpr (Or.inl rfl))
              have hlast := (hcuts (nextcut.val + 2) (by omega)).mp
                ((hnext.2 (nextcut.val + 2) (by omega)).mpr (Or.inr rfl))
              omega
            | persistent nextcut =>
              have hnc := nextcut.is_lt
              have hlast := (hcuts (n + 1) (by omega)).mp
                ((hnext.2 (n + 1) (by omega)).mpr (Or.inr rfl))
              omega
            | terminal nextcut => rfl
          have happend (cut : ℕ) (hc : 0 < cut) (hcut : cut < n)
              (hsplit : (∀ first second, first < second → second < cut →
                p.getD first 0 < p.getD second 0) ∧
                (∀ first second, cut ≤ first → first < second → second < n →
                  p.getD first 0 < p.getD second 0) ∧
                p.getD cut 0 < p.getD (cut - 1) 0)
              (he : site ordinal = n) : weight height (n + 1) next = height + 1 := by
            apply hpersistent cut hc hcut
            intro gap hg
            dsimp [child]
            have hactive : p.insertIdx n (n + 1) ∈ family (n + 1) := by
              simpa only [child, he] using hchild ordinal
            rw [he, b_append_transition n p hm hactive gap hg]
            constructor
            · rintro (hlast | ⟨hg, hpref, hsuff⟩)
              · exact Or.inr hlast
              · by_cases hl : gap < cut
                · have := hsuff (cut - 1) cut (by omega) (by omega) hcut
                  have := hsplit.2.2
                  omega
                · by_cases hr : cut < gap
                  · have := hpref (cut - 1) cut (by omega) hr
                    have := hsplit.2.2
                    omega
                  · exact Or.inl (by omega)
            · rintro (heq | hlast)
              · subst gap
                exact Or.inr ⟨by omega, hsplit.1, hsplit.2.1⟩
              · exact Or.inl hlast
          cases label with
          | increasing =>
            obtain ⟨hp, hsites⟩ := hspec
            dsimp [branchWeight]
            by_cases he : ordinal.val = n
            · rw [if_pos he]
              have hs : site ordinal = n := he
              have hactive : p.insertIdx n (n + 1) ∈ family (n + 1) := by
                simpa only [child, hs] using hchild ordinal
              have hzero : (child ordinal).insertIdx 0 (n + 2) ∈ family (n + 2) := by
                change (p.insertIdx (site ordinal) (n + 1)).insertIdx 0 (n + 2) ∈ _
                rw [hs, b_append_transition n p hm hactive 0 (by omega)]
                refine Or.inr ⟨by omega, ?_, ?_⟩
                · intro first second hfs hs
                  omega
                · intro first second _ hfs hs
                  rw [hp, List.getD_eq_getElem _ 0 (by simp; omega),
                    List.getD_eq_getElem _ 0 (by simp; omega),
                    List.getElem_range', List.getElem_range']
                  simp only [Nat.one_mul]
                  omega
              cases next with
              | increasing => rfl
              | adjacent cut =>
                have hh := (hnext.2 0 (by omega)).mp hzero
                omega
              | persistent cut =>
                have hh := (hnext.2 0 (by omega)).mp hzero
                omega
              | terminal cut =>
                have hh := (hnext 0 (by omega)).mp hzero
                omega
            · rw [if_neg he]
              have hi : site ordinal < n := by
                change ordinal.val < n
                dsimp only [degree] at hb
                omega
              have hh := hadjacent (site ordinal + 1) (by omega) (by omega) (by
                intro gap hg
                rw [b_internal_transition n p hm (site ordinal) hi (hchild ordinal) gap hg]
                simp only [hsites (site ordinal + 1) (by omega), and_true])
              simpa only [site, Nat.add_right_cancel_iff] using hh
          | adjacent cut =>
            obtain ⟨hsplit, hsites⟩ := hspec
            have hc := cut.is_lt
            dsimp [branchWeight]
            by_cases hfirst : ordinal.val = 0
            · rw [if_pos hfirst]
              have hs : site ordinal = cut.val + 1 := by
                dsimp only [site]
                rw [if_pos hfirst]
              have hi : site ordinal < n := by omega
              have hh := hadjacent (site ordinal + 1) (by omega) (by omega) (by
                intro gap hg
                rw [b_internal_transition n p hm (site ordinal) hi (hchild ordinal) gap hg]
                have ha := (hsites (site ordinal + 1) (by omega)).mpr (Or.inr (by omega))
                simp only [ha, and_true])
              simpa only [hs, Nat.add_right_cancel_iff] using hh
            · rw [if_neg hfirst]
              have hs : site ordinal = cut.val + 2 := by
                dsimp only [site]
                rw [if_neg hfirst]
              by_cases he : cut.val + 2 = n
              · rw [if_pos he]
                exact happend (cut.val + 1) (by omega) (by omega) (hsplit he) (by omega)
              · rw [if_neg he]
                have hi : site ordinal < n := by omega
                apply hterminal (site ordinal + 1) (by omega) (by omega)
                intro gap hg
                rw [b_internal_transition n p hm (site ordinal) hi (hchild ordinal) gap hg]
                have hnot : p.insertIdx (site ordinal + 1) (n + 1) ∉ family (n + 1) := by
                  intro hh
                  have := (hsites (site ordinal + 1) (by omega)).mp hh
                  omega
                dsimp only [family] at hnot
                simp only [hnot, and_false, or_false]
          | persistent cut =>
            obtain ⟨hsplit, hsites⟩ := hspec
            have hc := cut.is_lt
            dsimp [branchWeight]
            by_cases hfirst : ordinal.val = 0
            · rw [if_pos hfirst]
              have hs : site ordinal = cut.val + 1 := by
                dsimp only [site]
                rw [if_pos hfirst]
              have hi : site ordinal < n := by omega
              apply hterminal (site ordinal + 1) (by omega) (by omega)
              intro gap hg
              rw [b_internal_transition n p hm (site ordinal) hi (hchild ordinal) gap hg]
              have hnot : p.insertIdx (site ordinal + 1) (n + 1) ∉ family (n + 1) := by
                intro hh
                have := (hsites (site ordinal + 1) (by omega)).mp hh
                omega
              dsimp only [family] at hnot
              simp only [hnot, and_false, or_false]
            · rw [if_neg hfirst]
              exact happend (cut.val + 1) (by omega) (by omega) hsplit
                (by dsimp only [site]; rw [if_neg hfirst])
          | terminal cut =>
            have hc := cut.is_lt
            have hs : site ordinal = cut.val + 1 := rfl
            have hi : site ordinal < n := by omega
            apply hterminal (site ordinal + 1) (by omega) (by omega)
            intro gap hg
            rw [b_internal_transition n p hm (site ordinal) hi (hchild ordinal) gap hg]
            have hnot : p.insertIdx (site ordinal + 1) (n + 1) ∉ family (n + 1) := by
              intro hh
              have := (hspec (site ordinal + 1) (by omega)).mp hh
              omega
            dsimp only [family] at hnot
            simp only [hnot, and_false, or_false]
        have hsize : n + (height + 1) = n + 1 + height := by omega
        rw [hsize]
        change Nat.card Future = _
        rw [hsum]
        simp_rw [hbranch]
        cases label with
        | increasing =>
          change (∑ ordinal : Fin (n + 1), if ordinal.val = n then
            weight height (n + 1) .increasing else if ordinal.val + 1 = n then
            1 + (height + 1).choose 2 else height + 1) =
            weight (height + 1) n .increasing
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.val_last, ↓reduceIte, Fin.val_castSucc]
          have hsumconstant : (∑ ordinal : Fin n, if ordinal.val = n then
              weight height (n + 1) .increasing else if ordinal.val + 1 = n then
              1 + (height + 1).choose 2 else height + 1) =
              (n - 1) * (height + 1) + 1 + (height + 1).choose 2 := by
            obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
            rw [Fin.sum_univ_castSucc]
            simp only [Fin.val_last, Fin.val_castSucc]
            have hsmall (ordinal : Fin previous) :
                ordinal.val ≠ previous + 1 ∧ ordinal.val + 1 ≠ previous + 1 := by
              have := ordinal.is_lt
              omega
            have hlt (ordinal : Fin previous) : ordinal.val ≠ previous :=
              Nat.ne_of_lt ordinal.is_lt
            simp [hsmall, hlt, Nat.succ_eq_add_one, Nat.add_assoc]
          rw [hsumconstant]
          have hnEq : n - 1 + 1 = n := by omega
          simp only [weight, Nat.choose_succ_succ, Nat.choose_one_right,
            Nat.choose_zero_right]
          nlinarith
        | adjacent cut =>
          change (∑ ordinal : Fin 2, if ordinal.val = 0 then
            (if cut.val + 2 = n then 1 + (height + 1).choose 2 else height + 1)
            else if cut.val + 2 = n then height + 1 else 1) =
            weight (height + 1) n (.adjacent cut)
          rw [Fin.sum_univ_two]
          by_cases he : cut.val + 2 = n <;>
            simp [weight, he, Nat.choose_succ_succ, Nat.choose_one_right] <;> omega
        | persistent cut =>
          change (∑ ordinal : Fin 2, if ordinal.val = 0 then 1 else height + 1) =
            weight (height + 1) n (.persistent cut)
          rw [Fin.sum_univ_two]
          simp [weight]
          omega
        | terminal cut =>
          change (∑ _ordinal : Fin 1, 1) = weight (height + 1) n (.terminal cut)
          simp [weight]
    have hroot : [1] ∈ family 1 := by
      refine ⟨by simp [List.range'], ?_⟩
      intro pattern hp hocc
      obtain ⟨values, _, _, hsub, _⟩ := hocc
      have hl := hsub.length_le
      simp only [List.length_map, List.length_cons, List.length_nil] at hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp at hl
    by_cases hz : size = 0
    · subst size
      have heq : family 0 = {[]} := by
        ext word
        constructor
        · intro hm
          exact List.perm_nil.mp hm.1
        · intro he
          have heq : word = [] := he
          subst word
          refine ⟨by simp, ?_⟩
          intro pattern hp hocc
          obtain ⟨values, _, _, hsub, _⟩ := hocc
          have hl := hsub.length_le
          simp only [List.length_map, List.length_nil] at hl
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl <;> simp at hl
      change (family 0).ncard = _
      simp [heq]
    · obtain ⟨rootLabel, hrootSpec⟩ := b_classification 1 [1] hroot
      have hlabel : rootLabel = .increasing := by
        cases rootLabel with
        | increasing => rfl
        | adjacent cut => exact Fin.elim0 cut
        | persistent cut => exact Fin.elim0 cut
        | terminal cut => exact Fin.elim0 cut
      have hcount := hdescendants (size - 1) 1 (by omega) [1] hroot rootLabel hrootSpec
      rw [hlabel, show 1 + (size - 1) = size by omega] at hcount
      let forget : {q : family size // q.val.filter (fun value => value ≤ 1) = [1]} →
          family size := fun q => q.val
      have hforget : Function.Bijective forget := by
        constructor
        · intro first second heq
          exact Subtype.ext heq
        · intro q
          refine ⟨⟨q, ?_⟩, rfl⟩
          have hm := hinitial size q.val q.property 1 (by omega)
          exact List.perm_singleton.mp (by simpa [List.range'] using hm.1)
      have hcard : Nat.card (family size) = weight (size - 1) 1 .increasing := by
        rw [← Nat.card_congr (Equiv.ofBijective forget hforget)]
        exact hcount
      rw [← Nat.card_coe_set_eq]
      change Nat.card (family size) = _
      rw [hcard, if_neg hz]
      obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      simp only [weight, Nat.succ_sub_one, Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.choose_zero_right]
      norm_num only [Nat.succ_eq_add_one]
      omega
  intro n
  have hfishburn := FishburnTenTenAEnumeration.a_enumeration n
  have hfirst := b_enumeration n
  have hsecond := FishburnTenTenCCount.c_enumeration n
  exact ⟨hfishburn.trans hfirst.symm, hfirst.trans hsecond.symm⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenTen
