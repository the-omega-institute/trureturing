/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenNine
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenNine
   mirror-E: none(waiver:classical-splitting-and-labelled-tree-count)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.NoZeroDivisors]
   utility: none
   digest: Fishburn 2143 and 3124 avoiders are equinumerous with classical 231 and 4123 avoiders. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenNineSuccessors
import D5.S3.Combinatorics.Fishburn.FishburnTenNineTreeCount
import D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalCount
import D5.S3.Combinatorics.Fishburn.FishburnBasicInitialValues
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenNine

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs
open FishburnTenNineClassicalSplit FishburnTenNineAuxiliaryCount
open FishburnDefs FishburnBasicParents FishburnBasicInitialValues
open FishburnTenNineStructure FishburnTenNineSuccessors FishburnTenNineTreeCount
open FishburnTenNineClassicalCount
open Finset PowerSeries

theorem result : FishburnClassicalDefs.claim109 := by
  classical
  have hdescendantCount (height n initial extra : ℕ) (p : List ℕ)
      (hparent : p ∈ avoiders n [[2, 1, 4, 3], [3, 1, 2, 4]])
      (hie : initial ≤ extra) (hen : extra ≤ n)
      (hprefix : p.take initial = List.range' 1 initial)
      (hbreak : initial < n → p.getD initial 0 ≠ initial + 1)
      (hcuts : ∀ gap, gap ≤ p.length →
        (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] ↔
          gap ≤ initial ∨ initial < extra ∧ gap = extra))
      (hmaximum : initial < extra → ∃ maximum, initial ≤ maximum ∧ maximum < extra ∧
        p.getD maximum 0 = n) :
      Nat.card {q : avoiders (n + height) [[2, 1, 4, 3], [3, 1, 2, 4]] //
        q.val.filter (fun value => value ≤ n) = p} =
        descendants height initial
          (if initial = n then 0 else if initial = extra then 3
            else if p.getD initial 0 = n then 1 else 2) := by
    classical
    have hfinite (size : ℕ) :
        (avoiders size [[2, 1, 4, 3], [3, 1, 2, 4]]).Finite := by
      apply (List.finite_toSet (List.range' 1 size).permutations).subset
      intro word hw
      exact List.mem_permutations.mpr hw.1
    have hfilterSelf (size : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 size)) :
        word.filter (fun value => value ≤ size) = word := by
      apply List.filter_eq_self.mpr
      intro value hm
      have hr := hp.mem_iff.mp hm
      simp only [List.mem_range'_1] at hr
      simpa using (show value ≤ size by omega)
    have hfilterTwice (size : ℕ) (word : List ℕ) :
        (word.filter (fun value => value ≤ size + 1)).filter (fun value => value ≤ size) =
          word.filter (fun value => value ≤ size) := by
      rw [List.filter_filter]
      congr 1
      funext value
      by_cases hv : value ≤ size
      · simp [hv, show value ≤ size + 1 by omega]
      · simp [hv]
    have hfilterInsert (size : ℕ) (word : List ℕ) (site : ℕ)
        (hsite : site ≤ word.length) :
        (word.insertIdx site (size + 1)).filter (fun value => value ≤ size) =
          word.filter (fun value => value ≤ size) := by
      induction word generalizing site with
      | nil =>
        have hs : site = 0 := by simpa using hsite
        subst site
        simp
      | cons head tail ih =>
        cases site with
        | zero => simp
        | succ site =>
          simp only [List.insertIdx_succ_cons, List.filter_cons]
          rw [ih site (by simp only [List.length_cons] at hsite; omega)]
    induction height generalizing n p initial extra with
    | zero =>
      simp only [Nat.add_zero, descendants]
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨⟨p, hparent⟩, hfilterSelf n p hparent.1⟩, ?_⟩
      intro q
      apply Subtype.ext
      apply Subtype.ext
      have hq := q.property
      rw [hfilterSelf n q.val.val q.val.property.1] at hq
      exact hq
    | succ height ih =>
      let extraCount : ℕ := if initial < extra then 1 else 0
      let Choices := Fin (initial + 1 + extraCount)
      let site : Choices → ℕ := fun ordinal =>
        if ordinal.val ≤ initial then ordinal.val else extra
      let child : Choices → List ℕ := fun ordinal => p.insertIdx (site ordinal) (n + 1)
      have hlen : p.length = n := by simpa using hparent.1.length_eq
      have hsite (ordinal : Choices) : site ordinal ≤ p.length := by
        dsimp only [site]
        split_ifs <;> omega
      have hchild (ordinal : Choices) : child ordinal ∈
          avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] := by
        apply (hcuts (site ordinal) (hsite ordinal)).mpr
        dsimp only [site]
        split_ifs with ho
        · exact Or.inl ho
        · have hb := ordinal.is_lt
          have he : initial < extra := by
            dsimp only [Choices, extraCount] at hb
            split_ifs at hb <;> omega
          exact Or.inr ⟨he, rfl⟩
      have hsiteInjective : Function.Injective site := by
        intro first second heq
        apply Fin.ext
        have hf := first.is_lt
        have hs := second.is_lt
        dsimp only [site] at heq
        by_cases hfirst : first.val ≤ initial
        · by_cases hsecond : second.val ≤ initial
          · simpa only [if_pos hfirst, if_pos hsecond] using heq
          · have he : initial < extra := by
              dsimp only [Choices, extraCount] at hs
              split_ifs at hs <;> omega
            simp only [if_pos hfirst, if_neg hsecond] at heq
            omega
        · by_cases hsecond : second.val ≤ initial
          · have he : initial < extra := by
              dsimp only [Choices, extraCount] at hf
              split_ifs at hf <;> omega
            simp only [if_neg hfirst, if_pos hsecond] at heq
            omega
          · dsimp only [Choices, extraCount] at hf hs
            split_ifs at hf hs <;> omega
      let Branches := Σ ordinal : Choices,
        {q : avoiders (n + 1 + height) [[2, 1, 4, 3], [3, 1, 2, 4]] //
          q.val.filter (fun value => value ≤ n + 1) = child ordinal}
      let Future := {q : avoiders (n + 1 + height) [[2, 1, 4, 3], [3, 1, 2, 4]] //
        q.val.filter (fun value => value ≤ n) = p}
      let assemble : Branches → Future := fun entry => ⟨entry.2.val, by
        rw [← hfilterTwice n, entry.2.property]
        dsimp only [child]
        rw [hfilterInsert n p (site entry.1) (hsite entry.1), hfilterSelf n p hparent.1]⟩
      have hbijective : Function.Bijective assemble := by
        constructor
        · intro first second heq
          have hq : first.2.val = second.2.val := congrArg Subtype.val heq
          have hc : child first.1 = child second.1 := by
            rw [← first.2.property, ← second.2.property, hq]
          let firstEntry : {entry : List ℕ × ℕ //
            entry.1 ∈ avoiders n [[2, 1, 4, 3], [3, 1, 2, 4]] ∧
            entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
              avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]]} :=
            ⟨(p, site first.1), hparent, hsite first.1, hchild first.1⟩
          let secondEntry : {entry : List ℕ × ℕ //
            entry.1 ∈ avoiders n [[2, 1, 4, 3], [3, 1, 2, 4]] ∧
            entry.2 ≤ entry.1.length ∧ entry.1.insertIdx entry.2 (n + 1) ∈
              avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]]} :=
            ⟨(p, site second.1), hparent, hsite second.1, hchild second.1⟩
          have he : firstEntry = secondEntry :=
            (maximum_insertion_bijection n [[2, 1, 4, 3], [3, 1, 2, 4]]).1
              (Subtype.ext hc)
          have ho : first.1 = second.1 := hsiteInjective (congrArg (fun e => e.val.2) he)
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
          have hfiltered := initial_values_avoider [[2, 1, 4, 3], [3, 1, 2, 4]]
            (n + 1 + height) q.val.val q.val.property (n + 1) (by omega)
          obtain ⟨entry, heq⟩ :=
            (maximum_insertion_bijection n [[2, 1, 4, 3], [3, 1, 2, 4]]).2
              ⟨q.val.val.filter (fun value => value ≤ n + 1), hfiltered⟩
          have hword : entry.val.1.insertIdx entry.val.2 (n + 1) =
              q.val.val.filter (fun value => value ≤ n + 1) := congrArg Subtype.val heq
          have hp : entry.val.1 = p := by
            have hf := congrArg (fun word : List ℕ =>
              word.filter (fun value => value ≤ n)) hword
            rw [hfilterInsert n entry.val.1 entry.val.2 entry.property.2.1,
              hfilterSelf n entry.val.1 entry.property.1.1, hfilterTwice n] at hf
            exact hf.trans q.property
          have hgap : entry.val.2 ≤ p.length := by simpa only [hp] using entry.property.2.1
          have hactive : p.insertIdx entry.val.2 (n + 1) ∈
              avoiders (n + 1) [[2, 1, 4, 3], [3, 1, 2, 4]] := by
            simpa only [hp] using entry.property.2.2
          have hc := (hcuts entry.val.2 hgap).mp hactive
          obtain ⟨ordinal, ho⟩ : ∃ ordinal : Choices, site ordinal = entry.val.2 := by
            rcases hc with hg | ⟨he, hg⟩
            · refine ⟨⟨entry.val.2, by omega⟩, ?_⟩
              exact if_pos hg
            · refine ⟨⟨initial + 1, by simp [Choices, extraCount, he]⟩, ?_⟩
              dsimp only [site]
              rw [if_neg (by omega : ¬ initial + 1 ≤ initial)]
              exact hg.symm
          have hbranch : q.val.val.filter (fun value => value ≤ n + 1) = child ordinal := by
            dsimp only [child]
            rw [ho]
            simpa only [hp] using hword.symm
          exact ⟨⟨ordinal, ⟨q.val, hbranch⟩⟩, Subtype.ext rfl⟩
      let : Finite (avoiders (n + 1 + height) [[2, 1, 4, 3], [3, 1, 2, 4]]) :=
        (hfinite _).to_subtype
      have hcount : Nat.card Future = ∑ ordinal : Choices,
          Nat.card {q : avoiders (n + 1 + height) [[2, 1, 4, 3], [3, 1, 2, 4]] //
            q.val.filter (fun value => value ≤ n + 1) = child ordinal} := by
        rw [← Nat.card_congr (Equiv.ofBijective assemble hbijective)]
        exact Nat.card_sigma
      let weight : ℕ → ℕ := fun ordinal =>
        if ordinal < initial then descendants height ordinal 1
        else if ordinal = initial then
          if initial = n then descendants height (initial + 1) 0
          else if initial < extra ∧ p.getD initial 0 = n then descendants height initial 1
          else descendants height initial 3
        else descendants height initial 2
      have hweight (ordinal : Choices) :
          Nat.card {q : avoiders (n + 1 + height) [[2, 1, 4, 3], [3, 1, 2, 4]] //
            q.val.filter (fun value => value ≤ n + 1) = child ordinal} = weight ordinal.val := by
        obtain ⟨nextInitial, nextExtra, hnie, hnen, hnp, hnb, hnc, hnm⟩ :=
          active_sites_structure (n + 1) (child ordinal) (hchild ordinal)
        have hrules := labelled_successors n initial extra (site ordinal)
          nextInitial nextExtra p hparent hie hen hprefix hbreak hcuts hmaximum
          (hsite ordinal) (hchild ordinal) hnie hnen hnp hnb hnc
        rw [ih (n + 1) nextInitial nextExtra (child ordinal)
          (hchild ordinal) hnie hnen hnp hnb hnc hnm]
        by_cases hsmall : ordinal.val < initial
        · have hs : site ordinal = ordinal.val := if_pos (by omega)
          have hni : nextInitial = ordinal.val := by simpa only [hs, if_pos hsmall] using hrules.1
          have hne : nextExtra = ordinal.val + 2 := by
            simpa only [hs, if_pos hsmall] using hrules.2.1
          have hv : (child ordinal).getD nextInitial 0 = n + 1 :=
            (hrules.2.2 (by omega)).mpr (by omega)
          have hn : nextInitial ≠ n + 1 := by omega
          have he : nextInitial ≠ nextExtra := by omega
          rw [if_neg hn, if_neg he, if_pos hv]
          simp only [weight, if_pos hsmall, hni]
        by_cases heq : ordinal.val = initial
        · have hs : site ordinal = initial := by dsimp [site]; simp [heq]
          by_cases hid : initial = n
          · have hni : nextInitial = n + 1 := by
              simpa only [hs, if_neg (Nat.lt_irrefl initial), if_pos hid] using hrules.1
            rw [if_pos hni]
            simp only [hni, weight, if_neg hsmall, if_pos heq, if_pos hid]
            rw [hid]
          · have hni : nextInitial = initial := by
              simpa only [hs, if_neg (Nat.lt_irrefl initial), if_neg hid] using hrules.1
            have hn : nextInitial ≠ n + 1 := by omega
            by_cases hb : initial < extra ∧ p.getD initial 0 = n
            · have hne : nextExtra = extra + 1 := by
                simpa only [hs, if_neg (Nat.lt_irrefl initial), if_neg hid,
                  if_pos (show initial < extra ∧
                    (initial = extra ∨ p.getD initial 0 = n) from ⟨hb.1, Or.inr hb.2⟩)]
                  using hrules.2.1
              have hv : (child ordinal).getD nextInitial 0 = n + 1 :=
                (hrules.2.2 (by omega)).mpr (by omega)
              have he : nextInitial ≠ nextExtra := by omega
              rw [if_neg hn, if_neg he, if_pos hv]
              simp only [weight, if_neg hsmall, if_pos heq, if_neg hid, if_pos hb, hni]
            · have hc : ¬ (initial < extra ∧
                  (initial = extra ∨ p.getD initial 0 = n)) := by
                rintro ⟨he, hsame | hv⟩
                · omega
                · exact hb ⟨he, hv⟩
              have hne : nextExtra = initial := by
                simpa only [hs, if_neg (Nat.lt_irrefl initial), if_neg hid, if_neg hc]
                  using hrules.2.1
              rw [if_neg hn, if_pos (hni.trans hne.symm)]
              simp only [hni, weight, if_neg hsmall, if_pos heq, if_neg hid, if_neg hb]
        · have ho := ordinal.is_lt
          have he : initial < extra := by
            dsimp only [Choices, extraCount] at ho
            split_ifs at ho <;> omega
          have hs : site ordinal = extra := if_neg (by omega)
          have hn : initial ≠ n := by omega
          have hni : nextInitial = initial := by
            simpa only [hs, if_neg (by omega : ¬ extra < initial), if_neg hn] using hrules.1
          have hne : nextExtra = extra + 1 := by
            have hh := hrules.2.1
            rw [if_neg (by rw [hs]; omega), if_neg hn,
              if_pos (show initial < extra ∧
                (site ordinal = extra ∨ p.getD initial 0 = n) from ⟨he, Or.inl hs⟩)] at hh
            exact hh
          have hv : (child ordinal).getD nextInitial 0 ≠ n + 1 := by
            intro hv
            have hh := (hrules.2.2 (by omega)).mp hv
            omega
          have hnNext : nextInitial ≠ n + 1 := by omega
          have heNext : nextInitial ≠ nextExtra := by omega
          rw [if_neg hnNext, if_neg heNext, if_neg hv]
          simp only [weight, if_neg hsmall, if_neg heq, hni]
      have hsum : Nat.card Future = ∑ ordinal ∈ range (initial + 1 + extraCount),
          weight ordinal := by
        rw [hcount]
        simp_rw [hweight]
        exact Fin.sum_univ_eq_sum_range weight _
      have hsmallWeight : ∑ ordinal ∈ range initial, weight ordinal =
          ∑ ordinal ∈ range initial, descendants height ordinal 1 := by
        apply sum_congr rfl
        intro ordinal ho
        simp only [weight, if_pos (mem_range.mp ho)]
      rw [sum_range_add, sum_range_succ, hsmallWeight] at hsum
      have heqSize : n + (height + 1) = n + 1 + height := by omega
      rw [heqSize]
      change Nat.card Future = _
      rw [hsum]
      by_cases hid : initial = n
      · have he : ¬ initial < extra := by omega
        simp only [weight, extraCount, if_neg he, sum_range_zero, add_zero,
          if_neg (Nat.lt_irrefl initial), if_pos rfl, if_pos hid, descendants, if_true]
      · by_cases he : initial = extra
        · have hnot : ¬ initial < extra := by omega
          simp only [weight, extraCount, if_neg hnot, sum_range_zero, add_zero,
            if_neg (Nat.lt_irrefl initial), if_pos rfl, if_neg hid, if_pos he,
            false_and, if_false, descendants, show (3 : Fin 4) ≠ 0 by decide,
            show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide]
          simp only [if_true, hnot, false_and, if_false]
        · have heStrict : initial < extra := by omega
          by_cases hb : p.getD initial 0 = n
          · have hcondition : initial < extra ∧ p.getD initial 0 = n := ⟨heStrict, hb⟩
            simp only [weight, extraCount, if_pos heStrict, sum_range_one, add_zero,
              if_neg (Nat.lt_irrefl initial), if_pos rfl, if_neg hid, if_neg he,
              if_pos hb, if_pos hcondition, if_true, descendants,
              if_neg (show ¬ initial + 1 < initial by omega),
              if_neg (show initial + 1 ≠ initial by omega),
              show (1 : Fin 4) ≠ 0 by decide]
            simp only [if_false, if_true]
            omega
          · have hcondition : ¬ (initial < extra ∧ p.getD initial 0 = n) := fun hc => hb hc.2
            simp only [weight, extraCount, if_pos heStrict, sum_range_one, add_zero,
              if_neg (Nat.lt_irrefl initial), if_pos rfl, if_neg hid, if_neg he,
              if_neg hb, if_neg hcondition, if_false, descendants,
              if_neg (show ¬ initial + 1 < initial by omega),
              if_neg (show initial + 1 ≠ initial by omega),
              show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]
            simp only [if_false, if_true]
            omega
  have hroot : [] ∈ FishburnDefs.avoiders 0 [[2, 1, 4, 3], [3, 1, 2, 4]] := by
    refine ⟨by simp, ?_, ?_⟩
    · intro first last horder hlast
      simp at hlast
    · intro pattern hpattern hocc
      have hp : pattern = [2, 1, 4, 3] ∨ pattern = [3, 1, 2, 4] := by
        simpa using hpattern
      obtain ⟨values, _, _, hsub, _⟩ := hocc
      have hl := hsub.length_le
      rcases hp with rfl | rfl <;> simp at hl
  have hfishCount (height : ℕ) :
      (FishburnDefs.avoiders height [[2, 1, 4, 3], [3, 1, 2, 4]]).ncard =
        descendants height 0 0 := by
    have hz (q : FishburnDefs.avoiders height [[2, 1, 4, 3], [3, 1, 2, 4]]) :
        q.val.filter (fun value => value ≤ 0) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro value hm
      have hr := q.property.1.mem_iff.mp hm
      simp only [List.mem_range'_1] at hr
      simp only [decide_eq_true_eq]
      omega
    let lift : FishburnDefs.avoiders height [[2, 1, 4, 3], [3, 1, 2, 4]] →
        {q : FishburnDefs.avoiders height [[2, 1, 4, 3], [3, 1, 2, 4]] //
          q.val.filter (fun value => value ≤ 0) = []} := fun q => ⟨q, hz q⟩
    have hbij : Function.Bijective lift := by
      constructor
      · intro first second heq
        exact congrArg Subtype.val heq
      · intro q
        exact ⟨q.val, Subtype.ext rfl⟩
    obtain ⟨initial, extra, hie, hen, hp, hb, hc, hm⟩ := active_sites_structure 0 [] hroot
    have hi : initial = 0 := by omega
    have he : extra = 0 := by omega
    subst initial extra
    have hcount := hdescendantCount height 0 0 0 [] hroot hie hen hp hb hc hm
    rw [Nat.zero_add height] at hcount
    simp only [if_true] at hcount
    rw [← hcount]
    exact Nat.card_congr (Equiv.ofBijective lift hbij)
  let fishSeries : PowerSeries ℤ := mk (fun height => (descendants height 0 0 : ℤ))
  let classicalSeries : PowerSeries ℤ := mk (fun height =>
    ((classicalAvoiders height [[2, 3, 1], [4, 1, 2, 3]]).ncard : ℤ))
  let auxiliarySeries : PowerSeries ℤ := mk (fun height => (1 + height.choose 2 : ℤ))
  let denominator : PowerSeries ℤ := 1 - 4 * X + 5 * X ^ 2 - 3 * X ^ 3
  have hzero : (classicalAvoiders 0 [[2, 3, 1], [4, 1, 2, 3]]).ncard = 1 := by
    have heq : classicalAvoiders 0 [[2, 3, 1], [4, 1, 2, 3]] = {[]} := by
      ext word
      constructor
      · intro hw
        exact List.perm_nil.mp hw.1
      · intro hw
        have he := Set.mem_singleton_iff.mp hw
        subst word
        refine ⟨by simp, ?_⟩
        intro pattern hpattern hocc
        have hp : pattern = [2, 3, 1] ∨ pattern = [4, 1, 2, 3] := by
          simpa using hpattern
        obtain ⟨values, _, _, hsub, _⟩ := hocc
        have hl := hsub.length_le
        rcases hp with rfl | rfl <;> simp at hl
    rw [heq, Set.ncard_singleton]
  have hclassicalSeries : classicalSeries = 1 + X * (classicalSeries * auxiliarySeries) := by
    ext height
    cases height with
    | zero => simp [classicalSeries, hzero]
    | succ height =>
      rw [map_add, coeff_succ_X_mul]
      simp only [classicalSeries, auxiliarySeries, coeff_mk, map_add, coeff_one,
        Nat.succ_ne_zero, if_false, zero_add, coeff_mul]
      rw [classical_count_recurrence height]
      simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one, coeff_mk]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hauxiliarySeries : auxiliarySeries =
      (mk 1 : PowerSeries ℤ) + X ^ 2 * mk (fun height => ((2 + height).choose 2 : ℤ)) := by
    ext height
    cases height with
    | zero => simp [auxiliarySeries]
    | succ height =>
      cases height with
      | zero => simp [auxiliarySeries, coeff_X_pow_mul']
      | succ height =>
        change coeff (height + 2) auxiliarySeries =
          coeff (height + 2) ((mk 1 : PowerSeries ℤ) +
            X ^ 2 * mk (fun height => ((2 + height).choose 2 : ℤ)))
        rw [map_add, coeff_X_pow_mul]
        simp [auxiliarySeries, Nat.add_comm]
  have hauxiliaryScaled : (1 - X) ^ 3 * auxiliarySeries =
      (1 - 2 * X + 2 * X ^ 2 : PowerSeries ℤ) := by
    rw [hauxiliarySeries]
    have hg1 := mk_one_mul_one_sub_eq_one ℤ
    have hg3 := mk_add_choose_mul_one_sub_pow_eq_one ℤ 2
    linear_combination (1 - X) ^ 2 * hg1 + X ^ 2 * hg3
  have hclassicalPolynomial : denominator * classicalSeries = (1 - X) ^ 3 := by
    dsimp only [denominator]
    linear_combination (1 - X) ^ 3 * hclassicalSeries +
      X * classicalSeries * hauxiliaryScaled
  have hfishPolynomial : denominator * fishSeries = (1 - X) ^ 3 := abstract_tree_enumeration
  have hnonzero : denominator ≠ 0 := by
    intro heq
    have hc := congrArg (constantCoeff : PowerSeries ℤ →+* ℤ) heq
    norm_num [denominator] at hc
  have hseries : fishSeries = classicalSeries :=
    mul_left_cancel₀ hnonzero (hfishPolynomial.trans hclassicalPolynomial.symm)
  intro n _
  have hc := congrArg (coeff n) hseries
  simp only [fishSeries, classicalSeries, coeff_mk, Nat.cast_inj] at hc
  exact (hfishCount n).trans hc

end D5.S3.Combinatorics.Fishburn.FishburnTenNine
