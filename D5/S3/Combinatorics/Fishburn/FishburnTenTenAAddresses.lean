/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenAAddresses
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenAAddresses
   mirror-E: none(waiver:fishburn-a-unique-live-addresses)
   anchors: []
   utility: none
   digest: Entries recover unique live addresses and identify precisely the nonterminal A nodes. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenATree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenAAddresses

open D5.S3.Combinatorics Nonnesting FishburnDefs
open FishburnTenTenAMonotone FishburnTenTenALayered FishburnTenTenAValley
open FishburnTenTenATree

set_option maxHeartbeats 1600000 in
theorem a_live_addresses (n : ℕ) (hn : 2 ≤ n) :
    let layered := fun pair : ℕ × ℕ =>
      List.range' 1 pair.1 ++ (List.range' (pair.1 + 1) (pair.2 - pair.1)).reverse ++
        List.range' (pair.2 + 1) (n - pair.2)
    let valley := fun pair : ℕ × ℕ =>
      (List.range' (pair.1 + 1) (pair.2 - pair.1)).reverse ++ [1] ++
        List.range' (pair.2 + 1) (n - pair.2) ++ (List.range' 2 (pair.1 - 1)).reverse
    let address := Unit ⊕ ({pair : ℕ × ℕ // pair.1 + 2 ≤ pair.2 ∧ pair.2 ≤ n} ⊕
      {pair : ℕ × ℕ // 2 ≤ pair.1 ∧ pair.1 < pair.2 ∧ pair.2 ≤ n})
    let decode : address → List ℕ := fun entry =>
      match entry with
      | .inl _ => List.range' 1 n
      | .inr (.inl pair) => layered pair.val
      | .inr (.inr pair) => valley pair.val
    Function.Injective decode ∧
      ∀ p, (p ∈ avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ∧
        ∃ site, 0 < site ∧ site ≤ n ∧ p.insertIdx site (n + 1) ∈
          avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]) ↔
        p ∈ Set.range decode := by
  let layered := fun pair : ℕ × ℕ =>
    List.range' 1 pair.1 ++ (List.range' (pair.1 + 1) (pair.2 - pair.1)).reverse ++
      List.range' (pair.2 + 1) (n - pair.2)
  let valley := fun pair : ℕ × ℕ =>
    (List.range' (pair.1 + 1) (pair.2 - pair.1)).reverse ++ [1] ++
      List.range' (pair.2 + 1) (n - pair.2) ++ (List.range' 2 (pair.1 - 1)).reverse
  let address := Unit ⊕ ({pair : ℕ × ℕ // pair.1 + 2 ≤ pair.2 ∧ pair.2 ≤ n} ⊕
    {pair : ℕ × ℕ // 2 ≤ pair.1 ∧ pair.1 < pair.2 ∧ pair.2 ≤ n})
  let decode : address → List ℕ := fun entry =>
    match entry with
    | .inl _ => List.range' 1 n
    | .inr (.inl pair) => layered pair.val
    | .inr (.inr pair) => valley pair.val
  change Function.Injective decode ∧ _
  have hie (index : ℕ) (hi : index < n) :
      (List.range' 1 n).getD index 0 = index + 1 := by
    rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
    simp only [Nat.one_mul, Nat.add_comm]
  have hle (start finish index : ℕ) (hs : start + 2 ≤ finish) (hf : finish ≤ n)
      (hi : index < n) :
      (layered (start, finish)).getD index 0 =
        if index < start then index + 1
        else if index < finish then start + finish - index else index + 1 := by
    dsimp only [layered]
    rw [List.append_assoc]
    by_cases hleft : index < start
    · rw [List.getD_append _ _ _ _ (by simp; omega),
        List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
      simp only [hleft, ↓reduceIte, Nat.one_mul, Nat.add_comm]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_range']
      by_cases hmiddle : index < finish
      · rw [List.getD_append _ _ _ _ (by simp; omega),
          List.getD_reverse (index - start) (by simp; omega)]
        simp only [List.length_range']
        rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
        simp only [hleft, hmiddle, ↓reduceIte, Nat.one_mul]
        omega
      · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_reverse, List.length_range']
        rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
        simp only [hleft, hmiddle, ↓reduceIte, Nat.one_mul]
        omega
  have hve (lower upper index : ℕ) (hl : 2 ≤ lower) (hu : lower < upper)
      (hs : upper ≤ n) (hi : index < n) :
      (valley (lower, upper)).getD index 0 =
        if index < upper - lower then upper - index
        else if index = upper - lower then 1
        else if index < n - lower + 1 then index + lower else n - index + 1 := by
    dsimp only [valley]
    simp only [List.append_assoc, List.cons_append]
    by_cases hleft : index < upper - lower
    · rw [List.getD_append _ _ _ _ (by simp; omega),
        List.getD_reverse index (by simp; omega)]
      simp only [List.length_range']
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
      simp only [hleft, ↓reduceIte, Nat.one_mul]
      omega
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_reverse, List.length_range']
      by_cases hone : index = upper - lower
      · subst index
        simp
      · have hsub : index - (upper - lower) = (index - (upper - lower) - 1) + 1 := by
          omega
        rw [hsub, List.getD_cons_succ]
        simp only [List.nil_append]
        by_cases hmiddle : index < n - lower + 1
        · rw [List.getD_append _ _ _ _ (by simp; omega),
            List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
          simp only [hleft, hone, hmiddle, ↓reduceIte, Nat.one_mul]
          omega
        · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [List.length_range']
          rw [List.getD_reverse _ (by simp; omega)]
          simp only [List.length_range']
          rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
          simp only [hleft, hone, hmiddle, ↓reduceIte, Nat.one_mul]
          omega
  have hinc_layer (start finish : ℕ) (hs : start + 2 ≤ finish) (hf : finish ≤ n) :
      List.range' 1 n ≠ layered (start, finish) := by
    intro heq
    have hh := congrArg (fun word : List ℕ => word.getD start 0) heq
    rw [hie start (by omega), hle start finish start hs hf (by omega)] at hh
    split_ifs at hh <;> omega
  have hinc_valley (lower upper : ℕ) (hl : 2 ≤ lower) (hu : lower < upper)
      (hf : upper ≤ n) : List.range' 1 n ≠ valley (lower, upper) := by
    intro heq
    have hh := congrArg (fun word : List ℕ => word.getD 0 0) heq
    rw [hie 0 (by omega), hve lower upper 0 hl hu hf (by omega)] at hh
    split_ifs at hh <;> omega
  have hdistinct (start finish lower upper : ℕ) (hs : start + 2 ≤ finish)
      (hf : finish ≤ n) (hl : 2 ≤ lower) (hu : lower < upper) (hp : upper ≤ n) :
      layered (start, finish) ≠ valley (lower, upper) := by
    intro heq
    have hlast := congrArg (fun word : List ℕ => word.getD (n - 1) 0) heq
    rw [hle start finish (n - 1) hs hf (by omega),
      hve lower upper (n - 1) hl hu hp (by omega)] at hlast
    have hstart : start = 1 := by split_ifs at hlast <;> omega
    have hfirst := congrArg (fun word : List ℕ => word.getD 0 0) heq
    rw [hle start finish 0 hs hf (by omega), hve lower upper 0 hl hu hp (by omega)]
      at hfirst
    split_ifs at hfirst <;> omega
  have hlayer_inj (first second : {pair : ℕ × ℕ // pair.1 + 2 ≤ pair.2 ∧ pair.2 ≤ n})
      (heq : layered first.val = layered second.val) : first = second := by
    obtain ⟨⟨start, finish⟩, hs, hf⟩ := first
    obtain ⟨⟨start', finish'⟩, hs', hf'⟩ := second
    have hstart : start = start' := by
      by_contra hnot
      rcases lt_or_gt_of_ne hnot with hlt | hgt
      · have hh := congrArg (fun word : List ℕ => word.getD start 0) heq
        rw [hle start finish start hs hf (by omega),
          hle start' finish' start hs' hf' (by omega)] at hh
        split_ifs at hh <;> omega
      · have hh := congrArg (fun word : List ℕ => word.getD start' 0) heq
        rw [hle start finish start' hs hf (by omega),
          hle start' finish' start' hs' hf' (by omega)] at hh
        split_ifs at hh <;> omega
    have hh := congrArg (fun word : List ℕ => word.getD start 0) heq
    have hfinish : finish = finish' := by
      rw [hle start finish start hs hf (by omega),
        hle start' finish' start hs' hf' (by omega)] at hh
      split_ifs at hh <;> omega
    apply Subtype.ext
    exact Prod.ext hstart hfinish
  have hvalley_inj
      (first second : {pair : ℕ × ℕ // 2 ≤ pair.1 ∧ pair.1 < pair.2 ∧ pair.2 ≤ n})
      (heq : valley first.val = valley second.val) : first = second := by
    obtain ⟨⟨lower, upper⟩, hl, hu, hf⟩ := first
    obtain ⟨⟨lower', upper'⟩, hl', hu', hf'⟩ := second
    have hupper : upper = upper' := by
      have hh := congrArg (fun word : List ℕ => word.getD 0 0) heq
      rw [hve lower upper 0 hl hu hf (by omega),
        hve lower' upper' 0 hl' hu' hf' (by omega)] at hh
      split_ifs at hh <;> omega
    have hlower : lower = lower' := by
      have hh := congrArg (fun word : List ℕ => word.getD (upper - lower) 0) heq
      rw [hve lower upper (upper - lower) hl hu hf (by omega),
        hve lower' upper' (upper - lower) hl' hu' hf' (by omega)] at hh
      split_ifs at hh <;> omega
    apply Subtype.ext
    exact Prod.ext hlower hupper
  constructor
  · intro first second heq
    cases first with
    | inl first =>
      cases second with
      | inl second => rfl
      | inr second =>
        cases second with
        | inl pair =>
          exact False.elim
            (hinc_layer pair.val.1 pair.val.2 pair.property.1 pair.property.2 heq)
        | inr pair =>
          exact False.elim (hinc_valley pair.val.1 pair.val.2
            pair.property.1 pair.property.2.1 pair.property.2.2 heq)
    | inr first =>
      cases first with
      | inl first =>
        cases second with
        | inl second =>
          exact False.elim
            (hinc_layer first.val.1 first.val.2 first.property.1 first.property.2 heq.symm)
        | inr second =>
          cases second with
          | inl second =>
            exact congrArg (fun pair => Sum.inr (Sum.inl pair))
              (hlayer_inj first second heq)
          | inr second =>
            exact False.elim (hdistinct first.val.1 first.val.2
              second.val.1 second.val.2 first.property.1 first.property.2 second.property.1
                second.property.2.1 second.property.2.2 heq)
      | inr first =>
        cases second with
        | inl second =>
          exact False.elim (hinc_valley first.val.1 first.val.2
            first.property.1 first.property.2.1 first.property.2.2 heq.symm)
        | inr second =>
          cases second with
          | inl second =>
            exact False.elim (hdistinct second.val.1 second.val.2
              first.val.1 first.val.2 second.property.1 second.property.2 first.property.1
                first.property.2.1 first.property.2.2 heq.symm)
          | inr second =>
            exact congrArg (fun pair => Sum.inr (Sum.inr pair))
              (hvalley_inj first second heq)
  · intro p
    constructor
    · rintro ⟨hp, site, hpositive, hsite, hactive⟩
      rcases a_classification n hn p hp with hinc | hlayer | hvalley | hterm
      · exact ⟨.inl (), hinc.symm⟩
      · obtain ⟨start, finish, hs, hf, heq⟩ := hlayer
        exact ⟨.inr (.inl ⟨(start, finish), hs, hf⟩), heq.symm⟩
      · obtain ⟨lower, upper, hl, hu, hf, heq⟩ := hvalley
        exact ⟨.inr (.inr ⟨(lower, upper), hl, hu, hf⟩), heq.symm⟩
      · have hh := (hterm site hsite).mp hactive
        omega
    · rintro ⟨entry, rfl⟩
      cases entry with
      | inl entry =>
        refine ⟨(a_monotone_forms n).1, n, by omega, le_rfl, ?_⟩
        exact ((a_monotone_forms n).2.2 n le_rfl).1.mpr (Or.inr (by omega))
      | inr entry =>
        cases entry with
        | inl pair =>
          have hh := a_layered_forms n pair.val.1 pair.val.2 pair.property.1 pair.property.2
          refine ⟨hh.1, n, by omega, le_rfl, ?_⟩
          exact (hh.2 n le_rfl).mpr (Or.inr (Or.inl rfl))
        | inr pair =>
          have hh := a_valley_forms n pair.val.1 pair.val.2 pair.property.1
            pair.property.2.1 pair.property.2.2
          refine ⟨hh.1, n - pair.val.1 + 1, by omega, by omega, ?_⟩
          exact (hh.2 _ (by omega)).mpr (Or.inr rfl)

end D5.S3.Combinatorics.Fishburn.FishburnTenTenAAddresses
