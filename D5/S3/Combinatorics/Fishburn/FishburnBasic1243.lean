/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasic1243
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasic1243
   mirror-E: none(waiver:maximum-1243-occurrence-witness)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: A new 1243 occurrence straddles the inserted maximum with a prefix ascent. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicInsertion
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasic1243

open D5.S3.Combinatorics Nonnesting

theorem maximum_1243_test (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (cut : ℕ) (hcut : cut ≤ p.length) :
    NonnestingDefs.Occurs [1, 2, 4, 3] (p.insertIdx cut (n + 1)) ↔
      NonnestingDefs.Occurs [1, 2, 4, 3] p ∨
        ∃ first second third, first < second ∧ second < cut ∧ cut ≤ third ∧
          third < p.length ∧ p.getD first 0 < p.getD second 0 ∧
          p.getD second 0 < p.getD third 0 := by
  let child := p.insertIdx cut (n + 1)
  have hlength : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hcut (n + 1)
  have hbound (value : ℕ) (hm : value ∈ p) : value ≤ n := by
    have hrange := hperm.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, hvalue⟩ := hrange
    omega
  have hentry (index : ℕ) (hi : index < p.length) : p.getD index 0 ≤ n := by
    rw [List.getD_eq_getElem p 0 hi]
    exact hbound _ (List.getElem_mem hi)
  have hbefore (index : ℕ) (hi : index < cut) :
      child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega), List.getElem_insertIdx_of_lt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD cut 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  have hafter (index : ℕ) (hi : cut < index) (hb : index < child.length) :
      child.getD index 0 = p.getD (index - 1) 0 := by
    rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hmaxpos (index : ℕ) (hi : index < child.length)
      (he : child.getD index 0 = n + 1) : index = cut := by
    rcases lt_trichotomy index cut with hlt | heq | hgt
    · rw [hbefore index hlt] at he
      have := hentry index (by omega)
      omega
    · exact heq
    · rw [hafter index hgt hi] at he
      have := hentry (index - 1) (by omega)
      omega
  have hfilter : ∀ (word : List ℕ) (site : ℕ), site ≤ word.length →
      (∀ value ∈ word, value ≠ n + 1) →
      (word.insertIdx site (n + 1)).filter (· != n + 1) = word := by
    intro word site
    induction site generalizing word with
    | zero =>
      intro _ hword
      simp only [List.insertIdx_zero, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte]
      apply List.filter_eq_self.mpr
      intro value hm
      simpa using hword value hm
    | succ site ih =>
      cases word with
      | nil => simp
      | cons head tail =>
        intro hsite hword
        have hhead := hword head (by simp)
        have htail : ∀ value ∈ tail, value ≠ n + 1 := by
          intro value hm
          exact hword value (by simp [hm])
        simpa [List.insertIdx_succ_cons, hhead] using
          congrArg (head :: ·) (ih tail (by simpa using hsite) htail)
  have hfiltered : child.filter (· != n + 1) = p :=
    hfilter p cut hcut (fun value hm => by have := hbound value hm; omega)
  change ArrowWilfDefs.Contains [1, 2, 4, 3] [] 4 child ↔
    ArrowWilfDefs.Contains [1, 2, 4, 3] [] 4 p ∨ _
  constructor
  · rintro ⟨values, hstep, hmem, hsub, _⟩
    have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
    have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
    have h34 : values 3 < values 4 := hstep 3 (by omega) (by omega)
    by_cases htop : values 4 = n + 1
    · right
      obtain ⟨positions, hpositions⟩ :=
        List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let first := positions ⟨0, by simp⟩
      let second := positions ⟨1, by simp⟩
      let maximum := positions ⟨2, by simp⟩
      let last := positions ⟨3, by simp⟩
      have hfs : first.val < second.val :=
        positions.strictMono (by change (0 : ℕ) < 1; omega)
      have hsm : second.val < maximum.val :=
        positions.strictMono (by change (1 : ℕ) < 2; omega)
      have hml : maximum.val < last.val :=
        positions.strictMono (by change (2 : ℕ) < 3; omega)
      have hfirst : child.getD first.val 0 = values 1 := by
        rw [List.getD_eq_get]
        simpa [first] using (hpositions ⟨0, by simp⟩).symm
      have hsecond : child.getD second.val 0 = values 2 := by
        rw [List.getD_eq_get]
        simpa [second] using (hpositions ⟨1, by simp⟩).symm
      have hmaximum : child.getD maximum.val 0 = values 4 := by
        rw [List.getD_eq_get]
        simpa [maximum] using (hpositions ⟨2, by simp⟩).symm
      have hlast : child.getD last.val 0 = values 3 := by
        rw [List.getD_eq_get]
        simpa [last] using (hpositions ⟨3, by simp⟩).symm
      have hmaximumcut := hmaxpos maximum.val maximum.is_lt (hmaximum.trans htop)
      have hlastbound := last.is_lt
      rw [hbefore first.val (by omega)] at hfirst
      rw [hbefore second.val (by omega)] at hsecond
      rw [hafter last.val (by omega) hlastbound] at hlast
      exact ⟨first.val, second.val, last.val - 1, hfs, by omega, by omega,
        by omega, by omega, by omega⟩
    · left
      have htopbound := hbound (values 4)
        ((List.eq_or_mem_of_mem_insertIdx (hmem 4 (by omega) (by omega))).resolve_left htop)
      have hsmall (rank : ℕ) (hlo : 1 ≤ rank) (hhi : rank ≤ 4) :
          values rank ≠ n + 1 := by
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
        rcases hc with rfl | rfl | rfl | rfl <;> omega
      refine ⟨values, hstep, ?_, ?_, by simp⟩
      · intro rank hlo hhi
        exact (List.eq_or_mem_of_mem_insertIdx (hmem rank hlo hhi)).resolve_left
          (hsmall rank hlo hhi)
      · have hf := hsub.filter (· != n + 1)
        rw [hfiltered] at hf
        have hself : ([1, 2, 4, 3].map values).filter (· != n + 1) =
            [1, 2, 4, 3].map values := by
          apply List.filter_eq_self.mpr
          intro value hm
          obtain ⟨rank, hrank, rfl⟩ := List.mem_map.mp hm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hrank
          simpa using hsmall rank (by omega) (by omega)
        rwa [hself] at hf
  · rintro (⟨values, hstep, hmem, hsub, _⟩ |
      ⟨first, second, third, hfs, hsecond, hthird, hthirdbound, hlow, hhigh⟩)
    · refine ⟨values, hstep, ?_, hsub.trans (List.sublist_insertIdx p cut (n + 1)),
        by simp⟩
      intro rank hlo hhi
      exact List.subset_insertIdx p cut (n + 1) (hmem rank hlo hhi)
    · let values : ℕ → ℕ := fun rank =>
        if rank = 1 then p.getD first 0 else if rank = 2 then p.getD second 0
        else if rank = 3 then p.getD third 0 else n + 1
      have hsub : ([1, 2, 4, 3].map values).Sublist child := by
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        let select : Fin ([1, 2, 4, 3].map values).length → Fin child.length :=
          fun index => if index.val = 0 then ⟨first, by omega⟩
            else if index.val = 1 then ⟨second, by omega⟩
            else if index.val = 2 then ⟨cut, by omega⟩ else ⟨third + 1, by omega⟩
        have hmono : StrictMono select := by
          intro left right hlt
          change left.val < right.val at hlt
          have hl := left.is_lt
          have hr := right.is_lt
          simp only [List.length_map, List.length_cons, List.length_nil] at hl hr
          dsimp [select]
          split_ifs <;> simp only [Fin.mk_lt_mk] <;> omega
        refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
        intro index
        have hi := index.is_lt
        simp only [List.length_map, List.length_cons, List.length_nil] at hi
        have hc : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨ index.val = 3 := by omega
        rcases hc with heq | heq | heq | heq
        all_goals
          simp only [List.get_eq_getElem, OrderEmbedding.coe_ofStrictMono,
            List.getElem_map, select, heq, Nat.reduceEqDiff, ↓reduceIte,
            List.getElem_cons_zero, List.getElem_cons_succ]
        · rw [← List.getD_eq_getElem child 0 (by omega), hbefore first (by omega)]
          simp [values]
        · rw [← List.getD_eq_getElem child 0 (by omega), hbefore second hsecond]
          simp [values]
        · rw [← List.getD_eq_getElem child 0 (by omega), hat]
          simp [values]
        · rw [← List.getD_eq_getElem child 0 (by omega),
            hafter (third + 1) (by omega) (by omega), Nat.add_sub_cancel]
          simp [values]
      refine ⟨values, ?_, ?_, hsub, by simp⟩
      · intro rank hlo hhi
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        have hb := hentry third hthirdbound
        rcases hc with rfl | rfl | rfl <;>
          simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
      · intro rank hlo hhi
        have hrank : rank ∈ [1, 2, 4, 3] := by simp; omega
        exact hsub.subset (List.mem_map.mpr ⟨rank, hrank, rfl⟩)

end D5.S3.Combinatorics.Fishburn.FishburnBasic1243
