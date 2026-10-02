/- GID: D5/S3/Combinatorics/PopStack/PopStackMinimum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackMinimum
   mirror-E: none(waiver:minimum-insertion-pattern-argument)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Inserting rank new minimum in the first three positions preserves class membership. -/

import D5.S3.Combinatorics.PopStack.PopStackDefs
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackMinimum

open PopStackDefs

theorem minimum_insertion_inC (permutation : List ℕ)
    (hpositive : ∀ rank ∈ permutation, 1 ≤ rank)
    (gap : ℕ) (hg : gap ≤ 2)
    (hgap : gap ≤ permutation.length) :
    InC ((permutation.map Nat.succ).insertIdx gap 1) ↔ InC permutation := by
  have htable : ∀ pattern ∈ basis,
      (∃ minimumIndex ∈ [3, 4], pattern[minimumIndex]? = some 1) ∧
      (∀ rank ∈ pattern, 1 ≤ rank ∧ rank ≤ pattern.length) := by
    decide
  have hinsert : (permutation.map Nat.succ).Sublist
      ((permutation.map Nat.succ).insertIdx gap 1) := by
    have hh := List.eraseIdx_sublist ((permutation.map Nat.succ).insertIdx gap 1) gap
    simpa only [List.eraseIdx_insertIdx_self] using hh
  have hfilter : ∀ (remaining : List ℕ) (index : ℕ), (∀ rank ∈ remaining, 1 ≤ rank) →
      ((remaining.map Nat.succ).insertIdx index 1).filter (· != 1) = remaining.map Nat.succ := by
    intro remaining index hs
    induction index generalizing remaining with
    | zero =>
      simp only [List.insertIdx_zero, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte]
      apply List.filter_eq_self.mpr
      intro value hvalue
      obtain ⟨rank, ha, rfl⟩ := List.mem_map.mp hvalue
      have hh := hs rank ha
      simp only [bne_iff_ne]
      omega
    | succ index ih =>
      cases remaining with
      | nil => simp
      | cons rank remaining =>
        have ha := hs rank (by simp)
        have htail : ∀ value ∈ remaining, 1 ≤ value := fun value hvalue =>
          hs value (List.mem_cons_of_mem rank hvalue)
        simpa [show rank ≠ 0 by omega] using
          congrArg (List.cons (rank + 1)) (ih remaining htail)
  have hocc : ∀ pattern ∈ basis,
      Occurs pattern ((permutation.map Nat.succ).insertIdx gap 1) ↔
        Occurs pattern permutation := by
    intro pattern hσ
    obtain ⟨⟨minimumIndex, hj, hget⟩, hranks⟩ := htable pattern hσ
    have hjlow : 3 ≤ minimumIndex := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> omega
    have hjlen : minimumIndex < pattern.length := by
      obtain ⟨hh, _⟩ := List.getElem?_eq_some_iff.mp hget
      exact hh
    have hk : 1 ≤ pattern.length := by omega
    constructor
    · rintro ⟨values, hinc, hmem, hsub, _⟩
      have hleast : ∀ rank, 1 ≤ rank → rank ≤ pattern.length →
          values 1 ≤ values rank := by
        intro rank ha hb
        induction rank with
        | zero => omega
        | succ rank ih =>
          by_cases heq : rank = 0
          · subst rank; exact le_rfl
          · have hh := ih (by omega) (by omega)
            have hi := hinc rank (by omega) (by omega)
            omega
      have hxpos : 1 ≤ values 1 := by
        have hh := hmem 1 (by omega) hk
        rw [List.mem_insertIdx (by simpa using hgap)] at hh
        rcases hh with hh | hh
        · omega
        · obtain ⟨rank, _, hh⟩ := List.mem_map.mp hh
          omega
      have hxne : values 1 ≠ 1 := by
        intro heq
        obtain ⟨positions, hpositions⟩ :=
          List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp hsub
        have hbound : ∀ index : ℕ, index ≤ positions index := by
          intro index
          induction index with
          | zero => omega
          | succ index ih =>
            have hh : positions index < positions (index + 1) :=
              positions.strictMono (Nat.lt_succ_self index)
            change index + 1 ≤ positions (index + 1)
            omega
        have hafter : gap < positions minimumIndex := by have hh := hbound minimumIndex; omega
        have hh := hpositions minimumIndex
        simp only [List.getElem?_map, hget, Option.map_some, heq] at hh
        rw [List.getElem?_insertIdx_of_gt hafter] at hh
        simp only [List.getElem?_map] at hh
        cases hvalue : permutation[positions minimumIndex - 1]? with
        | none => simp [hvalue] at hh
        | some value =>
          have hpos := hpositive value (List.mem_of_getElem? hvalue)
          simp only [hvalue, Option.map_some, Option.some.injEq] at hh
          omega
      have hvalues : ∀ rank, 1 ≤ rank → rank ≤ pattern.length → 2 ≤ values rank := by
        intro rank ha hb
        have hh := hleast rank ha hb
        omega
      have hsubold : (pattern.map values).Sublist (permutation.map Nat.succ) := by
        have hh := hsub.filter (· != 1)
        rw [hfilter permutation gap hpositive] at hh
        have hkeep : (pattern.map values).filter (· != 1) = pattern.map values := by
          apply List.filter_eq_self.mpr
          intro value hvalue
          obtain ⟨rank, ha, rfl⟩ := List.mem_map.mp hvalue
          obtain ⟨halow, hahigh⟩ := hranks rank ha
          have hh := hvalues rank halow hahigh
          simp only [bne_iff_ne]
          omega
        rwa [hkeep] at hh
      refine ⟨fun rank => values rank - 1, ?_, ?_, ?_, by simp⟩
      · intro rank ha hb
        dsimp only
        have hh := hinc rank ha hb
        have hpos := hvalues rank ha (by omega)
        omega
      · intro rank ha hb
        have hh := hmem rank ha hb
        rw [List.mem_insertIdx (by simpa using hgap)] at hh
        have hpos := hvalues rank ha hb
        rcases hh with hh | hh
        · omega
        · obtain ⟨value, hvalue, heq⟩ := List.mem_map.mp hh
          have heq' : values rank - 1 = value := by omega
          simpa only [heq'] using hvalue
      · have hh := hsubold.map Nat.pred
        simp only [List.map_map, Function.comp_def, Nat.pred_succ] at hh
        simpa only [Nat.pred_eq_sub_one, List.map_id'] using hh
    · rintro ⟨values, hinc, hmem, hsub, _⟩
      refine ⟨fun rank => (values rank).succ, ?_, ?_, ?_, by simp⟩
      · intro rank ha hb
        exact Nat.succ_lt_succ (hinc rank ha hb)
      · intro rank ha hb
        exact hinsert.subset (List.mem_map.mpr ⟨values rank, hmem rank ha hb, rfl⟩)
      · simpa only [List.map_map, Function.comp_def] using
          (hsub.map Nat.succ).trans hinsert
  constructor
  · intro hC pattern hσ hσr
    exact hC pattern hσ ((hocc pattern hσ).mpr hσr)
  · intro hC pattern hσ hσr
    exact hC pattern hσ ((hocc pattern hσ).mp hσr)

end D5.S3.Combinatorics.PopStack.PopStackMinimum
