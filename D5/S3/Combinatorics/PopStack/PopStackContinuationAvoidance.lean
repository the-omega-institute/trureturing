/- GID: D5/S3/Combinatorics/PopStack/PopStackContinuationAvoidance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackContinuationAvoidance
   mirror-E: none(waiver:ordinary-continuation-pattern-witnesses)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Ordinary prefix continuation excludes new forbidden patterns by explicit witnesses. -/

import D5.S3.Combinatorics.PopStack.PopStackContinuation
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackContinuationAvoidance

open PopStackDefs PopStackContinuation

theorem ordinary_continuation (permutation : List ℕ)
    (hperm : permutation.Perm (List.range' 1 permutation.length))
    (hlength : 2 ≤ permutation.length) (hC : InC permutation)
    (hsecond : permutation.getD 1 0 < permutation.length)
    (hbond : permutation.getD 0 0 ≠ permutation.getD 1 0 + 1) :
    InC (W permutation) ∧
    (4 ≤ permutation.length → IsSimple permutation →
      (W permutation).Perm (List.range' 1 (permutation.length + 1)) ∧
        IsSimple (W permutation)) := by
  constructor
  ·
    classical
    let beta := permutation.getD 1 0
    let shift := fun entry => if beta < entry then entry + 1 else entry
    let contract := fun entry => if beta < entry then entry - 1 else entry
    let old := permutation.map shift
    let value := fun index => old.getD index 0
    let expanded := W permutation
    have hshape : expanded = (beta + 1) :: old := rfl
    have hnewLength : expanded.length = permutation.length + 1 := by simp [expanded, W]
    have holdLength : old.length = permutation.length := by simp [old]
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hshiftMono : StrictMono shift := by
      intro first second hlt
      dsimp only [shift]
      split_ifs <;> omega
    have holdNodup : old.Nodup := hnodup.map hshiftMono.injective
    have hmissing : ∀ entry, shift entry ≠ beta + 1 := by
      intro entry
      dsimp only [shift]
      split_ifs <;> omega
    have hinverse : ∀ entry, contract (shift entry) = entry := by
      intro entry
      dsimp only [contract, shift]
      split_ifs <;> omega
    have hcontract : old.map contract = permutation := by
      change (permutation.map shift).map contract = permutation
      rw [List.map_map, show contract ∘ shift = id from funext hinverse, List.map_id]
    have hvalueMem : ∀ index, index < old.length → value index ∈ old := by
      intro index hindex
      dsimp only [value]
      rw [List.getD_eq_getElem _ 0 hindex]
      exact List.getElem_mem hindex
    have hnotNew : ∀ entry ∈ old, entry ≠ beta + 1 := by
      intro entry hentry
      obtain ⟨rank, _, rfl⟩ := List.mem_map.mp hentry
      exact hmissing rank
    have hbeta : value 1 = beta := by
      dsimp only [value, old]
      rw [List.getD_eq_getElem _ 0 (by simp only [List.length_map]; omega),
        List.getElem_map, ← List.getD_eq_getElem permutation 0 (by omega)]
      simp [shift, beta]
    have hbetaMem : beta ∈ old := hbeta ▸ hvalueMem 1 (by omega)
    have holdC : InC old := by
      intro pattern hpattern hocc
      obtain ⟨ranks, hinc, hmem, hsub, _⟩ := hocc
      apply hC pattern hpattern
      refine ⟨contract ∘ ranks, ?_, ?_, ?_, by simp⟩
      · intro rank hpositive hupper
        have hleft := hnotNew _ (hmem rank hpositive (by omega))
        have hright := hnotNew _ (hmem (rank + 1) (by omega) (by omega))
        have hh := hinc rank hpositive hupper
        dsimp only [Function.comp_def, contract]
        split_ifs <;> omega
      · intro rank hpositive hupper
        rw [← hcontract]
        exact List.mem_map.mpr ⟨_, hmem rank hpositive hupper, rfl⟩
      · have hh := hsub.map contract
        rw [hcontract, List.map_map] at hh
        exact hh
    have hselected : ∀ positions : List ℕ, positions.Pairwise (· < ·) →
        (∀ position ∈ positions, position < old.length) →
        (positions.map value).Sublist old := by
      intro positions horder hbound
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      let select : Fin (positions.map value).length → Fin old.length := fun index =>
        ⟨positions[index.val]'(by simpa using index.isLt),
          hbound _ (List.getElem_mem (by simpa using index.isLt))⟩
      have hmono : StrictMono select := by
        intro first second hlt
        exact List.pairwise_iff_getElem.mp horder first.val second.val
          (by simpa using first.isLt) (by simpa using second.isLt) hlt
      refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
      intro index
      simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
      change value positions[index.val] = old[(select index).val]
      dsimp only [select, value]
      exact List.getD_eq_getElem _ _ (hbound _ (List.getElem_mem (by simpa using index.isLt)))
    have htemplates : ∀ pattern ∈ basis, pattern.Perm (List.range' 1 pattern.length) :=
      by decide
    have forbid : ∀ pattern ∈ basis, ∀ positions ranks : List ℕ,
        positions.Pairwise (· < ·) → (∀ position ∈ positions, position < old.length) →
        ranks.Pairwise (· < ·) → ranks.length = pattern.length →
        pattern.map (fun rank => ranks.getD (rank - 1) 0) = positions.map value → False := by
      intro pattern hpattern positions ranks hpositions hbound hranks hlength hmatch
      let witness := fun rank => ranks.getD (rank - 1) 0
      have hsub := hselected positions hpositions hbound
      apply holdC pattern hpattern
      refine ⟨witness, ?_, ?_, ?_, by simp⟩
      · intro rank hrank hlast
        have hleft : rank - 1 < ranks.length := by omega
        have hright : rank < ranks.length := by omega
        dsimp only [witness]
        rw [Nat.add_sub_cancel, List.getD_eq_getElem _ 0 hleft,
          List.getD_eq_getElem _ 0 hright]
        exact List.pairwise_iff_getElem.mp hranks (rank - 1) rank hleft hright (by omega)
      · intro rank hrank hlast
        have hmem : rank ∈ pattern := (htemplates pattern hpattern).mem_iff.mpr
          (List.mem_range'_1.mpr ⟨hrank, by omega⟩)
        apply hsub.subset
        rw [← hmatch]
        exact List.mem_map.mpr ⟨rank, hmem, rfl⟩
      · rw [show pattern.map witness = positions.map value from hmatch]
        exact hsub
    have htable : ∀ pattern ∈ basis, 4 ≤ pattern.length ∧
        (pattern.getD 0 0 < pattern.getD 1 0 ∨
          pattern.getD 1 0 + 2 ≤ pattern.getD 0 0) ∧
        (pattern.getD 0 0 < pattern.getD 2 0 ∨
          pattern.getD 2 0 + 2 ≤ pattern.getD 0 0) := by decide
    intro pattern hpattern hocc
    obtain ⟨ranks, hinc, hmem, hsub, _⟩ := hocc
    obtain ⟨positions, hpositions⟩ :=
      List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp hsub
    obtain ⟨hsize, hpair, htriple⟩ := htable pattern hpattern
    have hstrict : ∀ first second, 1 ≤ first → second ≤ pattern.length →
        first < second →
        ranks first < ranks second := by
      have walk : ∀ upper lower, 1 ≤ lower → lower < upper → upper ≤ pattern.length →
          ranks lower < ranks upper := by
        intro upper
        induction upper with
        | zero => intro lower _ hlt _; omega
        | succ upper ih =>
          intro lower hpositive hlt hbound
          by_cases heq : lower = upper
          · subst lower; exact hinc upper hpositive (by omega)
          · exact lt_trans (ih lower hpositive (by omega) (by omega))
              (hinc upper (by omega) (by omega))
      intro first second hpositive hupper hlt
      exact walk second first hpositive hlt hupper
    have hgap : ∀ first second, 1 ≤ first → second ≤ pattern.length →
        first + 2 ≤ second →
        ranks first + 2 ≤ ranks second := by
      intro first second hpositive hupper hlt
      have hh := hinc first hpositive (by omega)
      have hs := hstrict (first + 1) second (by omega) hupper (by omega)
      omega
    have hrankBounds : ∀ index, index < pattern.length →
        1 ≤ pattern.getD index 0 ∧ pattern.getD index 0 ≤ pattern.length := by
      intro index hindex
      have hh : pattern.getD index 0 ∈ pattern := by
        rw [List.getD_eq_getElem _ 0 hindex]
        exact List.getElem_mem hindex
      have hb := List.mem_range'_1.mp ((htemplates pattern hpattern).mem_iff.mp hh)
      omega
    have hentry : ∀ index, index < pattern.length →
        expanded[positions index]? = some (ranks (pattern.getD index 0)) := by
      intro index hindex
      rw [← hpositions, List.getElem?_map, List.getElem?_eq_getElem hindex,
        Option.map_some, ← List.getD_eq_getElem _ 0 hindex]
    have hpositionBound : ∀ index, index < pattern.length → positions index < expanded.length :=
      fun index hindex => (List.getElem?_eq_some_iff.mp (hentry index hindex)).1
    have holdEntry : ∀ index, index < pattern.length → 0 < positions index →
        value (positions index - 1) = ranks (pattern.getD index 0) := by
      intro index hindex hpositive
      have hh := hentry index hindex
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_succ_of_ne_zero
        (by omega : positions index ≠ 0)
      rw [hshape, hoffset, List.getElem?_cons_succ] at hh
      dsimp only [value]
      rw [hoffset]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right,
        List.getD_eq_getElem?_getD, hh, Option.getD_some]
    have hbetaWhere : ∀ position, expanded[position]? = some beta → position = 2 := by
      intro position hget
      by_cases hzero : position = 0
      · subst position
        simp [hshape] at hget
      have hpositive : 0 < position := by omega
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : position ≠ 0)
      rw [hshape, hoffset, List.getElem?_cons_succ] at hget
      have hbound := (List.getElem?_eq_some_iff.mp hget).1
      have hvalue : value offset = beta := by
        simp only [value, List.getD_eq_getElem?_getD, hget, Option.getD_some]
      have hh := (List.getD_inj hbound (by omega : 1 < old.length) holdNodup).mp
        (hvalue.trans hbeta.symm)
      omega
    have hfirstBounds := hrankBounds 0 (by omega)
    have hsecondBounds := hrankBounds 1 (by omega)
    have hthirdBounds := hrankBounds 2 (by omega)
    have hfirst : ranks (pattern.getD 0 0) = beta + 1 := by
      by_contra hnot
      have htail : (pattern.map ranks).Sublist old := by
        cases pattern with
        | nil => simp at hsize
        | cons first tail =>
          change (ranks first :: tail.map ranks).Sublist ((beta + 1) :: old) at hsub
          exact hsub.of_cons_of_ne hnot
      apply holdC pattern hpattern
      refine ⟨ranks, hinc, ?_, htail, by simp⟩
      intro rank hpositive hupper
      apply htail.subset
      exact List.mem_map.mpr ⟨rank, (htemplates pattern hpattern).mem_iff.mpr
        (List.mem_range'_1.mpr ⟨hpositive, by omega⟩), rfl⟩
    have hfirstPosition : positions 0 = 0 := by
      by_contra hnot
      have hh := holdEntry 0 (by omega) (by omega)
      have hbound := hpositionBound 0 (by omega)
      exact hnotNew _ (hvalueMem _ (by omega)) (hh.trans hfirst)
    have hindexLower : ∀ index, index ≤ positions index := by
      intro index
      induction index with
      | zero => omega
      | succ index ih =>
        have hh := positions.strictMono (Nat.lt_succ_self index)
        change positions index < positions (index + 1) at hh
        change index + 1 ≤ positions (index + 1)
        omega
    have hnotBetaAt : ∀ index, index < pattern.length →
        ranks (pattern.getD index 0) ≠ beta := by
      intro index hindex heq
      have hwhere := hbetaWhere (positions index) (by simpa only [heq] using hentry index hindex)
      have hindexSmall : index = 1 ∨ index = 2 := by
        have hlower := hindexLower index
        by_cases hzero : index = 0
        · subst index; omega
        omega
      rcases hindexSmall with rfl | rfl
      · rcases hpair with hh | hh
        · have hs := hstrict _ _ hfirstBounds.1 hsecondBounds.2 hh
          omega
        · have hs := hgap _ _ hsecondBounds.1 hfirstBounds.2 hh
          omega
      · rcases htriple with hh | hh
        · have hs := hstrict _ _ hfirstBounds.1 hthirdBounds.2 hh
          omega
        · have hs := hgap _ _ hthirdBounds.1 hfirstBounds.2 hh
          omega
    have hnotBeta : ∀ rank, 1 ≤ rank → rank ≤ pattern.length → ranks rank ≠ beta := by
      intro rank hpositive hupper
      obtain ⟨index, hindex, heq⟩ := List.mem_iff_getElem.mp
        ((htemplates pattern hpattern).mem_iff.mpr
          (List.mem_range'_1.mpr ⟨hpositive, by omega⟩))
      have hh := hnotBetaAt index hindex
      rw [List.getD_eq_getElem _ 0 hindex, heq] at hh
      exact hh
    have hbelow : ∀ rank, 1 ≤ rank → rank < pattern.getD 0 0 → ranks rank < beta := by
      intro rank hpositive hlow
      have hh := hstrict rank _ hpositive hfirstBounds.2 hlow
      have hn := hnotBeta rank hpositive (by omega)
      omega
    have hthirdPosition : 2 < positions 2 := by
      have hh := positions.strictMono (by omega : 0 < 1)
      have hs := positions.strictMono (by omega : 1 < 2)
      have hne : positions 2 ≠ 2 := by
        intro heq
        apply hnotBetaAt 2 (by omega)
        have hv := hentry 2 (by omega)
        rw [hshape, heq] at hv
        simp only [List.getElem?_cons_succ] at hv
        have hb : old[1]? = some beta := by
          rw [List.getElem?_eq_getElem (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
          exact congrArg some hbeta
        rw [hb] at hv
        exact Option.some.inj hv.symm
      omega
    have locateBetween : beta + 1 < value 0 →
        ∃ index, 2 ≤ index ∧ index < old.length ∧
          beta + 1 < value index ∧ value index < value 0 := by
      intro hwAbove
      have hvalueFirst : value 0 = shift (permutation.getD 0 0) := by
        dsimp only [value, old]
        rw [List.getD_eq_getElem _ 0 (by simp only [List.length_map]; omega),
          List.getElem_map, ← List.getD_eq_getElem _ 0 (by omega)]
      have hfirstOld : permutation.getD 0 0 > beta + 1 := by
        dsimp only [shift] at hvalueFirst
        split_ifs at hvalueFirst <;> omega
      have hfirstUpper : permutation.getD 0 0 ≤ permutation.length := by
        have hh := List.mem_range'_1.mp (hperm.mem_iff.mp
          (List.getElem_mem (l := permutation) (n := 0) (by omega)))
        rw [← List.getD_eq_getElem permutation 0 (by omega)] at hh
        omega
      obtain ⟨index, hindex, heq⟩ := List.mem_iff_getElem.mp
        (hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨by omega, by omega⟩ :
          beta + 1 ∈ List.range' 1 permutation.length))
      have hdeltaValue : value index = beta + 2 := by
        dsimp only [value, old]
        rw [List.getD_eq_getElem _ 0 (by simpa using hindex), List.getElem_map, heq]
        simp [shift]
      have hnzero : index ≠ 0 := by
        intro heqIndex; subst index
        rw [← List.getD_eq_getElem permutation 0 (by omega)] at heq
        omega
      have hnone : index ≠ 1 := by
        intro heqIndex; subst index
        rw [← List.getD_eq_getElem permutation 0 (by omega)] at heq
        change beta = beta + 1 at heq
        omega
      refine ⟨index, by omega, by omega, by omega, ?_⟩
      dsimp only [shift] at hvalueFirst
      rw [if_pos (by omega)] at hvalueFirst
      omega
    by_cases husesSecond : positions 1 = 1
    · have hw : value 0 = ranks (pattern.getD 1 0) := by
        have hh := holdEntry 1 (by omega) (by omega)
        simpa only [husesSecond] using hh
      have hs2 := holdEntry 2 (by omega) (by omega)
      have hs3 := holdEntry 3 (by omega)
        (by have hh := positions.strictMono (by omega : 2 < 3); omega)
      have hp2 := hpositionBound 2 (by omega)
      have hp3 := hpositionBound 3 (by omega)
      have horder23 := positions.strictMono (by omega : 2 < 3)
      have hx12 := hinc 1 (by omega) (by omega)
      have hx23 := hinc 2 (by omega) (by omega)
      have hx34 := hinc 3 (by omega) (by omega)
      norm_num only at hx12 hx23 hx34
      have hn1 := hnotBeta 1 (by omega) (by omega)
      have hn2 := hnotBeta 2 (by omega) (by omega)
      have hn3 := hnotBeta 3 (by omega) (by omega)
      simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [List.getD_cons_zero, List.getD_cons_succ] at hfirst hw hs2 hs3
      · have hbetaLow : ranks 1 < beta := by omega
        have hwAbove : beta + 1 < value 0 := by omega
        obtain ⟨delta, hdLower, hdBound, hdLow, hdHigh⟩ := locateBetween hwAbove
        have hdNot2 : delta ≠ positions 2 - 1 := by intro heq; rw [heq] at hdHigh; omega
        have hdNot3 : delta ≠ positions 3 - 1 := by intro heq; rw [heq] at hdLow; omega
        by_cases hdBefore : delta < positions 2 - 1
        · exact forbid [2, 3, 4, 1] (by simp [basis])
            [1, delta, positions 2 - 1, positions 3 - 1]
            [ranks 1, beta, value delta, ranks 4]
            (by simp [List.pairwise_cons]; omega)
            (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hbeta, hs2, hs3])
        by_cases hdMiddle : delta < positions 3 - 1
        · exact forbid [4, 2, 5, 3, 1] (by simp [basis])
            [0, 1, positions 2 - 1, delta, positions 3 - 1]
            [ranks 1, beta, value delta, ranks 3, ranks 4]
            (by simp [List.pairwise_cons]; omega)
            (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs3])
        · exact forbid [4, 2, 5, 1, 3] (by simp [basis])
            [0, 1, positions 2 - 1, positions 3 - 1, delta]
            [ranks 1, beta, value delta, ranks 3, ranks 4]
            (by simp [List.pairwise_cons]; omega)
            (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs3])
      all_goals
        have hs4 := holdEntry 4 (by decide)
          (by have hh := positions.strictMono (by omega : 2 < 4); omega)
        have hp4 := hpositionBound 4 (by decide)
        have horder34 := positions.strictMono (by omega : 3 < 4)
        have hx45 := hinc 4 (by decide) (by decide)
        norm_num only at hx45
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hs4
      · exact forbid [5, 2, 3, 1, 4] (by simp [basis])
          [0, 1, positions 2 - 1, positions 3 - 1, positions 4 - 1]
          [ranks 1, beta, ranks 3, ranks 4, ranks 5]
          (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
          (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs3, hs4])
      · exact forbid [2, 3, 4, 1] (by simp [basis])
          [0, 1, positions 2 - 1, positions 3 - 1] [ranks 1, ranks 2, beta, ranks 5]
          (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
          (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs3])
      · exact forbid [2, 3, 4, 1] (by simp [basis])
          [0, 1, positions 2 - 1, positions 4 - 1] [ranks 1, ranks 2, beta, ranks 5]
          (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
          (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs4])
      · obtain ⟨delta, hdLower, hdBound, hdLow, hdHigh⟩ := locateBetween (by omega)
        have hdNot2 : delta ≠ positions 2 - 1 := by intro heq; rw [heq] at hdLow; omega
        have hdNot3 : delta ≠ positions 3 - 1 := by intro heq; rw [heq] at hdLow; omega
        have hdNot4 : delta ≠ positions 4 - 1 := by intro heq; rw [heq] at hdLow; omega
        by_cases hdBefore : delta < positions 2 - 1
        · exact forbid [4, 5, 2, 1, 3] (by simp [basis])
            [1, delta, positions 2 - 1, positions 3 - 1, positions 4 - 1]
            [ranks 1, ranks 2, ranks 3, beta, value delta]
            (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hbeta, hs2, hs3, hs4])
        by_cases hdMiddle : delta < positions 3 - 1
        · exact forbid [4, 2, 5, 1, 3] (by simp [basis])
            [1, positions 2 - 1, delta, positions 3 - 1, positions 4 - 1]
            [ranks 1, ranks 2, ranks 3, beta, value delta]
            (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hbeta, hs2, hs3, hs4])
        by_cases hdLast : delta < positions 4 - 1
        · exact forbid [6, 4, 2, 1, 5, 3] (by simp [basis])
            [0, 1, positions 2 - 1, positions 3 - 1, delta, positions 4 - 1]
            [ranks 1, ranks 2, ranks 3, beta, value delta, ranks 5]
            (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs3, hs4])
        · exact forbid [6, 4, 2, 1, 3, 5] (by simp [basis])
            [0, 1, positions 2 - 1, positions 3 - 1, positions 4 - 1, delta]
            [ranks 1, ranks 2, ranks 3, beta, value delta, ranks 5]
            (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs3, hs4])
      · obtain ⟨delta, hdLower, hdBound, hdLow, hdHigh⟩ := locateBetween (by omega)
        have hdNot2 : delta ≠ positions 2 - 1 := by intro heq; rw [heq] at hdLow; omega
        have hdNot3 : delta ≠ positions 3 - 1 := by intro heq; rw [heq] at hdLow; omega
        have hdNot4 : delta ≠ positions 4 - 1 := by intro heq; rw [heq] at hdLow; omega
        by_cases hdBefore : delta < positions 2 - 1
        · exact forbid [4, 5, 2, 3, 1] (by simp [basis])
            [1, delta, positions 2 - 1, positions 3 - 1, positions 4 - 1]
            [ranks 1, ranks 2, ranks 3, beta, value delta]
            (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hbeta, hs2, hs3, hs4])
        by_cases hdMiddle : delta < positions 3 - 1
        · exact forbid [4, 2, 5, 3, 1] (by simp [basis])
            [1, positions 2 - 1, delta, positions 3 - 1, positions 4 - 1]
            [ranks 1, ranks 2, ranks 3, beta, value delta]
            (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hbeta, hs2, hs3, hs4])
        by_cases hdLast : delta < positions 4 - 1
        · exact forbid [2, 3, 4, 1] (by simp [basis])
            [positions 2 - 1, positions 3 - 1, delta, positions 4 - 1]
            [ranks 1, ranks 2, ranks 3, value delta]
            (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hs2, hs3, hs4])
        · exact forbid [5, 2, 3, 1, 4] (by simp [basis])
            [0, positions 2 - 1, positions 3 - 1, positions 4 - 1, delta]
            [ranks 1, ranks 2, ranks 3, value delta, ranks 5]
            (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hs2, hs3, hs4])
      · have hx4beta := hbelow 4 (by decide) (by decide)
        exact forbid [2, 5, 3, 1, 4] (by simp [basis])
          [0, 1, positions 2 - 1, positions 3 - 1, positions 4 - 1]
          [ranks 1, ranks 2, ranks 3, ranks 4, beta]
          (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
          (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs3, hs4])
      · have hx4beta := hbelow 4 (by decide) (by decide)
        exact forbid [4, 5, 2, 1, 3] (by simp [basis])
          [0, 1, positions 2 - 1, positions 3 - 1, positions 4 - 1]
          [ranks 1, ranks 2, ranks 3, ranks 4, beta]
          (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
          (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs3, hs4])
      · have hx4beta := hbelow 4 (by decide) (by decide)
        have hs5 := holdEntry 5 (by decide)
          (by have hh := positions.strictMono (by omega : 4 < 5); omega)
        have hp5 := hpositionBound 5 (by decide)
        have horder45 := positions.strictMono (by omega : 4 < 5)
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hs5
        exact forbid [4, 5, 2, 1, 3] (by simp [basis])
          [0, 1, positions 2 - 1, positions 3 - 1, positions 5 - 1]
          [ranks 1, ranks 2, ranks 3, ranks 4, beta]
          (by simp [List.pairwise_cons]; omega) (by intro index hi; simp at hi; omega)
          (by simp [List.pairwise_cons]; omega) rfl (by simp [hw, hbeta, hs2, hs3, hs5])
    · have hsecondPosition : 2 < positions 1 := by
        have hlower := hindexLower 1
        have hn : positions 1 ≠ 2 := by
          intro heq
          apply hnotBetaAt 1 (by omega)
          have hh := hentry 1 (by omega)
          rw [hshape, heq] at hh
          simp only [List.getElem?_cons_succ] at hh
          have hb : old[1]? = some beta := by
            rw [List.getElem?_eq_getElem (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
            exact congrArg some hbeta
          rw [hb] at hh
          exact Option.some.inj hh.symm
        omega
      let replace := fun entry => if entry = beta + 1 then beta else entry
      let witness := replace ∘ ranks
      let select := fun index => if index = 0 then 1 else positions index - 1
      have hselectMono : StrictMono select := by
        intro first second hlt
        have horder := positions.strictMono hlt
        have hfirstLower := hindexLower first
        have hsecondLower := hindexLower second
        dsimp only [select]
        split_ifs with hfirstZero hsecondZero
        · omega
        · subst first
          have hh := positions.monotone (by omega : 1 ≤ second)
          omega
        · omega
        · omega
      have hwitnessInc : ∀ rank, 1 ≤ rank → rank < pattern.length →
          witness rank < witness (rank + 1) := by
        intro rank hpositive hupper
        have hleft := hnotBeta rank hpositive (by omega)
        have hright := hnotBeta (rank + 1) (by omega) (by omega)
        have hh := hinc rank hpositive hupper
        dsimp only [witness, Function.comp_def, replace]
        split_ifs <;> omega
      have hwitnessMem : ∀ rank, 1 ≤ rank → rank ≤ pattern.length →
          witness rank ∈ old := by
        intro rank hpositive hupper
        have hh := hmem rank hpositive hupper
        change ranks rank ∈ expanded at hh
        rw [hshape, List.mem_cons] at hh
        dsimp only [witness, Function.comp_def, replace]
        split_ifs with heq
        · exact hbetaMem
        · exact hh.resolve_left heq
      have hnewSub : (pattern.map witness).Sublist old := by
        apply List.sublist_iff_exists_orderEmbedding_getElem?_eq.mpr
        refine ⟨OrderEmbedding.ofStrictMono select hselectMono, ?_⟩
        intro index
        simp only [OrderEmbedding.coe_ofStrictMono]
        by_cases hindex : index < pattern.length
        · rw [List.getElem?_map, List.getElem?_eq_getElem hindex, Option.map_some]
          by_cases hzero : index = 0
          · subst index
            have hw : witness pattern[0] = beta := by
              rw [← List.getD_eq_getElem pattern 0 (by omega)]
              dsimp only [witness, Function.comp_def, replace]
              rw [if_pos hfirst]
            rw [hw]
            dsimp only [select]
            rw [if_pos rfl, List.getElem?_eq_getElem (by omega),
              ← List.getD_eq_getElem _ 0 (by omega)]
            exact congrArg some hbeta.symm
          · have hpositive : 0 < positions index := by have hh := hindexLower index; omega
            have hh := holdEntry index hindex hpositive
            have hb := hpositionBound index hindex
            have hnot : ranks (pattern.getD index 0) ≠ beta + 1 := by
              intro heq
              exact hnotNew _ (hvalueMem (positions index - 1) (by omega)) (hh.trans heq)
            have hw : witness pattern[index] = ranks (pattern.getD index 0) := by
              rw [← List.getD_eq_getElem pattern 0 hindex]
              dsimp only [witness, Function.comp_def, replace]
              rw [if_neg hnot]
            rw [hw]
            dsimp only [select]
            rw [if_neg hzero, List.getElem?_eq_getElem (by omega),
              ← List.getD_eq_getElem _ 0 (by omega)]
            exact congrArg some hh.symm
        · have hnone : (pattern.map witness)[index]? = none :=
            List.getElem?_eq_none (by simp only [List.length_map]; omega)
          rw [hnone]
          have hh := hpositions index
          have hnoneOld : (pattern.map ranks)[index]? = none :=
            List.getElem?_eq_none (by simp only [List.length_map]; omega)
          rw [hnoneOld] at hh
          have hb : expanded.length ≤ positions index := List.getElem?_eq_none_iff.mp hh.symm
          have hnzero : index ≠ 0 := by omega
          dsimp only [select]
          rw [if_neg hnzero, List.getElem?_eq_none (by omega)]
      exact holdC pattern hpattern ⟨witness, hwitnessInc, hwitnessMem, hnewSub, by simp⟩
  · intro hlength hsimple
    let beta := permutation.getD 1 0
    let shift := fun entry => if beta < entry then entry + 1 else entry
    let contract := fun entry => if beta < entry then entry - 1 else entry
    let expanded := W permutation
    have hshape : expanded = (beta + 1) :: permutation.map shift := rfl
    have hnewLength : expanded.length = permutation.length + 1 := by
      simp [expanded, W]
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hbounds : ∀ entry ∈ permutation, 1 ≤ entry ∧ entry ≤ permutation.length := by
      intro entry hentry
      have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hentry)
      omega
    have hbetaMem : beta ∈ permutation := by
      dsimp only [beta]
      rw [List.getD_eq_getElem _ 0 (by omega)]
      exact List.getElem_mem (by omega)
    have hbetaBounds := hbounds beta hbetaMem
    have hbetaUpper : beta < permutation.length := hsecond
    have hshiftMono : StrictMono shift := by
      intro first second hlt
      dsimp only [shift]
      split_ifs <;> omega
    have hmissing : ∀ entry, shift entry ≠ beta + 1 := by
      intro entry
      dsimp only [shift]
      split_ifs <;> omega
    have hinverse : ∀ entry, contract (shift entry) = entry := by
      intro entry
      dsimp only [contract, shift]
      split_ifs <;> omega
    have hnewNodup : expanded.Nodup := by
      rw [hshape, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨entry, _, heq⟩ := List.mem_map.mp hmem
        exact hmissing entry heq
      · exact hnodup.map hshiftMono.injective
    have hnewPerm : expanded.Perm (List.range' 1 expanded.length) := by
      apply (List.perm_ext_iff_of_nodup hnewNodup (List.nodup_range' _)).mpr
      intro entry
      rw [hnewLength, hshape]
      simp only [List.mem_cons, List.mem_map, List.mem_range'_1]
      constructor
      · rintro (rfl | ⟨old, hold, heq⟩)
        · omega
        · have hh := hbounds old hold
          dsimp only [shift] at heq
          split_ifs at heq <;> omega
      · rintro ⟨hpositive, hupper⟩
        by_cases heq : entry = beta + 1
        · exact Or.inl heq
        right
        by_cases hlow : entry ≤ beta
        · refine ⟨entry, hperm.mem_iff.mpr (List.mem_range'_1.mpr ?_), ?_⟩
          · omega
          · dsimp only [shift]; rw [if_neg (by omega)]
        · refine ⟨entry - 1, hperm.mem_iff.mpr (List.mem_range'_1.mpr ?_), ?_⟩
          · omega
          · dsimp only [shift]; rw [if_pos (by omega)]; omega
    have hsegments : ∀ start count, 0 < start →
        ((expanded.drop start).take count) =
          ((permutation.drop (start - 1)).take count).map shift := by
      intro start count hstart
      obtain ⟨index, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : start ≠ 0)
      simp [hshape, List.drop_succ_cons, ← List.map_drop, ← List.map_take]
    have hmapInverse : ∀ segment : List ℕ, (segment.map shift).map contract = segment := by
      intro segment
      simp only [List.map_map]
      have heq : contract ∘ shift = id := funext hinverse
      rw [heq, List.map_id]
    have hcontractRange : ∀ lower count, beta + 1 ∉ List.range' lower count →
        (List.range' lower count).map contract =
          List.range' (if beta < lower then lower - 1 else lower) count := by
      intro lower count hmissingRange
      have houtside : lower + count ≤ beta + 1 ∨ beta + 1 < lower := by
        simp only [List.mem_range'_1] at hmissingRange
        omega
      simp only [List.range'_eq_map_range, List.map_map]
      apply List.map_congr_left
      intro offset hoffset
      have hbound := List.mem_range.mp hoffset
      dsimp only [Function.comp_def, contract]
      rcases houtside with hbelow | habove
      · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_pos (by omega), if_pos (by omega)]
        omega
    refine ⟨by simpa only [hnewLength] using hnewPerm, ?_⟩
    change IsSimple expanded
    intro start count lower hcount hproper hbound hinterval
    by_cases hstart : 0 < start
    · have hslice : (((permutation.drop (start - 1)).take count).map shift).Perm
          (List.range' lower count) := by
        simpa only [hsegments start count hstart] using hinterval
      have hmissingRange : beta + 1 ∉ List.range' lower count := by
        intro hmem
        obtain ⟨entry, _, heq⟩ := List.mem_map.mp (hslice.mem_iff.mpr hmem)
        exact hmissing entry heq
      have hcontracted := hslice.map contract
      rw [hmapInverse, hcontractRange lower count hmissingRange] at hcontracted
      have holdBound : start - 1 + count ≤ permutation.length := by omega
      have holdProper : count < permutation.length := by
        by_contra hnot
        have hfull : count = permutation.length ∧ start = 1 := by omega
        have hall : ((permutation.drop (start - 1)).take count) = permutation := by
          rw [hfull.1, hfull.2]
          simp
        rw [hall] at hslice
        have hone : 1 ∈ permutation := hperm.mem_iff.mpr
          (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        have hmax : permutation.length ∈ permutation := hperm.mem_iff.mpr
          (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        have hlowMem : shift 1 ∈ List.range' lower count :=
          hslice.mem_iff.mp (List.mem_map.mpr ⟨1, hone, rfl⟩)
        have hhighMem : shift permutation.length ∈ List.range' lower count :=
          hslice.mem_iff.mp (List.mem_map.mpr ⟨permutation.length, hmax, rfl⟩)
        have hlowValue : shift 1 = 1 := by dsimp [shift]; rw [if_neg (by omega)]
        have hhighValue : shift permutation.length = permutation.length + 1 := by
          dsimp [shift]; rw [if_pos hbetaUpper]
        rw [hlowValue, List.mem_range'_1] at hlowMem
        rw [hhighValue, List.mem_range'_1] at hhighMem
        exact hmissingRange (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      exact hsimple (start - 1) count _ hcount holdProper holdBound hcontracted
    have hzero : start = 0 := by omega
    subst start
    have hprefix : ((expanded.drop 0).take count) =
        (beta + 1) :: (permutation.take (count - 1)).map shift := by
      obtain ⟨size, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : count ≠ 0)
      simp [hshape]
    rw [hprefix] at hinterval
    have hvRange : beta + 1 ∈ List.range' lower count :=
      hinterval.mem_iff.mp (by simp)
    have hvBounds := List.mem_range'_1.mp hvRange
    by_cases htwo : count = 2
    · subst count
      let alpha := permutation.getD 0 0
      have halphaMem : alpha ∈ permutation := by
        dsimp only [alpha]
        rw [List.getD_eq_getElem _ 0 (by omega)]
        exact List.getElem_mem (by omega)
      have hhead : permutation.take 1 = [alpha] := by
        rw [List.take_one, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        simp only [Option.toList_some]
        congr 1
        exact (List.getD_eq_getElem _ 0 (by omega)).symm
      have haRange : shift alpha ∈ List.range' lower 2 := by
        apply hinterval.mem_iff.mp
        rw [hhead]
        simp
      have haBounds := List.mem_range'_1.mp haRange
      have hdistinct : alpha ≠ beta := by
        intro heq
        have hh := (List.getD_inj (by omega : 0 < permutation.length)
          (by omega : 1 < permutation.length) hnodup).mp heq
        omega
      have halpha : alpha = beta + 1 := by
        have hneq := hmissing alpha
        dsimp only [shift] at haBounds hneq
        split_ifs at haBounds hneq <;> omega
      have hpair : permutation.take 2 = [alpha, beta] := by
        apply List.ext_getElem
        · simp only [List.length_take, List.length_cons, List.length_nil]; omega
        · intro offset hleft hright
          have hoffset : offset = 0 ∨ offset = 1 := by simp at hright; omega
          rcases hoffset with rfl | rfl
          · simp only [List.getElem_take, List.getElem_cons_zero]
            exact (List.getD_eq_getElem _ 0 (by omega)).symm
          · simp only [List.getElem_take, List.getElem_cons_succ, List.getElem_cons_zero]
            exact (List.getD_eq_getElem _ 0 (by omega)).symm
      apply hsimple 0 2 beta (by omega) (by omega) (by omega)
      rw [List.drop_zero, hpair, halpha]
      simp only [List.range'_succ, List.range'_zero]
      exact List.Perm.swap _ _ _
    have hlarge : 3 ≤ count := by omega
    have hbetaPrefix : beta ∈ permutation.take (count - 1) := by
      apply List.mem_iff_getElem?.mpr
      refine ⟨1, ?_⟩
      rw [List.getElem?_take_of_lt (by omega),
        List.getElem?_eq_getElem (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
    have hbetaRange : beta ∈ List.range' lower count := by
      apply hinterval.mem_iff.mp
      right
      have hfix : shift beta = beta := by simp [shift]
      exact List.mem_map.mpr ⟨beta, hbetaPrefix, hfix⟩
    have hbetaRangeBounds := List.mem_range'_1.mp hbetaRange
    have holdInterval : (permutation.take (count - 1)).Perm
        (List.range' lower (count - 1)) := by
      apply (List.perm_ext_iff_of_nodup hnodup.take (List.nodup_range' _)).mpr
      intro entry
      constructor
      · intro hentry
        have hshiftRange : shift entry ∈ List.range' lower count :=
          hinterval.mem_iff.mp
            (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, hentry, rfl⟩))
        have hh := List.mem_range'_1.mp hshiftRange
        have hlastMissing : lower + count - 1 ∉ permutation.take (count - 1) := by
          intro hlast
          have hlastRange : shift (lower + count - 1) ∈ List.range' lower count :=
            hinterval.mem_iff.mp
              (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, hlast, rfl⟩))
          have hlastBound := List.mem_range'_1.mp hlastRange
          dsimp only [shift] at hlastBound
          rw [if_pos (by omega)] at hlastBound
          omega
        have hnotLast : entry ≠ lower + count - 1 := by
          intro heq; subst entry; exact hlastMissing hentry
        apply List.mem_range'_1.mpr
        dsimp only [shift] at hh
        split_ifs at hh <;> omega
      · intro hentry
        have hh := List.mem_range'_1.mp hentry
        have hshiftRange : shift entry ∈ List.range' lower count := by
          apply List.mem_range'_1.mpr
          dsimp only [shift]
          split_ifs <;> omega
        rcases List.mem_cons.mp (hinterval.mem_iff.mpr hshiftRange) with heq | hmem
        · exact False.elim (hmissing entry heq)
        · obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmem
          exact hshiftMono.injective heq ▸ hold
    exact hsimple 0 (count - 1) lower (by omega) (by omega) (by omega)
      (by simpa only [List.drop_zero] using holdInterval)

end D5.S3.Combinatorics.PopStack.PopStackContinuationAvoidance
