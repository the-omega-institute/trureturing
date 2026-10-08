/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Counting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Counting
   mirror-E: none(waiver:actual-continuation-partition)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A bounded first-entry and tail bijection partitions actual inversion continuations. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Counting

theorem continuation_card_succ (patterns : List (List ℕ)) (word : List ℕ) (depth : ℕ) :
    {suffix : List ℕ | suffix.length = depth + 1 ∧
      word ++ suffix ∈ InversionSeqDefs.avoiders (word.length + (depth + 1)) patterns}.ncard =
      ∑ value ∈ Finset.range (word.length + 1),
        {suffix : List ℕ | suffix.length = depth ∧
          (word ++ [value]) ++ suffix ∈
            InversionSeqDefs.avoiders ((word ++ [value]).length + depth) patterns}.ncard := by
  classical
  let continuations (initial : List ℕ) (length : ℕ) : Set (List ℕ) :=
    {suffix | suffix.length = length ∧
      initial ++ suffix ∈ InversionSeqDefs.avoiders (initial.length + length) patterns}
  have hfinite (initial : List ℕ) (length : ℕ) : (continuations initial length).Finite := by
    let enumerate (values : Fin length → Fin (initial.length + length + 1)) : List ℕ :=
      List.ofFn fun index => (values index).val
    apply (Set.finite_range enumerate).subset
    intro suffix hsuffix
    have hlength : suffix.length = length := hsuffix.1
    have hbound (index : ℕ) (hindex : index < length) :
        suffix.getD index 0 < initial.length + length + 1 := by
      have hinversion := hsuffix.2.2.1 (initial.length + index)
        (by simp only [List.length_append, hlength]; omega)
      rw [List.getD_append_right _ _ _ _ (by omega)] at hinversion
      simp only [Nat.add_sub_cancel_left] at hinversion
      omega
    let values (index : Fin length) : Fin (initial.length + length + 1) :=
      ⟨suffix.getD index.val 0, hbound index.val index.is_lt⟩
    refine ⟨values, ?_⟩
    apply List.ext_getElem
    · simpa [enumerate] using hlength.symm
    · intro index henumerate hsuffixIndex
      simp [enumerate, values, List.getD, hsuffixIndex]
  have hdecompose (suffix : List ℕ) (hlength : suffix.length = depth + 1) :
      suffix = suffix.getD 0 0 :: suffix.tail := by
    cases suffix with
    | nil => simp at hlength
    | cons value suffix => rfl
  let parents := continuations word (depth + 1)
  let children (value : Fin (word.length + 1)) := continuations (word ++ [value.val]) depth
  have hfirst (suffix : parents) : suffix.val.getD 0 0 < word.length + 1 := by
    have hlength : suffix.val.length = depth + 1 := suffix.property.1
    have hinversion := suffix.property.2.2.1 word.length
      (by simp only [List.length_append, hlength]; omega)
    rw [List.getD_append_right _ _ _ _ (by omega)] at hinversion
    simpa using Nat.lt_succ_of_le hinversion
  let split (suffix : parents) : Σ value : Fin (word.length + 1), children value :=
    ⟨⟨suffix.val.getD 0 0, hfirst suffix⟩,
      ⟨suffix.val.tail, by
        have hlength : suffix.val.length = depth + 1 := suffix.property.1
        constructor
        · simp [List.length_tail, hlength]
        · have hparent := suffix.property.2
          change (word ++ [suffix.val.getD 0 0]) ++ suffix.val.tail ∈
            InversionSeqDefs.avoiders ((word ++ [suffix.val.getD 0 0]).length + depth)
              patterns
          rw [List.append_assoc, List.singleton_append, ← hdecompose suffix.val hlength]
          simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hparent⟩⟩
  let join (child : Σ value : Fin (word.length + 1), children value) : parents :=
    ⟨child.1.val :: child.2.val, by
      have hlength : child.2.val.length = depth := child.2.property.1
      constructor
      · simp [hlength]
      · have hchild := child.2.property.2
        change word ++ child.1.val :: child.2.val ∈
          InversionSeqDefs.avoiders (word.length + (depth + 1)) patterns
        simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchild⟩
  let equivalence : parents ≃ Σ value : Fin (word.length + 1), children value :=
    { toFun := split
      invFun := join
      left_inv := by
        intro suffix
        apply Subtype.ext
        exact (hdecompose suffix.val suffix.property.1).symm
      right_inv := by
        rintro ⟨value, suffix⟩
        rfl }
  let : Fintype parents := (hfinite word (depth + 1)).fintype
  let : ∀ value : Fin (word.length + 1), Fintype (children value) :=
    fun value => (hfinite (word ++ [value.val]) depth).fintype
  have hcard := Fintype.card_congr equivalence
  simp only [Fintype.card_sigma, Set.fintypeCard_eq_ncard] at hcard
  change parents.ncard = ∑ value : Fin (word.length + 1),
    (continuations (word ++ [value.val]) depth).ncard at hcard
  rw [Fin.sum_univ_eq_sum_range
    (fun value => (continuations (word ++ [value]) depth).ncard) (word.length + 1)] at hcard
  exact hcard

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Counting
