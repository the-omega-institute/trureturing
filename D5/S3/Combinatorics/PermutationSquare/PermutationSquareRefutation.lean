/- GID: D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation
   mirror-E: none(waiver:component-count-refutes-recurrence)
   anchors: [mathlib/module/Mathlib.Data.List.Sublists]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.claim; result=D5/S3/Combinatorics/PermutationSquare/PermutationSquareRefutation.result; claim=D5/S3/Combinatorics/PermutationSquare/PermutationSquareDefs.claim
   digest: A verified maximum-insertion search gives nine components at size eleven, not ten. -/

import D5.S3.Combinatorics.PermutationSquare.PermutationSquareCounting
import Mathlib.Data.List.Sublists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PermutationSquare.PermutationSquareRefutation

open D5.S3.Combinatorics Nonnesting NonnestingBasicSum
open PermutationSquareDefs PermutationSquareStructure

def componentCandidates : ℕ → List (List ℕ)
  | 0 => [[1]]
  | size + 1 => (componentCandidates size).flatMap fun word =>
      (List.range 3).filterMap fun offset =>
        let suffix := offset + 1
        let cut := word.length - suffix
        if suffix ≤ word.length ∧ (word.drop cut).Pairwise (fun first last => last < first)
        then some (word.take cut ++ (size + 2) :: word.drop cut) else none

theorem component_candidates_complete (size : ℕ) (word : List ℕ)
    (hperm : word.Perm (List.range' 1 (size + 1))) (hend : word.getLast? = some 1)
    (h312 : ¬ NonnestingDefs.Occurs [3, 1, 2] word)
    (h54321 : ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1] word) :
    word ∈ componentCandidates size := by
  induction size generalizing word with
  | zero =>
    have : word = [1] := by simpa using hperm
    simp [componentCandidates, this]
  | succ size ih =>
    have hmaximum : size + 2 ∈ word := by
      apply hperm.mem_iff.mpr
      simp only [List.mem_range', Nat.one_mul]
      exact ⟨size + 1, by omega, by omega⟩
    obtain ⟨left, right, heq, _⟩ := List.eq_append_cons_of_mem hmaximum
    have hnd := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hbound (value : ℕ) (hv : value ∈ right) : value < size + 2 := by
      have hm := hperm.mem_iff.mp (show value ∈ word by simp [heq, hv])
      simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨offset, hoffset, hvalue⟩ := hm
      have hne : value ≠ size + 2 := by
        rw [heq, List.nodup_append] at hnd
        intro hequal
        exact (List.nodup_cons.mp hnd.2.1).1 (hequal ▸ hv)
      omega
    have hright : right ≠ [] := by
      intro hnil
      simp [heq, hnil] at hend
    have hrend : right.getLast? = some 1 := by
      rw [heq, List.getLast?_append, List.getLast?_cons_of_ne_nil hright] at hend
      cases hlast : right.getLast? with
      | none => exact False.elim (hright (List.getLast?_eq_none_iff.mp hlast))
      | some value => simpa [hlast] using hend
    have hdecreasing : right.Pairwise (fun first last => last < first) := by
      apply List.pairwise_of_forall_sublist
      intro first last hsub
      have hfirst := hbound first (hsub.subset (by simp))
      have hlast := hbound last (hsub.subset (by simp))
      have hdistinct : first ≠ last := by
        have hrightnd : right.Nodup := by
          rw [heq, List.nodup_append] at hnd
          exact (List.nodup_cons.mp hnd.2.1).2
        simpa using (hrightnd.sublist hsub)
      by_contra hnot
      have hlt : first < last := by omega
      apply h312
      let values : ℕ → ℕ := fun rank =>
        if rank = 1 then first else if rank = 2 then last else size + 2
      refine ⟨values, ?_, ?_, ?_, by simp⟩
      · intro rank hrank hupper
        change rank < 3 at hupper
        have : rank = 1 ∨ rank = 2 := by omega
        rcases this with rfl | rfl <;> simp [values, hlt, hlast]
      · intro rank hrank hupper
        change rank ≤ 3 at hupper
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl
        · simp [values, heq, hsub.subset (by simp : first ∈ [first, last])]
        · simp [values, heq, hsub.subset (by simp : last ∈ [first, last])]
        · simp [values, heq]
      · change [size + 2, first, last].Sublist word
        rw [heq]
        exact (List.Sublist.cons_cons _ hsub).trans (List.sublist_append_right _ _)
    have hshort : right.length ≤ 3 := by
      by_contra hnot
      cases right with
      | nil => simp at hnot
      | cons first rest =>
        cases rest with
        | nil => simp at hnot
        | cons second rest =>
          cases rest with
          | nil => simp at hnot
          | cons third rest =>
            cases rest with
            | nil => simp at hnot
            | cons fourth rest =>
              have hfirst := hbound first (by simp)
              simp only [List.pairwise_cons, List.mem_cons, List.mem_cons,
                List.mem_cons, forall_eq_or_imp] at hdecreasing
              have h12 : second < first := hdecreasing.1.1
              have h23 : third < second := hdecreasing.2.1.1
              have h34 : fourth < third := hdecreasing.2.2.1.1
              apply h54321
              let values : ℕ → ℕ := fun rank =>
                if rank = 1 then fourth else if rank = 2 then third
                else if rank = 3 then second else if rank = 4 then first else size + 2
              refine ⟨values, ?_, ?_, ?_, by simp⟩
              · intro rank hrank hupper
                change rank < 5 at hupper
                have : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
                rcases this with rfl | rfl | rfl | rfl <;>
                  simp [values, h12, h23, h34, hfirst]
              · intro rank hrank hupper
                change rank ≤ 5 at hupper
                have : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 ∨ rank = 5 := by
                  omega
                rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [values, heq]
              · change [size + 2, first, second, third, fourth].Sublist word
                rw [heq]
                exact (List.prefix_append _ rest).sublist.trans
                  (List.sublist_append_right left _)
    let parent := left ++ right
    have hparentperm : parent.Perm (List.range' 1 (size + 1)) := by
      have hfront : ((size + 2) :: parent).Perm word := by
        rw [heq]
        exact List.perm_middle.symm
      have hrange : ((size + 2) :: List.range' 1 (size + 1)).Perm
          (List.range' 1 (size + 1 + 1)) := by
        conv_rhs => rw [List.range'_concat]
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (List.perm_middle (l₁ := List.range' 1 (size + 1))
          (l₂ := []) (a := size + 2)).symm
      exact (hfront.trans hperm |>.trans hrange.symm).cons_inv
    have hsub : parent.Sublist word := by
      rw [heq]
      exact List.Sublist.append (List.Sublist.refl left)
        (List.Sublist.cons _ (List.Sublist.refl right))
    have hparentend : parent.getLast? = some 1 := by
      simp [parent, List.getLast?_append, hrend]
    have hparent312 : ¬ NonnestingDefs.Occurs [3, 1, 2] parent := by
      rintro ⟨values, hmono, hmem, hpattern, haux⟩
      exact h312 ⟨values, hmono, fun rank hr hu => hsub.subset (hmem rank hr hu),
        hpattern.trans hsub, by simp⟩
    have hparent54321 : ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1] parent := by
      rintro ⟨values, hmono, hmem, hpattern, haux⟩
      exact h54321 ⟨values, hmono, fun rank hr hu => hsub.subset (hmem rank hr hu),
        hpattern.trans hsub, by simp⟩
    have hmember := ih parent hparentperm hparentend hparent312 hparent54321
    have hpositive : 0 < right.length := List.length_pos_iff.mpr hright
    have hcut : parent.length - (right.length - 1 + 1) = left.length := by
      simp only [parent, List.length_append]
      omega
    have htake : parent.take left.length = left := by simp [parent]
    have hdrop : parent.drop left.length = right := by simp [parent]
    simp only [componentCandidates, List.mem_flatMap]
    refine ⟨parent, hmember, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨right.length - 1, List.mem_range.mpr (by omega), ?_⟩
    simp only [hcut, htake, hdrop]
    have hcondition : right.length - 1 + 1 ≤ parent.length ∧
        right.Pairwise (fun first last => last < first) := by
      exact ⟨by simp only [parent, List.length_append]; omega, hdecreasing⟩
    simp [hcondition, heq]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem result : ¬ PermutationSquareDefs.claim := by
  let test132 : List ℕ → Bool := fun
    | [first, middle, last] => decide (first < last ∧ last < middle)
    | _ => false
  let test312 : List ℕ → Bool := fun
    | [first, middle, last] => decide (middle < last ∧ last < first)
    | _ => false
  let clear132 := fun word : List ℕ => !(word.sublistsLen 3).any test132
  let clear312 := fun word : List ℕ => !(word.sublistsLen 3).any test312
  let clear54321 := fun word : List ℕ =>
    !(word.sublistsLen 5).any (fun subword =>
      decide (subword.Pairwise (fun first last => last < first)))
  have h132 (word : List ℕ) :
      (word.sublistsLen 3).any test132 = true ↔ NonnestingDefs.Occurs [1, 3, 2] word := by
    constructor
    · intro hbad
      obtain ⟨subword, hmember, htest⟩ := List.any_eq_true.mp hbad
      obtain ⟨hsub, hlength⟩ := List.mem_sublistsLen.mp hmember
      rcases subword with _ | ⟨first, subword⟩
      · simp at hlength
      rcases subword with _ | ⟨middle, subword⟩
      · simp at hlength
      rcases subword with _ | ⟨last, subword⟩
      · simp at hlength
      have hnil : subword = [] := by simpa using hlength
      subst subword
      have horder : first < last ∧ last < middle := by simpa [test132] using htest
      let values : ℕ → ℕ := fun rank =>
        if rank = 1 then first else if rank = 2 then last else middle
      refine ⟨values, ?_, ?_, ?_, by simp⟩
      · intro rank hrank hupper
        change rank < 3 at hupper
        have : rank = 1 ∨ rank = 2 := by omega
        rcases this with rfl | rfl <;> simp [values, horder.1, horder.2]
      · intro rank hrank hupper
        change rank ≤ 3 at hupper
        have : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        rcases this with rfl | rfl | rfl <;>
          simp [values, hsub.subset (by simp : first ∈ [first, middle, last]),
            hsub.subset (by simp : middle ∈ [first, middle, last]),
            hsub.subset (by simp : last ∈ [first, middle, last])]
      · simpa [values] using hsub
    · rintro ⟨values, hmono, _, hsub, _⟩
      have h12 : values 1 < values 2 := hmono 1 (by omega) (by decide)
      have h23 : values 2 < values 3 := hmono 2 (by omega) (by decide)
      apply List.any_eq_true.mpr
      refine ⟨[values 1, values 3, values 2], ?_, ?_⟩
      · apply List.mem_sublistsLen.mpr
        exact ⟨by simpa using hsub, by simp⟩
      · simp [test132, h12, h23]
  have hclear132 (word : List ℕ) :
      clear132 word = true ↔ ¬ NonnestingDefs.Occurs [1, 3, 2] word := by
    simpa [clear132] using not_congr (h132 word)
  have hclear312 (word : List ℕ) (hclear : clear312 word = true) :
      ¬ NonnestingDefs.Occurs [3, 1, 2] word := by
    rintro ⟨values, hmono, _, hsub, _⟩
    have h12 : values 1 < values 2 := hmono 1 (by omega) (by decide)
    have h23 : values 2 < values 3 := hmono 2 (by omega) (by decide)
    have hbad : (word.sublistsLen 3).any test312 = true := by
      apply List.any_eq_true.mpr
      refine ⟨[values 3, values 1, values 2], ?_, ?_⟩
      · apply List.mem_sublistsLen.mpr
        exact ⟨by simpa using hsub, by simp⟩
      · simp [test312, h12, h23]
    simp [clear312, hbad] at hclear
  have hclear54321 (word : List ℕ) (hclear : clear54321 word = true) :
      ¬ NonnestingDefs.Occurs [5, 4, 3, 2, 1] word := by
    rintro ⟨values, hmono, _, hsub, _⟩
    have h12 : values 1 < values 2 := hmono 1 (by omega) (by decide)
    have h23 : values 2 < values 3 := hmono 2 (by omega) (by decide)
    have h34 : values 3 < values 4 := hmono 3 (by omega) (by decide)
    have h45 : values 4 < values 5 := hmono 4 (by omega) (by decide)
    have hbad : (word.sublistsLen 5).any (fun subword =>
        decide (subword.Pairwise (fun first last => last < first))) = true := by
      apply List.any_eq_true.mpr
      refine ⟨[values 5, values 4, values 3, values 2, values 1], ?_, ?_⟩
      · apply List.mem_sublistsLen.mpr
        exact ⟨by simpa using hsub, by simp⟩
      · simp only [decide_eq_true_eq]
        simp [List.pairwise_cons]
        omega
    simp [clear54321, hbad] at hclear
  let nine : List (List ℕ) :=
    [[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1],
     [2, 4, 3, 5, 6, 7, 8, 9, 10, 11, 1],
     [2, 5, 4, 3, 6, 7, 8, 9, 10, 11, 1],
     [2, 5, 4, 7, 6, 3, 8, 9, 10, 11, 1],
     [2, 5, 4, 7, 6, 9, 8, 3, 10, 11, 1],
     [4, 3, 5, 6, 7, 8, 9, 10, 11, 2, 1],
     [4, 3, 5, 7, 6, 9, 8, 11, 10, 2, 1],
     [4, 3, 6, 5, 8, 7, 10, 9, 2, 11, 1],
     [4, 3, 6, 7, 5, 8, 9, 10, 11, 2, 1]]
  have hexhaust : (componentCandidates 10).filter (fun word => clear132 (square word)) =
      nine := by decide +kernel
  have hvalid : ∀ word ∈ nine, word.Perm (List.range' 1 11) ∧
      word.getLast? = some 1 ∧ clear312 word = true ∧ clear54321 word = true ∧
      clear132 (square word) = true := by decide +kernel
  have hset : {word : List ℕ | word ∈ avoiders 11 ∧ sumIndecomposable word} =
      (nine.toFinset : Set (List ℕ)) := by
    ext word
    constructor
    · rintro ⟨hword, hindecomp⟩
      have hlength : word.length = 11 := by simpa using hword.1.length_eq
      have hnonempty : word ≠ [] := by intro hnil; simp [hnil] at hlength
      have hend := component_ends_one word hnonempty (by simpa [hlength] using hword.1)
        hindecomp hword.2.1
      have hcandidates := component_candidates_complete 10 word hword.1 hend
        hword.2.1 hword.2.2.1
      have hmember : word ∈ (componentCandidates 10).filter
          (fun word => clear132 (square word)) :=
        List.mem_filter.mpr ⟨hcandidates, (hclear132 _).mpr hword.2.2.2⟩
      rw [hexhaust] at hmember
      simpa using hmember
    · intro hmember
      have hmember' : word ∈ nine := by simpa using hmember
      obtain ⟨hperm, hend, h312, h54321, hsquare⟩ := hvalid word hmember'
      refine ⟨⟨hperm, hclear312 word h312, hclear54321 word h54321,
        (hclear132 _).mp hsquare⟩, ?_⟩
      have hlength : word.length = 11 := by simpa using hperm.length_eq
      intro cut hpositive
      have hcut : cut.val < word.length := cut.is_lt
      let first : Fin (word.take cut.val).length := ⟨0, by
        simp only [List.length_take]
        omega⟩
      let suffix := word.drop cut.val
      have hsuffix : 0 < suffix.length := by
        simp only [suffix, List.length_drop]
        omega
      let last : Fin suffix.length := ⟨suffix.length - 1, by omega⟩
      have hsuffixend : suffix.getLast? = some 1 := by
        simp [suffix, List.getLast?_drop, Nat.not_le.mpr hcut, hend]
      have hsuffixne : suffix ≠ [] := List.length_pos_iff.mp hsuffix
      have hlast : suffix.get last = 1 := by
        have heq : suffix.getLast hsuffixne = 1 :=
          Option.some.inj ((List.getLast?_eq_some_getLast hsuffixne).symm.trans hsuffixend)
        simpa [last, List.getLast_eq_getElem] using heq
      refine ⟨first, last, ?_⟩
      change suffix.get last ≤ (word.take cut.val).get first
      rw [hlast]
      have hfirstmem : (word.take cut.val).get first ∈ word :=
        (List.take_sublist _ _).subset (List.get_mem _ first)
      have hrange := hperm.mem_iff.mp hfirstmem
      simp only [List.mem_range', Nat.one_mul] at hrange
      obtain ⟨offset, _, heq⟩ := hrange
      omega
  have hcount : {word : List ℕ | word ∈ avoiders 11 ∧ sumIndecomposable word}.ncard =
      9 := by
    rw [hset, Set.ncard_coe_finset]
    decide +kernel
  intro hclaim
  have hrecurrence := PermutationSquareCounting.count_recurrence 11 (by omega)
  rw [hcount] at hrecurrence
  have hwrong := hclaim 11 (by omega)
  norm_num at hrecurrence hwrong
  omega

end D5.S3.Combinatorics.PermutationSquare.PermutationSquareRefutation
