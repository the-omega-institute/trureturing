/- GID: D5/S1/Words/Patterns/ShiehYangYuTwelveDotFibre
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/ShiehYangYuTwelveDotFibre
   mirror-E: none(waiver:record-endpoint-cut-reconstruction)
   anchors: [mathlib/module/Mathlib.Data.List.SplitBy]
   utility: none
   digest: Ordered peak partitions describe entire fibres and recover selected cut endpoints. -/

import D5.S1.Words.Patterns.ShiehYangYuTwelveDotWest
import D5.S3.Combinatorics.ArrowWilfDefs
import Mathlib.Data.List.SplitBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre

open ShiehYangYuTwelveDotDefs ShiehYangYuTwelveDotWest

def fibre_equiv (output : List ℕ) :
    {input : List ℕ // s12 input = output} ≃
      {blocks : List (List ℕ) // blocks.flatten = output ∧
        (∀ block ∈ blocks.map List.reverse, ∃ leader body,
          block = leader :: body ∧ ∀ entry ∈ body, entry ≤ leader) ∧
        (blocks.map List.reverse).Pairwise (fun earlier later =>
          ∀ entry ∈ earlier, ∀ leader body, later = leader :: body → entry < leader)} := by
  have reconstruction (blocks : List (List ℕ))
      (bounded : ∀ block ∈ blocks, ∃ leader body,
        block = leader :: body ∧ ∀ entry ∈ body, entry ≤ leader)
      (ordered : blocks.Pairwise (fun earlier later =>
        ∀ entry ∈ earlier, ∀ leader body, later = leader :: body → entry < leader)) :
      peakRuns blocks.flatten = blocks := by
    induction blocks with
    | nil => simp [peakRuns]
    | cons block remaining induction =>
      obtain ⟨leader, body, rfl, body_bound⟩ := bounded block (by simp)
      obtain ⟨next_bound, remaining_ordered⟩ := List.pairwise_cons.mp ordered
      have remaining_bounded : ∀ block ∈ remaining, ∃ leader body,
          block = leader :: body ∧ ∀ entry ∈ body, entry ≤ leader := by
        intro block member
        exact bounded block (by simp [member])
      let test := fun entry => decide (entry ≤ leader)
      have remaining_take : remaining.flatten.takeWhile test = [] := by
        cases remaining with
        | nil => simp
        | cons next rest =>
          obtain ⟨next_leader, next_body, rfl, _⟩ := remaining_bounded next (by simp)
          have large := next_bound (next_leader :: next_body) (by simp)
            leader (by simp) next_leader next_body rfl
          simp [List.flatten_cons, test, Nat.not_le.mpr large]
      have remaining_drop : remaining.flatten.dropWhile test = remaining.flatten := by
        cases remaining with
        | nil => simp
        | cons next rest =>
          obtain ⟨next_leader, next_body, rfl, _⟩ := remaining_bounded next (by simp)
          have large := next_bound (next_leader :: next_body) (by simp)
            leader (by simp) next_leader next_body rfl
          simp [List.flatten_cons, test, Nat.not_le.mpr large]
      have cut_aux (entries : List ℕ) (entries_bound : ∀ entry ∈ entries, entry ≤ leader) :
          (entries ++ remaining.flatten).takeWhile test = entries ∧
            (entries ++ remaining.flatten).dropWhile test = remaining.flatten := by
        induction entries with
        | nil => exact ⟨remaining_take, remaining_drop⟩
        | cons entry rest induction =>
          have passed : test entry = true := by
            simpa [test] using entries_bound entry (by simp)
          have tail_bound : ∀ entry ∈ rest, entry ≤ leader := by
            intro entry member
            exact entries_bound entry (by simp [member])
          simpa only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons,
            passed, Bool.true_eq, if_true, List.cons.injEq, true_and] using induction tail_bound
      have cut := cut_aux body body_bound
      simp only [List.flatten_cons, List.cons_append, peakRuns]
      rw [cut.1, cut.2, induction remaining_bounded remaining_ordered]
  have twice (blocks : List (List ℕ)) :
      (blocks.map List.reverse).map List.reverse = blocks := by
    simp
  refine
    { toFun := fun input => ⟨(peakRuns input.val).map List.reverse, ?_⟩
      invFun := fun blocks => ⟨(blocks.val.map List.reverse).flatten, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have run_structure := peak_structure input.val
    refine ⟨input.property, ?_, ?_⟩
    · rw [twice]
      exact run_structure.2.2.1
    · rw [twice]
      exact run_structure.2.2.2
  · unfold s12
    rw [reconstruction (blocks.val.map List.reverse) blocks.property.2.1 blocks.property.2.2]
    rw [twice]
    exact blocks.property.1
  · intro input
    apply Subtype.ext
    change (((peakRuns input.val).map List.reverse).map List.reverse).flatten = input.val
    rw [twice]
    exact (peak_structure input.val).1
  · intro blocks
    apply Subtype.ext
    change (peakRuns (blocks.val.map List.reverse).flatten).map List.reverse = blocks.val
    rw [reconstruction (blocks.val.map List.reverse) blocks.property.2.1 blocks.property.2.2]
    exact twice blocks.val

def recordCuts (word : List ℕ) : Finset ℕ :=
  word.toFinset.filter fun value =>
    D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax word (word.idxOf value)


end D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre
