/- GID: D5/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DottedStack/ShiehYangYuTwelveDotWest
   mirror-E: none(waiver:stack-and-peak-run-structure)
   anchors: []
   utility: none
   digest: West's stack algorithm sorts precisely the distinct words avoiding 231. -/

import D5.S1.Words.Patterns.ShiehYangYuTwelveDotDefs
import D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

open private westRun westRun_perm s_split_max from
  D5.S1.Words.Patterns.ShiehYangYuMachineConvergence

namespace D5.S3.Combinatorics.DottedStack.ShiehYangYuTwelveDotWest

open D5.S1.Words.Patterns

open D5.S1.Words.Patterns.ShiehYangYuMachineConvergence
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotDefs
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs
open D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalSplit

theorem west_criterion (word : List ℕ) (distinct : word.Nodup) :
    (s word).Pairwise (· < ·) ↔ ¬ Occurs [2, 3, 1] word := by
  classical
  induction word using WellFounded.induction (measure List.length).wf with
  | h word induction =>
    cases word with
    | nil =>
      have absent : ¬ Occurs [2, 3, 1] [] := by
        rintro ⟨values, _, _, contained, _⟩
        have impossible := contained.length_le
        simp at impossible
      simp [s, westRun, absent]
    | cons head tail =>
      obtain ⟨maximum, maximum_mem, maximal⟩ :=
        (head :: tail).toFinset.exists_max_image id (by simp)
      have maximum_in : maximum ∈ head :: tail := by simpa using maximum_mem
      have bound : ∀ value ∈ head :: tail, value ≤ maximum := by simpa using maximal
      obtain ⟨left, right, split, before⟩ := List.eq_append_cons_of_mem maximum_in
      have left_distinct := distinct.sublist
        (split ▸ (List.sublist_append_left left (maximum :: right)))
      have right_distinct := distinct.sublist
        (split ▸ ((List.sublist_cons_self maximum right).trans
          (List.sublist_append_right left (maximum :: right))))
      have left_bound : ∀ value ∈ left, value < maximum := by
        intro value member
        have le := bound value (split ▸ (by simp [member]))
        exact lt_of_le_of_ne le (fun equal => before (equal ▸ member))
      have right_bound : ∀ value ∈ right, value < maximum := by
        intro value member
        have le := bound value (split ▸ (by simp [member]))
        have missing : maximum ∉ right := by
          exact (List.nodup_cons.mp
            ((List.nodup_append.mp (split ▸ distinct)).2.1)).1
        exact lt_of_le_of_ne le (fun equal => missing (equal ▸ member))
      have left_short : left.length < (head :: tail).length := by
        rw [split, List.length_append, List.length_cons]
        omega
      have right_short : right.length < (head :: tail).length := by
        rw [split, List.length_append, List.length_cons]
        omega
      have left_perm : (s left).Perm left := by
        simpa [s] using westRun_perm [] left
      have right_perm : (s right).Perm right := by
        simpa [s] using westRun_perm [] right
      have separated :
          (∀ lower ∈ s left, ∀ upper ∈ s right, lower < upper) ↔
            ∀ lower ∈ left, ∀ upper ∈ right, lower < upper := by
        constructor
        · intro ordered lower lower_mem upper upper_mem
          exact ordered lower (left_perm.mem_iff.mpr lower_mem)
            upper (right_perm.mem_iff.mpr upper_mem)
        · intro ordered lower lower_mem upper upper_mem
          exact ordered lower (left_perm.mem_iff.mp lower_mem)
            upper (right_perm.mem_iff.mp upper_mem)
      have last_bound : ∀ value ∈ s left ++ s right, value < maximum := by
        intro value member
        rcases List.mem_append.mp member with member | member
        · exact left_bound value (left_perm.mem_iff.mp member)
        · exact right_bound value (right_perm.mem_iff.mp member)
      rw [split, s_split_max left right maximum left_bound
        (fun value member => (right_bound value member).le)]
      rw [List.pairwise_append]
      simp only [List.pairwise_singleton, List.mem_singleton]
      have finishing : ∀ entry ∈ s left ++ s right, ∀ value : ℕ,
          value = maximum → entry < value := by
        intro entry member value equal
        subst value
        exact last_bound entry member
      have terminal_iff :
          ((s left ++ s right).Pairwise (· < ·) ∧ True ∧
            ∀ entry ∈ s left ++ s right, ∀ value : ℕ,
              value = maximum → entry < value) ↔
            (s left ++ s right).Pairwise (· < ·) :=
        ⟨And.left, fun initial => ⟨initial, trivial, finishing⟩⟩
      rw [terminal_iff]
      rw [List.pairwise_append, separated,
        induction left left_short left_distinct, induction right right_short right_distinct]
      exact (avoids231_maxSplit_iff left right maximum
        (by
          intro value member
          rcases List.mem_append.mp member with member | member
          · exact left_bound value member
          · exact right_bound value member)
        (split ▸ distinct)).symm

theorem peak_structure (word : List ℕ) :
    (peakRuns word).flatten = word ∧ (s12 word).Perm word ∧
      (∀ block ∈ peakRuns word, ∃ leader body,
        block = leader :: body ∧ ∀ entry ∈ body, entry ≤ leader) ∧
      (peakRuns word).Pairwise (fun earlier later =>
        ∀ entry ∈ earlier, ∀ leader body, later = leader :: body → entry < leader) := by
  fun_induction peakRuns word with
  | case1 => simp [peakRuns, s12]
  | case2 leader tail induction =>
    let test := fun entry => decide (entry ≤ leader)
    obtain ⟨partition, permutation, blocks, increasing⟩ := induction
    have body_bound : ∀ entry ∈ tail.takeWhile test, entry ≤ leader := by
      intro entry member
      simpa [test] using List.mem_takeWhile_imp member
    have later_bound : ∀ later ∈ peakRuns (tail.dropWhile test),
        ∀ next body, later = next :: body → leader < next := by
      intro later member next body equal
      cases remainder : tail.dropWhile test with
      | nil => simp [remainder, peakRuns] at member
      | cons first rest =>
        have first_large : leader < first := by
          have stopped := List.head?_dropWhile_not test tail
          simp only [remainder, List.head?_cons, test, decide_eq_false_iff_not] at stopped
          omega
        rw [remainder, peakRuns] at member
        rcases List.mem_cons.mp member with current | following
        · have same : first = next := (List.cons.inj (current.symm.trans equal)).1
          exact same ▸ first_large
        · rw [remainder, peakRuns] at increasing
          have ordered := (List.pairwise_cons.mp increasing).1 later following
          exact first_large.trans (ordered first (by simp) next body equal)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.flatten_cons, partition, List.cons_append,
        List.takeWhile_append_dropWhile]
    · have reverse_perm := (List.reverse_perm (leader :: tail.takeWhile test)).append
        permutation
      simpa only [s12, peakRuns, List.map_cons, List.flatten_cons,
        List.cons_append, List.takeWhile_append_dropWhile, test] using reverse_perm
    · intro block member
      rcases List.mem_cons.mp member with equal | following
      · exact ⟨leader, tail.takeWhile test, equal, body_bound⟩
      · exact blocks block following
    · rw [List.pairwise_cons]
      refine ⟨?_, increasing⟩
      intro later member entry entry_mem next body equal
      have large := later_bound later member next body equal
      rcases List.mem_cons.mp entry_mem with rfl | member
      · exact large
      · exact (body_bound entry member).trans_lt large


end D5.S3.Combinatorics.DottedStack.ShiehYangYuTwelveDotWest
