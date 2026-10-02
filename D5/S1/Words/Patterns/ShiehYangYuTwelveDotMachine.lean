/- GID: D5/S1/Words/Patterns/ShiehYangYuTwelveDotMachine
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/ShiehYangYuTwelveDotMachine
   mirror-E: none(waiver:machine-record-cut-equivalence)
   anchors: []
   utility: none
   digest: Machine-sortable inputs correspond to avoiding words decorated by record subsets. -/

import D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ShiehYangYuTwelveDotMachine

open D5.S1.Words.Patterns.ShiehYangYuTwelveDotDefs
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotWest
open D5.S1.Words.Patterns.ShiehYangYuMachineConvergence
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs

open private westRun westRun_perm from
  D5.S1.Words.Patterns.ShiehYangYuMachineConvergence

noncomputable def machine_record_equiv (size : ℕ) :
    {input : List ℕ // input ∈ sortable (size + 1)} ≃
      {z : Σ word : List ℕ, {marks : Finset ℕ // marks ⊆ recordCuts word} //
        z.1.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] z.1} := by
  have record_fibre_equiv (initial : List ℕ) (maximum : ℕ)
      (distinct : (initial ++ [maximum]).Nodup)
      (bound : ∀ entry ∈ initial, entry < maximum) :
      {input : List ℕ // s12 input = initial ++ [maximum]} ≃
        {marks : Finset ℕ // marks ⊆ recordCuts initial} := by
    have block_split (block : List ℕ) (nonempty : block ≠ []) :
        block.dropLast ++ [block.getLastD 0] = block := by
      simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast nonempty,
        Option.getD_some] using List.dropLast_append_getLast nonempty
    have last_mem (block : List ℕ) (nonempty : block ≠ []) : block.getLastD 0 ∈ block := by
      rw [← block_split block nonempty]
      simp
    have prefix_take (value : ℕ) (member : value ∈ initial) :
        (initial ++ [maximum]).takeWhile (fun entry => decide (entry ≠ value)) =
          initial.takeWhile (fun entry => decide (entry ≠ value)) := by
      obtain ⟨before, after, split, absent⟩ := List.eq_append_cons_of_mem member
      have passed : ∀ entry ∈ before, decide (entry ≠ value) = true := by
        intro entry member
        exact decide_eq_true (fun equal => absent (equal ▸ member))
      rw [split, List.append_assoc, List.takeWhile_append_of_pos passed,
        List.takeWhile_append_of_pos passed]
      simp
    have interiors (blocks : List (List ℕ)) (distinct : blocks.flatten.Nodup)
        (nonempty : ∀ block ∈ blocks, block ≠ []) :
        ∀ block ∈ blocks, ∀ entry ∈ block.dropLast,
          entry ∉ (blocks.map (fun next => next.getLastD 0)).toFinset := by
      induction blocks with
      | nil => simp
      | cons first remaining induction =>
        have first_nonempty := nonempty first (by simp)
        have split_distinct : (first ++ remaining.flatten).Nodup := distinct
        obtain ⟨first_distinct, remaining_distinct, separated⟩ :=
          List.nodup_append.mp split_distinct
        have tail_nonempty : ∀ block ∈ remaining, block ≠ [] := by
          intro block member
          exact nonempty block (by simp [member])
        have inherited := induction remaining_distinct tail_nonempty
        intro block member entry inside selected
        obtain ⟨next, next_mem, endpoint⟩ :=
          List.mem_map.mp (List.mem_toFinset.mp selected)
        rcases List.mem_cons.mp member with same | following <;>
          rcases List.mem_cons.mp next_mem with next_same | next_mem
        · have own_distinct : (first.dropLast ++ [first.getLastD 0]).Nodup := by
            rw [block_split first first_nonempty]
            exact first_distinct
          exact (List.nodup_append.mp own_distinct).2.2
            entry (same ▸ inside) entry
            (List.mem_singleton.mpr (by rw [← next_same]; exact endpoint.symm)) rfl
        · exact separated entry (List.mem_of_mem_dropLast (same ▸ inside)) entry
            (List.mem_flatten.mpr ⟨next, next_mem, endpoint ▸
              last_mem next (tail_nonempty next next_mem)⟩) rfl
        · exact separated entry (by rw [← endpoint, next_same]; exact last_mem _ first_nonempty)
            entry (List.mem_flatten.mpr
              ⟨block, following, List.mem_of_mem_dropLast inside⟩) rfl
        · exact inherited block following entry inside
            (List.mem_toFinset.mpr (List.mem_map.mpr ⟨next, next_mem, endpoint⟩))
    refine (fibre_equiv (initial ++ [maximum])).trans
      { toFun := fun blocks =>
          ⟨(blocks.val.dropLast.map (fun block => block.getLastD 0)).toFinset, ?_⟩
        invFun := fun marks => ⟨cutBlocks marks.val (initial ++ [maximum]), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro value selected
      obtain ⟨block, member, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp selected)
      have all_distinct : blocks.val.flatten.Nodup := by
        simpa only [blocks.property.1] using distinct
      have nonempty : ∀ block ∈ blocks.val, block ≠ [] := by
        intro block member empty
        obtain ⟨leader, body, reversed, _⟩ :=
          blocks.property.2.1 block.reverse (by simp [member])
        simp [empty] at reversed
      have blocks_nonempty : blocks.val ≠ [] :=
        List.ne_nil_of_mem (List.mem_of_mem_dropLast member)
      obtain ⟨before, after, split, _⟩ := List.eq_append_cons_of_mem member
      have whole_split : blocks.val =
          before ++ block :: (after ++ [blocks.val.getLastD []]) := by
        have last_split : blocks.val.dropLast ++ [blocks.val.getLastD []] = blocks.val := by
          simpa only [List.getLastD_eq_getLast?,
            List.getLast?_eq_some_getLast blocks_nonempty, Option.getD_some]
            using List.dropLast_append_getLast blocks_nonempty
        exact last_split.symm.trans (by rw [split]; simp)
      obtain ⟨body, endpoint, shape, record⟩ := fibre_records blocks.val all_distinct
        blocks.property.2.1 blocks.property.2.2 before block _ whole_split
      have endpoint_eq : block.getLastD 0 = endpoint := by simp [shape]
      rw [endpoint_eq]
      have alphabet (entry : ℕ) (member : entry ∈ blocks.val.flatten) : entry ≤ maximum := by
        rw [blocks.property.1] at member
        rcases List.mem_append.mp member with in_prefix | final
        · exact (bound entry in_prefix).le
        · have equal : entry = maximum := by simpa using final
          omega
      have smaller : endpoint < maximum := by
        have following_nonempty : after ++ [blocks.val.getLastD []] ≠ [] := by simp
        cases following : after ++ [blocks.val.getLastD []] with
        | nil => exact (following_nonempty following).elim
        | cons next remaining =>
          have next_split : blocks.val = (before ++ [block]) ++ next :: remaining := by
            have adjusted := whole_split
            rw [following] at adjusted
            simpa only [List.append_assoc, List.singleton_append] using adjusted
          obtain ⟨inner, next_endpoint, next_shape, next_record⟩ :=
            fibre_records blocks.val all_distinct blocks.property.2.1 blocks.property.2.2
              (before ++ [block]) next remaining next_split
          have strictly := next_record endpoint (by simp [shape])
          exact strictly.trans_le (alphabet next_endpoint (by
            apply List.mem_flatten.mpr
            refine ⟨next, ?_, by simp [next_shape]⟩
            rw [next_split]
            simp only [List.mem_append, List.mem_cons]
            exact Or.inr (Or.inl trivial)))
      have endpoint_member : endpoint ∈ initial := by
        have member : endpoint ∈ blocks.val.flatten :=
          List.mem_flatten.mpr
            ⟨block, List.mem_of_mem_dropLast member, by simp [shape]⟩
        rw [blocks.property.1] at member
        rcases List.mem_append.mp member with member | final
        · exact member
        · have equal : endpoint = maximum := by simpa using final
          omega
      have whole_word : initial ++ [maximum] =
          (before.flatten ++ body) ++ endpoint ::
            (after ++ [blocks.val.getLastD []]).flatten := by
        have flattened := congrArg List.flatten whole_split
        simpa only [List.flatten_append, List.flatten_cons, shape, List.append_assoc,
          List.singleton_append] using blocks.property.1.symm.trans flattened
      have passed : ∀ entry ∈ before.flatten ++ body,
          decide (entry ≠ endpoint) = true := by
        intro entry member
        exact decide_eq_true (Nat.ne_of_lt (record entry member))
      have taken : (initial ++ [maximum]).takeWhile (fun entry => decide (entry ≠ endpoint)) =
          before.flatten ++ body := by
        rw [whole_word, List.takeWhile_append_of_pos passed]
        simp
      refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr endpoint_member, ?_⟩
      rw [← prefix_take endpoint endpoint_member, taken]
      exact record
    · have records := marks.property
      have marked : ∀ value ∈ marks.val, value ∈ initial ++ [maximum] →
          value ∈ recordCuts (initial ++ [maximum]) := by
        intro value selected _
        have record := Finset.mem_filter.mp (records selected)
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp record.1))
        · rw [prefix_take value (List.mem_toFinset.mp record.1)]
          exact record.2
      obtain ⟨shapes, ordered⟩ := record_cut_structure marks.val (initial ++ [maximum])
        distinct marked (by simpa using bound)
      refine ⟨(cut_blocks marks.val _).1, ?_, ordered⟩
      intro block member
      obtain ⟨original, original_mem, rfl⟩ := List.mem_map.mp member
      obtain ⟨body, endpoint, shape, _, body_bound⟩ := shapes original original_mem
      refine ⟨endpoint, body.reverse, by simp [shape], ?_⟩
      intro entry member
      exact (body_bound entry (List.mem_reverse.mp member)).le
    · intro blocks
      apply Subtype.ext
      have all_distinct : blocks.val.flatten.Nodup := by
        simpa only [blocks.property.1] using distinct
      have nonempty : ∀ block ∈ blocks.val, block ≠ [] := by
        intro block member empty
        obtain ⟨leader, body, reversed, _⟩ :=
          blocks.property.2.1 block.reverse (by simp [member])
        simp [empty] at reversed
      change cutBlocks (blocks.val.dropLast.map (fun block => block.getLastD 0)).toFinset
        (initial ++ [maximum]) = blocks.val
      have reconstructed : cutBlocks
          (blocks.val.dropLast.map (fun block => block.getLastD 0)).toFinset
          blocks.val.flatten = blocks.val := by
        apply cut_reconstruction _ _ nonempty
        · intro block member entry inside selected
          obtain ⟨next, next_mem, endpoint⟩ :=
            List.mem_map.mp (List.mem_toFinset.mp selected)
          exact interiors blocks.val all_distinct nonempty block member entry inside
            (List.mem_toFinset.mpr (List.mem_map.mpr
              ⟨next, List.mem_of_mem_dropLast next_mem, endpoint⟩))
        · intro block member
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨block, member, rfl⟩)
      simpa only [blocks.property.1] using reconstructed
    · intro marks
      apply Subtype.ext
      change (((cutBlocks marks.val (initial ++ [maximum])).dropLast).map
        (fun block => block.getLastD 0)).toFinset = marks.val
      rw [(cut_blocks marks.val (initial ++ [maximum])).2.2.2]
      simp only [List.dropLast_concat]
      apply Finset.inter_eq_left.mpr
      intro value selected
      exact (Finset.mem_filter.mp (marks.property selected)).1
  
  have prefix_bound (word : List ℕ) (permutation : word.Perm (List.range' 1 size)) :
      ∀ entry ∈ word, entry < size + 1 := by
    intro entry member
    obtain ⟨index, index_bound, equal⟩ := List.mem_range'.mp (permutation.mem_iff.mp member)
    omega
  have extended_perm (word : List ℕ) (permutation : word.Perm (List.range' 1 size)) :
      (word ++ [size + 1]).Perm (List.range' 1 (size + 1)) := by
    simpa only [List.range'_1_concat, Nat.add_comm] using
      permutation.append_right [size + 1]
  have extended_avoid (word : List ℕ) (permutation : word.Perm (List.range' 1 size)) :
      ¬ Occurs [2, 3, 1] (word ++ [size + 1]) ↔ ¬ Occurs [2, 3, 1] word := by
    have decomposition :=
      D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalSplit.avoids231_maxSplit_iff
        word [] (size + 1) (by simpa using prefix_bound word permutation)
        ((extended_perm word permutation).nodup_iff.mpr (List.nodup_range' 1))
    have empty_avoid : ¬ Occurs [2, 3, 1] ([] : List ℕ) := by
      rintro ⟨values, increasing, membership, sublist, _⟩
      have empty := List.sublist_nil.mp sublist
      have length := congrArg List.length empty
      simp at length
    simpa [empty_avoid] using decomposition
  have output_shape (input : List ℕ) (permutation : input.Perm (List.range' 1 (size + 1))) :
      s12 input = (s12 input).dropLast ++ [size + 1] := by
    have maximum_mem : size + 1 ∈ input := by
      apply permutation.mem_iff.mpr
      exact List.mem_range'.mpr ⟨size, by omega, by omega⟩
    obtain ⟨left, right, split, absent⟩ := List.eq_append_cons_of_mem maximum_mem
    have alphabet (entry : ℕ) (member : entry ∈ input) : entry ≤ size + 1 := by
      obtain ⟨index, index_bound, equal⟩ := List.mem_range'.mp (permutation.mem_iff.mp member)
      omega
    have left_bound : ∀ entry ∈ left, entry < size + 1 := by
      intro entry member
      have smaller := alphabet entry (by simp [split, member])
      have unequal : entry ≠ size + 1 := by
        intro equal
        exact absent (equal ▸ member)
      omega
    have right_bound : ∀ entry ∈ right, entry ≤ size + 1 := by
      intro entry member
      exact alphabet entry (by simp [split, member])
    have transformed : s12 input = (s12 left ++ right.reverse) ++ [size + 1] := by
      simp only [s12, split, peak_split_max left right (size + 1) left_bound right_bound,
        List.map_append, List.map_singleton, List.flatten_append, List.flatten_singleton,
        List.reverse_cons, List.append_assoc]
    have initial := congrArg List.dropLast transformed
    simp only [List.dropLast_concat] at initial
    exact transformed.trans
      (congrArg (fun word => word ++ [size + 1]) initial).symm
  have output_prefix_perm (input : List ℕ)
      (permutation : input.Perm (List.range' 1 (size + 1))) :
      (s12 input).dropLast.Perm (List.range' 1 size) := by
    have output_perm := (peak_structure input).2.1.trans permutation
    rw [output_shape input permutation, List.range'_1_concat] at output_perm
    apply (List.perm_append_right_iff [size + 1]).mp
    simpa only [Nat.add_comm] using output_perm
  refine
    { toFun := fun input => ?_
      invFun := fun z => ?_
      left_inv := ?_
      right_inv := ?_ }
  · let word := (s12 input.val).dropLast
    have permutation := output_prefix_perm input.val input.property.1
    have distinct := (extended_perm word permutation).nodup_iff.mpr (List.nodup_range' 1)
    have bound := prefix_bound word permutation
    let marks := record_fibre_equiv word (size + 1) distinct bound
      ⟨input.val, output_shape input.val input.property.1⟩
    have sorted : (s (s12 input.val)).Pairwise (· < ·) := by
      rw [input.property.2]
      exact List.pairwise_lt_range'
    have avoiding : ¬ Occurs [2, 3, 1] (s12 input.val) :=
      (west_criterion _ ((peak_structure input.val).2.1.trans input.property.1
        |>.nodup_iff.mpr (List.nodup_range' 1))).1 sorted
    have prefix_avoid : ¬ Occurs [2, 3, 1] word := by
      apply (extended_avoid word permutation).mp
      dsimp only [word]
      rw [← output_shape input.val input.property.1]
      exact avoiding
    exact ⟨⟨word, marks⟩, permutation, prefix_avoid⟩
  · rcases z with ⟨⟨word, marks⟩, permutation, avoiding⟩
    have output_perm := extended_perm word permutation
    have distinct := output_perm.nodup_iff.mpr (List.nodup_range' 1)
    have bound := prefix_bound word permutation
    let input := (record_fibre_equiv word (size + 1) distinct bound).symm marks
    have input_perm : input.val.Perm (List.range' 1 (size + 1)) := by
      have reversed := (peak_structure input.val).2.1.symm
      rw [input.property] at reversed
      exact reversed.trans output_perm
    have increasing : (s (word ++ [size + 1])).Pairwise (· < ·) :=
      (west_criterion _ distinct).2 ((extended_avoid word permutation).mpr avoiding)
    have stack_perm : (s (word ++ [size + 1])).Perm (List.range' 1 (size + 1)) := by
      have west_perm : (s (word ++ [size + 1])).Perm (word ++ [size + 1]) := by
        simpa [s] using westRun_perm [] (word ++ [size + 1])
      exact west_perm.trans output_perm
    have sorted : s (word ++ [size + 1]) = List.range' 1 (size + 1) :=
      List.Perm.eq_of_pairwise (by omega) increasing (List.pairwise_lt_range' 1) stack_perm
    exact ⟨input.val, input_perm, by rw [input.property, sorted]⟩
  · intro input
    apply Subtype.ext
    let word := (s12 input.val).dropLast
    have permutation := output_prefix_perm input.val input.property.1
    have distinct := (extended_perm word permutation).nodup_iff.mpr (List.nodup_range' 1)
    have bound := prefix_bound word permutation
    change ((record_fibre_equiv word (size + 1) distinct bound).symm
      ((record_fibre_equiv word (size + 1) distinct bound)
        ⟨input.val, output_shape input.val input.property.1⟩)).val = input.val
    exact congrArg Subtype.val (Equiv.symm_apply_apply
      (record_fibre_equiv word (size + 1) distinct bound)
      ⟨input.val, output_shape input.val input.property.1⟩)
  · rintro ⟨⟨word, marks⟩, permutation, avoiding⟩
    apply Subtype.ext
    have distinct := (extended_perm word permutation).nodup_iff.mpr (List.nodup_range' 1)
    have bound := prefix_bound word permutation
    let input := (record_fibre_equiv word (size + 1) distinct bound).symm marks
    refine Sigma.ext ?_ ?_
    · change (s12 input.val).dropLast = word
      rw [input.property]
      simp
    · change HEq ((record_fibre_equiv (s12 input.val).dropLast (size + 1) _ _)
        ⟨input.val, _⟩) marks
      have transport (first second : List ℕ) (same : first = second)
          (first_distinct : (first ++ [size + 1]).Nodup)
          (second_distinct : (second ++ [size + 1]).Nodup)
          (first_bound : ∀ entry ∈ first, entry < size + 1)
          (second_bound : ∀ entry ∈ second, entry < size + 1)
          (first_input : {input : List ℕ // s12 input = first ++ [size + 1]})
          (second_input : {input : List ℕ // s12 input = second ++ [size + 1]})
          (same_input : first_input.val = second_input.val) :
          HEq ((record_fibre_equiv first (size + 1) first_distinct first_bound) first_input)
            ((record_fibre_equiv second (size + 1) second_distinct second_bound) second_input) := by
        subst second
        have identical : first_input = second_input := Subtype.ext same_input
        subst second_input
        rfl
      have same : (s12 input.val).dropLast = word := by
        rw [input.property]
        simp
      have generated_distinct : ((s12 input.val).dropLast ++ [size + 1]).Nodup := by
        rw [same]
        exact distinct
      have generated_bound : ∀ entry ∈ (s12 input.val).dropLast, entry < size + 1 := by
        rw [same]
        exact bound
      refine HEq.trans (transport _ _ same generated_distinct distinct generated_bound bound
        ⟨input.val, ?_⟩ input rfl) ?_
      · rw [same]
        exact input.property
      · exact heq_of_eq (Equiv.apply_symm_apply
          (record_fibre_equiv word (size + 1) distinct bound) marks)

end D5.S1.Words.Patterns.ShiehYangYuTwelveDotMachine
