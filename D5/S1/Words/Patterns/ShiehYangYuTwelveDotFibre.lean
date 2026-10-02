/- GID: D5/S1/Words/Patterns/ShiehYangYuTwelveDotFibre
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/ShiehYangYuTwelveDotFibre
   mirror-E: none(waiver:record-endpoint-cut-reconstruction)
   anchors: []
   utility: none
   digest: Ordered peak partitions describe entire fibres and recover selected cut endpoints. -/

import D5.S1.Words.Patterns.ShiehYangYuTwelveDotWest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre

open ShiehYangYuTwelveDotDefs ShiehYangYuTwelveDotWest

def cutBlocks (marks : Finset ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | entry :: tail =>
      if entry ∈ marks then [entry] :: cutBlocks marks tail
      else
        match cutBlocks marks tail with
        | [] => [[entry]]
        | block :: remaining => (entry :: block) :: remaining

theorem cut_blocks (marks : Finset ℕ) (word : List ℕ) :
    (cutBlocks marks word).flatten = word ∧
      (∀ block ∈ cutBlocks marks word, block ≠ []) ∧
      (∀ block ∈ cutBlocks marks word, ∀ entry ∈ block.dropLast, entry ∉ marks) ∧
      (((cutBlocks marks word).dropLast).map (fun block => block.getLastD 0)).toFinset =
        marks ∩ word.dropLast.toFinset := by
  induction word with
  | nil => simp [cutBlocks]
  | cons entry tail induction =>
    obtain ⟨partition, nonempty, interior, endpoints⟩ := induction
    by_cases marked : entry ∈ marks
    · rw [cutBlocks, if_pos marked]
      refine ⟨by simp [partition], ?_, ?_, ?_⟩
      · intro block member
        rcases List.mem_cons.mp member with rfl | member
        · simp
        · exact nonempty block member
      · intro block member value value_mem
        rcases List.mem_cons.mp member with rfl | member
        · simp at value_mem
        · exact interior block member value value_mem
      · cases tail with
        | nil => simp [cutBlocks]
        | cons next rest =>
          have remaining_nonempty : cutBlocks marks (next :: rest) ≠ [] := by
            intro empty
            rw [empty] at partition
            simp at partition
          cases blocks : cutBlocks marks (next :: rest) with
          | nil => exact (remaining_nonempty blocks).elim
          | cons first following =>
            simp only [blocks, List.dropLast_cons_cons, List.map_cons, List.toFinset_cons,
              List.getLastD_cons, List.getLastD_nil] at endpoints ⊢
            rw [endpoints]
            ext value
            simp only [Finset.mem_insert, Finset.mem_inter, List.mem_toFinset]
            constructor
            · rintro (rfl | ⟨selected, contained⟩)
              · exact ⟨marked, Or.inl rfl⟩
              · exact ⟨selected, Or.inr contained⟩
            · rintro ⟨selected, equal | contained⟩
              · exact Or.inl equal
              · exact Or.inr ⟨selected, contained⟩
    · rw [cutBlocks, if_neg marked]
      cases blocks : cutBlocks marks tail with
      | nil =>
        have empty_tail : tail = [] := by simpa [blocks] using partition.symm
        subst tail
        simp
      | cons first following =>
        have first_nonempty : first ≠ [] := nonempty first (by simp [blocks])
        have first_interior : ∀ value ∈ first.dropLast, value ∉ marks := by
          intro value member
          exact interior first (by simp [blocks]) value member
        have tail_nonempty : tail ≠ [] := by
          intro empty
          have flattened : first ++ following.flatten = [] := by
            rw [blocks, List.flatten_cons] at partition
            exact partition.trans empty
          exact first_nonempty (List.append_eq_nil_iff.mp flattened).1
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa only [blocks, List.flatten_cons, List.cons_append] using
            congrArg (entry :: ·) partition
        · intro block member
          rcases List.mem_cons.mp member with rfl | member
          · simp
          · exact nonempty block (by simp [blocks, member])
        · intro block member value value_mem
          rcases List.mem_cons.mp member with rfl | member
          · rw [List.dropLast_cons_of_ne_nil first_nonempty] at value_mem
            rcases List.mem_cons.mp value_mem with rfl | member
            · exact marked
            · exact first_interior value member
          · exact interior block (by simp [blocks, member]) value value_mem
        · have same_endpoint : (entry :: first).getLastD 0 = first.getLastD 0 := by
            cases first with
            | nil => exact (first_nonempty rfl).elim
            | cons value rest => simp
          cases following with
          | nil =>
            have no_endpoints : marks ∩ tail.dropLast.toFinset = ∅ := by
              simpa [blocks] using endpoints.symm
            rw [List.dropLast_cons_of_ne_nil tail_nonempty]
            simp only [List.dropLast_singleton, List.map_nil, List.toFinset_nil,
              List.toFinset_cons, Finset.inter_insert_of_notMem marked, no_endpoints]
          | cons next rest =>
            rw [blocks] at endpoints
            simp only [List.dropLast_cons_cons, List.map_cons, List.toFinset_cons]
              at endpoints ⊢
            rw [same_endpoint, endpoints, List.dropLast_cons_of_ne_nil tail_nonempty]
            simp [marked]

theorem cut_reconstruction (marks : Finset ℕ) (blocks : List (List ℕ))
    (nonempty : ∀ block ∈ blocks, block ≠ [])
    (interior : ∀ block ∈ blocks, ∀ entry ∈ block.dropLast, entry ∉ marks)
    (endpoints : ∀ block ∈ blocks.dropLast, block.getLastD 0 ∈ marks) :
    cutBlocks marks blocks.flatten = blocks := by
  have cut_prefix (entries : List ℕ) (endpoint : ℕ) (suffix : List ℕ)
      (unmarked : ∀ entry ∈ entries, entry ∉ marks)
      (stop : endpoint ∈ marks ∨ suffix = []) :
      cutBlocks marks (entries ++ endpoint :: suffix) =
        (entries ++ [endpoint]) :: cutBlocks marks suffix := by
    induction entries with
    | nil =>
      rcases stop with marked | rfl
      · simp [cutBlocks, marked]
      · by_cases marked : endpoint ∈ marks <;> simp [cutBlocks, marked]
    | cons entry tail induction =>
      have head_unmarked := unmarked entry (by simp)
      have tail_unmarked : ∀ entry ∈ tail, entry ∉ marks := by
        intro entry member
        exact unmarked entry (by simp [member])
      rw [List.cons_append, cutBlocks, if_neg head_unmarked, induction tail_unmarked]
      rfl
  induction blocks with
  | nil => simp [cutBlocks]
  | cons block remaining induction =>
    have block_nonempty := nonempty block (by simp)
    have split : block.dropLast ++ [block.getLastD 0] = block := by
      simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast block_nonempty,
        Option.getD_some] using List.dropLast_append_getLast block_nonempty
    have remaining_nonempty : ∀ block ∈ remaining, block ≠ [] := by
      intro block member
      exact nonempty block (by simp [member])
    have remaining_interior : ∀ block ∈ remaining,
        ∀ entry ∈ block.dropLast, entry ∉ marks := by
      intro block member entry entry_mem
      exact interior block (by simp [member]) entry entry_mem
    have remaining_endpoints : ∀ block ∈ remaining.dropLast, block.getLastD 0 ∈ marks := by
      intro next member
      cases remaining with
      | nil => simp at member
      | cons first rest =>
        exact endpoints next (by
          simp only [List.dropLast_cons_cons, List.mem_cons]
          exact Or.inr member)
    have stop : block.getLastD 0 ∈ marks ∨ remaining.flatten = [] := by
      cases remaining with
      | nil => exact Or.inr rfl
      | cons first rest =>
        exact Or.inl (endpoints block (by simp))
    rw [List.flatten_cons, ← split, List.append_assoc]
    simpa only [split, List.singleton_append] using
      (cut_prefix block.dropLast (block.getLastD 0) remaining.flatten
        (interior block (by simp)) stop).trans
        (congrArg ((block.dropLast ++ [block.getLastD 0]) :: ·)
          (induction remaining_nonempty remaining_interior remaining_endpoints))

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
    ∀ earlier ∈ word.takeWhile (fun entry => decide (entry ≠ value)), earlier < value

theorem fibre_records (blocks : List (List ℕ))
    (distinct : blocks.flatten.Nodup)
    (bounded : ∀ block ∈ blocks.map List.reverse, ∃ leader body,
      block = leader :: body ∧ ∀ entry ∈ body, entry ≤ leader)
    (ordered : (blocks.map List.reverse).Pairwise (fun earlier later =>
      ∀ entry ∈ earlier, ∀ leader body, later = leader :: body → entry < leader)) :
    ∀ before block after, blocks = before ++ block :: after →
      ∃ body leader, block = body ++ [leader] ∧
        ∀ entry ∈ before.flatten ++ body, entry < leader := by
  induction blocks with
  | nil =>
    intro before block after split
    have impossible := congrArg List.length split
    simp at impossible
  | cons first remaining induction =>
    obtain ⟨leader, body, reversed, body_bound⟩ :=
      bounded first.reverse (by simp)
    have first_shape : first = body.reverse ++ [leader] := by
      simpa using congrArg List.reverse reversed
    have first_distinct := (List.nodup_flatten.mp distinct).1 first (by simp)
    have leader_absent : leader ∉ body := by
      have reversed_distinct : first.reverse.Nodup := List.nodup_reverse.mpr first_distinct
      rw [reversed, List.nodup_cons] at reversed_distinct
      exact reversed_distinct.1
    have strict : ∀ entry ∈ body.reverse, entry < leader := by
      intro entry member
      have body_member := List.mem_reverse.mp member
      have unequal : entry ≠ leader := by
        intro equal
        exact leader_absent (equal ▸ body_member)
      exact lt_of_le_of_ne (body_bound entry body_member) unequal
    have remaining_distinct : remaining.flatten.Nodup := by
      exact (List.nodup_append.mp (by simpa only [List.flatten_cons] using distinct)).2.1
    have remaining_bounded : ∀ block ∈ remaining.map List.reverse, ∃ leader body,
        block = leader :: body ∧ ∀ entry ∈ body, entry ≤ leader := by
      intro block member
      exact bounded block (by simp [member])
    obtain ⟨head_order, tail_order⟩ := List.pairwise_cons.mp ordered
    intro before block after split
    cases before with
    | nil =>
      obtain ⟨rfl, _⟩ := List.cons.inj split
      exact ⟨body.reverse, leader, first_shape, by simpa using strict⟩
    | cons earlier before =>
      obtain ⟨rfl, tail_split⟩ := List.cons.inj split
      obtain ⟨inner, endpoint, block_shape, bound⟩ :=
        induction remaining_distinct remaining_bounded tail_order before block after tail_split
      refine ⟨inner, endpoint, block_shape, ?_⟩
      intro entry member
      simp only [List.flatten_cons, List.append_assoc, List.mem_append] at member
      rcases member with first_member | later_member
      · have block_member : block ∈ remaining := by simp [tail_split]
        exact head_order block.reverse (by simp [block_member]) entry
          (List.mem_reverse.mpr first_member) endpoint inner.reverse
          (by simp [block_shape])
      · exact bound entry (List.mem_append.mpr later_member)

theorem record_cut_structure (marks : Finset ℕ) (word : List ℕ)
    (distinct : word.Nodup)
    (marked : ∀ value ∈ marks, value ∈ word → value ∈ recordCuts word)
    (terminal : ∀ value ∈ word.dropLast, value < word.getLastD 0) :
    (∀ block ∈ cutBlocks marks word, ∃ body endpoint,
      block = body ++ [endpoint] ∧
        (endpoint ∈ marks ∨ endpoint = word.getLastD 0) ∧
        ∀ entry ∈ body, entry < endpoint) ∧
      ((cutBlocks marks word).map List.reverse).Pairwise (fun earlier later =>
        ∀ entry ∈ earlier, ∀ leader body, later = leader :: body → entry < leader) := by
  induction word with
  | nil => simp [cutBlocks]
  | cons entry tail induction =>
    by_cases empty_tail : tail = []
    · subst tail
      by_cases selected : entry ∈ marks <;>
        simp only [cutBlocks, selected, if_true, if_false]
      all_goals
        refine ⟨?_, by simp⟩
        intro block member
        have same : block = [entry] := by simpa using member
        subst block
        exact ⟨[], entry, rfl, Or.inr (by simp), by simp⟩
    have tail_last : (entry :: tail).getLastD 0 = tail.getLastD 0 := by
      cases tail with
      | nil => contradiction
      | cons next rest => simp [List.getLastD_eq_getLast?]
    have tail_terminal : ∀ value ∈ tail.dropLast, value < tail.getLastD 0 := by
      intro value member
      rw [← tail_last]
      apply terminal value
      cases tail with
      | nil => contradiction
      | cons next rest => simpa using Or.inr member
    have tail_marked : ∀ value ∈ marks, value ∈ tail → value ∈ recordCuts tail := by
      intro value selected member
      have unequal : entry ≠ value := by
        intro equal
        exact (List.nodup_cons.mp distinct).1 (equal ▸ member)
      have inherited := marked value selected (by simp [member])
      refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr member, ?_⟩
      intro earlier earlier_mem
      apply (Finset.mem_filter.mp inherited).2 earlier
      simp only [List.takeWhile_cons,
        show decide (entry ≠ value) = true from decide_eq_true unequal, if_true]
      exact List.mem_cons.mpr (Or.inr earlier_mem)
    obtain ⟨tail_blocks, tail_order⟩ :=
      induction (List.nodup_cons.mp distinct).2 tail_marked tail_terminal
    have larger (endpoint : ℕ) (member : endpoint ∈ tail)
        (selected : endpoint ∈ marks ∨ endpoint = tail.getLastD 0) : entry < endpoint := by
      rcases selected with selected | rfl
      · have unequal : entry ≠ endpoint := by
          intro equal
          exact (List.nodup_cons.mp distinct).1 (equal ▸ member)
        have record := (Finset.mem_filter.mp (marked endpoint selected (by simp [member]))).2
        apply record entry
        simp [unequal]
      · rw [← tail_last]
        apply terminal entry
        cases tail with
        | nil => contradiction
        | cons next rest => simp
    have leader_large (block : List ℕ) (member : block ∈ cutBlocks marks tail)
        (leader : ℕ) (body : List ℕ) (reversed : block.reverse = leader :: body) :
        entry < leader := by
      obtain ⟨inner, endpoint, shape, selected, _⟩ := tail_blocks block member
      have same : endpoint = leader := by
        have head := congrArg List.head? reversed
        simpa [shape] using head
      subst endpoint
      apply larger leader _ selected
      rw [← (cut_blocks marks tail).1]
      exact List.mem_flatten.mpr ⟨block, member, by simp [shape]⟩
    by_cases selected : entry ∈ marks
    · rw [cutBlocks, if_pos selected]
      refine ⟨?_, ?_⟩
      · intro block member
        rcases List.mem_cons.mp member with rfl | following
        · exact ⟨[], entry, rfl, Or.inl selected, by simp⟩
        · obtain ⟨body, endpoint, shape, choice, bound⟩ := tail_blocks block following
          exact ⟨body, endpoint, shape, tail_last ▸ choice, bound⟩
      · simp only [List.map_cons, List.reverse_singleton, List.pairwise_cons]
        refine ⟨?_, tail_order⟩
        intro block member value value_mem leader body reversed
        obtain ⟨original, original_mem, rfl⟩ := List.mem_map.mp member
        have same : value = entry := by simpa using value_mem
        subst value
        exact leader_large original original_mem leader body reversed
    · cases scan : cutBlocks marks tail with
      | nil =>
        have partition := (cut_blocks marks tail).1
        exact (empty_tail (by simpa only [scan, List.flatten_nil] using partition.symm)).elim
      | cons block remaining =>
        obtain ⟨body, endpoint, shape, choice, bound⟩ :=
          tail_blocks block (by simp [scan])
        have endpoint_mem : endpoint ∈ tail := by
          rw [← (cut_blocks marks tail).1]
          exact List.mem_flatten.mpr ⟨block, by simp [scan], by simp [shape]⟩
        have entry_bound := larger endpoint endpoint_mem choice
        rw [cutBlocks, if_neg selected, scan]
        refine ⟨?_, ?_⟩
        · intro current member
          rcases List.mem_cons.mp member with rfl | following
          · refine ⟨entry :: body, endpoint, by simp [shape], ?_, ?_⟩
            · rw [tail_last]
              exact choice
            · intro value member
              rcases List.mem_cons.mp member with rfl | member
              · exact entry_bound
              · exact bound value member
          · obtain ⟨body, endpoint, shape, choice, bound⟩ :=
              tail_blocks current (by simp [scan, following])
            exact ⟨body, endpoint, shape, tail_last ▸ choice, bound⟩
        · rw [scan] at tail_order
          obtain ⟨first_order, rest_order⟩ := List.pairwise_cons.mp tail_order
          rw [List.map_cons, List.pairwise_cons]
          refine ⟨?_, rest_order⟩
          intro later member value value_mem leader rest reversed
          obtain ⟨original, original_mem, rfl⟩ := List.mem_map.mp member
          simp only [List.reverse_cons, List.mem_append, List.mem_singleton] at value_mem
          rcases value_mem with previous | rfl
          · exact first_order original.reverse (by simp [original_mem]) value previous
              leader rest reversed
          · exact leader_large original (by simp [scan, original_mem]) leader rest reversed

end D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre
