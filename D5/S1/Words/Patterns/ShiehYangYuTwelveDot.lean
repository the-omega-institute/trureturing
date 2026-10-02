/- GID: D5/S1/Words/Patterns/ShiehYangYuTwelveDot
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/ShiehYangYuTwelveDot
   mirror-E: none(waiver:machine-permutation-count)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Data.List.OfFn]
   utility: none
   digest: Excursion reflection and up-step subsets count all permutations sorted by the machine. -/

import D5.S1.Words.Patterns.ShiehYangYuTwelveDotPaths
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.OfFn
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S1.Words.Patterns.ShiehYangYuTwelveDot

open D5.S1.Words.Patterns.ShiehYangYuTwelveDotDefs
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotDyck
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotPaths
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotWest
open D5.S1.Words.Patterns.ShiehYangYuMachineConvergence
open D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs
open private westRun westRun_perm from
  D5.S1.Words.Patterns.ShiehYangYuMachineConvergence

theorem result : ShiehYangYuTwelveDotDefs.claim := by
  classical
  let linked := fun (marks : Finset ℕ) (entry : ℕ) (_ : ℕ) => decide (entry ∉ marks)
  have split_cons (marks : Finset ℕ) (entry : ℕ) (tail : List ℕ) :
      (entry :: tail).splitBy (linked marks) =
        if entry ∈ marks then [entry] :: tail.splitBy (linked marks)
        else match tail.splitBy (linked marks) with
          | [] => [[entry]]
          | block :: remaining => (entry :: block) :: remaining := by
    let relation := linked marks
    by_cases selected : entry ∈ marks
    · rw [if_pos selected]
      change ([entry] ++ tail).splitBy relation = _
      rw [List.splitBy_append]
      · simp [relation, linked, List.splitBy_of_isChain (by simp : [entry] ≠ []) (by simp)]
      · simp [relation, linked, selected]
    · rw [if_neg selected]
      cases scan : tail.splitBy relation with
      | nil =>
        have empty : tail = [] := List.splitBy_eq_nil.mp scan
        subst tail
        simp [List.splitBy_of_isChain (by simp : [entry] ≠ []) (by simp)]
      | cons block remaining =>
        have facts := List.splitBy_eq_iff.mp scan
        have nonempty : block ≠ [] := fun empty => facts.2.1 (by simp [empty])
        apply List.splitBy_eq_iff.mpr
        refine ⟨by simpa using congrArg (entry :: ·) facts.1,
          by simpa using (show [] ∉ remaining from fun member =>
            facts.2.1 (List.mem_cons_of_mem _ member)), ?_, ?_⟩
        · intro current member
          rcases List.mem_cons.mp member with rfl | member
          · apply List.IsChain.cons (facts.2.2.1 block (by simp))
            intro value contained
            exact decide_eq_true selected
          · exact facts.2.2.1 current (by simp [member])
        · obtain ⟨first, rest⟩ := List.isChain_cons.mp facts.2.2.2
          apply List.isChain_cons.mpr
          refine ⟨?_, rest⟩
          intro next contained
          obtain ⟨head_nonempty, next_nonempty, broken⟩ := first next contained
          refine ⟨by simp, next_nonempty, ?_⟩
          simpa only [List.getLast_cons nonempty] using broken
  have split_facts (marks : Finset ℕ) (word : List ℕ) :
      ((word.splitBy (linked marks))).flatten = word ∧
        (∀ block ∈ (word.splitBy (linked marks)), block ≠ []) ∧
        (∀ block ∈ word.splitBy (linked marks),
          ∀ entry ∈ block.dropLast, entry ∉ marks) ∧
        ((((word.splitBy (linked marks))).dropLast).map (fun block => block.getLastD 0)).toFinset =
          marks ∩ word.dropLast.toFinset := by
    induction word with
    | nil => simp
    | cons entry tail induction =>
      obtain ⟨partition, nonempty, interior, endpoints⟩ := induction
      by_cases marked : entry ∈ marks
      · rw [split_cons, if_pos marked]
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
          | nil => simp
          | cons next rest =>
            have remaining_nonempty : ((next :: rest).splitBy (linked marks)) ≠ [] := by
              intro empty
              rw [empty] at partition
              simp at partition
            cases blocks : ((next :: rest).splitBy (linked marks)) with
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
      · rw [split_cons, if_neg marked]
        cases blocks : (tail.splitBy (linked marks)) with
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
  have record_mem (entries : List ℕ) (value : ℕ) :
      value ∈ recordCuts entries ↔ value ∈ entries.toFinset ∧
        ∀ earlier ∈ entries.takeWhile (fun entry => decide (entry ≠ value)),
          earlier < value := by
    simp only [recordCuts, Finset.mem_filter]
    apply and_congr_right
    intro contained
    have index_bound := List.idxOf_lt_length_of_mem (List.mem_toFinset.mp contained)
    have taken : entries.takeWhile (fun entry => decide (entry ≠ value)) =
        entries.take (entries.idxOf value) := by
      simp [List.takeWhile_eq_take_findIdx_not, List.idxOf, Bool.beq_eq_decide_eq]
    rw [taken, List.forall_mem_iff_getElem]
    simp only [List.getElem_take, List.length_take_of_le index_bound.le]
    unfold D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax
    rw [List.getD_eq_getElem entries 0 index_bound, List.getElem_idxOf]
    constructor <;> intro bound position smaller <;>
      simpa only [List.getD_eq_getElem entries 0 (smaller.trans index_bound)]
        using bound position smaller
  have peak_split_max (left right : List ℕ) (maximum : ℕ)
      (left_bound : ∀ entry ∈ left, entry < maximum)
      (right_bound : ∀ entry ∈ right, entry ≤ maximum) :
      peakRuns (left ++ maximum :: right) = peakRuns left ++ [maximum :: right] := by
    fun_induction peakRuns left with
    | case1 =>
      have taken : right.takeWhile (fun entry => decide (entry ≤ maximum)) = right :=
        List.takeWhile_eq_self_iff.mpr (by simpa using right_bound)
      have dropped : right.dropWhile (fun entry => decide (entry ≤ maximum)) = [] :=
        List.dropWhile_eq_nil_iff.mpr (by simpa using right_bound)
      simp [peakRuns, taken, dropped]
    | case2 leader tail induction =>
      let test := fun entry => decide (entry ≤ leader)
      have stop : test maximum = false := by
        simp [test, Nat.not_le.mpr (left_bound leader (by simp))]
      have split (entries : List ℕ) :
          (entries ++ maximum :: right).takeWhile test = entries.takeWhile test ∧
            (entries ++ maximum :: right).dropWhile test =
              entries.dropWhile test ++ maximum :: right := by
        induction entries with
        | nil => simp [stop]
        | cons entry rest induction =>
          cases passed : test entry <;> simp [passed, induction]
      have remaining_bound : ∀ entry ∈ tail.dropWhile test, entry < maximum := by
        intro entry member
        exact left_bound entry (by simp [List.dropWhile_subset test member])
      simp only [List.cons_append, peakRuns]
      rw [(split tail).1, (split tail).2, induction remaining_bound]
  have machine_record_equiv (size : ℕ) :
      {input : List ℕ // input ∈ sortable (size + 1)} ≃
        {z : Σ word : List ℕ, {marks : Finset ℕ // marks ⊆ recordCuts word} //
          z.1.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] z.1} := by
    have record_fibre_equiv (initial : List ℕ) (maximum : ℕ)
        (distinct : (initial ++ [maximum]).Nodup)
        (bound : ∀ entry ∈ initial, entry < maximum) :
        {input : List ℕ // s12 input = initial ++ [maximum]} ≃
          {marks : Finset ℕ // marks ⊆ recordCuts initial} := by
      have fibre_records (blocks : List (List ℕ)) (distinct : blocks.flatten.Nodup)
          (bounded : ∀ block ∈ blocks.map List.reverse, ∃ leader body,
            block = leader :: body ∧ ∀ entry ∈ body, entry ≤ leader)
          (ordered : (blocks.map List.reverse).Pairwise (fun earlier later =>
            ∀ entry ∈ earlier, ∀ leader body, later = leader :: body → entry < leader)) :
          ∀ before block after, blocks = before ++ block :: after →
            ∃ body leader, block = body ++ [leader] ∧
              ∀ entry ∈ before.flatten ++ body, entry < leader := by
        intro before block after split
        have block_member : block ∈ blocks := by rw [split]; simp
        obtain ⟨leader, body, reversed, body_bound⟩ :=
          bounded block.reverse (List.mem_map.mpr ⟨block, block_member, rfl⟩)
        have shape : block = body.reverse ++ [leader] := by
          simpa using congrArg List.reverse reversed
        have block_distinct := (List.nodup_flatten.mp distinct).1 block block_member
        have leader_absent : leader ∉ body := by
          have reversed_distinct := List.nodup_reverse.mpr block_distinct
          rw [reversed, List.nodup_cons] at reversed_distinct
          exact reversed_distinct.1
        have separated := (List.pairwise_append.mp (by
          simpa only [split, List.map_append, List.map_cons] using ordered)).2.2
        refine ⟨body.reverse, leader, shape, ?_⟩
        intro entry member
        rcases List.mem_append.mp member with earlier | interior
        · obtain ⟨previous, previous_mem, inside⟩ := List.mem_flatten.mp earlier
          exact separated previous.reverse
            (List.mem_map.mpr ⟨previous, previous_mem, rfl⟩) block.reverse
            (by simp) entry (List.mem_reverse.mpr inside) leader body reversed
        · have body_member := List.mem_reverse.mp interior
          have unequal : entry ≠ leader := fun equal => leader_absent (equal ▸ body_member)
          exact lt_of_le_of_ne (body_bound entry body_member) unequal
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
        let _ : Std.Symm (List.Disjoint (α := ℕ)) := ⟨fun _ _ => List.Disjoint.symm⟩
        intro block member entry inside selected
        obtain ⟨next, next_mem, endpoint⟩ := List.mem_map.mp (List.mem_toFinset.mp selected)
        by_cases same : block = next
        · subst next
          have own_distinct := (List.nodup_flatten.mp distinct).1 block member
          rw [← block_split block (nonempty block member)] at own_distinct
          exact (List.nodup_append.mp own_distinct).2.2 entry inside entry
            (List.mem_singleton.mpr endpoint.symm) rfl
        · have separated := (List.nodup_flatten.mp distinct).2.forall member next_mem same
          exact separated (List.mem_of_mem_dropLast inside)
            (endpoint ▸ last_mem next (nonempty next next_mem))
      refine (fibre_equiv (initial ++ [maximum])).trans
        { toFun := fun blocks =>
            ⟨(blocks.val.dropLast.map (fun block => block.getLastD 0)).toFinset, ?_⟩
          invFun := fun marks => ⟨((initial ++ [maximum]).splitBy (linked marks.val)), ?_⟩
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
        have alphabet (entry : ℕ) (member : entry ∈ blocks.val.flatten) :
            entry ≤ maximum := by
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
        refine (record_mem _ _).mpr ⟨List.mem_toFinset.mpr endpoint_member, ?_⟩
        rw [← prefix_take endpoint endpoint_member, taken]
        exact record
      · have records := marks.property
        have marked : ∀ value ∈ marks.val, value ∈ initial ++ [maximum] →
            value ∈ recordCuts (initial ++ [maximum]) := by
          intro value selected _
          have record := (record_mem _ _).mp (records selected)
          refine (record_mem _ _).mpr ⟨?_, ?_⟩
          · exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp record.1))
          · rw [prefix_take value (List.mem_toFinset.mp record.1)]
            exact record.2
        have record_cut_structure (marks : Finset ℕ) (word : List ℕ)
            (distinct : word.Nodup)
            (marked : ∀ value ∈ marks, value ∈ word → value ∈ recordCuts word)
            (terminal : ∀ value ∈ word.dropLast, value < word.getLastD 0) :
            (∀ block ∈ (word.splitBy (linked marks)), ∃ body endpoint,
              block = body ++ [endpoint] ∧
                (endpoint ∈ marks ∨ endpoint = word.getLastD 0) ∧
                ∀ entry ∈ body, entry < endpoint) ∧
              (((word.splitBy (linked marks))).map List.reverse).Pairwise (fun earlier later =>
                ∀ entry ∈ earlier, ∀ leader body, later = leader :: body →
                  entry < leader) := by
          induction word with
          | nil => simp
          | cons entry tail induction =>
            by_cases empty_tail : tail = []
            · subst tail
              by_cases selected : entry ∈ marks <;>
                simp only [split_cons, selected, if_true, if_false]
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
            have tail_marked : ∀ value ∈ marks, value ∈ tail →
                value ∈ recordCuts tail := by
              intro value selected member
              have unequal : entry ≠ value := by
                intro equal
                exact (List.nodup_cons.mp distinct).1 (equal ▸ member)
              have inherited := marked value selected (by simp [member])
              refine (record_mem _ _).mpr ⟨List.mem_toFinset.mpr member, ?_⟩
              intro earlier earlier_mem
              apply ((record_mem _ _).mp inherited).2 earlier
              simp only [List.takeWhile_cons,
                show decide (entry ≠ value) = true from decide_eq_true unequal, if_true]
              exact List.mem_cons.mpr (Or.inr earlier_mem)
            obtain ⟨tail_blocks, tail_order⟩ :=
              induction (List.nodup_cons.mp distinct).2 tail_marked tail_terminal
            have larger (endpoint : ℕ) (member : endpoint ∈ tail)
                (selected : endpoint ∈ marks ∨ endpoint = tail.getLastD 0) :
                entry < endpoint := by
              rcases selected with selected | rfl
              · have unequal : entry ≠ endpoint := by
                  intro equal
                  exact (List.nodup_cons.mp distinct).1 (equal ▸ member)
                have record := ((record_mem _ _).mp
                  (marked endpoint selected (by simp [member]))).2
                apply record entry
                simp [unequal]
              · rw [← tail_last]
                apply terminal entry
                cases tail with
                | nil => contradiction
                | cons next rest => simp
            have leader_large (block : List ℕ) (member : block ∈ (tail.splitBy (linked marks)))
                (leader : ℕ) (body : List ℕ) (reversed : block.reverse = leader :: body) :
                entry < leader := by
              obtain ⟨inner, endpoint, shape, selected, _⟩ := tail_blocks block member
              have same : endpoint = leader := by
                have head := congrArg List.head? reversed
                simpa [shape] using head
              subst endpoint
              apply larger leader _ selected
              rw [← (split_facts marks tail).1]
              exact List.mem_flatten.mpr ⟨block, member, by simp [shape]⟩
            by_cases selected : entry ∈ marks
            · rw [split_cons, if_pos selected]
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
            · cases scan : (tail.splitBy (linked marks)) with
              | nil =>
                have partition := (split_facts marks tail).1
                exact (empty_tail (by simpa [scan] using partition.symm)).elim
              | cons block remaining =>
                obtain ⟨body, endpoint, shape, choice, bound⟩ :=
                  tail_blocks block (by simp [scan])
                have endpoint_mem : endpoint ∈ tail := by
                  rw [← (split_facts marks tail).1]
                  exact List.mem_flatten.mpr ⟨block, by simp [scan], by simp [shape]⟩
                have entry_bound := larger endpoint endpoint_mem choice
                rw [split_cons, if_neg selected, scan]
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
        obtain ⟨shapes, ordered⟩ := record_cut_structure marks.val (initial ++ [maximum])
          distinct marked (by simpa using bound)
        refine ⟨(split_facts marks.val _).1, ?_, ordered⟩
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
        let chosen := (blocks.val.dropLast.map (fun block => block.getLastD 0)).toFinset
        change (initial ++ [maximum]).splitBy (linked chosen) = blocks.val
        have reconstructed : blocks.val.flatten.splitBy (linked chosen) = blocks.val := by
          apply List.splitBy_flatten
          · intro empty
            exact nonempty [] empty rfl
          · intro block member
            apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
            intro first second before after split
            have inside : first ∈ block.dropLast := by
              rw [split, List.dropLast_append_cons, List.dropLast_cons_cons]
              simp
            apply decide_eq_true
            intro selected
            obtain ⟨next, next_mem, endpoint⟩ :=
              List.mem_map.mp (List.mem_toFinset.mp selected)
            exact interiors blocks.val all_distinct nonempty block member first inside
              (List.mem_toFinset.mpr (List.mem_map.mpr
                ⟨next, List.mem_of_mem_dropLast next_mem, endpoint⟩))
          · apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
            intro first second before after split
            have first_mem : first ∈ blocks.val := by rw [split]; simp
            have second_mem : second ∈ blocks.val := by rw [split]; simp
            have inside : first ∈ blocks.val.dropLast := by
              rw [split, List.dropLast_append_cons, List.dropLast_cons_cons]
              simp
            refine ⟨nonempty first first_mem, nonempty second second_mem, ?_⟩
            have selected : first.getLastD 0 ∈ chosen :=
              List.mem_toFinset.mpr (List.mem_map.mpr ⟨first, inside, rfl⟩)
            simpa only [linked, List.getLastD_eq_getLast?,
              List.getLast?_eq_some_getLast (nonempty first first_mem), Option.getD_some,
              decide_eq_false_iff_not, not_not] using selected
        simpa only [blocks.property.1] using reconstructed
      · intro marks
        apply Subtype.ext
        change (((((initial ++ [maximum]).splitBy (linked marks.val))).dropLast).map
          (fun block => block.getLastD 0)).toFinset = marks.val
        rw [(split_facts marks.val (initial ++ [maximum])).2.2.2]
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
              ((record_fibre_equiv second (size + 1) second_distinct second_bound)
                second_input) := by
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
  have decorated_path_equiv (size : ℕ) :
      {z : Σ word : List ℕ, {marks : Finset ℕ // marks ⊆ recordCuts word} //
        z.1.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] z.1} ≃
        {z : Σ path : DyckWord, Fin (excursions path).length → Bool //
          z.1.semilength = size} := by
    classical
    have subset_bits (records : Finset ℕ) :
        {marks : Finset ℕ // marks ⊆ records} ≃ (Fin records.card → Bool) := by
      let indices := (records.orderIsoOfFin rfl).toEquiv
      let selected (bits : Fin records.card → Bool) : Finset ℕ :=
        (Finset.univ.filter (fun index => bits index = true)).image
          (fun index => (indices index).val)
      have inside (bits : Fin records.card → Bool) : selected bits ⊆ records := by
        intro value member
        obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp member
        exact (indices index).property
      have marked (bits : Fin records.card → Bool) (index : Fin records.card) :
          (indices index).val ∈ selected bits ↔ bits index = true := by
        constructor
        · intro member
          obtain ⟨other, eligible, equal⟩ := Finset.mem_image.mp member
          have same : other = index := indices.injective (Subtype.ext equal)
          subst other
          exact (Finset.mem_filter.mp eligible).2
        · intro bit
          exact Finset.mem_image.mpr ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, bit⟩,
            rfl⟩
      refine ⟨fun marks index => decide ((indices index).val ∈ marks.val),
        fun bits => ⟨selected bits, inside bits⟩, ?_, ?_⟩
      · intro marks
        apply Subtype.ext
        apply Finset.ext
        intro value
        by_cases member : value ∈ records
        · let index := indices.symm ⟨value, member⟩
          have recovered : (indices index).val = value :=
            congrArg Subtype.val (indices.apply_symm_apply ⟨value, member⟩)
          rw [← recovered, marked]
          simp only [decide_eq_true_eq]
        · exact iff_of_false (fun selected_member => member (inside _ selected_member))
            (fun marks_member => member (marks.property marks_member))
      · intro bits
        funext index
        change decide ((indices index).val ∈ selected bits) = bits index
        simp only [marked]
        cases bits index <;> rfl
    let avoiding := {word : List ℕ //
      word.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] word}
    let paths := {path : DyckWord // path.semilength = size}
    have transport (first_size second_size : ℕ)
        (first : {word : List ℕ // word.Perm (List.range' 1 first_size) ∧
          ¬ Occurs [2, 3, 1] word})
        (second : {word : List ℕ // word.Perm (List.range' 1 second_size) ∧
          ¬ Occurs [2, 3, 1] word})
        (sizes : first_size = second_size) (words : first.val = second.val) :
        (avoiding_encode first_size first).val =
          (avoiding_encode second_size second).val := by
      subst second_size
      rw [Subtype.ext words]
    let plain : avoiding ≃ paths :=
      { toFun := avoiding_encode size
        invFun := fun path => ⟨(avoiding_decode path.val).val, by
          simpa only [path.property] using (avoiding_decode path.val).property⟩
        left_inv := fun word => Subtype.ext (avoiding_inverse.1 size word)
        right_inv := fun path => by
          apply Subtype.ext
          exact (transport size path.val.semilength _ (avoiding_decode path.val)
            path.property.symm rfl).trans (avoiding_inverse.2.1 path.val) }
    let unpack := Equiv.subtypeSigmaEquiv
      (fun word : List ℕ => {marks : Finset ℕ // marks ⊆ recordCuts word})
      (fun word => word.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] word)
    let colors : (Σ word : avoiding, {marks : Finset ℕ // marks ⊆ recordCuts word.val}) ≃
        (Σ word : avoiding, Fin (recordCuts word.val).card → Bool) :=
      Equiv.sigmaCongrRight (fun word => subset_bits (recordCuts word.val))
    let transfer : (Σ word : avoiding, Fin (recordCuts word.val).card → Bool) ≃
        (Σ path : paths, Fin (excursions path.val).length → Bool) :=
      Equiv.sigmaCongr plain (fun word =>
        Equiv.piCongrLeft (fun _ => Bool)
          (finCongr (avoiding_inverse.2.2 size word)))
    let pack := (Equiv.subtypeSigmaEquiv
      (fun path : DyckWord => Fin (excursions path).length → Bool)
      (fun path => path.semilength = size)).symm
    exact unpack.trans (colors.trans (transfer.trans pack))
  let colored_lists : (Σ pieces : List DyckWord, Fin pieces.length → Bool) ≃
      List (Bool × DyckWord) := by
    refine
      { toFun := fun pieces => List.ofFn (fun index => (pieces.2 index, pieces.1.get index))
        invFun := fun pieces => ⟨pieces.map Prod.snd,
          fun index => (pieces.get ⟨index.val, by simpa using index.isLt⟩).1⟩
        left_inv := ?_
        right_inv := ?_ }
    · rintro ⟨pieces, bits⟩
      have interiors :
          (List.ofFn (fun index => (bits index, pieces.get index))).map Prod.snd = pieces := by
        simpa only [List.map_ofFn, Function.comp_def] using List.ofFn_get pieces
      apply Sigma.ext interiors
      apply (Fin.heq_fun_iff (congrArg List.length interiors)).mpr
      intro index
      simp only [List.get_ofFn]
      rfl
    · intro pieces
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_map]
      · intro index first_bound second_bound
        simp only [List.getElem_ofFn, List.get_eq_getElem, List.getElem_map]
  let colored : (Σ path : DyckWord, Fin (excursions path).length → Bool) ≃
      (Σ pieces : List DyckWord, Fin pieces.length → Bool) :=
    Equiv.sigmaCongr excursion_equiv
    (fun path => Equiv.refl (Fin (excursions path).length → Bool))
  let forests := colored.trans colored_lists
  have interiors (pieces : Σ entries : List DyckWord, Fin entries.length → Bool) :
      (colored_lists pieces).map Prod.snd = pieces.1 := by
    change (List.ofFn (fun index => (pieces.2 index, pieces.1.get index))).map Prod.snd = _
    simpa only [List.map_ofFn, Function.comp_def] using List.ofFn_get pieces.1
  have assembly_weight : ∀ pieces : List DyckWord,
      ((pieces.map DyckWord.nest).sum).semilength =
        (pieces.map (fun piece => piece.semilength + 1)).sum := by
    intro pieces
    induction pieces with
    | nil => rfl
    | cons piece pieces induction =>
      rw [List.map_cons, List.sum_cons, DyckWord.semilength_add,
        DyckWord.semilength_nest, induction, List.map_cons, List.sum_cons]
  have forest_weight (object : Σ path : DyckWord, Fin (excursions path).length → Bool) :
      ((forests object).map (fun piece => piece.2.semilength + 1)).sum =
        object.1.semilength := by
    have recovered := excursion_equiv.left_inv object.1
    change ((excursions object.1).map DyckWord.nest).sum = object.1 at recovered
    have alphabet := interiors (colored object)
    change (forests object).map Prod.snd = excursions object.1 at alphabet
    calc
      _ = (((forests object).map Prod.snd).map (fun piece => piece.semilength + 1)).sum := by
        simp only [List.map_map, Function.comp_def]
      _ = ((excursions object.1).map (fun piece => piece.semilength + 1)).sum := by
        rw [alphabet]
      _ = object.1.semilength := by rw [← assembly_weight, recovered]
  have step_total : ∀ word : List DyckStep,
      word.count DyckStep.U + word.count DyckStep.D = word.length := by
    intro word
    induction word with
    | nil => rfl
    | cons step word induction => cases step <;> simp_all <;> omega
  have up_indices : ∀ word : List DyckStep,
      (Finset.univ.filter (fun index : Fin word.length => word.get index = DyckStep.U)).card =
        word.count DyckStep.U := by
    intro word
    induction word with
    | nil => simp
    | cons step word induction =>
      rw [Finset.card_filter]
      change (∑ index : Fin (word.length + 1),
        if (step :: word).get index = DyckStep.U then 1 else 0) = _
      rw [Fin.sum_univ_succ]
      change (if step = DyckStep.U then 1 else 0) +
        (∑ index : Fin word.length, if word.get index = DyckStep.U then 1 else 0) = _
      rw [← Finset.card_filter, induction]
      cases step <;> simp [Nat.add_comm]
  intro size positive
  obtain ⟨length, size_eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
  subst size
  let colored_restricted :
      {z : Σ path : DyckWord, Fin (excursions path).length → Bool //
        z.1.semilength = length} ≃
      {pieces : List (Bool × DyckWord) //
        (pieces.map (fun piece => piece.2.semilength + 1)).sum = length} :=
    Equiv.subtypeEquiv forests (fun object => by rw [forest_weight object])
  let bridges := {word : List DyckStep //
    word.count DyckStep.U = length ∧ word.count DyckStep.D = length}
  let subsets := ↥((Finset.univ : Finset (Fin (2 * length))).powersetCard length)
  have bridge_subsets : bridges ≃ subsets := by
    have word_length (word : bridges) : word.val.length = 2 * length := by
      have total := step_total word.val
      rw [word.property.1, word.property.2] at total
      omega
    let selected (word : bridges) : Finset (Fin (2 * length)) :=
      Finset.univ.filter (fun index => word.val[index.val]'(by
        rw [word_length word]; exact index.isLt) = DyckStep.U)
    have selected_card (word : bridges) : (selected word).card = length := by
      have transport (word : List DyckStep) (amount : ℕ) (equal : word.length = amount) :
          (Finset.univ.filter (fun index : Fin amount =>
            word[index.val]'(equal.symm ▸ index.isLt) = DyckStep.U)).card =
          word.count DyckStep.U := by
        subst amount
        exact up_indices word
      exact (transport word.val _ (word_length word)).trans word.property.1
    let build (marks : subsets) : List DyckStep :=
      List.ofFn (fun index : Fin (2 * length) =>
        if index ∈ marks.val then DyckStep.U else DyckStep.D)
    have build_up (marks : subsets) : (build marks).count DyckStep.U = length := by
      have indices := up_indices (build marks)
      have transport (amount : ℕ) (bits : Fin amount → DyckStep) :
          (Finset.univ.filter (fun index : Fin (List.ofFn bits).length =>
            (List.ofFn bits).get index = DyckStep.U)).card =
            (Finset.univ.filter (fun index => bits index = DyckStep.U)).card := by
        apply Finset.card_equiv (finCongr (List.length_ofFn))
        intro index
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.get_ofFn]
        rfl
      rw [transport] at indices
      have alphabet : (Finset.univ.filter (fun index : Fin (2 * length) =>
          (if index ∈ marks.val then DyckStep.U else DyckStep.D) = DyckStep.U)) =
          marks.val := by
        ext index
        simp
      rw [alphabet] at indices
      exact indices.symm.trans (Finset.mem_powersetCard.mp marks.property).2
    have build_down (marks : subsets) : (build marks).count DyckStep.D = length := by
      have total := step_total (build marks)
      have amount : (build marks).length = 2 * length := List.length_ofFn
      rw [build_up marks, amount] at total
      omega
    refine
      { toFun := fun word => ⟨selected word,
          Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, selected_card word⟩⟩
        invFun := fun marks => ⟨build marks, build_up marks, build_down marks⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro word
      apply Subtype.ext
      apply List.ext_getElem
      · exact List.length_ofFn.trans (word_length word).symm
      · intro index built_bound word_bound
        change (List.ofFn (fun index : Fin (2 * length) =>
          if index ∈ selected word then DyckStep.U else DyckStep.D))[index] = word.val[index]
        rw [List.getElem_ofFn]
        simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
        cases word.val[index] <;> simp
    · intro marks
      apply Subtype.ext
      apply Finset.ext
      intro index
      change index ∈ selected ⟨build marks, build_up marks, build_down marks⟩ ↔ _
      simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and,
        build, List.getElem_ofFn]
      simp
  let equivalence := (machine_record_equiv length).trans
    ((decorated_path_equiv length).trans
      (colored_restricted.trans ((signed_bridge_equiv length).trans bridge_subsets)))
  have cardinal := Nat.card_congr equivalence
  rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at cardinal
  change (sortable (length + 1)).ncard = (2 * (length + 1) - 2).choose (length + 1 - 1)
  exact cardinal
end D5.S1.Words.Patterns.ShiehYangYuTwelveDot
