/- GID: D5/S1/Words/Patterns/ShiehYangYuTwelveDotDyck
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/ShiehYangYuTwelveDotDyck
   mirror-E: none(waiver:avoiding-permutation-record-grammar)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DyckWord]
   utility: none
   digest: Maximum splitting constructs the unique avoiding grammar and its record statistic. -/

import D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre
import Mathlib.Combinatorics.Enumerative.DyckWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Patterns.ShiehYangYuTwelveDotDyck

open D5.S1.Words.Patterns.ShiehYangYuTwelveDotFibre
open D5.S3.Combinatorics.Nonnesting.NonnestingDefs
open D5.S3.Combinatorics.Fishburn.FishburnTenNineClassicalSplit

noncomputable def avoiding_encode : (size : ℕ) →
    {word : List ℕ // word.Perm (List.range' 1 size) ∧ ¬ Occurs [2, 3, 1] word} →
      {path : DyckWord // path.semilength = size}
  | 0, _ => ⟨0, rfl⟩
  | size + 1, word => by
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
      have avoiding_decomposition (size : ℕ) (word : List ℕ)
          (permutation : word.Perm (List.range' 1 (size + 1)))
          (avoiding : ¬ Occurs [2, 3, 1] word) :
          ∃ pieces : Σ _cut : Fin (size + 1), List ℕ × List ℕ,
            pieces.2.1.Perm (List.range' 1 pieces.1.val) ∧
            ¬ Occurs [2, 3, 1] pieces.2.1 ∧
            pieces.2.2.Perm (List.range' 1 (size - pieces.1.val)) ∧
            ¬ Occurs [2, 3, 1] pieces.2.2 ∧
            word = pieces.2.1 ++ (size + 1) ::
              pieces.2.2.map (fun entry => entry + pieces.1.val) ∧
            recordCuts word = insert (size + 1) (recordCuts pieces.2.1) := by
        have shift_occurrence (pattern entries : List ℕ) (offset : ℕ) :
            Occurs pattern (entries.map (fun entry => entry + offset)) ↔
              Occurs pattern entries := by
          constructor
          · rintro ⟨values, increasing, membership, sublist, _⟩
            refine ⟨fun rank => values rank - offset, ?_, ?_, ?_, by simp⟩
            · intro rank lower upper
              obtain ⟨first, _, first_equal⟩ :=
                List.mem_map.mp (membership rank lower (by omega))
              obtain ⟨second, _, second_equal⟩ :=
                List.mem_map.mp (membership (rank + 1) (by omega) (by omega))
              have comparison := increasing rank lower upper
              change values rank - offset < values (rank + 1) - offset
              omega
            · intro rank lower upper
              obtain ⟨entry, member, equal⟩ := List.mem_map.mp (membership rank lower upper)
              have recovered : values rank - offset = entry := by omega
              simpa only [recovered] using member
            · simpa [List.map_map, Function.comp_def] using
                sublist.map (fun entry => entry - offset)
          · rintro ⟨values, increasing, membership, sublist, _⟩
            refine ⟨fun rank => values rank + offset, ?_, ?_, ?_, by simp⟩
            · intro rank lower upper
              exact Nat.add_lt_add_right (increasing rank lower upper) offset
            · intro rank lower upper
              exact List.mem_map_of_mem (membership rank lower upper)
            · simpa [List.map_map, Function.comp_def] using
                sublist.map (fun entry => entry + offset)
        have maximum_mem : size + 1 ∈ word :=
          permutation.mem_iff.mpr (List.mem_range'.mpr ⟨size, by omega, by omega⟩)
        obtain ⟨left, right, split, absent⟩ := List.eq_append_cons_of_mem maximum_mem
        have distinct : (left ++ (size + 1) :: right).Nodup :=
          split ▸ permutation.nodup_iff.mpr (List.nodup_range' 1)
        have maximum_bound : ∀ entry ∈ left ++ right, entry < size + 1 := by
          intro entry member
          have in_word : entry ∈ word := by
            rw [split]
            rcases List.mem_append.mp member with member | member
            · exact List.mem_append_left _ member
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
          obtain ⟨index, index_bound, equal⟩ :=
            List.mem_range'.mp (permutation.mem_iff.mp in_word)
          have unequal : entry ≠ size + 1 := by
            intro equal
            rw [equal] at member
            rcases List.mem_append.mp member with in_left | in_right
            · exact (List.nodup_append.mp distinct).2.2 (size + 1) in_left
                (size + 1) (by simp) rfl
            · exact (List.nodup_cons.mp (List.nodup_append.mp distinct).2.1).1 in_right
          omega
        obtain ⟨left_avoid, right_avoid, separated⟩ :=
          (avoids231_maxSplit_iff left right (size + 1) maximum_bound distinct).mp
            (split ▸ avoiding)
        have parent_perm : (left ++ right).Perm (List.range' 1 size) := by
          have rearranged := List.perm_middle.symm.trans (split ▸ permutation)
          rw [List.range'_1_concat] at rearranged
          have range_rearranged : (List.range' 1 size ++ [1 + size]).Perm
              ((size + 1) :: List.range' 1 size) := by
            simpa only [List.append_nil, Nat.add_comm] using
              (List.perm_middle : (List.range' 1 size ++ (size + 1) :: []).Perm
                ((size + 1) :: (List.range' 1 size ++ [])))
          exact (rearranged.trans range_rearranged).cons_inv
        have sorted_pair : (left.mergeSort (· ≤ ·) ++ right.mergeSort (· ≤ ·)).Pairwise
            (· ≤ ·) := by
          refine List.pairwise_append.mpr
            ⟨List.pairwise_mergeSort' (· ≤ ·) left,
              List.pairwise_mergeSort' (· ≤ ·) right, ?_⟩
          intro first first_mem second second_mem
          exact (separated first ((List.mergeSort_perm left (· ≤ ·)).mem_iff.mp first_mem)
            second ((List.mergeSort_perm right (· ≤ ·)).mem_iff.mp second_mem)).le
        have sorted : left.mergeSort (· ≤ ·) ++ right.mergeSort (· ≤ ·) =
            List.range' 1 size := by
          apply List.Perm.eq_of_pairwise' sorted_pair List.pairwise_le_range'
          exact ((List.mergeSort_perm left (· ≤ ·)).append
            (List.mergeSort_perm right (· ≤ ·))).trans parent_perm
        obtain ⟨cut, cut_bound, left_sorted, right_sorted⟩ :=
          List.range'_eq_append_iff.mp sorted.symm
        have left_perm : left.Perm (List.range' 1 cut) := by
          simpa only [left_sorted] using (List.mergeSort_perm left (· ≤ ·)).symm
        have right_perm : right.Perm (List.range' (cut + 1) (size - cut)) := by
          simpa only [left_sorted, right_sorted, Nat.mul_one, Nat.add_comm] using
            (List.mergeSort_perm right (· ≤ ·)).symm
        let unshifted := right.map (fun entry => entry - cut)
        have unshifted_perm : unshifted.Perm (List.range' 1 (size - cut)) := by
          simpa only [List.map_sub_range' (by omega : cut ≤ cut + 1), Nat.add_sub_cancel_left]
            using right_perm.map (fun entry => entry - cut)
        have recovered_right : unshifted.map (fun entry => entry + cut) = right := by
          rw [List.map_map]
          conv_rhs => rw [← List.map_id right]
          apply List.map_congr_left
          intro entry member
          have interval := right_perm.mem_iff.mp member
          simp only [List.mem_range'_1] at interval
          change entry - cut + cut = entry
          omega
        have unshifted_avoid : ¬ Occurs [2, 3, 1] unshifted := by
          apply (not_congr (shift_occurrence [2, 3, 1] unshifted cut)).mp
          simpa only [recovered_right] using right_avoid
        have records : recordCuts word = insert (size + 1) (recordCuts left) := by
          ext value
          by_cases equal : value = size + 1
          · subst value
            have record : size + 1 ∈ recordCuts word :=
              (record_mem _ _).mpr ⟨List.mem_toFinset.mpr maximum_mem, by
                rw [split, List.takeWhile_append_of_pos (fun entry member =>
                  decide_eq_true (Nat.ne_of_lt (maximum_bound entry (by simp [member]))))]
                simpa using fun entry member => maximum_bound entry (by simp [member])⟩
            simp only [record, Finset.mem_insert_self]
          · by_cases member : value ∈ left
            · obtain ⟨before, after, left_split, absent⟩ := List.eq_append_cons_of_mem member
              have passed : ∀ entry ∈ before, decide (entry ≠ value) = true :=
                fun entry contained => decide_eq_true (fun equal => absent (equal ▸ contained))
              have taken : word.takeWhile (fun entry => decide (entry ≠ value)) =
                  left.takeWhile (fun entry => decide (entry ≠ value)) := by
                rw [split, left_split, List.append_assoc,
                  List.takeWhile_append_of_pos passed, List.takeWhile_append_of_pos passed]
                simp
              have in_word : value ∈ word := by simp [split, member]
              simp only [Finset.mem_insert, equal, false_or, record_mem,
                List.mem_toFinset, in_word, member, true_and, taken]
            · have not_record : value ∉ recordCuts word := by
                intro record
                obtain ⟨in_word, bound⟩ := (record_mem _ _).mp record
                have in_right : value ∈ right := by
                  simpa only [split, List.mem_append, List.mem_cons, member, equal, false_or]
                    using List.mem_toFinset.mp in_word
                have maximum_before : size + 1 ∈
                    word.takeWhile (fun entry => decide (entry ≠ value)) := by
                  rw [split, List.takeWhile_append_of_pos (fun entry (contained : entry ∈ left) =>
                    decide_eq_true (show entry ≠ value from
                      fun same => member (same ▸ contained)))]
                  simp [Ne.symm equal]
                have too_large := bound (size + 1) maximum_before
                have too_small := maximum_bound value (by simp [in_right])
                omega
              simp only [not_record, Finset.mem_insert, equal, record_mem,
                List.mem_toFinset, member, false_and, or_self]
        refine ⟨⟨⟨cut, by omega⟩, left, unshifted⟩,
          ⟨left_perm, left_avoid, unshifted_perm, unshifted_avoid, ?_, records⟩⟩
        simpa only [recovered_right] using split
      let decomposition := avoiding_decomposition size word.val
        word.property.1 word.property.2
      let pieces := Classical.choose decomposition
      have specification := Classical.choose_spec decomposition
      let left_path := avoiding_encode pieces.1.val
        ⟨pieces.2.1, specification.1, specification.2.1⟩
      let right_path := avoiding_encode (size - pieces.1.val)
        ⟨pieces.2.2, specification.2.2.1, specification.2.2.2.1⟩
      refine ⟨left_path.val + right_path.val.nest, ?_⟩
      rw [DyckWord.semilength_add, DyckWord.semilength_nest,
        left_path.property, right_path.property]
      have cut_bound := pieces.1.is_lt
      omega
termination_by size _ => size
decreasing_by
  all_goals
    have cut_bound := pieces.1.is_lt
    omega

def lastExcursion (path : DyckWord) : DyckWord × DyckWord :=
  if _empty : path = 0 then (0, 0)
  else if path.outsidePart = 0 then (0, path.insidePart)
  else
    let previous := lastExcursion path.outsidePart
    (path.insidePart.nest + previous.1, previous.2)
termination_by path.semilength
decreasing_by exact DyckWord.semilength_outsidePart_lt _empty

theorem last_excursion :
    (∀ path : DyckWord, path ≠ 0 →
      path = (lastExcursion path).1 + (lastExcursion path).2.nest) ∧
      ∀ before inside : DyckWord, lastExcursion (before + inside.nest) = (before, inside) := by
  constructor
  · intro path
    induction length_eq : path.semilength using Nat.strong_induction_on generalizing path with
    | h height induction =>
      intro nonempty
      by_cases outside_empty : path.outsidePart = 0
      · have scan : lastExcursion path = (0, path.insidePart) := by
          rw [lastExcursion, dif_neg nonempty, if_pos outside_empty]
        rw [scan]
        simpa only [outside_empty, add_zero, zero_add] using
          (DyckWord.nest_insidePart_add_outsidePart nonempty).symm
      · have smaller : path.outsidePart.semilength < height := by
          simpa only [length_eq] using DyckWord.semilength_outsidePart_lt nonempty
        have previous := induction _ smaller path.outsidePart rfl outside_empty
        have scan : lastExcursion path =
            (path.insidePart.nest + (lastExcursion path.outsidePart).1,
              (lastExcursion path.outsidePart).2) := by
          rw [lastExcursion, dif_neg nonempty, if_neg outside_empty]
        rw [scan]
        dsimp only
        rw [add_assoc, ← previous]
        exact (DyckWord.nest_insidePart_add_outsidePart nonempty).symm
  · intro before
    induction length_eq : before.semilength using Nat.strong_induction_on generalizing before with
    | h height induction =>
      intro inside
      by_cases empty : before = 0
      · subst before
        rw [zero_add, lastExcursion, dif_neg DyckWord.nest_ne_zero,
          DyckWord.outsidePart_nest, if_pos rfl, DyckWord.insidePart_nest]
      · have composite_nonempty : before + inside.nest ≠ 0 := by
          intro equality
          have lengths := congrArg DyckWord.semilength equality
          simp only [DyckWord.semilength_add, DyckWord.semilength_nest,
            DyckWord.semilength_zero] at lengths
          omega
        have outside_nonempty : (before + inside.nest).outsidePart ≠ 0 := by
          rw [DyckWord.outsidePart_add empty]
          intro equality
          have lengths := congrArg DyckWord.semilength equality
          simp only [DyckWord.semilength_add, DyckWord.semilength_nest,
            DyckWord.semilength_zero] at lengths
          omega
        have smaller : before.outsidePart.semilength < height := by
          simpa only [length_eq] using DyckWord.semilength_outsidePart_lt empty
        have previous := induction _ smaller before.outsidePart rfl inside
        rw [lastExcursion, dif_neg composite_nonempty, if_neg outside_nonempty,
          DyckWord.insidePart_add empty, DyckWord.outsidePart_add empty, previous]
        dsimp only
        rw [DyckWord.nest_insidePart_add_outsidePart empty]

noncomputable def avoiding_decode (path : DyckWord) :
    {word : List ℕ // word.Perm (List.range' 1 path.semilength) ∧ ¬ Occurs [2, 3, 1] word} :=
  if empty : path = 0 then
    ⟨[], by simp [empty], by
      rintro ⟨values, increasing, membership, sublist, _⟩
      have impossible := congrArg List.length (List.sublist_nil.mp sublist)
      simp at impossible⟩
  else by
    let parts := lastExcursion path
    have total : parts.1.semilength + parts.2.semilength + 1 = path.semilength := by
      have lengths := congrArg DyckWord.semilength (last_excursion.1 path empty)
      simpa only [DyckWord.semilength_add, DyckWord.semilength_nest, Nat.add_assoc]
        using lengths.symm
    let left := avoiding_decode parts.1
    let right := avoiding_decode parts.2
    let offset := parts.1.semilength
    let suffix := right.val.map (fun entry => entry + offset)
    have suffix_perm : suffix.Perm (List.range' (offset + 1) parts.2.semilength) := by
      have shifted := right.property.1.map (fun entry => offset + entry)
      rw [List.map_add_range'] at shifted
      simpa only [suffix, Nat.add_comm] using shifted
    have parent_perm : (left.val ++ suffix).Perm
        (List.range' 1 (parts.1.semilength + parts.2.semilength)) := by
      have interval : List.range' 1 (parts.1.semilength + parts.2.semilength) =
          List.range' 1 parts.1.semilength ++
            List.range' (offset + 1) parts.2.semilength := by
        apply List.range'_eq_append_iff.mpr
        refine ⟨offset, by dsimp [offset]; omega, rfl, ?_⟩
        dsimp only [offset]
        simp only [Nat.mul_one, Nat.add_comm, Nat.add_sub_cancel_left]
      rw [interval]
      exact left.property.1.append suffix_perm
    have input_perm : (left.val ++ path.semilength :: suffix).Perm
        (List.range' 1 path.semilength) := by
      have rearranged := List.perm_middle.trans (parent_perm.cons path.semilength)
      rw [← total] at rearranged
      rw [← total, List.range'_1_concat]
      apply rearranged.trans
      simpa only [List.append_nil, Nat.add_comm] using
        (List.perm_middle :
          (List.range' 1 (parts.1.semilength + parts.2.semilength) ++
            (parts.1.semilength + parts.2.semilength + 1) :: []).Perm
          ((parts.1.semilength + parts.2.semilength + 1) ::
            (List.range' 1 (parts.1.semilength + parts.2.semilength) ++ []))).symm
    have maximum_bound : ∀ entry ∈ left.val ++ suffix, entry < path.semilength := by
      intro entry member
      have interval := parent_perm.mem_iff.mp member
      simp only [List.mem_range'_1] at interval
      omega
    have separated : ∀ first ∈ left.val, ∀ second ∈ suffix, first < second := by
      intro first first_mem second second_mem
      have first_interval := left.property.1.mem_iff.mp first_mem
      have second_interval := suffix_perm.mem_iff.mp second_mem
      simp only [List.mem_range'_1] at first_interval second_interval
      dsimp only [offset] at second_interval
      omega
    have suffix_avoid : ¬ Occurs [2, 3, 1] suffix := by
      rintro ⟨values, increasing, membership, sublist, _⟩
      apply right.property.2
      refine ⟨fun rank => values rank - offset, ?_, ?_, ?_, by simp⟩
      · intro rank lower upper
        obtain ⟨first, _, first_equal⟩ := List.mem_map.mp (membership rank lower (by omega))
        obtain ⟨second, _, second_equal⟩ :=
          List.mem_map.mp (membership (rank + 1) (by omega) (by omega))
        have comparison := increasing rank lower upper
        change values rank - offset < values (rank + 1) - offset
        omega
      · intro rank lower upper
        obtain ⟨entry, member, equal⟩ := List.mem_map.mp (membership rank lower upper)
        have recovered : values rank - offset = entry := by omega
        simpa only [recovered] using member
      · simpa [suffix, List.map_map, Function.comp_def] using
          sublist.map (fun entry => entry - offset)
    refine ⟨left.val ++ path.semilength :: suffix, input_perm, ?_⟩
    exact (avoids231_maxSplit_iff left.val suffix path.semilength maximum_bound
      (input_perm.nodup_iff.mpr (List.nodup_range' 1))).mpr
        ⟨left.property.2, suffix_avoid, separated⟩
termination_by path.semilength
decreasing_by
  all_goals
    have total_length := total
    dsimp only [parts] at total_length ⊢
    omega

def excursions (path : DyckWord) : List DyckWord :=
  if _empty : path = 0 then []
  else path.insidePart :: excursions path.outsidePart
termination_by path.semilength
decreasing_by exact DyckWord.semilength_outsidePart_lt _empty

theorem avoiding_inverse :
    (∀ size word, (avoiding_decode (avoiding_encode size word).val).val = word.val) ∧
      (∀ path, (avoiding_encode path.semilength (avoiding_decode path)).val = path) ∧
      ∀ size word, (recordCuts word.val).card =
        (excursions (avoiding_encode size word).val).length := by
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
  have avoiding_decomposition (size : ℕ) (word : List ℕ)
      (permutation : word.Perm (List.range' 1 (size + 1)))
      (avoiding : ¬ Occurs [2, 3, 1] word) :
      ∃ pieces : Σ _cut : Fin (size + 1), List ℕ × List ℕ,
        pieces.2.1.Perm (List.range' 1 pieces.1.val) ∧
        ¬ Occurs [2, 3, 1] pieces.2.1 ∧
        pieces.2.2.Perm (List.range' 1 (size - pieces.1.val)) ∧
        ¬ Occurs [2, 3, 1] pieces.2.2 ∧
        word = pieces.2.1 ++ (size + 1) ::
          pieces.2.2.map (fun entry => entry + pieces.1.val) ∧
        recordCuts word = insert (size + 1) (recordCuts pieces.2.1) := by
    have shift_occurrence (pattern entries : List ℕ) (offset : ℕ) :
        Occurs pattern (entries.map (fun entry => entry + offset)) ↔
          Occurs pattern entries := by
      constructor
      · rintro ⟨values, increasing, membership, sublist, _⟩
        refine ⟨fun rank => values rank - offset, ?_, ?_, ?_, by simp⟩
        · intro rank lower upper
          obtain ⟨first, _, first_equal⟩ := List.mem_map.mp (membership rank lower (by omega))
          obtain ⟨second, _, second_equal⟩ :=
            List.mem_map.mp (membership (rank + 1) (by omega) (by omega))
          have comparison := increasing rank lower upper
          change values rank - offset < values (rank + 1) - offset
          omega
        · intro rank lower upper
          obtain ⟨entry, member, equal⟩ := List.mem_map.mp (membership rank lower upper)
          have recovered : values rank - offset = entry := by omega
          simpa only [recovered] using member
        · simpa [List.map_map, Function.comp_def] using
            sublist.map (fun entry => entry - offset)
      · rintro ⟨values, increasing, membership, sublist, _⟩
        refine ⟨fun rank => values rank + offset, ?_, ?_, ?_, by simp⟩
        · intro rank lower upper
          exact Nat.add_lt_add_right (increasing rank lower upper) offset
        · intro rank lower upper
          exact List.mem_map_of_mem (membership rank lower upper)
        · simpa [List.map_map, Function.comp_def] using
            sublist.map (fun entry => entry + offset)
    have maximum_mem : size + 1 ∈ word :=
      permutation.mem_iff.mpr (List.mem_range'.mpr ⟨size, by omega, by omega⟩)
    obtain ⟨left, right, split, absent⟩ := List.eq_append_cons_of_mem maximum_mem
    have distinct : (left ++ (size + 1) :: right).Nodup :=
      split ▸ permutation.nodup_iff.mpr (List.nodup_range' 1)
    have maximum_bound : ∀ entry ∈ left ++ right, entry < size + 1 := by
      intro entry member
      have in_word : entry ∈ word := by
        rw [split]
        rcases List.mem_append.mp member with member | member
        · exact List.mem_append_left _ member
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
      obtain ⟨index, index_bound, equal⟩ := List.mem_range'.mp (permutation.mem_iff.mp in_word)
      have unequal : entry ≠ size + 1 := by
        intro equal
        rw [equal] at member
        rcases List.mem_append.mp member with in_left | in_right
        · exact (List.nodup_append.mp distinct).2.2 (size + 1) in_left
            (size + 1) (by simp) rfl
        · exact (List.nodup_cons.mp (List.nodup_append.mp distinct).2.1).1 in_right
      omega
    obtain ⟨left_avoid, right_avoid, separated⟩ :=
      (avoids231_maxSplit_iff left right (size + 1) maximum_bound distinct).mp (split ▸ avoiding)
    have parent_perm : (left ++ right).Perm (List.range' 1 size) := by
      have rearranged := List.perm_middle.symm.trans (split ▸ permutation)
      rw [List.range'_1_concat] at rearranged
      have range_rearranged : (List.range' 1 size ++ [1 + size]).Perm
          ((size + 1) :: List.range' 1 size) := by
        simpa only [List.append_nil, Nat.add_comm] using
          (List.perm_middle : (List.range' 1 size ++ (size + 1) :: []).Perm
            ((size + 1) :: (List.range' 1 size ++ [])))
      exact (rearranged.trans range_rearranged).cons_inv
    have sorted_pair : (left.mergeSort (· ≤ ·) ++ right.mergeSort (· ≤ ·)).Pairwise
        (· ≤ ·) := by
      refine List.pairwise_append.mpr
        ⟨List.pairwise_mergeSort' (· ≤ ·) left,
          List.pairwise_mergeSort' (· ≤ ·) right, ?_⟩
      intro first first_mem second second_mem
      exact (separated first ((List.mergeSort_perm left (· ≤ ·)).mem_iff.mp first_mem)
        second ((List.mergeSort_perm right (· ≤ ·)).mem_iff.mp second_mem)).le
    have sorted : left.mergeSort (· ≤ ·) ++ right.mergeSort (· ≤ ·) =
        List.range' 1 size := by
      apply List.Perm.eq_of_pairwise' sorted_pair List.pairwise_le_range'
      exact ((List.mergeSort_perm left (· ≤ ·)).append
        (List.mergeSort_perm right (· ≤ ·))).trans parent_perm
    obtain ⟨cut, cut_bound, left_sorted, right_sorted⟩ :=
      List.range'_eq_append_iff.mp sorted.symm
    have left_perm : left.Perm (List.range' 1 cut) := by
      simpa only [left_sorted] using (List.mergeSort_perm left (· ≤ ·)).symm
    have right_perm : right.Perm (List.range' (cut + 1) (size - cut)) := by
      simpa only [left_sorted, right_sorted, Nat.mul_one, Nat.add_comm] using
        (List.mergeSort_perm right (· ≤ ·)).symm
    let unshifted := right.map (fun entry => entry - cut)
    have unshifted_perm : unshifted.Perm (List.range' 1 (size - cut)) := by
      simpa only [List.map_sub_range' (by omega : cut ≤ cut + 1), Nat.add_sub_cancel_left]
        using right_perm.map (fun entry => entry - cut)
    have recovered_right : unshifted.map (fun entry => entry + cut) = right := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id right]
      apply List.map_congr_left
      intro entry member
      have interval := right_perm.mem_iff.mp member
      simp only [List.mem_range'_1] at interval
      change entry - cut + cut = entry
      omega
    have unshifted_avoid : ¬ Occurs [2, 3, 1] unshifted := by
      apply (not_congr (shift_occurrence [2, 3, 1] unshifted cut)).mp
      simpa only [recovered_right] using right_avoid
    have records : recordCuts word = insert (size + 1) (recordCuts left) := by
      ext value
      by_cases equal : value = size + 1
      · subst value
        have record : size + 1 ∈ recordCuts word :=
          (record_mem _ _).mpr ⟨List.mem_toFinset.mpr maximum_mem, by
            rw [split, List.takeWhile_append_of_pos (fun entry member =>
              decide_eq_true (Nat.ne_of_lt (maximum_bound entry (by simp [member]))))]
            simpa using fun entry member => maximum_bound entry (by simp [member])⟩
        simp only [record, Finset.mem_insert_self]
      · by_cases member : value ∈ left
        · obtain ⟨before, after, left_split, absent⟩ := List.eq_append_cons_of_mem member
          have passed : ∀ entry ∈ before, decide (entry ≠ value) = true :=
            fun entry contained => decide_eq_true (fun equal => absent (equal ▸ contained))
          have taken : word.takeWhile (fun entry => decide (entry ≠ value)) =
              left.takeWhile (fun entry => decide (entry ≠ value)) := by
            rw [split, left_split, List.append_assoc,
              List.takeWhile_append_of_pos passed, List.takeWhile_append_of_pos passed]
            simp
          have in_word : value ∈ word := by simp [split, member]
          simp only [Finset.mem_insert, equal, false_or, record_mem,
            List.mem_toFinset, in_word, member, true_and, taken]
        · have not_record : value ∉ recordCuts word := by
            intro record
            obtain ⟨in_word, bound⟩ := (record_mem _ _).mp record
            have in_right : value ∈ right := by
              simpa only [split, List.mem_append, List.mem_cons, member, equal, false_or]
                using List.mem_toFinset.mp in_word
            have maximum_before : size + 1 ∈
                word.takeWhile (fun entry => decide (entry ≠ value)) := by
              rw [split, List.takeWhile_append_of_pos (fun entry (contained : entry ∈ left) =>
                decide_eq_true (show entry ≠ value from fun same => member (same ▸ contained)))]
              simp [Ne.symm equal]
            have too_large := bound (size + 1) maximum_before
            have too_small := maximum_bound value (by simp [in_right])
            omega
          simp only [not_record, Finset.mem_insert, equal, record_mem,
            List.mem_toFinset, member, false_and, or_self]
    refine ⟨⟨⟨cut, by omega⟩, left, unshifted⟩,
      ⟨left_perm, left_avoid, unshifted_perm, unshifted_avoid, ?_, records⟩⟩
    simpa only [recovered_right] using split
  have decode_step (before inside : DyckWord) :
      (avoiding_decode (before + inside.nest)).val =
        (avoiding_decode before).val ++
          (before.semilength + inside.semilength + 1) ::
            (avoiding_decode inside).val.map (fun entry => entry + before.semilength) := by
    have nonempty : before + inside.nest ≠ 0 := by
      intro equal
      have lengths := congrArg DyckWord.semilength equal
      simp only [DyckWord.semilength_add, DyckWord.semilength_nest,
        DyckWord.semilength_zero] at lengths
      omega
    rw [avoiding_decode, dif_neg nonempty]
    dsimp only
    rw [last_excursion.2]
    simp only [DyckWord.semilength_add, DyckWord.semilength_nest, Nat.add_assoc]
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
  have encode_step (size : ℕ)
      (word : {word : List ℕ //
        word.Perm (List.range' 1 (size + 1)) ∧ ¬ Occurs [2, 3, 1] word})
      (cut : Fin (size + 1))
      (left : {word : List ℕ // word.Perm (List.range' 1 cut.val) ∧
        ¬ Occurs [2, 3, 1] word})
      (right : {word : List ℕ // word.Perm (List.range' 1 (size - cut.val)) ∧
        ¬ Occurs [2, 3, 1] word})
      (split : word.val = left.val ++ (size + 1) ::
        right.val.map (fun entry => entry + cut.val)) :
      (avoiding_encode (size + 1) word).val =
        (avoiding_encode cut.val left).val +
          (avoiding_encode (size - cut.val) right).val.nest := by
    let existence := avoiding_decomposition size word.val
      word.property.1 word.property.2
    let chosen := Classical.choose existence
    have spec := Classical.choose_spec existence
    have taken (initial : List ℕ) (suffix : List ℕ)
        (bound : ∀ entry ∈ initial, entry < size + 1) :
        (initial ++ (size + 1) :: suffix).takeWhile
          (fun entry => decide (entry ≠ size + 1)) = initial := by
      rw [List.takeWhile_append_of_pos (fun entry member =>
        decide_eq_true (Nat.ne_of_lt (bound entry member)))]
      simp
    have left_bound : ∀ entry ∈ left.val, entry < size + 1 := by
      intro entry member
      have interval := left.property.1.mem_iff.mp member
      simp only [List.mem_range'_1] at interval
      have bounded := cut.is_lt
      omega
    have chosen_bound : ∀ entry ∈ chosen.2.1, entry < size + 1 := by
      intro entry member
      have interval := spec.1.mem_iff.mp member
      simp only [List.mem_range'_1] at interval
      have bounded := chosen.1.is_lt
      omega
    have prefixes : chosen.2.1 = left.val := by
      have equality := congrArg
        (List.takeWhile (fun entry => decide (entry ≠ size + 1)))
        (spec.2.2.2.2.1.symm.trans split)
      change (chosen.2.1 ++ (size + 1) ::
        chosen.2.2.map (fun entry => entry + chosen.1.val)).takeWhile _ = _ at equality
      simpa only [taken _ _ chosen_bound, taken _ _ left_bound] using equality
    have cuts : chosen.1 = cut := by
      apply Fin.ext
      have lengths := congrArg List.length prefixes
      rw [spec.1.length_eq, left.property.1.length_eq] at lengths
      simpa only [List.length_range'] using lengths
    have suffixes : chosen.2.2 = right.val := by
      have equality := spec.2.2.2.2.1.symm.trans split
      rw [prefixes, cuts] at equality
      have mapped := (List.cons.inj (List.append_cancel_left equality)).2
      exact (List.map_inj_right (fun first second equal =>
        Nat.add_right_cancel equal)).mp mapped
    rw [avoiding_encode]
    change (avoiding_encode chosen.1.val
      ⟨chosen.2.1, spec.1, spec.2.1⟩).val +
      (avoiding_encode (size - chosen.1.val)
        ⟨chosen.2.2, spec.2.2.1, spec.2.2.2.1⟩).val.nest = _
    rw [transport _ _ _ left (congrArg Fin.val cuts) prefixes,
      transport _ _ _ right (congrArg (fun index : Fin (size + 1) => size - index.val)
        cuts) suffixes]
  constructor
  · intro size
    induction size using Nat.strong_induction_on with
    | h size induction =>
      intro word
      cases size with
      | zero =>
        have empty : word.val = [] := List.Perm.eq_nil
          (by simpa only [List.range'_zero] using word.property.1)
        simp [avoiding_encode, avoiding_decode, empty]
      | succ size =>
        obtain ⟨pieces, spec⟩ := avoiding_decomposition size word.val
          word.property.1 word.property.2
        let left : {word : List ℕ // word.Perm (List.range' 1 pieces.1.val) ∧
          ¬ Occurs [2, 3, 1] word} := ⟨pieces.2.1, spec.1, spec.2.1⟩
        let right : {word : List ℕ // word.Perm (List.range' 1 (size - pieces.1.val)) ∧
          ¬ Occurs [2, 3, 1] word} := ⟨pieces.2.2, spec.2.2.1, spec.2.2.2.1⟩
        rw [encode_step size word pieces.1 left right spec.2.2.2.2.1, decode_step]
        have smaller_left : pieces.1.val < size + 1 := pieces.1.is_lt
        have smaller_right : size - pieces.1.val < size + 1 := by omega
        rw [induction _ smaller_left left, induction _ smaller_right right,
          (avoiding_encode _ left).property, (avoiding_encode _ right).property]
        rw [show pieces.1.val + (size - pieces.1.val) + 1 = size + 1 by omega]
        exact spec.2.2.2.2.1.symm
  · constructor
    · intro path
      suffices inverse : ∀ height, ∀ path : DyckWord, path.semilength = height →
          (avoiding_encode path.semilength (avoiding_decode path)).val = path from
        inverse path.semilength path rfl
      intro height
      induction height using Nat.strong_induction_on with
      | h height induction =>
        intro path height_eq
        by_cases empty : path = 0
        · subst path
          let empty_word : {word : List ℕ // word.Perm (List.range' 1 0) ∧
            ¬ Occurs [2, 3, 1] word} := ⟨(avoiding_decode 0).val, by
              simpa only [DyckWord.semilength_zero] using (avoiding_decode 0).property⟩
          exact (transport _ _ (avoiding_decode 0) empty_word
            DyckWord.semilength_zero rfl).trans
              (congrArg Subtype.val (avoiding_encode.eq_1 empty_word))
        · let parts := lastExcursion path
          have reconstruction : path = parts.1 + parts.2.nest := last_excursion.1 path empty
          have total : parts.1.semilength + parts.2.semilength + 1 = path.semilength := by
            rw [reconstruction, DyckWord.semilength_add, DyckWord.semilength_nest]
            omega
          have positive : 0 < path.semilength := by omega
          obtain ⟨size, successor_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
          have size_eq : path.semilength = size + 1 := successor_eq
          have cut_bound : parts.1.semilength < size + 1 := by omega
          have right_size : size - parts.1.semilength = parts.2.semilength := by omega
          have decoded : (avoiding_decode path).val =
              (avoiding_decode parts.1).val ++ (size + 1) ::
                (avoiding_decode parts.2).val.map
                  (fun entry => entry + parts.1.semilength) := by
            conv_lhs => rw [reconstruction]
            rw [decode_step]
            congr 2
            omega
          have encoded := encode_step size
            ⟨(avoiding_decode path).val, by
              rw [← size_eq]; exact (avoiding_decode path).property⟩
            ⟨parts.1.semilength, cut_bound⟩ (avoiding_decode parts.1)
            ⟨(avoiding_decode parts.2).val, by
              rw [right_size]; exact (avoiding_decode parts.2).property⟩ decoded
          have smaller_left : parts.1.semilength < height := by omega
          have smaller_right : parts.2.semilength < height := by omega
          have left_inverse := induction _ smaller_left parts.1 rfl
          have right_inverse := induction _ smaller_right parts.2 rfl
          have right_equal :
              (avoiding_encode (size - parts.1.semilength)
                ⟨(avoiding_decode parts.2).val, by
                  rw [right_size]; exact (avoiding_decode parts.2).property⟩).val = parts.2 := by
            exact (transport _ _ _ (avoiding_decode parts.2) right_size rfl).trans right_inverse
          rw [left_inverse, right_equal] at encoded
          have parent_equal :
              (avoiding_encode (size + 1)
                ⟨(avoiding_decode path).val, by
                  rw [← size_eq]; exact (avoiding_decode path).property⟩).val = path :=
            encoded.trans reconstruction.symm
          exact (transport _ _ (avoiding_decode path) _ size_eq rfl).trans parent_equal
    · have excursion_add : ∀ before inside : DyckWord,
          excursions (before + inside.nest) = excursions before ++ [inside] := by
        intro before
        induction height_eq : before.semilength using Nat.strong_induction_on
            generalizing before with
        | h height induction =>
          intro inside
          by_cases empty : before = 0
          · subst before
            rw [zero_add, excursions.eq_def inside.nest, dif_neg DyckWord.nest_ne_zero,
              DyckWord.insidePart_nest, DyckWord.outsidePart_nest,
              excursions.eq_def 0, dif_pos rfl, List.nil_append]
          · have nonempty : before + inside.nest ≠ 0 := by
              intro equal
              have lengths := congrArg DyckWord.semilength equal
              simp only [DyckWord.semilength_add, DyckWord.semilength_nest,
                DyckWord.semilength_zero] at lengths
              omega
            rw [excursions.eq_def (before + inside.nest), dif_neg nonempty,
              excursions.eq_def before, dif_neg empty,
              DyckWord.insidePart_add empty, DyckWord.outsidePart_add empty]
            have smaller : before.outsidePart.semilength < height := by
              rw [← height_eq]
              exact DyckWord.semilength_outsidePart_lt empty
            rw [induction _ smaller before.outsidePart rfl inside, List.cons_append]
      intro size
      induction size using Nat.strong_induction_on with
      | h size induction =>
        intro word
        cases size with
        | zero =>
          have empty : word.val = [] := List.Perm.eq_nil
            (by simpa only [List.range'_zero] using word.property.1)
          rw [avoiding_encode.eq_1]
          rw [excursions.eq_def 0, dif_pos rfl]
          simp only [empty, recordCuts, List.toFinset_nil, Finset.filter_empty,
            Finset.card_empty, List.length_nil]
        | succ size =>
          obtain ⟨pieces, spec⟩ := avoiding_decomposition size word.val
            word.property.1 word.property.2
          let left : {word : List ℕ // word.Perm (List.range' 1 pieces.1.val) ∧
            ¬ Occurs [2, 3, 1] word} := ⟨pieces.2.1, spec.1, spec.2.1⟩
          let right : {word : List ℕ // word.Perm (List.range' 1 (size - pieces.1.val)) ∧
            ¬ Occurs [2, 3, 1] word} := ⟨pieces.2.2, spec.2.2.1, spec.2.2.2.1⟩
          have absent : size + 1 ∉ recordCuts pieces.2.1 := by
            intro member
            have interval := spec.1.mem_iff.mp
              (List.mem_toFinset.mp (Finset.mem_filter.mp member).1)
            simp only [List.mem_range'_1] at interval
            have bound := pieces.1.is_lt
            omega
          rw [encode_step size word pieces.1 left right spec.2.2.2.2.1,
            excursion_add, List.length_append, List.length_singleton,
            spec.2.2.2.2.2, Finset.card_insert_of_notMem absent]
          rw [← induction _ pieces.1.is_lt left]

def excursion_equiv : DyckWord ≃ List DyckWord where
  toFun := excursions
  invFun pieces := (pieces.map DyckWord.nest).sum
  left_inv path := by
    change ((excursions path).map DyckWord.nest).sum = path
    induction height_eq : path.semilength using Nat.strong_induction_on generalizing path with
    | h height induction =>
      by_cases empty : path = 0
      · subst path
        rw [excursions.eq_def, dif_pos rfl]
        rfl
      · rw [excursions.eq_def, dif_neg empty, List.map_cons, List.sum_cons]
        have smaller : path.outsidePart.semilength < height := by
          rw [← height_eq]
          exact DyckWord.semilength_outsidePart_lt empty
        rw [induction _ smaller path.outsidePart rfl]
        exact DyckWord.nest_insidePart_add_outsidePart empty
  right_inv pieces := by
    change excursions ((pieces.map DyckWord.nest).sum) = pieces
    induction pieces with
    | nil =>
      rw [List.map_nil, List.sum_nil, excursions.eq_def, dif_pos rfl]
    | cons inside pieces induction =>
      rw [List.map_cons, List.sum_cons]
      have nonempty : inside.nest + (pieces.map DyckWord.nest).sum ≠ 0 := by
        intro equal
        have lengths := congrArg DyckWord.semilength equal
        simp only [DyckWord.semilength_add, DyckWord.semilength_nest,
          DyckWord.semilength_zero] at lengths
        omega
      rw [excursions.eq_def, dif_neg nonempty,
        DyckWord.insidePart_add DyckWord.nest_ne_zero, DyckWord.insidePart_nest,
        DyckWord.outsidePart_add DyckWord.nest_ne_zero, DyckWord.outsidePart_nest,
        zero_add, induction]

end D5.S1.Words.Patterns.ShiehYangYuTwelveDotDyck
