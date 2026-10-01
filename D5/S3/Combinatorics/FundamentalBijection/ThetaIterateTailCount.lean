/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateTailCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateTailCount
   mirror-E: none(waiver:fixed-tail-counting-bijection)
   anchors: []
   utility: none
   digest: Appending and deleting the final maximum biject every finite iterate-avoidance layer. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTail
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateScan
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTailCount

open D5.S3.Combinatorics.FundamentalBijection
open ThetaFixedDefs
open D5.S3.Combinatorics.ArrowWilfDefs

open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
open D5.S3.Combinatorics.FundamentalBijection.ThetaIteratePosition

local notation "B" =>
  (fun word : List ℕ => List.map (hat word) (List.range' 1 (List.length word)))

set_option maxHeartbeats 1600000 in
theorem final_tail_count (size layers : ℕ) :
    {word : List ℕ | word ∈ ThetaIterateDefs.iterateAvoiders (size + 1) layers [1, 3, 2] ∧
      word.getD size 0 = size + 1}.ncard =
      (ThetaIterateDefs.iterateAvoiders size layers [1, 3, 2]).ncard := by
  have theta_record_inverse (word : List ℕ)
      (valid : word.Perm (List.range' 1 word.length)) :
      (∀ seed, seed.Perm (List.range' 1 seed.length) → theta (B seed) = seed) ∧
      (∀ seed, seed.Perm (List.range' 1 seed.length) →
        (B seed).Perm (List.range' 1 seed.length)) ∧
      (theta word).Perm (List.range' 1 word.length) ∧ B (theta word) = word := by
    open ThetaBasicInverseGeneral ThetaBasicInverseBlocks in
    have cuts (seed : List ℕ) (start : ℕ) (bound : start < seed.length) :
        let finish := nextBoundary (IsLtrMax seed) seed.length start
        start < finish ∧ finish ≤ seed.length ∧
          (finish = seed.length ∨ IsLtrMax seed finish) ∧
          ∀ index, start < index → index < finish → ¬ IsLtrMax seed index := by
      simp only [nextBoundary, dif_pos bound]
      let predicate := fun finish => start < finish ∧ finish ≤ seed.length ∧
        (finish = seed.length ∨ IsLtrMax seed finish)
      have exists_cut : ∃ finish, predicate finish :=
        ⟨seed.length, bound, le_refl _, Or.inl rfl⟩
      have spec := Nat.find_spec exists_cut
      refine ⟨spec.1, spec.2.1, spec.2.2, ?_⟩
      intro index after before record
      have := Nat.find_min' exists_cut ⟨after, by omega, Or.inr record⟩
      omega
    have inverse_left (seed : List ℕ)
        (valid : seed.Perm (List.range' 1 seed.length)) : theta (B seed) = seed := by
      let records := (List.Ico 0 seed.length).filter (IsLtrMax seed)
      have distinct : seed.Nodup := valid.nodup_iff.mpr List.nodup_range'
      have entry (index : ℕ) (bound : index < seed.length) :
          seed.getD index 0 ∈ seed := by
        rw [List.getD_eq_getElem _ 0 bound]; exact List.getElem_mem bound
      have leader (index : ℕ) (bound : index < seed.length)
          (record : IsLtrMax seed index) :
          ThetaFixedDefs.IsLeader (B seed) (seed.getD index 0) := by
        have boundary := cuts seed index bound
        rw [ThetaFixedDefs.IsLeader, cycleFrom_B_record_block seed valid index
          (nextBoundary (IsLtrMax seed) seed.length index) boundary.1 boundary.2.1
          record boundary.2.2.2 boundary.2.2.1]
        intro value member
        obtain ⟨offset, offset_bound, value_eq⟩ := List.mem_iff_getElem.mp member
        have offset_limit : index + offset <
            nextBoundary (IsLtrMax seed) seed.length index := by
          have := List.length_take_le
            (nextBoundary (IsLtrMax seed) seed.length index - index) (seed.drop index)
          omega
        have position_bound : index + offset < seed.length := by omega
        have greatest : Nat.findGreatest (IsLtrMax seed) (index + offset) = index :=
          Nat.findGreatest_eq_iff.mpr ⟨by omega, fun _ => record,
            fun position after before => boundary.2.2.2 position after (by omega)⟩
        rw [← value_eq, List.getElem_take, List.getElem_drop]
        simpa only [greatest, List.getD_eq_getElem _ 0 position_bound] using
          last_record_bounds_prefix seed (index + offset) position_bound
            (index + offset) (le_refl _)
      have leaders : (List.range' 1 seed.length).filter
          (fun value => decide (ThetaFixedDefs.IsLeader (B seed) value)) =
          records.map (fun index => seed.getD index 0) := by
        apply List.Pairwise.eq_of_mem_iff
          ((List.pairwise_lt_range' 1 (by omega : 0 < (1 : ℕ))).filter _)
        · apply List.pairwise_iff_getElem.mpr
          intro left right left_bound right_bound ordered
          have left_record : left < records.length := by simpa using left_bound
          have right_record : right < records.length := by simpa using right_bound
          simp only [List.getElem_map]
          have indices := List.pairwise_iff_getElem.mp
            ((List.Ico.pairwise_lt 0 seed.length).filter (IsLtrMax seed))
            left right left_record right_record ordered
          exact (decide_eq_true_eq.mp
            (List.mem_filter.mp (List.getElem_mem right_record)).2) _ indices
        · intro value
          constructor
          · intro member
            obtain ⟨in_range, is_leader⟩ := List.mem_filter.mp member
            have in_seed := valid.mem_iff.mpr in_range
            have record : IsLtrMax seed (seed.idxOf value) := by
              by_contra not_record
              exact nonrecord_not_B_leader seed valid value in_seed not_record
                (decide_eq_true_eq.mp is_leader)
            have bound := List.idxOf_lt_length_of_mem in_seed
            refine List.mem_map.mpr ⟨seed.idxOf value,
              List.mem_filter.mpr ⟨List.Ico.mem.mpr ⟨Nat.zero_le _, bound⟩,
                decide_eq_true record⟩, ?_⟩
            rw [List.getD_eq_getElem _ 0 bound]; exact List.getElem_idxOf bound
          · intro member
            obtain ⟨index, in_records, rfl⟩ := List.mem_map.mp member
            obtain ⟨in_interval, record⟩ := List.mem_filter.mp in_records
            have bound := (List.Ico.mem.mp in_interval).2
            exact List.mem_filter.mpr ⟨valid.mem_iff.mp (entry index bound),
              decide_eq_true (leader index bound (decide_eq_true_eq.mp record))⟩
      unfold theta
      rw [show (B seed).length = seed.length by simp, leaders, List.flatMap_map]
      have cycles : ∀ index ∈ records, ThetaFixedDefs.cycleFrom (B seed)
          (seed.getD index 0) = (seed.drop index).take
            (nextBoundary (IsLtrMax seed) seed.length index - index) := by
        intro index member
        obtain ⟨in_interval, record⟩ := List.mem_filter.mp member
        have boundary := cuts seed index (List.Ico.mem.mp in_interval).2
        exact cycleFrom_B_record_block seed valid index _ boundary.1 boundary.2.1
          (decide_eq_true_eq.mp record) boundary.2.2.2 boundary.2.2.1
      rw [List.flatMap_congr cycles]
      simpa only [records, List.Ico.zero_bot, Nat.zero_le, List.drop_zero] using
        filter_interval_partition seed (IsLtrMax seed) 0 (Nat.zero_le _)
          (by intro _ index impossible; omega)
    have inverse_valid (seed : List ℕ)
        (valid : seed.Perm (List.range' 1 seed.length)) :
        (B seed).Perm (List.range' 1 seed.length) := by
      have distinct : seed.Nodup := valid.nodup_iff.mpr List.nodup_range'
      have mapped_distinct := distinct.map_on (hat_inj_on seed distinct)
      have subset : (seed.map (hat seed)).toFinset ⊆ seed.toFinset := by
        intro value member
        obtain ⟨predecessor, in_seed, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
        have bound := List.idxOf_lt_length_of_mem in_seed
        apply List.mem_toFinset.mpr
        unfold hat
        dsimp only
        split_ifs with branch
        · rw [List.getD_eq_getElem _ 0 branch.1]; exact List.getElem_mem branch.1
        · have record_bound : Nat.findGreatest (IsLtrMax seed)
              (seed.idxOf predecessor) < seed.length :=
            lt_of_le_of_lt (Nat.findGreatest_le _) bound
          rw [List.getD_eq_getElem _ 0 record_bound]; exact List.getElem_mem record_bound
      have equal_card : (seed.map (hat seed)).toFinset.card = seed.toFinset.card := by
        simp [List.card_toFinset, List.dedup_eq_self.mpr mapped_distinct,
          List.dedup_eq_self.mpr distinct]
      exact ((valid.symm.map _).trans
        (List.perm_of_nodup_nodup_toFinset_eq mapped_distinct distinct
          (Finset.eq_of_subset_of_card_le subset (by omega)))).trans valid
    let words := {seed : List ℕ // seed.Perm (List.range' 1 word.length)}
    have finite_words : Set.Finite {seed : List ℕ |
        seed.Perm (List.range' 1 word.length)} := by
      convert (List.permutations (List.range' 1 word.length)).finite_toSet using 1
      ext seed; exact List.mem_permutations.symm
    have : Finite words := finite_words
    have valid_word (seed : words) : seed.val.Perm (List.range' 1 seed.val.length) := by
      have length_eq : seed.val.length = word.length := by simpa using seed.property.length_eq
      simpa only [length_eq] using seed.property
    let inverse : words → words := fun seed => ⟨B seed.val, by
      have length_eq : seed.val.length = word.length := by simpa using seed.property.length_eq
      simpa only [length_eq] using inverse_valid seed.val (valid_word seed)⟩
    have injective : Function.Injective inverse := by
      intro left right equal
      have maps_equal : B left.val = B right.val := congrArg Subtype.val equal
      apply Subtype.ext
      rw [← inverse_left left.val (valid_word left),
        maps_equal, inverse_left right.val (valid_word right)]
    obtain ⟨seed, equal⟩ := Finite.surjective_of_injective injective (⟨word, valid⟩ : words)
    have canonical : B seed.val = word := congrArg Subtype.val equal
    have image_eq : theta word = seed.val := by
      exact (congrArg theta canonical).symm.trans (inverse_left seed.val (valid_word seed))
    exact ⟨inverse_left, inverse_valid, by rw [image_eq]; exact seed.property,
      by rw [image_eq]; exact canonical⟩
  have append_max_132_iff (dimension : ℕ) (word : List ℕ)
      (hperm : word.Perm (List.range' 1 dimension)) :
      (¬ Contains [1, 3, 2] [] 3 (word ++ [dimension + 1])) ↔
        ¬ Contains [1, 3, 2] [] 3 word := by
    rw [ThetaIterateScan.avoids132_append_iff]
    constructor
    · exact And.left
    · intro havoid
      refine ⟨havoid, ?_⟩
      intro first middle _ hmiddle hcross
      have hmember : word.getD middle 0 ∈ word := by
        rw [List.getD_eq_getElem _ 0 hmiddle]
        exact List.getElem_mem hmiddle
      obtain ⟨index, hindex, hvalue⟩ :=
        List.mem_range'.mp (hperm.mem_iff.mp hmember)
      omega
  let seeds := ThetaIterateDefs.iterateAvoiders size layers [1, 3, 2]
  let family : Set (List ℕ) := {word |
    word ∈ ThetaIterateDefs.iterateAvoiders (size + 1) layers [1, 3, 2] ∧
      word.getD size 0 = size + 1}
  let extend : List ℕ → List ℕ := fun word => word ++ [size + 1]
  have hrange : List.range' 1 (size + 1) = List.range' 1 size ++ [size + 1] := by
    simpa [Nat.add_comm] using
      (List.range'_append_1 (s := 1) (m := size) (n := 1)).symm
  have orbit_perm (word : List ℕ) (hperm : word.Perm (List.range' 1 size)) (power : ℕ) :
      (theta^[power] word).Perm (List.range' 1 size) := by
    induction power with
    | zero => exact hperm
    | succ power ih =>
      rw [Function.iterate_succ_apply']
      have hlength : (theta^[power] word).length = size := by simpa using ih.length_eq
      have hperm' : (theta^[power] word).Perm
          (List.range' 1 (theta^[power] word).length) := by
        simpa only [hlength] using ih
      simpa only [hlength] using (theta_record_inverse _ hperm').2.2.1
  have orbit_extend (word : List ℕ) (hperm : word.Perm (List.range' 1 size)) (power : ℕ) :
      theta^[power] (extend word) = theta^[power] word ++ [size + 1] := by
    induction power with
    | zero => rfl
    | succ power ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      have hpermPower := orbit_perm word hperm power
      have hlength : (theta^[power] word).length = size := by
        simpa using hpermPower.length_eq
      have hperm' : (theta^[power] word).Perm
          (List.range' 1 (theta^[power] word).length) := by
        simpa only [hlength] using hpermPower
      simpa only [hlength] using ThetaIterateTail.theta_append_max _ hperm'
  have membership (word : List ℕ) (hperm : word.Perm (List.range' 1 size)) :
      extend word ∈ family ↔ word ∈ seeds := by
    have hlength : word.length = size := by simpa using hperm.length_eq
    constructor
    · intro hword
      refine ⟨hperm, ?_⟩
      intro power hpower
      have havoid := hword.1.2 power hpower
      rw [orbit_extend word hperm power] at havoid
      exact (append_max_132_iff size _
        (orbit_perm word hperm power)).mp havoid
    · intro hword
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · change (word ++ [size + 1]).Perm (List.range' 1 (size + 1))
        rw [hrange]
        exact hperm.append (List.Perm.refl _)
      · intro power hpower
        rw [orbit_extend word hperm power]
        exact (append_max_132_iff size _
          (orbit_perm word hperm power)).mpr (hword.2 power hpower)
      · change (word ++ [size + 1]).getD size 0 = size + 1
        rw [List.getD_append_right _ _ _ _ (by omega), hlength]
        simp
  have hfamily : family = extend '' seeds := by
    ext word
    constructor
    · intro hword
      have hlength : word.length = size + 1 := by simpa using hword.1.1.length_eq
      let stem := word.take size
      have hstemLength : stem.length = size := by simp [stem, hlength]
      have hdrop : word.drop size = [size + 1] := by
        apply List.ext_getElem
        · simp [hlength]
        · intro index hindex hsingleton
          have hzero : index = 0 := by simpa using hsingleton
          subst index
          rw [List.getElem_drop]
          simpa only [Nat.add_zero, List.getElem_cons_zero,
            List.getD_eq_getElem word 0 (by omega : size < word.length)] using hword.2
      have hsplit : word = stem ++ [size + 1] := by
        rw [← hdrop]
        exact (List.take_append_drop size word).symm
      have hstemPerm : stem.Perm (List.range' 1 size) := by
        apply (List.perm_append_right_iff [size + 1]).mp
        simpa only [← hsplit, ← hrange] using hword.1.1
      have hextend : extend stem = word := hsplit.symm
      refine ⟨stem, (membership stem hstemPerm).mp ?_, hextend⟩
      rw [hextend]
      exact hword
    · rintro ⟨stem, hstem, rfl⟩
      exact (membership stem hstem.1).mpr hstem
  have hinjective : Function.Injective extend := by
    intro left right hequal
    exact List.append_cancel_right hequal
  change family.ncard = seeds.ncard
  rw [hfamily, Set.ncard_image_of_injective seeds hinjective]

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateTailCount
