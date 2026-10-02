/- GID: D5/S3/Combinatorics/LevelSequence/LevelSequenceSpine
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LevelSequence/LevelSequenceSpine
   mirror-E: none(waiver:canonical-spine-band-split)
   anchors: [mathlib/module/Mathlib.Data.List.TakeWhile]
   utility: none
   digest: The first rising spine block splits off a uniquely determined lower band. -/

import D5.S3.Combinatorics.LevelSequence.LevelSequenceDescent
import Mathlib.Data.List.TakeWhile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LevelSequence.LevelSequenceSpine

open LevelSequenceDefs LevelSequenceDescent

theorem initial_spine_band (word : List ℕ)
    (nonzero : ∃ entry ∈ word, 0 < entry) :
    (IsLevel word ∧ ¬ Contains101 word ∧ ¬ Contains102 word) ↔
      ∃! pieces : ℕ × ℕ × List ℕ × List ℕ,
        0 < pieces.1 ∧ 0 < pieces.2.1 ∧
        word = List.replicate pieces.1 0 ++
          (pieces.2.1 :: pieces.2.2.1) ++ pieces.2.2.2 ∧
        (∀ entry ∈ pieces.2.2.1, pieces.2.1 ≤ entry) ∧
        (∀ entry ∈ pieces.2.2.2, entry < pieces.2.1) ∧
        (∀ index < (pieces.2.1 :: pieces.2.2.1).length,
          (pieces.2.1 :: pieces.2.2.1).getD index 0 ≤
            pieces.1 + lev ((pieces.2.1 :: pieces.2.2.1).take index)) ∧
        (¬ Contains101 pieces.2.2.1 ∧ ¬ Contains102 pieces.2.2.1) ∧
        (¬ Contains101 pieces.2.2.2 ∧ ¬ Contains102 pieces.2.2.2) := by
  classical
  have entryMem (block : List ℕ) (index : ℕ) (inside : index < block.length) :
      block.getD index 0 ∈ block := by
    rw [List.getD_eq_getElem _ _ inside]
    exact List.getElem_mem inside
  have levCons (first second : ℕ) (tail : List ℕ) :
      lev (first :: second :: tail) =
        (if first = second then 1 else 0) + lev (second :: tail) := by
    simp only [lev, List.tail_cons, List.zip_cons_cons, List.filter_cons]
    split <;> simp_all [Nat.add_comm]
  have levMono (before after : List ℕ) : lev before ≤ lev (before ++ after) := by
    induction before with
    | nil => simp [lev]
    | cons first tail ih =>
        cases tail with
        | nil => simp [lev]
        | cons second rest =>
            simp only [List.cons_append, levCons] at *
            omega
  have levZeros (count : ℕ) (block : List ℕ)
      (head : block = [] ∨ 0 < block.getD 0 0) :
      lev (List.replicate (count + 1) 0 ++ block) = count + lev block := by
    induction count with
    | zero =>
        cases block with
        | nil => simp [lev]
        | cons first tail =>
            have positive : 0 < first := by simpa using head
            simp [List.replicate_succ, levCons, show (0 : ℕ) ≠ first by omega]
    | succ count ih =>
        rw [List.replicate_succ, List.cons_append]
        have shape : List.replicate (count + 1) 0 ++ block =
            0 :: (List.replicate count 0 ++ block) := by simp [List.replicate_succ]
        rw [shape, levCons, if_pos rfl]
        rw [← shape, ih]
        omega
  have prefixLev (zeros letter : ℕ) (upper : List ℕ) (positive : 0 < letter)
      (index : ℕ) :
      lev (List.replicate (zeros + 1) 0 ++ (letter :: upper).take index) =
        zeros + lev ((letter :: upper).take index) := by
    apply levZeros
    cases index with
    | zero => exact Or.inl rfl
    | succ index => exact Or.inr (by simpa using positive)
  have slice (before block after : List ℕ)
      (avoids : ¬ Contains101 (before ++ block ++ after) ∧
        ¬ Contains102 (before ++ block ++ after)) :
      ¬ Contains101 block ∧ ¬ Contains102 block := by
    apply (strong_descent block).mpr
    intro first middle last beforeIndex afterIndex inside drop
    have access (index : ℕ) (bound : index < block.length) :
        (before ++ block ++ after).getD (before.length + index) 0 =
          block.getD index 0 := by
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    have descent := (strong_descent _).mp avoids
      (before.length + first) (before.length + middle) (before.length + last)
      (by omega) (by omega) (by simp; omega)
    rw [access first (by omega), access middle (by omega), access last inside] at descent
    exact descent drop
  have recoverZeros (zeros letter : ℕ) (tail : List ℕ) (positive : 0 < letter) :
      (List.replicate zeros 0 ++ letter :: tail).takeWhile
        (fun entry => decide (entry = 0)) = List.replicate zeros 0 := by
    rw [List.takeWhile_append_of_pos (by simp)]
    simp [Nat.ne_of_gt positive]
  have recoverUpper (letter : ℕ) (upper lower : List ℕ)
      (high : ∀ entry ∈ upper, letter ≤ entry)
      (low : ∀ entry ∈ lower, entry < letter) :
      (upper ++ lower).takeWhile (fun entry => decide (letter ≤ entry)) = upper := by
    rw [List.takeWhile_append_of_pos (by simpa using high)]
    have empty : lower.takeWhile (fun entry => decide (letter ≤ entry)) = [] := by
      apply List.takeWhile_eq_nil_iff.mpr
      intro positive
      have bound := low (lower.get ⟨0, positive⟩) (List.get_mem _ _)
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      omega
    simp [empty]
  constructor
  · rintro ⟨level, no101, no102⟩
    let initial := word.takeWhile (fun entry => decide (entry = 0))
    let rest := word.dropWhile (fun entry => decide (entry = 0))
    have initialZero : initial = List.replicate initial.length 0 := by
      apply List.eq_replicate_length.mpr
      intro entry member
      exact of_decide_eq_true
        (List.mem_takeWhile_imp (p := fun entry => decide (entry = 0)) member)
    have decomposition : word = List.replicate initial.length 0 ++ rest := by
      rw [← initialZero]
      exact List.takeWhile_append_dropWhile.symm
    have restNonempty : rest ≠ [] := by
      intro empty
      obtain ⟨entry, member, positive⟩ := nonzero
      rw [decomposition, empty, List.append_nil] at member
      have zero : entry = 0 := List.eq_of_mem_replicate member
      omega
    cases restShape : rest with
    | nil => exact (restNonempty restShape).elim
    | cons letter tail =>
        have letterPositive : 0 < letter := by
          have failure := List.dropWhile_get_zero_not
            (fun entry => decide (entry = 0)) word
            (show 0 < rest.length by simp [restShape])
          change ¬ decide (rest.get ⟨0, _⟩ = 0) = true at failure
          simp only [decide_eq_true_eq] at failure
          have head : rest.get ⟨0, by simp [restShape]⟩ = letter := by simp [restShape]
          rw [head] at failure
          omega
        have zerosPositive : 0 < initial.length := by
          by_contra notPositive
          have zero : initial.length = 0 := by omega
          have shape : word = letter :: tail := by simpa [zero, restShape] using decomposition
          have bound := level 0 (by simp [shape])
          simp [shape] at bound
          omega
        let upper := tail.takeWhile (fun entry => decide (letter ≤ entry))
        let lower := tail.dropWhile (fun entry => decide (letter ≤ entry))
        have tailSplit : tail = upper ++ lower := List.takeWhile_append_dropWhile.symm
        have split : word = List.replicate initial.length 0 ++
            (letter :: upper) ++ lower := by
          simpa [restShape, tailSplit, List.append_assoc] using decomposition
        have high : ∀ entry ∈ upper, letter ≤ entry := by
          intro entry member
          exact of_decide_eq_true
            (List.mem_takeWhile_imp (p := fun entry => decide (letter ≤ entry)) member)
        have low : ∀ entry ∈ lower, entry < letter := by
          cases lowerShape : lower with
          | nil => simp
          | cons head tailLower =>
              have headBelow : head < letter := by
                have failure := List.dropWhile_get_zero_not
                  (fun entry => decide (letter ≤ entry)) tail
                  (show 0 < lower.length by simp [lowerShape])
                change ¬ decide (letter ≤ lower.get ⟨0, _⟩) = true at failure
                simp only [decide_eq_true_eq] at failure
                have value : lower.get ⟨0, by simp [lowerShape]⟩ = head := by
                  simp [lowerShape]
                rw [value] at failure
                omega
              intro entry member
              rw [List.mem_cons] at member
              rcases member with rfl | member
              · exact headBelow
              · obtain ⟨index, inside, value⟩ := List.mem_iff_getElem.mp member
                have tailAvoids := slice (List.replicate initial.length 0)
                  (letter :: tail) [] (by simpa [decomposition, restShape] using
                    (show ¬ Contains101 word ∧ ¬ Contains102 word from ⟨no101, no102⟩))
                have middleEntry : (letter :: tail).getD (upper.length + 1) 0 = head := by
                  rw [List.getD_cons_succ, tailSplit]
                  rw [List.getD_append_right _ _ _ _ le_rfl]
                  simp [lowerShape]
                have lastEntry :
                    (letter :: tail).getD (upper.length + (index + 1) + 1) 0 = entry := by
                  rw [List.getD_cons_succ, tailSplit]
                  rw [List.getD_append_right _ _ _ _ (by omega)]
                  simp only [Nat.add_sub_cancel_left, lowerShape, List.getD_cons_succ]
                  rw [List.getD_eq_getElem _ _ inside, value]
                have descent := (strong_descent _).mp tailAvoids 0 (upper.length + 1)
                  (upper.length + (index + 1) + 1) (by omega) (by omega)
                  (by simp [tailSplit, lowerShape]; omega)
                simpa only [List.getD_cons_zero, middleEntry, lastEntry] using
                  descent (by simpa only [List.getD_cons_zero, middleEntry] using headBelow)
        have upperAvoids : ¬ Contains101 upper ∧ ¬ Contains102 upper := by
          apply slice (List.replicate initial.length 0 ++ [letter]) upper lower
          simpa [split, List.append_assoc] using
            (show ¬ Contains101 word ∧ ¬ Contains102 word from ⟨no101, no102⟩)
        have lowerAvoids : ¬ Contains101 lower ∧ ¬ Contains102 lower := by
          apply slice (List.replicate initial.length 0 ++ (letter :: upper)) lower []
          simpa [split] using
            (show ¬ Contains101 word ∧ ¬ Contains102 word from ⟨no101, no102⟩)
        have bounds : ∀ index < (letter :: upper).length,
            (letter :: upper).getD index 0 ≤
              initial.length + lev ((letter :: upper).take index) := by
          intro index inside
          have indexBound : index < upper.length + 1 := by simpa using inside
          have bound := level (initial.length + index)
            (by simp only [split, List.length_append, List.length_replicate,
              List.length_cons]; omega)
          have access : word.getD (initial.length + index) 0 =
              (letter :: upper).getD index 0 := by
            rw [split, List.getD_append _ _ _ _
              (by simp only [List.length_append, List.length_replicate,
                List.length_cons]; omega)]
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp
          have prefixEq : word.take (initial.length + index) =
              List.replicate initial.length 0 ++ (letter :: upper).take index := by
            rw [split, List.take_append_of_le_length
              (by simp only [List.length_append, List.length_replicate,
                List.length_cons]; omega)]
            rw [List.take_append]
            simp
          rw [access, prefixEq, if_neg (by omega)] at bound
          have zerosEq : initial.length = (initial.length - 1) + 1 := by omega
          rw [zerosEq, prefixLev _ _ _ letterPositive] at bound
          omega
        refine ⟨(initial.length, letter, upper, lower),
          ⟨zerosPositive, letterPositive, split, high, low, bounds,
            upperAvoids, lowerAvoids⟩, ?_⟩
        rintro ⟨otherZeros, otherLetter, otherUpper, otherLower⟩
          ⟨_, otherPositive, otherSplit, otherHigh, otherLow, _, _, _⟩
        dsimp only at otherPositive otherSplit otherHigh otherLow
        have sameZeros : otherZeros = initial.length := by
          have equality := congrArg
            (fun block => (block.takeWhile (fun entry => decide (entry = 0))).length)
            (otherSplit.symm.trans split)
          simpa only [List.append_assoc, List.cons_append,
            recoverZeros _ _ _ otherPositive, recoverZeros _ _ _ letterPositive,
            List.length_replicate] using equality
        subst otherZeros
        have sameTail : otherLetter :: (otherUpper ++ otherLower) =
            letter :: (upper ++ lower) := by
          apply List.append_cancel_left (as := List.replicate initial.length 0)
          simpa [List.append_assoc] using otherSplit.symm.trans split
        have sameLetter : otherLetter = letter := (List.cons.inj sameTail).1
        subst otherLetter
        have equalTail := (List.cons.inj sameTail).2
        have sameUpper : otherUpper = upper := by
          exact (recoverUpper letter otherUpper otherLower otherHigh otherLow).symm.trans
            ((congrArg (List.takeWhile (fun entry => decide (letter ≤ entry))) equalTail).trans
              (recoverUpper letter upper lower high low))
        have sameLower : otherLower = lower := by
          rw [sameUpper] at equalTail
          exact List.append_cancel_left equalTail
        simp [sameUpper, sameLower]
  · rintro ⟨⟨zeros, letter, upper, lower⟩,
      ⟨zerosPositive, letterPositive, split, high, low, bounds, upperAvoids, lowerAvoids⟩, _⟩
    dsimp only at zerosPositive letterPositive split high low bounds upperAvoids lowerAvoids
    have upperEntry (index : ℕ) (inside : index < (letter :: upper).length) :
        word.getD (zeros + index) 0 = (letter :: upper).getD index 0 := by
      have bound : index < upper.length + 1 := by simpa using inside
      rw [split, List.getD_append _ _ _ _
        (by simp only [List.length_append, List.length_replicate, List.length_cons]; omega)]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    have lowerEntry (index : ℕ) :
        word.getD (zeros + (letter :: upper).length + index) 0 = lower.getD index 0 := by
      rw [split, List.getD_append_right _ _ _ _ (by simp)]
      simp
    have zeroEntry (index : ℕ) (inside : index < zeros) : word.getD index 0 = 0 := by
      rw [split, List.getD_append _ _ _ _ (by simp; omega)]
      rw [List.getD_append _ _ _ _ (by simpa using inside)]
      exact List.getD_replicate 0 inside
    have prefixEq (index : ℕ) (inside : index ≤ (letter :: upper).length) :
        word.take (zeros + index) =
          List.replicate zeros 0 ++ (letter :: upper).take index := by
      rw [split, List.take_append_of_le_length
        (by simp only [List.length_append, List.length_replicate]; omega)]
      rw [List.take_append]
      simp
    have level : IsLevel word := by
      intro index inside
      by_cases initial : index < zeros
      · rw [zeroEntry index initial]
        exact Nat.zero_le _
      · have nonzeroIndex : index ≠ 0 := by omega
        rw [if_neg nonzeroIndex]
        by_cases inUpper : index < zeros + (letter :: upper).length
        · have entry := upperEntry (index - zeros) (by omega)
          have take := prefixEq (index - zeros) (by omega)
          have sum : zeros + (index - zeros) = index := by omega
          rw [sum] at entry take
          rw [entry, take]
          have zerosEq : zeros = (zeros - 1) + 1 := by omega
          have measure := prefixLev (zeros - 1) letter upper letterPositive (index - zeros)
          rw [← zerosEq] at measure
          rw [measure]
          have bound := bounds (index - zeros) (by omega)
          omega
        · have last : index = zeros + (letter :: upper).length +
              (index - zeros - (letter :: upper).length) := by omega
          have access := lowerEntry (index - zeros - (letter :: upper).length)
          rw [← last] at access
          rw [access]
          have lowerInside : index - zeros - (letter :: upper).length < lower.length := by
            simp only [split, List.length_append, List.length_replicate] at inside
            omega
          have below := low _ (entryMem lower _ lowerInside)
          have anchor := bounds 0 (by simp)
          simp only [List.getD_cons_zero, List.take_zero, lev, List.zip_nil_left,
            List.filter_nil, List.length_nil, Nat.add_zero] at anchor
          have levBound : zeros - 1 ≤ lev (word.take index) := by
            have take : word.take index = List.replicate zeros 0 ++
                ((letter :: upper) ++ lower).take (index - zeros) := by
              rw [split, List.append_assoc, List.take_append]
              simp [List.take_replicate, Nat.min_eq_right (show zeros ≤ index by omega)]
            rw [take]
            have before := levMono (List.replicate zeros 0)
              (((letter :: upper) ++ lower).take (index - zeros))
            have zerosEq : zeros = (zeros - 1) + 1 := by omega
            have zeroLev : lev (List.replicate zeros 0) = zeros - 1 := by
              have value := levZeros (zeros - 1) [] (Or.inl rfl)
              simpa only [List.append_nil, show lev ([] : List ℕ) = 0 from rfl,
                Nat.add_zero, ← zerosEq] using value
            omega
          omega
    refine ⟨level, (strong_descent word).mpr ?_⟩
    intro first middle last before after inside drop
    by_cases initial : first < zeros
    · rw [zeroEntry first initial] at drop
      omega
    · have lengthBound : last < zeros + (letter :: upper).length + lower.length := by
        simp only [split, List.length_append, List.length_replicate] at inside
        exact inside
      have upperHigh (index : ℕ) (bound : index < (letter :: upper).length) :
          letter ≤ (letter :: upper).getD index 0 := by
        cases index with
        | zero => simp
        | succ index =>
            simp only [List.length_cons] at bound
            rw [List.getD_cons_succ]
            exact high _ (entryMem upper index (by omega))
      by_cases firstUpper : first < zeros + (letter :: upper).length
      · have firstAccess := upperEntry (first - zeros) (by omega)
        rw [show zeros + (first - zeros) = first by omega] at firstAccess
        by_cases lastUpper : last < zeros + (letter :: upper).length
        · have middleAccess := upperEntry (middle - zeros) (by omega)
          have lastAccess := upperEntry (last - zeros) (by omega)
          rw [show zeros + (middle - zeros) = middle by omega] at middleAccess
          rw [show zeros + (last - zeros) = last by omega] at lastAccess
          rw [firstAccess, middleAccess] at drop
          rw [firstAccess, lastAccess]
          by_cases firstAnchor : first - zeros = 0
          · rw [firstAnchor, List.getD_cons_zero] at drop
            have above := upperHigh (middle - zeros) (by omega)
            omega
          · have firstPos : 0 < first - zeros := by omega
            have middlePos : 0 < middle - zeros := by omega
            have lastPos : 0 < last - zeros := by omega
            have access (index : ℕ) (positive : 0 < index) :
                (letter :: upper).getD index 0 = upper.getD (index - 1) 0 := by
              rw [show index = (index - 1) + 1 by omega, List.getD_cons_succ]
              simp
            rw [access _ firstPos, access _ middlePos] at drop
            rw [access _ firstPos, access _ lastPos]
            exact (strong_descent upper).mp upperAvoids _ _ _
              (by omega) (by omega) (by simp at lastUpper; omega) drop
        · have lastAccess := lowerEntry (last - zeros - (letter :: upper).length)
          rw [show zeros + (letter :: upper).length +
            (last - zeros - (letter :: upper).length) = last by omega] at lastAccess
          rw [firstAccess, lastAccess]
          have above := upperHigh (first - zeros) (by omega)
          have below := low _ (entryMem lower (last - zeros - (letter :: upper).length)
            (by omega))
          omega
      · have access (index : ℕ) (bound : zeros + (letter :: upper).length ≤ index) :
            word.getD index 0 = lower.getD (index - zeros - (letter :: upper).length) 0 := by
          have value := lowerEntry (index - zeros - (letter :: upper).length)
          rw [show zeros + (letter :: upper).length +
            (index - zeros - (letter :: upper).length) = index by omega] at value
          exact value
        rw [access first (by omega), access middle (by omega)] at drop
        rw [access first (by omega), access last (by omega)]
        exact (strong_descent lower).mp lowerAvoids _ _ _
          (by omega) (by omega) (by omega) drop

end D5.S3.Combinatorics.LevelSequence.LevelSequenceSpine
