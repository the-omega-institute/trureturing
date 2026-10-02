/- GID: D5/S3/Combinatorics/LevelSequence/LevelSequenceSuccession
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LevelSequence/LevelSequenceSuccession
   mirror-E: none(waiver:slack-succession-bijection)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: The next spine block and its lower band realize the slack succession rule. -/

import D5.S3.Combinatorics.LevelSequence.LevelSequenceSlack
import D5.S3.Combinatorics.LevelSequence.LevelSequenceWordCount
import Mathlib.RingTheory.PowerSeries.Catalan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LevelSequence.LevelSequenceSuccession

open LevelSequenceDefs LevelSequenceDescent LevelSequenceSpine
open LevelSequenceSlack LevelSequenceWordCount

theorem slack_succession (slack : ℕ) (tail : List ℕ) (nonempty : tail ≠ []) :
    tail ∈ continuations slack tail.length ↔
      ∃! pieces : ℕ × ℕ × List ℕ × List ℕ,
        0 < pieces.1 ∧ pieces.1 ≤ slack ∧
        tail = List.replicate (pieces.2.1 + 1) pieces.1 ++
          pieces.2.2.1.map (pieces.1 + ·) ++ pieces.2.2.2 ∧
        pieces.2.2.1 ∈ continuations (slack - pieces.1 + pieces.2.1)
          pieces.2.2.1.length ∧
        pieces.2.2.2 ∈ words pieces.1 pieces.2.2.2.length := by
  classical
  have entryMem (block : List ℕ) (index : ℕ) (inside : index < block.length) :
      block.getD index 0 ∈ block := by
    rw [List.getD_eq_getElem _ _ inside]
    exact List.getElem_mem inside
  have levCons (first second : ℕ) (rest : List ℕ) :
      lev (first :: second :: rest) =
        (if first = second then 1 else 0) + lev (second :: rest) := by
    simp only [lev, List.tail_cons, List.zip_cons_cons, List.filter_cons]
    split <;> simp_all [Nat.add_comm]
  have levMap (base : ℕ) (block : List ℕ) : lev (block.map (base + ·)) = lev block := by
    induction block with
    | nil => rfl
    | cons first rest ih =>
        cases rest with
        | nil => rfl
        | cons second rest =>
            simpa only [List.map_cons, levCons, Nat.add_left_cancel_iff] using
              ih
  have levRun (count base : ℕ) (block : List ℕ)
      (head : block = [] ∨ block.getD 0 0 ≠ base) :
      lev (List.replicate (count + 1) base ++ block) = count + lev block := by
    induction count with
    | zero =>
        cases block with
        | nil => rfl
        | cons first rest =>
            have unequal : base ≠ first := by simpa [eq_comm] using head
            simp [List.replicate_succ, levCons, unequal]
    | succ count ih =>
        rw [List.replicate_succ, List.cons_append]
        have shape : List.replicate (count + 1) base ++ block =
            base :: (List.replicate count base ++ block) := by simp [List.replicate_succ]
        rw [shape, levCons, if_pos rfl, ← shape, ih]
        omega
  have mapAccess (base : ℕ) (block : List ℕ) (index : ℕ) (inside : index < block.length) :
      (block.map (base + ·)).getD index 0 = base + block.getD index 0 := by
    rw [List.getD_eq_getElem _ _ (by simpa using inside),
      List.getD_eq_getElem _ _ inside]
    simp
  have translate (base : ℕ) (block : List ℕ) :
      (¬ Contains101 (block.map (base + ·)) ∧ ¬ Contains102 (block.map (base + ·))) ↔
        (¬ Contains101 block ∧ ¬ Contains102 block) := by
    rw [strong_descent, strong_descent]
    constructor
    · intro descent first middle last before after inside drop
      have value := descent first middle last before after (by simpa using inside)
      rw [mapAccess _ _ first (by omega), mapAccess _ _ middle (by omega),
        mapAccess _ _ last inside] at value
      exact Nat.lt_of_add_lt_add_left (value (Nat.add_lt_add_left drop base))
    · intro descent first middle last before after inside drop
      have bound : last < block.length := by simpa using inside
      rw [mapAccess _ _ first (by omega), mapAccess _ _ middle (by omega)] at drop
      rw [mapAccess _ _ first (by omega), mapAccess _ _ last bound]
      exact Nat.add_lt_add_left
        (descent first middle last before after bound (Nat.lt_of_add_lt_add_left drop)) base
  have minPrefix (count base : ℕ) (block : List ℕ)
      (high : ∀ entry ∈ block, base ≤ entry)
      (avoids : ¬ Contains101 block ∧ ¬ Contains102 block) :
      ¬ Contains101 (List.replicate count base ++ block) ∧
        ¬ Contains102 (List.replicate count base ++ block) := by
    apply (strong_descent _).mpr
    intro first middle last before after inside drop
    have access (index : ℕ) (bound : count ≤ index) :
        (List.replicate count base ++ block).getD index 0 = block.getD (index - count) 0 := by
      rw [List.getD_append_right _ _ _ _ (by simpa using bound), List.length_replicate]
    by_cases initial : first < count
    · have firstEntry : (List.replicate count base ++ block).getD first 0 = base := by
        rw [List.getD_append _ _ _ _ (by simpa using initial)]
        exact List.getD_replicate base initial
      rw [firstEntry] at drop
      by_cases middleInitial : middle < count
      · have middleEntry : (List.replicate count base ++ block).getD middle 0 = base := by
          rw [List.getD_append _ _ _ _ (by simpa using middleInitial)]
          exact List.getD_replicate base middleInitial
        rw [middleEntry] at drop
        omega
      · rw [access middle (by omega)] at drop
        have middleBound : middle - count < block.length := by
          simp only [List.length_append, List.length_replicate] at inside
          omega
        have above := high _ (entryMem block _ middleBound)
        omega
    · rw [access first (by omega), access middle (by omega)] at drop
      rw [access first (by omega), access last (by omega)]
      exact (strong_descent block).mp avoids _ _ _ (by omega) (by omega)
        (by simp only [List.length_append, List.length_replicate] at inside; omega) drop
  have slice (before block after : List ℕ)
      (avoids : ¬ Contains101 (before ++ block ++ after) ∧
        ¬ Contains102 (before ++ block ++ after)) :
      ¬ Contains101 block ∧ ¬ Contains102 block := by
    apply (strong_descent block).mpr
    intro first middle last beforeIndex afterIndex inside drop
    have access (index : ℕ) (bound : index < block.length) :
        (before ++ block ++ after).getD (before.length + index) 0 = block.getD index 0 := by
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    have descent := (strong_descent _).mp avoids
      (before.length + first) (before.length + middle) (before.length + last)
      (by omega) (by omega) (by simp; omega)
    rw [access first (by omega), access middle (by omega), access last inside] at descent
    exact descent drop
  have recoverZero (count : ℕ) (block : List ℕ) (head : block = [] ∨ 0 < block.getD 0 0) :
      (List.replicate count 0 ++ block).takeWhile (fun entry => decide (entry = 0)) =
        List.replicate count 0 := by
    rw [List.takeWhile_append_of_pos (by simp)]
    cases block with
    | nil => simp
    | cons first rest =>
        have positive : 0 < first := by simpa using head
        simp [Nat.ne_of_gt positive]
  have recoverHigh (base : ℕ) (upper lower : List ℕ)
      (high : ∀ entry ∈ upper, base ≤ entry) (low : ∀ entry ∈ lower, entry < base) :
      (upper ++ lower).takeWhile (fun entry => decide (base ≤ entry)) = upper := by
    rw [List.takeWhile_append_of_pos (by simpa using high)]
    have empty : lower.takeWhile (fun entry => decide (base ≤ entry)) = [] := by
      apply List.takeWhile_eq_nil_iff.mpr
      intro positive
      have below := low (lower.get ⟨0, positive⟩) (List.get_mem _ _)
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      omega
    simp [empty]
  have synthetic (budget : ℕ) (block : List ℕ)
      (head : block = [] ∨ 0 < block.getD 0 0) :
      IsLevel (List.replicate budget 0 ++ block) ↔
        ∀ index < block.length, block.getD index 0 ≤ budget + lev (block.take index) := by
    have access (index : ℕ) :
        (List.replicate budget 0 ++ block).getD (budget + index) 0 = block.getD index 0 := by
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    have takeEq (index : ℕ) :
        (List.replicate budget 0 ++ block).take (budget + index) =
          List.replicate budget 0 ++ block.take index := by rw [List.take_append]; simp
    have measure (index : ℕ) (positive : 0 < budget) :
        lev (List.replicate budget 0 ++ block.take index) =
          budget - 1 + lev (block.take index) := by
      have budgetEq : budget = (budget - 1) + 1 := by omega
      rw [budgetEq]
      apply levRun
      cases index with
      | zero => exact Or.inl rfl
      | succ index =>
          cases block with
          | nil => exact Or.inl rfl
          | cons first rest =>
              have firstPositive : 0 < first := by simpa using head
              exact Or.inr (by simp; omega)
    constructor
    · intro level index inside
      have bound := level (budget + index) (by simp; omega)
      rw [access, takeEq] at bound
      by_cases positive : 0 < budget
      · rw [if_neg (by omega), measure index positive] at bound
        omega
      · have zero : budget = 0 := by omega
        by_cases empty : block = []
        · simp [empty] at inside
        · have firstPositive : 0 < block.getD 0 0 := head.resolve_left empty
          have firstBound := level 0 (by simpa [zero] using List.length_pos_iff.mpr empty)
          simp only [zero, List.replicate_zero, List.nil_append] at firstBound
          change block.getD 0 0 ≤ 0 at firstBound
          omega
    · intro bounds index inside
      by_cases initial : index < budget
      · have zero : (List.replicate budget 0 ++ block).getD index 0 = 0 := by
          rw [List.getD_append _ _ _ _ (by simpa using initial)]
          exact List.getD_replicate 0 initial
        rw [zero]
        exact Nat.zero_le _
      · have blockInside : index - budget < block.length := by
          simp only [List.length_append, List.length_replicate] at inside
          omega
        have bound := bounds (index - budget) blockInside
        by_cases positive : 0 < budget
        · have indexEq : budget + (index - budget) = index := by omega
          have value := access (index - budget)
          have taken := takeEq (index - budget)
          rw [indexEq] at value taken
          rw [value, taken, if_neg (by omega), measure _ positive]
          omega
        · have zero : budget = 0 := by omega
          by_cases empty : block = []
          · simp [zero, empty] at inside
          · have firstPositive : 0 < block.getD 0 0 := head.resolve_left empty
            have firstBound := bounds 0 (List.length_pos_iff.mpr empty)
            simp only [zero, List.take_zero, show lev ([] : List ℕ) = 0 from rfl,
              Nat.add_zero] at firstBound
            omega
  have normalize (budget base count : ℕ) (block : List ℕ) (baseBound : base ≤ budget)
      (head : block = [] ∨ 0 < block.getD 0 0) :
      (∀ index < (List.replicate (count + 1) base ++ block.map (base + ·)).length,
        (List.replicate (count + 1) base ++ block.map (base + ·)).getD index 0 ≤
          budget + lev ((List.replicate (count + 1) base ++ block.map (base + ·)).take
            index)) ↔ IsLevel (List.replicate (budget - base + count) 0 ++ block) := by
    rw [synthetic _ _ head]
    have measure (index : ℕ) :
        lev (List.replicate (count + 1) base ++ (block.take index).map (base + ·)) =
          count + lev (block.take index) := by
      rw [levRun, levMap]
      cases index with
      | zero => exact Or.inl rfl
      | succ index =>
          cases block with
          | nil => exact Or.inl rfl
          | cons first rest =>
              have positive : 0 < first := by simpa using head
              exact Or.inr (by simp; omega)
    have access (index : ℕ) (inside : index < block.length) :
        (List.replicate (count + 1) base ++ block.map (base + ·)).getD
          (count + 1 + index) 0 = base + block.getD index 0 := by
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_replicate, Nat.add_sub_cancel_left]
      exact mapAccess _ _ _ inside
    have takeEq (index : ℕ) :
        (List.replicate (count + 1) base ++ block.map (base + ·)).take (count + 1 + index) =
          List.replicate (count + 1) base ++ (block.take index).map (base + ·) := by
      rw [List.take_append]
      simp
    constructor
    · intro bounds index inside
      have bound := bounds (count + 1 + index) (by simp; omega)
      rw [access _ inside, takeEq, measure] at bound
      omega
    · intro bounds index inside
      by_cases initial : index < count + 1
      · rw [List.getD_append _ _ _ _ (by simpa using initial)]
        rw [List.getD_replicate base initial]
        omega
      · have blockInside : index - (count + 1) < block.length := by
          simp only [List.length_append, List.length_replicate, List.length_map] at inside
          omega
        have indexEq : count + 1 + (index - (count + 1)) = index := by omega
        have value := access (index - (count + 1)) blockInside
        have taken := takeEq (index - (count + 1))
        rw [indexEq] at value taken
        rw [value, taken, measure]
        have bound := bounds (index - (count + 1)) blockInside
        omega
  have assemble (zeros base : ℕ) (upper lower : List ℕ)
      (zerosPositive : 0 < zeros) (basePositive : 0 < base)
      (high : ∀ entry ∈ upper, base ≤ entry) (low : ∀ entry ∈ lower, entry < base)
      (bounds : ∀ index < (base :: upper).length,
        (base :: upper).getD index 0 ≤ zeros + lev ((base :: upper).take index))
      (upperAvoids : ¬ Contains101 upper ∧ ¬ Contains102 upper)
      (lowerAvoids : ¬ Contains101 lower ∧ ¬ Contains102 lower) :
      IsLevel (List.replicate zeros 0 ++ (base :: upper) ++ lower) ∧
        ¬ Contains101 (List.replicate zeros 0 ++ (base :: upper) ++ lower) ∧
        ¬ Contains102 (List.replicate zeros 0 ++ (base :: upper) ++ lower) := by
    apply (initial_spine_band _ ⟨base, by simp, basePositive⟩).mpr
    refine ⟨(zeros, base, upper, lower),
      ⟨zerosPositive, basePositive, rfl, high, low, bounds, upperAvoids, lowerAvoids⟩, ?_⟩
    rintro ⟨otherZeros, otherBase, otherUpper, otherLower⟩
      ⟨_, otherPositive, split, otherHigh, otherLow, _, _, _⟩
    dsimp only at otherPositive split otherHigh otherLow
    have head (entry : ℕ) (rest : List ℕ) (positive : 0 < entry) :
        entry :: rest = [] ∨ 0 < (entry :: rest).getD 0 0 := Or.inr (by simpa using positive)
    have sameZeros : otherZeros = zeros := by
      have equal := congrArg
        (fun block => (block.takeWhile (fun entry => decide (entry = 0))).length) split
      simpa only [List.append_assoc, List.cons_append,
        recoverZero _ _ (head _ _ basePositive),
        recoverZero _ _ (head _ _ otherPositive), List.length_replicate] using equal.symm
    subst otherZeros
    have sameTail : base :: (upper ++ lower) = otherBase :: (otherUpper ++ otherLower) := by
      apply List.append_cancel_left (as := List.replicate zeros 0)
      simpa [List.append_assoc] using split
    have sameBase : otherBase = base := (List.cons.inj sameTail).1.symm
    subst otherBase
    have equalTail := (List.cons.inj sameTail).2
    have sameUpper : otherUpper = upper := by
      exact (recoverHigh base otherUpper otherLower otherHigh otherLow).symm.trans
        ((congrArg (List.takeWhile (fun entry => decide (base ≤ entry))) equalTail.symm).trans
          (recoverHigh base upper lower high low))
    have sameLower : otherLower = lower := by
      rw [sameUpper] at equalTail
      exact (List.append_cancel_left equalTail).symm
    simp [sameUpper, sameLower]
  constructor
  · rintro ⟨_, level, avoids, head⟩
    have tailPositive : 0 < tail.getD 0 0 := head.resolve_left nonempty
    have slackPositive : 0 < slack := by
      by_contra failure
      have zero : slack = 0 := by omega
      have bound := level 0 (by simpa [zero] using List.length_pos_iff.mpr nonempty)
      simp only [zero, List.replicate_zero, List.nil_append] at bound
      change tail.getD 0 0 ≤ 0 at bound
      omega
    have fullAvoids := minPrefix slack 0 tail (by simp) avoids
    have fullNonzero : ∃ entry ∈ List.replicate slack 0 ++ tail, 0 < entry :=
      ⟨tail.getD 0 0, List.mem_append.mpr
        (Or.inr (entryMem tail 0 (List.length_pos_iff.mpr nonempty))), tailPositive⟩
    obtain ⟨⟨zeros, base, upper, lower⟩,
      ⟨zerosPositive, basePositive, split, high, low, bounds, upperAvoids, lowerAvoids⟩, _⟩ :=
      (initial_spine_band _ fullNonzero).mp
        ⟨level, fullAvoids.1, fullAvoids.2⟩
    dsimp only at zerosPositive basePositive split high low bounds upperAvoids lowerAvoids
    have sameZeros : zeros = slack := by
      have equality := congrArg
        (fun block => (block.takeWhile (fun entry => decide (entry = 0))).length) split
      rw [recoverZero _ _ head] at equality
      have otherHead : base :: (upper ++ lower) = [] ∨
          0 < (base :: (upper ++ lower)).getD 0 0 := Or.inr (by simpa using basePositive)
      simpa only [List.append_assoc, List.cons_append, recoverZero _ _ otherHead,
        List.length_replicate] using equality.symm
    subst zeros
    have tailSplit : tail = (base :: upper) ++ lower := by
      apply List.append_cancel_left (as := List.replicate slack 0)
      simpa only [List.append_assoc] using split
    have baseBound : base ≤ slack := by simpa [lev] using bounds 0 (by simp)
    let normalized := (base :: upper).map (· - base)
    let initial := normalized.takeWhile (fun entry => decide (entry = 0))
    let next := normalized.dropWhile (fun entry => decide (entry = 0))
    have initialZero : initial = List.replicate initial.length 0 := by
      apply List.eq_replicate_length.mpr
      intro entry member
      exact of_decide_eq_true
        (List.mem_takeWhile_imp (p := fun entry => decide (entry = 0)) member)
    have normalizedSplit : normalized = List.replicate initial.length 0 ++ next := by
      rw [← initialZero]
      exact List.takeWhile_append_dropWhile.symm
    have initialPositive : 0 < initial.length := by simp [initial, normalized]
    have nextHead : next = [] ∨ 0 < next.getD 0 0 := by
      by_cases empty : next = []
      · exact Or.inl empty
      · have failure := List.dropWhile_get_zero_not
          (fun entry => decide (entry = 0)) normalized (List.length_pos_iff.mpr empty)
        have same : next.get ⟨0, List.length_pos_iff.mpr empty⟩ = next.getD 0 0 := by
          rw [List.getD_eq_getElem _ _ (List.length_pos_iff.mpr empty)]
          rfl
        change ¬ decide (next.get ⟨0, _⟩ = 0) = true at failure
        rw [same] at failure
        simp only [decide_eq_true_eq] at failure
        exact Or.inr (by omega)
    have restore : normalized.map (base + ·) = base :: upper := by
      rw [List.map_map]
      calc
        _ = (base :: upper).map id := List.map_congr_left fun entry member => by
          have above : base ≤ entry := by
            rcases List.mem_cons.mp member with rfl | member
            · rfl
            · exact high entry member
          simp only [Function.comp_apply, id_eq]
          omega
        _ = _ := List.map_id _
    let count := initial.length - 1
    have countLength : count + 1 = initial.length := by dsimp [count]; omega
    have blockSplit : base :: upper =
        List.replicate (count + 1) base ++ next.map (base + ·) := by
      rw [← restore, normalizedSplit, List.map_append, List.map_replicate, countLength]
      simp
    have nextLevel : IsLevel (List.replicate (slack - base + count) 0 ++ next) := by
      apply (normalize slack base count next baseBound nextHead).mp
      simpa [← blockSplit] using bounds
    have nextAvoids : ¬ Contains101 next ∧ ¬ Contains102 next := by
      apply (translate base next).mp
      apply slice (List.replicate (count + 1) base) (next.map (base + ·)) []
      have blockAvoids := minPrefix 1 base upper high upperAvoids
      simpa [← blockSplit] using blockAvoids
    have nextMember : next ∈ continuations (slack - base + count) next.length :=
      ⟨rfl, nextLevel, nextAvoids, nextHead⟩
    have lowerMember : lower ∈ words base lower.length := ⟨rfl, low, lowerAvoids⟩
    have decomposition : tail =
        List.replicate (count + 1) base ++ next.map (base + ·) ++ lower := by
      rw [tailSplit, blockSplit]
    refine ⟨(base, count, next, lower),
      ⟨basePositive, baseBound, decomposition, nextMember, lowerMember⟩, ?_⟩
    rintro ⟨otherBase, otherCount, otherNext, otherLower⟩
      ⟨_, _, otherSplit, otherNextMember, otherLowerMember⟩
    dsimp only at otherSplit otherNextMember otherLowerMember
    have firstEntry (entry repeats : ℕ) (rest band : List ℕ) :
        (List.replicate (repeats + 1) entry ++ rest.map (entry + ·) ++ band).getD 0 0 =
          entry := by simp [List.replicate_succ]
    have sameBase : otherBase = base := by
      have equality := congrArg (fun block : List ℕ => block.getD 0 0)
        (otherSplit.symm.trans decomposition)
      simpa only [firstEntry] using equality
    subst otherBase
    have above (repeats : ℕ) (rest : List ℕ) :
        ∀ entry ∈ List.replicate (repeats + 1) base ++ rest.map (base + ·),
          base ≤ entry := by
      intro entry member
      rcases List.mem_append.mp member with member | member
      · have equal := List.eq_of_mem_replicate member
        omega
      · obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
        omega
    have sameBlock : List.replicate (otherCount + 1) base ++ otherNext.map (base + ·) =
        List.replicate (count + 1) base ++ next.map (base + ·) := by
      have equality := congrArg
        (List.takeWhile (fun entry => decide (base ≤ entry)))
        (otherSplit.symm.trans decomposition)
      rw [recoverHigh _ _ _ (above _ _) otherLowerMember.2.1,
        recoverHigh _ _ _ (above _ _) low] at equality
      exact equality
    have sameNormalized : List.replicate (otherCount + 1) 0 ++ otherNext =
        List.replicate (count + 1) 0 ++ next := by
      have equality := congrArg (List.map (· - base)) sameBlock
      simpa [List.map_append, List.map_map, Function.comp_def] using equality
    have sameCount : otherCount = count := by
      have equality := congrArg
        (fun block => (block.takeWhile (fun entry => decide (entry = 0))).length)
        sameNormalized
      rw [recoverZero _ _ otherNextMember.2.2.2, recoverZero _ _ nextHead] at equality
      simpa using equality
    subst otherCount
    have sameNext : otherNext = next := List.append_cancel_left sameNormalized
    have sameLower : otherLower = lower := by
      have equality := otherSplit.symm.trans decomposition
      rw [sameBlock] at equality
      exact List.append_cancel_left equality
    simp [sameNext, sameLower]
  · rintro ⟨⟨base, count, next, lower⟩,
      ⟨basePositive, baseBound, split, nextMember, lowerMember⟩, _⟩
    dsimp only at basePositive baseBound split nextMember lowerMember
    have slackPositive : 0 < slack := by omega
    let upper := List.replicate count base ++ next.map (base + ·)
    have high : ∀ entry ∈ upper, base ≤ entry := by
      intro entry member
      rcases List.mem_append.mp member with member | member
      · have equal := List.eq_of_mem_replicate member
        omega
      · obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
        omega
    have blockSplit : base :: upper =
        List.replicate (count + 1) base ++ next.map (base + ·) := by
      simp [upper, List.replicate_succ]
    have bounds : ∀ index < (base :: upper).length,
        (base :: upper).getD index 0 ≤ slack + lev ((base :: upper).take index) := by
      rw [blockSplit]
      exact (normalize slack base count next baseBound nextMember.2.2.2).mpr
        nextMember.2.1
    have shiftedAvoids := (translate base next).mpr nextMember.2.2.1
    have upperAvoids : ¬ Contains101 upper ∧ ¬ Contains102 upper := by
      apply minPrefix count base _ _ shiftedAvoids
      intro entry member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      omega
    have full := assemble slack base upper lower slackPositive basePositive high
      lowerMember.2.1 bounds upperAvoids lowerMember.2.2
    have tailSplit : tail = (base :: upper) ++ lower := by rw [blockSplit]; exact split
    have level : IsLevel (List.replicate slack 0 ++ tail) := by
      simpa [tailSplit, List.append_assoc] using full.1
    have avoids : ¬ Contains101 tail ∧ ¬ Contains102 tail := by
      apply slice (List.replicate slack 0) tail []
      simpa [tailSplit, List.append_assoc] using full.2
    have headPositive : 0 < tail.getD 0 0 := by simpa [tailSplit] using basePositive
    exact ⟨rfl, level, avoids, Or.inr headPositive⟩

end D5.S3.Combinatorics.LevelSequence.LevelSequenceSuccession
