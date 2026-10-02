/- GID: D5/S3/Combinatorics/LevelSequence/LevelSequenceCatalan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LevelSequence/LevelSequenceCatalan
   mirror-E: none(waiver:formal-kernel-enumeration)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Log]
   utility: none
   digest: The slack kernel specializes to the Catalan series in every degree. -/

import D5.S3.Combinatorics.LevelSequence.LevelSequenceSuccession
import Mathlib.RingTheory.PowerSeries.Log

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LevelSequence.LevelSequenceCatalan

open LevelSequenceDefs LevelSequenceWordCount LevelSequenceSlack
open LevelSequenceDescent LevelSequenceSpine LevelSequenceSuccession
open scoped PowerSeries.WithPiTopology

theorem result : LevelSequenceDefs.claim := by
  classical
  have initialBlockCount (size : ℕ) :
      (avoiders (size + 1)).ncard =
        ∑ run : Fin (size + 1), (continuations (run.val + 1) (size - run.val)).ncard := by
    classical
    have levBound (block : List ℕ) : lev block ≤ block.length := by
      have filtered := List.length_filter_le (fun pair : ℕ × ℕ => decide (pair.1 = pair.2))
        (block.zip block.tail)
      have zipped : (block.zip block.tail).length ≤ block.length := by
        simp only [List.length_zip]
        exact Nat.min_le_left _ _
      exact filtered.trans zipped
    have finiteContinuations (slack length : ℕ) : Finite (continuations slack length) := by
      let encode (tail : continuations slack length) (index : Fin length) :
          Fin (slack + length + 2) :=
        ⟨tail.1.getD index 0, by
          have inside : index.val < tail.1.length := by rw [tail.2.1]; exact index.isLt
          have bound := tail.2.2.1 (slack + index.val)
            (by simp only [List.length_append, List.length_replicate]; omega)
          have access : (List.replicate slack 0 ++ tail.1).getD (slack + index.val) 0 =
              tail.1.getD index.val 0 := by
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp
          rw [access] at bound
          have measure := (levBound
            ((List.replicate slack 0 ++ tail.1).take (slack + index.val))).trans
            (List.length_take_le _ _)
          split_ifs at bound <;> have indexBound := index.isLt <;> omega⟩
      apply Finite.of_injective encode
      intro left right equal
      apply Subtype.ext
      apply List.ext_getElem (left.2.1.trans right.2.1.symm)
      intro index leftInside rightInside
      have bounded : index < length := by rwa [left.2.1] at leftInside
      have value := congrArg Fin.val (congrFun equal ⟨index, bounded⟩)
      change left.1.getD index 0 = right.1.getD index 0 at value
      simpa only [List.getD_eq_getElem _ _ leftInside,
        List.getD_eq_getElem _ _ rightInside] using value
    have (slack length : ℕ) : Finite (continuations slack length) :=
      finiteContinuations slack length
    have addZeros (zeros : ℕ) (tail : List ℕ)
        (avoids : ¬ Contains101 tail ∧ ¬ Contains102 tail) :
        ¬ Contains101 (List.replicate zeros 0 ++ tail) ∧
          ¬ Contains102 (List.replicate zeros 0 ++ tail) := by
      apply (strong_descent _).mpr
      intro first middle last before after inside drop
      have access (index : ℕ) (bound : zeros ≤ index) :
          (List.replicate zeros 0 ++ tail).getD index 0 = tail.getD (index - zeros) 0 := by
        rw [List.getD_append_right _ _ _ _ (by simpa using bound), List.length_replicate]
      by_cases initial : first < zeros
      · have firstEntry : (List.replicate zeros 0 ++ tail).getD first 0 = 0 := by
          rw [List.getD_append _ _ _ _ (by simpa using initial)]
          exact List.getD_replicate 0 initial
        rw [firstEntry] at drop
        omega
      · rw [access first (by omega), access middle (by omega)] at drop
        rw [access first (by omega), access last (by omega)]
        exact (strong_descent tail).mp avoids _ _ _ (by omega) (by omega)
          (by simp only [List.length_append, List.length_replicate] at inside; omega) drop
    have removeZeros (zeros : ℕ) (tail : List ℕ)
        (avoids : ¬ Contains101 (List.replicate zeros 0 ++ tail) ∧
          ¬ Contains102 (List.replicate zeros 0 ++ tail)) :
        ¬ Contains101 tail ∧ ¬ Contains102 tail := by
      apply (strong_descent tail).mpr
      intro first middle last before after inside drop
      have access (index : ℕ) :
          (List.replicate zeros 0 ++ tail).getD (zeros + index) 0 = tail.getD index 0 := by
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp
      have descent := (strong_descent _).mp avoids
        (zeros + first) (zeros + middle) (zeros + last)
        (by omega) (by omega) (by simp; omega)
      rw [access first, access middle, access last] at descent
      exact descent drop
    have recover (zeros : ℕ) (tail : List ℕ) (head : tail = [] ∨ 0 < tail.getD 0 0) :
        (List.replicate zeros 0 ++ tail).takeWhile (fun entry => decide (entry = 0)) =
          List.replicate zeros 0 := by
      rw [List.takeWhile_append_of_pos (by simp)]
      cases tail with
      | nil => simp
      | cons first rest =>
          have positive : 0 < first := by simpa using head
          simp [Nat.ne_of_gt positive]
    let Pieces := Σ run : Fin (size + 1), continuations (run.val + 1) (size - run.val)
    let build (pieces : Pieces) : avoiders (size + 1) :=
      ⟨List.replicate (pieces.1.val + 1) 0 ++ pieces.2.1, by
        refine ⟨?_, pieces.2.2.2.1,
          (addZeros _ _ pieces.2.2.2.2.1).1, (addZeros _ _ pieces.2.2.2.2.1).2⟩
        simp only [List.length_append, List.length_replicate, pieces.2.2.1]
        have bound := pieces.1.isLt
        omega⟩
    have injective : Function.Injective build := by
      rintro ⟨leftRun, leftTail⟩ ⟨rightRun, rightTail⟩ equal
      have equality := congrArg Subtype.val equal
      change List.replicate (leftRun.val + 1) 0 ++ leftTail.1 =
        List.replicate (rightRun.val + 1) 0 ++ rightTail.1 at equality
      have sameRun : leftRun = rightRun := by
        apply Fin.ext
        have value := congrArg
          (fun block => (block.takeWhile (fun entry => decide (entry = 0))).length) equality
        rw [recover _ _ leftTail.2.2.2.2, recover _ _ rightTail.2.2.2.2] at value
        simpa only [List.length_replicate, Nat.add_right_cancel_iff] using value
      subst rightRun
      have sameTail : leftTail = rightTail :=
        Subtype.ext (List.append_cancel_left equality)
      subst rightTail
      rfl
    have surjective : Function.Surjective build := by
      rintro ⟨word, length, level, no101, no102⟩
      by_cases nonzero : ∃ entry ∈ word, 0 < entry
      · obtain ⟨⟨zeros, letter, upper, lower⟩,
          ⟨zerosPositive, letterPositive, split, _, _, _, _, _⟩, _⟩ :=
          (initial_spine_band word nonzero).mp ⟨level, no101, no102⟩
        dsimp only at zerosPositive letterPositive split
        let tail := letter :: (upper ++ lower)
        have wordSplit : word = List.replicate zeros 0 ++ tail := by
          simpa [tail, List.append_assoc] using split
        have lengths : zeros + tail.length = size + 1 := by
          simpa [wordSplit] using length
        let run : Fin (size + 1) := ⟨zeros - 1, by omega⟩
        have runLength : run.val + 1 = zeros := by dsimp [run]; omega
        have tailMember : tail ∈ continuations (run.val + 1) (size - run.val) := by
          refine ⟨?_, ?_, ?_, Or.inr ?_⟩
          · dsimp [run]
            omega
          · rw [runLength, ← wordSplit]
            exact level
          · apply removeZeros zeros tail
            simpa [← wordSplit] using
              (show ¬ Contains101 word ∧ ¬ Contains102 word from ⟨no101, no102⟩)
          · simpa [tail] using letterPositive
        refine ⟨⟨run, ⟨tail, tailMember⟩⟩, ?_⟩
        apply Subtype.ext
        change List.replicate (run.val + 1) 0 ++ tail = word
        rw [runLength, ← wordSplit]
      · have zeroWord : word = List.replicate (size + 1) 0 := by
          rw [← length]
          apply List.eq_replicate_length.mpr
          intro entry member
          have notPositive : ¬ 0 < entry := fun positive => nonzero ⟨entry, member, positive⟩
          omega
        let run : Fin (size + 1) := ⟨size, by omega⟩
        have tailMember : [] ∈ continuations (run.val + 1) (size - run.val) := by
          refine ⟨by simp [run], ?_, by simp [Contains101, Contains102], Or.inl rfl⟩
          simpa [run, ← zeroWord] using level
        refine ⟨⟨run, ⟨[], tailMember⟩⟩, ?_⟩
        apply Subtype.ext
        simpa [build, run] using zeroWord.symm
    have cardinal := Nat.card_congr (Equiv.ofBijective build ⟨injective, surjective⟩)
    change Nat.card Pieces = Nat.card (avoiders (size + 1)) at cardinal
    rw [← Nat.card_coe_set_eq, ← cardinal]
    change Nat.card (Σ run : Fin (size + 1),
      continuations (run.val + 1) (size - run.val)) = _
    rw [Nat.card_sigma]
    simp_rw [Nat.card_coe_set_eq]
  
  have slackCount (slack size : ℕ) :
      (continuations slack (size + 1)).ncard =
        ∑ gap : Fin slack, ∑ excess : Fin (size + 1),
          ∑ split : Fin (size - excess.val + 1),
            (continuations (slack - (gap.val + 1) + excess.val) split.val).ncard *
              (words (gap.val + 1) (size - excess.val - split.val)).ncard := by
    classical
    have levBound (block : List ℕ) : lev block ≤ block.length := by
      exact (List.length_filter_le _ _).trans (by simp [List.length_zip])
    have finiteTails (budget length : ℕ) : Finite (continuations budget length) := by
      let encode (tail : continuations budget length) (index : Fin length) :
          Fin (budget + length + 2) :=
        ⟨tail.1.getD index 0, by
          have bound := tail.2.2.1 (budget + index.val)
            (by simp only [List.length_append, List.length_replicate, tail.2.1]; omega)
          have access : (List.replicate budget 0 ++ tail.1).getD (budget + index.val) 0 =
              tail.1.getD index.val 0 := by
            rw [List.getD_append_right _ _ _ _ (by simp)]
            simp
          rw [access] at bound
          have measure := (levBound
            ((List.replicate budget 0 ++ tail.1).take (budget + index.val))).trans
            (List.length_take_le _ _)
          split_ifs at bound <;> have inside := index.isLt <;> omega⟩
      apply Finite.of_injective encode
      intro left right equal
      apply Subtype.ext
      apply List.ext_getElem (left.2.1.trans right.2.1.symm)
      intro index leftInside rightInside
      have inside : index < length := by rwa [left.2.1] at leftInside
      have entry := congrArg (fun code => (code ⟨index, inside⟩).val) equal
      simpa only [encode, List.getD_eq_getElem _ _ leftInside,
        List.getD_eq_getElem _ _ rightInside] using entry
    have finiteWords (alphabet length : ℕ) : Finite (words alphabet length) := by
      let encode (word : words alphabet length) (index : Fin length) : Fin alphabet :=
        ⟨word.1.getD index 0, word.2.2.1 _ (by
          rw [List.getD_eq_getElem _ _ (by rw [word.2.1]; exact index.isLt)]
          exact List.getElem_mem _)⟩
      apply Finite.of_injective encode
      intro left right equal
      apply Subtype.ext
      apply List.ext_getElem (left.2.1.trans right.2.1.symm)
      intro index leftInside rightInside
      have inside : index < length := by rwa [left.2.1] at leftInside
      have entry := congrArg (fun code => (code ⟨index, inside⟩).val) equal
      simpa only [encode, List.getD_eq_getElem _ _ leftInside,
        List.getD_eq_getElem _ _ rightInside] using entry
    let (budget length : ℕ) : Finite (continuations budget length) :=
      finiteTails budget length
    let (alphabet length : ℕ) : Finite (words alphabet length) :=
      finiteWords alphabet length
    let Pieces := Σ gap : Fin slack, Σ excess : Fin (size + 1),
      Σ split : Fin (size - excess.val + 1),
        continuations (slack - (gap.val + 1) + excess.val) split.val ×
          words (gap.val + 1) (size - excess.val - split.val)
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
    let build : Pieces → continuations slack (size + 1) := fun pieces => by
      rcases pieces with ⟨gap, excess, split, next, band⟩
      let tail := List.replicate (excess.val + 1) (gap.val + 1) ++
        next.1.map (gap.val + 1 + ·) ++ band.1
      have length : tail.length = size + 1 := by
        simp only [tail, List.length_append, List.length_replicate, List.length_map,
          next.2.1, band.2.1]
        have excessBound := excess.isLt
        have splitBound := split.isLt
        omega
      have nonempty : tail ≠ [] := by
        intro empty
        simp [empty] at length
      have nextMember : next.1 ∈ continuations (slack - (gap.val + 1) + excess.val)
          next.1.length := by simpa only [next.2.1] using next.2
      have bandMember : band.1 ∈ words (gap.val + 1) band.1.length := by
        simpa only [band.2.1] using band.2
      have unique : ∃! data : ℕ × ℕ × List ℕ × List ℕ,
          0 < data.1 ∧ data.1 ≤ slack ∧
          tail = List.replicate (data.2.1 + 1) data.1 ++
            data.2.2.1.map (data.1 + ·) ++ data.2.2.2 ∧
          data.2.2.1 ∈ continuations (slack - data.1 + data.2.1)
            data.2.2.1.length ∧ data.2.2.2 ∈ words data.1 data.2.2.2.length := by
        apply ExistsUnique.intro (gap.val + 1, excess.val, next.1, band.1)
          ⟨by omega, by have bound := gap.isLt; omega, rfl, nextMember, bandMember⟩
        rintro ⟨otherBase, otherCount, otherNext, otherBand⟩
          ⟨_, _, otherSplit, otherNextMember, otherBandMember⟩
        dsimp only at otherSplit otherNextMember otherBandMember
        have firstEntry (base count : ℕ) (rest lower : List ℕ) :
            (List.replicate (count + 1) base ++ rest.map (base + ·) ++ lower).getD 0 0 =
              base := by simp [List.replicate_succ]
        have baseEqual : otherBase = gap.val + 1 := by
          have equality := congrArg (fun block : List ℕ => block.getD 0 0) otherSplit
          simpa only [tail, firstEntry] using equality.symm
        subst otherBase
        have high (count : ℕ) (rest : List ℕ) :
            ∀ entry ∈ List.replicate (count + 1) (gap.val + 1) ++
              rest.map (gap.val + 1 + ·), gap.val + 1 ≤ entry := by
          intro entry member
          rcases List.mem_append.mp member with member | member
          · have equality := List.eq_of_mem_replicate member
            omega
          · obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
            omega
        have upperEqual : List.replicate (otherCount + 1) (gap.val + 1) ++
            otherNext.map (gap.val + 1 + ·) =
            List.replicate (excess.val + 1) (gap.val + 1) ++
              next.1.map (gap.val + 1 + ·) := by
          have equality := congrArg
            (List.takeWhile (fun entry => decide (gap.val + 1 ≤ entry))) otherSplit
          dsimp only [tail] at equality
          rw [recoverHigh _ _ _ (high _ _) band.2.2.1,
            recoverHigh _ _ _ (high _ _) otherBandMember.2.1] at equality
          exact equality.symm
        have normalized : List.replicate (otherCount + 1) 0 ++ otherNext =
            List.replicate (excess.val + 1) 0 ++ next.1 := by
          have equality := congrArg (List.map (· - (gap.val + 1))) upperEqual
          simpa [List.map_append, List.map_map, Function.comp_def] using equality
        have countEqual : otherCount = excess.val := by
          have equality := congrArg
            (fun block => (block.takeWhile (fun entry => decide (entry = 0))).length)
            normalized
          rw [recoverZero _ _ otherNextMember.2.2.2,
            recoverZero _ _ next.2.2.2.2] at equality
          simpa using equality
        subst otherCount
        have nextEqual : otherNext = next.1 := List.append_cancel_left normalized
        have bandEqual : otherBand = band.1 := by
          dsimp only [tail] at otherSplit
          rw [upperEqual] at otherSplit
          exact (List.append_cancel_left otherSplit).symm
        simp [nextEqual, bandEqual]
      have member := (slack_succession slack tail nonempty).mpr unique
      exact ⟨tail, by simpa only [length] using member⟩
    have decode (gap : Fin slack) (excess : Fin (size + 1))
        (split : Fin (size - excess.val + 1))
        (next : continuations (slack - (gap.val + 1) + excess.val) split.val)
        (band : words (gap.val + 1) (size - excess.val - split.val)) :
        (build ⟨gap, excess, split, next, band⟩).1 =
          List.replicate (excess.val + 1) (gap.val + 1) ++
            next.1.map (gap.val + 1 + ·) ++ band.1 := rfl
    have injective : Function.Injective build := by
      rintro ⟨leftGap, leftExcess, leftSplit, leftNext, leftBand⟩
        ⟨rightGap, rightExcess, rightSplit, rightNext, rightBand⟩ equal
      let tail := (build ⟨leftGap, leftExcess, leftSplit, leftNext, leftBand⟩).1
      have length : tail.length = size + 1 :=
        (build ⟨leftGap, leftExcess, leftSplit, leftNext, leftBand⟩).2.1
      have nonempty : tail ≠ [] := by intro empty; simp [empty] at length
      obtain ⟨data, _, uniqueness⟩ := (slack_succession slack tail nonempty).mp
        (by simpa only [length] using
          (build ⟨leftGap, leftExcess, leftSplit, leftNext, leftBand⟩).2)
      have validLeft : 0 < leftGap.val + 1 ∧ leftGap.val + 1 ≤ slack ∧
          tail = List.replicate (leftExcess.val + 1) (leftGap.val + 1) ++
            leftNext.1.map (leftGap.val + 1 + ·) ++ leftBand.1 ∧
          leftNext.1 ∈ continuations (slack - (leftGap.val + 1) + leftExcess.val)
            leftNext.1.length ∧ leftBand.1 ∈ words (leftGap.val + 1) leftBand.1.length :=
        ⟨by omega, by have bound := leftGap.isLt; omega, rfl,
          by simpa only [leftNext.2.1] using leftNext.2,
          by simpa only [leftBand.2.1] using leftBand.2⟩
      have validRight : 0 < rightGap.val + 1 ∧ rightGap.val + 1 ≤ slack ∧
          tail = List.replicate (rightExcess.val + 1) (rightGap.val + 1) ++
            rightNext.1.map (rightGap.val + 1 + ·) ++ rightBand.1 ∧
          rightNext.1 ∈ continuations (slack - (rightGap.val + 1) + rightExcess.val)
            rightNext.1.length ∧ rightBand.1 ∈ words (rightGap.val + 1) rightBand.1.length :=
        ⟨by omega, by have bound := rightGap.isLt; omega,
          congrArg Subtype.val equal,
          by simpa only [rightNext.2.1] using rightNext.2,
          by simpa only [rightBand.2.1] using rightBand.2⟩
      have same :=
        (uniqueness (leftGap.val + 1, leftExcess.val, leftNext.1, leftBand.1) validLeft).trans
          (uniqueness (rightGap.val + 1, rightExcess.val, rightNext.1, rightBand.1)
            validRight).symm
      have gapEqual : leftGap = rightGap := by
        apply Fin.ext
        have entry := congrArg Prod.fst same
        simpa using entry
      subst rightGap
      have excessEqual : leftExcess = rightExcess := by
        apply Fin.ext
        exact congrArg (fun data : ℕ × ℕ × List ℕ × List ℕ => data.2.1) same
      subst rightExcess
      have nextEqual : leftNext.1 = rightNext.1 :=
        congrArg (fun data : ℕ × ℕ × List ℕ × List ℕ => data.2.2.1) same
      have splitEqual : leftSplit = rightSplit := by
        apply Fin.ext
        have lengths := congrArg List.length nextEqual
        simpa only [leftNext.2.1, rightNext.2.1] using lengths
      subst rightSplit
      have nextSubtype : leftNext = rightNext := Subtype.ext nextEqual
      subst rightNext
      have bandEqual : leftBand = rightBand := Subtype.ext
        (congrArg (fun data : ℕ × ℕ × List ℕ × List ℕ => data.2.2.2) same)
      subst rightBand
      rfl
    have surjective : Function.Surjective build := by
      rintro ⟨tail, member⟩
      have length := member.1
      have nonempty : tail ≠ [] := by intro empty; simp [empty] at length
      obtain ⟨⟨base, count, next, band⟩, valid, _⟩ :=
        (slack_succession slack tail nonempty).mp (by simpa only [length] using member)
      rcases valid with ⟨positive, bound, decomposition, nextMember, bandMember⟩
      dsimp only at positive bound decomposition nextMember bandMember
      have lengths : count + 1 + next.length + band.length = size + 1 := by
        simpa only [decomposition, List.length_append, List.length_replicate,
          List.length_map] using length
      let gap : Fin slack := ⟨base - 1, by omega⟩
      let excess : Fin (size + 1) := ⟨count, by omega⟩
      let split : Fin (size - excess.val + 1) := ⟨next.length, by dsimp [excess]; omega⟩
      have baseEq : gap.val + 1 = base := by dsimp [gap]; omega
      have normalized : next ∈ continuations (slack - (gap.val + 1) + excess.val)
          split.val := by simpa only [baseEq] using nextMember
      have lower : band ∈ words (gap.val + 1) (size - excess.val - split.val) := by
        have bandLength : size - excess.val - split.val = band.length := by
          dsimp [excess, split]; omega
        simpa only [baseEq, bandLength] using bandMember
      refine ⟨⟨gap, excess, split, ⟨next, normalized⟩, ⟨band, lower⟩⟩, ?_⟩
      apply Subtype.ext
      simpa only [decode, baseEq] using decomposition.symm
    have cardinal := Nat.card_congr (Equiv.ofBijective build ⟨injective, surjective⟩)
    change Nat.card Pieces = Nat.card (continuations slack (size + 1)) at cardinal
    rw [← Nat.card_coe_set_eq, ← cardinal]
    change Nat.card (Σ gap : Fin slack, Σ excess : Fin (size + 1),
      Σ split : Fin (size - excess.val + 1),
        continuations (slack - (gap.val + 1) + excess.val) split.val ×
          words (gap.val + 1) (size - excess.val - split.val)) = _
    rw [Nat.card_sigma]
    simp_rw [Nat.card_sigma, Nat.card_prod, Nat.card_coe_set_eq]
  
  let f (alphabet size : ℕ) : ℚ := (words alphabet size).ncard
  let p (slack size : ℕ) : ℚ := (continuations slack size).ncard
  have emptyWord (alphabet : ℕ) : f alphabet 0 = 1 := by
    have equal : words alphabet 0 = {[]} := by
      ext word
      simp only [words, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro member
        exact List.length_eq_zero_iff.mp member.1
      · rintro rfl
        simp [Contains101, Contains102]
    simp [f, equal]
  have emptyTail (slack : ℕ) : p slack 0 = 1 := by
    have zeroLevel (amount : ℕ) : IsLevel (List.replicate amount 0) := by
      induction amount with
      | zero => simp [IsLevel]
      | succ amount ih =>
          cases amount with
          | zero =>
              intro index inside
              have equal : index = 0 := by simp only [List.length_replicate] at inside; omega
              simp [equal]
          | succ amount =>
              have nonempty : List.replicate (amount + 1) 0 ≠ [] := by simp
              have noDrop (first middle : ℕ) (before : first < middle)
                  (inside : middle < amount + 1) :
                  ¬ (List.replicate (amount + 1) 0).getD middle 0 <
                    (List.replicate (amount + 1) 0).getD first 0 := by
                rw [List.getD_replicate 0 inside, List.getD_replicate 0 (by omega)]
                omega
              have no101 : ¬ Contains101 (List.replicate (amount + 1) 0) := by
                rintro ⟨first, middle, last, before, after, inside, drop, _⟩
                simp only [List.length_replicate] at inside
                exact noDrop first middle before (by omega) drop
              have no102 : ¬ Contains102 (List.replicate (amount + 1) 0) := by
                rintro ⟨first, middle, last, before, after, inside, drop, _⟩
                simp only [List.length_replicate] at inside
                exact noDrop first middle before (by omega) drop
              have extended := (LevelSequenceDescent.append_criterion
                (List.replicate (amount + 1) 0) 0 nonempty).mpr
                ⟨ih, no101, no102, by omega, by
                  intro first middle before inside drop
                  simp only [List.length_replicate] at inside
                  exact (noDrop first middle before inside drop).elim⟩
              simpa only [List.replicate_succ'] using extended.1
    have equal : continuations slack 0 = {[]} := by
      ext tail
      simp only [continuations, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro member
        exact List.length_eq_zero_iff.mp member.1
      · rintro rfl
        refine ⟨rfl, ?_, by simp [Contains101, Contains102], Or.inl rfl⟩
        simpa only [List.append_nil] using zeroLevel slack
    simp [p, equal]
  have noAlphabet (size : ℕ) : f 0 (size + 1) = 0 := by
    have equal : words 0 (size + 1) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro word member
      have positive : 0 < word.length := by rw [member.1]; omega
      have impossible := member.2.1 (word.getD 0 0) (by
        rw [List.getD_eq_getElem _ _ positive]
        exact List.getElem_mem positive)
      omega
    simp [f, equal]
  have zeroSlack (size : ℕ) : p 0 (size + 1) = 0 := by
    dsimp only [p]
    rw [slackCount]
    simp
  let F (alphabet : ℕ) : PowerSeries ℚ := PowerSeries.mk (f alphabet)
  let T (slack : ℕ) : PowerSeries ℚ := PowerSeries.mk (p slack)
  let B (slack : ℕ) : PowerSeries ℚ := PowerSeries.mk fun size =>
    ∑ excess : Fin (size + 1), p (slack + excess.val) (size - excess.val)
  let H : PowerSeries (PowerSeries ℚ) := PowerSeries.mk F
  let P : PowerSeries (PowerSeries ℚ) := PowerSeries.mk T
  let A : PowerSeries (PowerSeries ℚ) := PowerSeries.mk B
  let G : PowerSeries (PowerSeries ℚ) := PowerSeries.mk fun _ => 1
  let x : PowerSeries (PowerSeries ℚ) := PowerSeries.C PowerSeries.X
  let y : PowerSeries (PowerSeries ℚ) := PowerSeries.X
  let L : PowerSeries ℚ := B 0
  have multiply (degree : ℕ) (left right : PowerSeries ℚ) :
      PowerSeries.coeff degree (left * right) =
        ∑ index : Fin (degree + 1),
          PowerSeries.coeff index.val left * PowerSeries.coeff (degree - index.val) right := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  have outerMultiply (degree : ℕ) (left right : PowerSeries (PowerSeries ℚ)) :
      PowerSeries.coeff degree (left * right) =
        ∑ index : Fin (degree + 1),
          PowerSeries.coeff index.val left * PowerSeries.coeff (degree - index.val) right := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  have fZero : F 0 = 1 := by
    ext size
    cases size with
    | zero => simp [F, emptyWord]
    | succ size => simp [F, noAlphabet]
  have alphabetSeries (alphabet : ℕ) :
      F alphabet = 1 + PowerSeries.X *
        ∑ first : Fin alphabet, F (alphabet - first.val) * F first.val := by
    ext size
    cases size with
    | zero => simp [F, emptyWord]
    | succ size =>
        rw [map_add, PowerSeries.coeff_succ_X_mul]
        simp only [PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add,
          map_sum, multiply, F, PowerSeries.coeff_mk]
        dsimp only [f]
        exact_mod_cast alphabet_recurrence alphabet size
  have hG : G * (1 - y) = 1 := by
    ext degree
    cases degree with
    | zero => simp [G, y]
    | succ degree => simp [mul_sub, G, y, PowerSeries.coeff_succ_mul_X]
  have hH : H = G + x * H * (H - 1) := by
    apply PowerSeries.ext
    intro alphabet
    cases alphabet with
    | zero => simp [H, G, x, fZero]
    | succ alphabet =>
        rw [mul_assoc x H (H - 1)]
        change PowerSeries.coeff (alphabet + 1) H =
          PowerSeries.coeff (alphabet + 1)
            (G + PowerSeries.C PowerSeries.X * (H * (H - 1)))
        rw [map_add, PowerSeries.coeff_C_mul, outerMultiply]
        simp only [H, G, PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_one]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_last, Nat.sub_self, fZero,
          ↓reduceIte, sub_self, mul_zero, add_zero, Fin.val_castSucc]
        have positive (index : Fin (alphabet + 1)) :
            alphabet + 1 - index.val ≠ 0 := by have bound := index.isLt; omega
        simp only [if_neg (positive _), sub_zero]
        rw [alphabetSeries]
        congr 1
        apply congrArg (PowerSeries.X * ·)
        apply Finset.sum_congr rfl
        intro index _
        exact mul_comm _ _
  have triangle (budget alphabet size : ℕ) :
      (∑ band : Fin (size + 1), ∑ excess : Fin (size - band.val + 1),
        f alphabet band.val * p (budget + excess.val) (size - band.val - excess.val)) =
      ∑ excess : Fin (size + 1), ∑ split : Fin (size - excess.val + 1),
        p (budget + excess.val) split.val * f alphabet (size - excess.val - split.val) := by
    let rotate : (Σ band : Fin (size + 1), Fin (size - band.val + 1)) ≃
        (Σ excess : Fin (size + 1), Fin (size - excess.val + 1)) :=
      { toFun := fun pair =>
          ⟨⟨pair.2.val, by have bound := pair.1.isLt; have other := pair.2.isLt; omega⟩,
            ⟨size - pair.1.val - pair.2.val, by dsimp; omega⟩⟩
        invFun := fun pair =>
          ⟨⟨size - pair.1.val - pair.2.val, by omega⟩,
            ⟨pair.1.val, by
              dsimp; have bound := pair.1.isLt; have other := pair.2.isLt; omega⟩⟩
        left_inv := by
          rintro ⟨band, excess⟩
          have bandBound := band.isLt
          have excessBound := excess.isLt
          apply Sigma.ext
          · apply Fin.ext; dsimp; omega
          · apply (Fin.heq_ext_iff (by dsimp; omega)).mpr
            rfl
        right_inv := by
          rintro ⟨excess, split⟩
          have excessBound := excess.isLt
          have splitBound := split.isLt
          apply Sigma.ext
          · apply Fin.ext; rfl
          · apply (Fin.heq_ext_iff rfl).mpr
            dsimp; omega }
    rw [← Fintype.sum_sigma', ← Fintype.sum_sigma']
    apply Fintype.sum_equiv rotate
    rintro ⟨band, excess⟩
    have bandBound := band.isLt
    have excessBound := excess.isLt
    dsimp [rotate]
    have cancel : size - excess.val - (size - band.val - excess.val) = band.val := by
      omega
    rw [cancel, mul_comm]
  have slackSeries (slack : ℕ) :
      T slack = 1 + PowerSeries.X *
        ∑ gap : Fin slack, F (gap.val + 1) * B (slack - (gap.val + 1)) := by
    ext size
    cases size with
    | zero => simp [T, emptyTail]
    | succ size =>
        rw [map_add, PowerSeries.coeff_succ_X_mul]
        simp only [PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add,
          map_sum, multiply, F, B, T,
          PowerSeries.coeff_mk, Finset.mul_sum]
        simp_rw [triangle]
        dsimp only [p, f]
        exact_mod_cast slackCount slack size
  have hP : P = G + x * (H - 1) * A := by
    apply PowerSeries.ext
    intro slack
    rw [mul_assoc x (H - 1) A]
    change PowerSeries.coeff slack P = PowerSeries.coeff slack
      (G + PowerSeries.C PowerSeries.X * ((H - 1) * A))
    rw [map_add, PowerSeries.coeff_C_mul, outerMultiply]
    simp only [P, G, H, A, PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_one]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, fZero, ↓reduceIte,
      sub_self, zero_mul, zero_add, Fin.val_succ]
    have positive (index : Fin slack) : index.val + 1 ≠ 0 := by omega
    simp only [if_neg (positive _), sub_zero]
    exact slackSeries slack
  have shifted (slack : ℕ) : B slack = T slack + PowerSeries.X * B (slack + 1) := by
    ext size
    cases size with
    | zero => simp [B, T]
    | succ size =>
        simp only [B, T, map_add, PowerSeries.coeff_mk,
          PowerSeries.coeff_succ_X_mul]
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, Nat.add_zero, Nat.sub_zero, Fin.val_succ]
        congr 1
        apply Finset.sum_congr rfl
        intro excess _
        have bound := excess.isLt
        have budgetEq : slack + (excess.val + 1) = slack + 1 + excess.val := by omega
        have sizeEq : size + 1 - (excess.val + 1) = size - excess.val := by omega
        rw [budgetEq, sizeEq]
  have hA : (x - y) * A = x * PowerSeries.C L - y * P := by
    apply PowerSeries.ext
    intro slack
    cases slack with
    | zero => simp [sub_mul, x, y, A, L]
    | succ slack =>
        simp only [sub_mul, map_sub, x, y, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
          PowerSeries.coeff_C, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
          ↓reduceIte, zero_sub, A, P, PowerSeries.coeff_mk, mul_zero]
        rw [shifted slack]
        ring
  have kernel : (x - y + x * y * (H - 1)) * P =
      (x - y) * G + x ^ 2 * (H - 1) * PowerSeries.C L := by
    calc
      (x - y + x * y * (H - 1)) * P =
          (x - y) * P + x * (H - 1) * (y * P) := by ring
      _ = (x - y) * (G + x * (H - 1) * A) + x * (H - 1) * (y * P) := by
          conv_lhs => arg 1; arg 2; rw [hP]
      _ = (x - y) * G + x * (H - 1) * ((x - y) * A + y * P) := by ring
      _ = (x - y) * G + x ^ 2 * (H - 1) * PowerSeries.C L := by rw [hA]; ring
  let C := PowerSeries.map (Nat.castRingHom ℚ) PowerSeries.catalanSeries
  have catalanEquation : PowerSeries.X * C ^ 2 + 1 = C := by
    have equal := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simpa only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X,
      mul_comm] using equal
  let unit := 1 + PowerSeries.X * C
  let Z := PowerSeries.X * C * unit⁻¹
  have inverse : unit * unit⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel unit (by simp [unit])
  have unitIdentity : (1 - Z) * unit = 1 := by
    dsimp only [Z]
    calc
      (1 - PowerSeries.X * C * unit⁻¹) * unit =
          unit - PowerSeries.X * C * (unit * unit⁻¹) := by ring
      _ = 1 := by rw [inverse]; dsimp [unit]; ring
  have zZero : PowerSeries.constantCoeff Z = 0 := by simp [Z]
  let : UniformSpace ℚ := ⊥
  let : DiscreteTopology ℚ := ⟨rfl⟩
  let evaluate := PowerSeries.eval₂Hom (φ := RingHom.id (PowerSeries ℚ))
    continuous_id ((PowerSeries.HasSubst.of_constantCoeff_zero' zZero).hasEval)
  have evalConstant (value : PowerSeries ℚ) : evaluate (PowerSeries.C value) = value := by
    rw [PowerSeries.coe_eval₂Hom]
    exact PowerSeries.eval₂_C _ _ _
  have evalVariable : evaluate y = Z := by
    rw [PowerSeries.coe_eval₂Hom]
    exact PowerSeries.eval₂_X _ _
  have evaluatedG : evaluate G = unit := by
    have equal := congrArg evaluate hG
    simp only [map_mul, map_sub, map_one, evalVariable] at equal
    calc
      evaluate G = evaluate G * ((1 - Z) * unit) := by rw [unitIdentity]; simp
      _ = unit := by rw [← mul_assoc, equal, one_mul]
  have evaluatedH : evaluate H = C := by
    have equal := congrArg evaluate hH
    simp only [map_add, map_mul, map_sub, map_one, x, evalConstant, evaluatedG] at equal
    have difference : evaluate H - C = PowerSeries.X *
        (evaluate H - C) * (evaluate H + C - 1) := by
      calc
        evaluate H - C = (unit + PowerSeries.X * evaluate H * (evaluate H - 1)) -
            (PowerSeries.X * C ^ 2 + 1) := by rw [← equal, catalanEquation]
        _ = PowerSeries.X * (evaluate H - C) * (evaluate H + C - 1) := by
          dsimp [unit]
          ring
    have vanish : ∀ degree, PowerSeries.coeff degree (evaluate H - C) = 0 := by
      intro degree
      induction degree using Nat.strong_induction_on with
      | h degree ih =>
          cases degree with
          | zero => rw [difference]; simp
          | succ degree =>
              rw [difference, mul_assoc, PowerSeries.coeff_succ_X_mul, multiply]
              apply Finset.sum_eq_zero
              intro index _
              rw [ih index.val (by have bound := index.isLt; omega), zero_mul]
    apply sub_eq_zero.mp
    ext degree
    simp [vanish]
  have root : PowerSeries.X - Z + PowerSeries.X * Z * (C - 1) = 0 := by
    have relation : Z * unit = PowerSeries.X * C := by
      dsimp only [Z]
      rw [mul_assoc, mul_comm unit⁻¹ unit, inverse, mul_one]
    apply (mul_right_cancel₀ (show unit ≠ 0 by
      intro zero; have impossible := congrArg PowerSeries.constantCoeff zero
      simp [unit] at impossible))
    rw [zero_mul]
    calc
      (PowerSeries.X - Z + PowerSeries.X * Z * (C - 1)) * unit =
          PowerSeries.X * unit - Z * unit +
            PowerSeries.X * (Z * unit) * (C - 1) := by ring
      _ = 0 := by
          rw [relation]
          dsimp only [unit]
          calc
            _ = PowerSeries.X * (PowerSeries.X * C ^ 2 + 1 - C) := by ring
            _ = 0 := by rw [catalanEquation]; ring
  have evaluatedKernel := congrArg evaluate kernel
  simp only [map_mul, map_add, map_sub, map_pow, map_one, x, evalConstant,
    evalVariable, evaluatedH, evaluatedG, root, zero_mul] at evaluatedKernel
  have cancel : PowerSeries.X * (C - 1) *
      (PowerSeries.X * L - Z * unit) = 0 := by
    have rootEquation : PowerSeries.X - Z = -(PowerSeries.X * Z * (C - 1)) :=
      eq_neg_of_add_eq_zero_left root
    calc
      PowerSeries.X * (C - 1) * (PowerSeries.X * L - Z * unit) =
          (PowerSeries.X - Z) * unit + PowerSeries.X ^ 2 * (C - 1) * L := by
            rw [rootEquation]
            ring
      _ = 0 := evaluatedKernel.symm
  have lCatalan : L = C := by
    have zIdentity : Z * unit = PowerSeries.X * C := by
      dsimp only [Z]
      rw [mul_assoc, mul_comm unit⁻¹ unit, inverse, mul_one]
    rw [zIdentity, ← mul_sub, ← mul_assoc] at cancel
    have xNonzero : (PowerSeries.X : PowerSeries ℚ) ≠ 0 := PowerSeries.X_ne_zero
    have cNonzero : C - 1 ≠ 0 := by
      intro equal
      have impossible := congrArg (PowerSeries.coeff 1) equal
      simp [C] at impossible
    exact sub_eq_zero.mp ((mul_eq_zero.mp cancel).resolve_left
      (mul_ne_zero (mul_ne_zero xNonzero cNonzero) xNonzero))
  intro size positive
  obtain ⟨degree, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
  have coefficient := congrArg (PowerSeries.coeff (degree + 1)) lCatalan
  simp only [L, B, PowerSeries.coeff_mk, C, PowerSeries.coeff_map,
    PowerSeries.catalanSeries_coeff] at coefficient
  simp only [Nat.zero_add] at coefficient
  change (∑ excess : Fin (degree + 2), p excess.val (degree + 1 - excess.val)) =
    (catalan (degree + 1) : ℚ) at coefficient
  rw [Fin.sum_univ_succ] at coefficient
  simp only [Fin.val_zero, Nat.sub_zero, zeroSlack, zero_add,
    Fin.val_succ, Nat.add_sub_add_right] at coefficient
  have counted := initialBlockCount degree
  dsimp only [p] at coefficient
  have countedNat :
      (∑ run : Fin (degree + 1),
        (continuations (run.val + 1) (degree - run.val)).ncard) = catalan (degree + 1) := by
    exact_mod_cast coefficient
  exact counted.trans countedNat

end D5.S3.Combinatorics.LevelSequence.LevelSequenceCatalan
