/- GID: D5/S3/Combinatorics/LevelSequence/LevelSequenceWordCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LevelSequence/LevelSequenceWordCount
   mirror-E: none(waiver:auxiliary-word-counting-bijection)
   anchors: [mathlib/module/Mathlib.Data.Finite.Sigma, mathlib/module/Mathlib.Data.List.TakeWhile]
   utility: none
   digest: The unique upper-lower split gives the auxiliary word convolution recurrence. -/

import D5.S3.Combinatorics.LevelSequence.LevelSequenceDescent
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.List.TakeWhile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LevelSequence.LevelSequenceWordCount

open LevelSequenceDefs LevelSequenceDescent
def words (alphabet size : ℕ) : Set (List ℕ) :=
  {word | word.length = size ∧ (∀ letter ∈ word, letter < alphabet) ∧
    ¬ Contains101 word ∧ ¬ Contains102 word}


theorem alphabet_recurrence (alphabet size : ℕ) :
    (words alphabet (size + 1)).ncard =
      ∑ first : Fin alphabet, ∑ split : Fin (size + 1),
        (words (alphabet - first) split).ncard * (words first (size - split)).ncard := by
  classical
  have word_decomposition (letter : ℕ) (tail : List ℕ) :
      (¬ Contains101 (letter :: tail) ∧ ¬ Contains102 (letter :: tail)) ↔
        ∃! pieces : List ℕ × List ℕ,
          tail = pieces.1 ++ pieces.2 ∧
          (∀ entry ∈ pieces.1, letter ≤ entry) ∧
          (∀ entry ∈ pieces.2, entry < letter) ∧
          (¬ Contains101 pieces.1 ∧ ¬ Contains102 pieces.1) ∧
          (¬ Contains101 pieces.2 ∧ ¬ Contains102 pieces.2) := by
    have entryMem (block : List ℕ) (index : ℕ) (inside : index < block.length) :
        block.getD index 0 ∈ block := by
      rw [List.getD_eq_getElem _ _ inside]
      exact List.getElem_mem inside
    have slice (beforeBlock block suffix : List ℕ)
        (avoids : ¬ Contains101 (beforeBlock ++ block ++ suffix) ∧
          ¬ Contains102 (beforeBlock ++ block ++ suffix)) :
        ¬ Contains101 block ∧ ¬ Contains102 block := by
      apply (strong_descent block).mpr
      intro first middle last before after inside drop
      have access (index : ℕ) (bound : index < block.length) :
          (beforeBlock ++ block ++ suffix).getD (beforeBlock.length + index) 0 =
            block.getD index 0 := by
        rw [List.getD_append _ _ _ _ (by simp; omega)]
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp
      have descent := (strong_descent _).mp avoids
        (beforeBlock.length + first) (beforeBlock.length + middle) (beforeBlock.length + last)
        (by omega) (by omega) (by simp; omega)
      rw [access first (by omega), access middle (by omega), access last inside] at descent
      exact descent drop
    have recover (upper lower : List ℕ)
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
    · intro avoids
      let upper := tail.takeWhile (fun entry => decide (letter ≤ entry))
      let lower := tail.dropWhile (fun entry => decide (letter ≤ entry))
      have split : tail = upper ++ lower := List.takeWhile_append_dropWhile.symm
      have high : ∀ entry ∈ upper, letter ≤ entry := by
        intro entry member
        have holds := List.mem_takeWhile_imp (p := fun value => decide (letter ≤ value))
          member
        exact of_decide_eq_true holds
      have low : ∀ entry ∈ lower, entry < letter := by
        cases lowerEq : lower with
        | nil => simp
        | cons head rest =>
            have positive : 0 < lower.length := by simp [lowerEq]
            have headBound : head < letter := by
              have failure := List.dropWhile_get_zero_not
                (fun entry => decide (letter ≤ entry)) tail positive
              change ¬ decide (letter ≤ lower.get ⟨0, positive⟩) = true at failure
              simp only [decide_eq_true_eq] at failure
              have value : lower.get ⟨0, positive⟩ = head := by simp [lowerEq]
              rw [value] at failure
              omega
            intro entry member
            rw [List.mem_cons] at member
            rcases member with rfl | member
            · exact headBound
            · obtain ⟨index, inside, value⟩ := List.mem_iff_getElem.mp member
              have headAccess :
                  (letter :: tail).getD (upper.length + 1) 0 = head := by
                rw [List.getD_cons_succ, split]
                rw [List.getD_append_right _ _ _ _ le_rfl]
                simp [lowerEq]
              have laterAccess :
                  (letter :: tail).getD (upper.length + (index + 1) + 1) 0 = entry := by
                rw [List.getD_cons_succ, split]
                rw [List.getD_append_right _ _ _ _ (by omega)]
                simp only [Nat.add_sub_cancel_left, lowerEq, List.getD_cons_succ]
                rw [List.getD_eq_getElem _ _ inside, value]
              have descent := (strong_descent _).mp avoids 0 (upper.length + 1)
                (upper.length + (index + 1) + 1) (by omega) (by omega)
                (by simp [split, lowerEq]; omega)
              simpa only [List.getD_cons_zero, headAccess, laterAccess] using
                descent (by simpa only [List.getD_cons_zero, headAccess] using headBound)
      have upperAvoids : ¬ Contains101 upper ∧ ¬ Contains102 upper := by
        apply slice [letter] upper lower
        simpa [split] using avoids
      have lowerAvoids : ¬ Contains101 lower ∧ ¬ Contains102 lower := by
        apply slice (letter :: upper) lower []
        simpa [split] using avoids
      refine ⟨(upper, lower), ⟨split, high, low, upperAvoids, lowerAvoids⟩, ?_⟩
      rintro ⟨otherUpper, otherLower⟩ ⟨otherSplit, otherHigh, otherLow, _, _⟩
      have sameUpper : otherUpper = upper := by
        rw [← recover otherUpper otherLower otherHigh otherLow, ← otherSplit]
      have sameLower : otherLower = lower := by
        have equality : upper ++ otherLower = upper ++ lower := by
          rw [← sameUpper, ← otherSplit, sameUpper, ← split]
        exact List.append_cancel_left equality
      exact Prod.ext sameUpper sameLower
    · rintro ⟨⟨upper, lower⟩, ⟨split, high, low, upperAvoids, lowerAvoids⟩, _⟩
      rw [split]
      apply (strong_descent _).mpr
      intro first middle last before after inside drop
      have upperEntry (index : ℕ) (bound : index < upper.length) :
          (letter :: (upper ++ lower)).getD (index + 1) 0 = upper.getD index 0 := by
        rw [List.getD_cons_succ, List.getD_append _ _ _ _ bound]
      have lowerEntry (index : ℕ) :
          (letter :: (upper ++ lower)).getD (upper.length + index + 1) 0 =
            lower.getD index 0 := by
        rw [List.getD_cons_succ, List.getD_append_right _ _ _ _ (by omega)]
        simp
      have lastBound : last < upper.length + lower.length + 1 := by simpa using inside
      by_cases firstZero : first = 0
      · subst first
        by_cases middleUpper : middle ≤ upper.length
        · have middlePositive : 0 < middle := before
          have middleAccess := upperEntry (middle - 1) (by omega)
          have above := high _ (entryMem upper (middle - 1) (by omega))
          rw [show middle - 1 + 1 = middle by omega] at middleAccess
          simp only [List.getD_cons_zero, middleAccess] at drop
          omega
        · have lastLower : last = upper.length + (last - upper.length - 1) + 1 := by
            omega
          rw [lastLower, lowerEntry, List.getD_cons_zero]
          exact low _ (entryMem lower _ (by omega))
      · by_cases firstUpper : first ≤ upper.length
        · have firstAccess := upperEntry (first - 1) (by omega)
          rw [show first - 1 + 1 = first by omega] at firstAccess
          by_cases lastUpper : last ≤ upper.length
          · have middleAccess := upperEntry (middle - 1) (by omega)
            have lastAccess := upperEntry (last - 1) (by omega)
            rw [show middle - 1 + 1 = middle by omega] at middleAccess
            rw [show last - 1 + 1 = last by omega] at lastAccess
            rw [firstAccess, middleAccess] at drop
            rw [firstAccess, lastAccess]
            exact (strong_descent upper).mp upperAvoids _ _ _ (by omega) (by omega)
              (by omega) drop
          · have lastLower : last = upper.length + (last - upper.length - 1) + 1 := by
              omega
            rw [firstAccess, lastLower, lowerEntry]
            have below := low _ (entryMem lower (last - upper.length - 1) (by omega))
            have above := high _ (entryMem upper (first - 1) (by omega))
            omega
        · have firstLower : first = upper.length + (first - upper.length - 1) + 1 := by
            omega
          have middleLower : middle = upper.length + (middle - upper.length - 1) + 1 := by
            omega
          have lastLower : last = upper.length + (last - upper.length - 1) + 1 := by omega
          have firstAccess := lowerEntry (first - upper.length - 1)
          have middleAccess := lowerEntry (middle - upper.length - 1)
          have lastAccess := lowerEntry (last - upper.length - 1)
          rw [← firstLower] at firstAccess
          rw [← middleLower] at middleAccess
          rw [← lastLower] at lastAccess
          rw [firstAccess, middleAccess] at drop
          rw [firstAccess, lastAccess]
          exact (strong_descent lower).mp lowerAvoids _ _ _ (by omega) (by omega)
            (by omega) drop
  
  have entryMem (block : List ℕ) (index : ℕ) (inside : index < block.length) :
      block.getD index 0 ∈ block := by
    rw [List.getD_eq_getElem _ _ inside]
    exact List.getElem_mem inside
  have finiteWords (bound length : ℕ) : Finite (words bound length) := by
    let encode (word : words bound length) (index : Fin length) : Fin bound :=
      ⟨word.1.getD index 0,
        word.2.2.1 _ (entryMem _ _ (by rw [word.2.1]; exact index.isLt))⟩
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
  have (bound length : ℕ) : Finite (words bound length) := finiteWords bound length
  have translate (base : ℕ) (block : List ℕ) :
      (¬ Contains101 (block.map (base + ·)) ∧ ¬ Contains102 (block.map (base + ·))) ↔
        (¬ Contains101 block ∧ ¬ Contains102 block) := by
    have access (index : ℕ) (inside : index < block.length) :
        (block.map (base + ·)).getD index 0 = base + block.getD index 0 := by
      rw [List.getD_eq_getElem _ _ (by simpa using inside),
        List.getD_eq_getElem _ _ inside]
      simp
    rw [strong_descent, strong_descent]
    constructor
    · intro descent first middle last before after inside drop
      have value := descent first middle last before after (by simpa using inside)
      rw [access first (by omega), access middle (by omega), access last inside] at value
      have strict : base + block.getD middle 0 < base + block.getD first 0 := by omega
      have result := value strict
      omega
    · intro descent first middle last before after inside drop
      have bound : last < block.length := by simpa using inside
      rw [access first (by omega), access middle (by omega)] at drop
      rw [access first (by omega), access last bound]
      have strict : block.getD middle 0 < block.getD first 0 := by omega
      have result := descent first middle last before after bound strict
      omega
  have unshift (base : ℕ) (block : List ℕ) :
      (block.map (base + ·)).map (· - base) = block := by
    simp [List.map_map, Function.comp_def]
  have restore (base : ℕ) (block : List ℕ) (high : ∀ entry ∈ block, base ≤ entry) :
      (block.map (· - base)).map (base + ·) = block := by
    rw [List.map_map]
    calc
      _ = block.map id := List.map_congr_left fun entry member => by
        simp only [Function.comp_apply, id_eq]
        have bound := high entry member
        omega
      _ = block := List.map_id _
  have recover (base : ℕ) (upper lower : List ℕ)
      (high : ∀ entry ∈ upper, base ≤ entry)
      (low : ∀ entry ∈ lower, entry < base) :
      (upper ++ lower).takeWhile (fun entry => decide (base ≤ entry)) = upper := by
    rw [List.takeWhile_append_of_pos (by simpa using high)]
    have empty : lower.takeWhile (fun entry => decide (base ≤ entry)) = [] := by
      apply List.takeWhile_eq_nil_iff.mpr
      intro positive
      have below := low (lower.get ⟨0, positive⟩) (List.get_mem _ _)
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      omega
    simp [empty]
  let Pieces := Σ first : Fin alphabet, Σ split : Fin (size + 1),
    words (alphabet - first) split × words first (size - split)
  let build (pieces : Pieces) : words alphabet (size + 1) := by
    rcases pieces with ⟨first, split, upper, lower⟩
    refine ⟨first :: (upper.1.map (first.val + ·) ++ lower.1), ?_⟩
    have high : ∀ entry ∈ upper.1.map (first.val + ·), first.val ≤ entry := by
      intro entry member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      omega
    have low : ∀ entry ∈ lower.1, entry < first.val := lower.2.2.1
    have avoids : ¬ Contains101 (first.val :: (upper.1.map (first.val + ·) ++ lower.1)) ∧
        ¬ Contains102 (first.val :: (upper.1.map (first.val + ·) ++ lower.1)) := by
      apply (word_decomposition _ _).mpr
      refine ⟨(upper.1.map (first.val + ·), lower.1),
        ⟨rfl, high, low, (translate _ _).mpr upper.2.2.2, lower.2.2.2⟩, ?_⟩
      rintro ⟨otherUpper, otherLower⟩ ⟨equal, otherHigh, otherLow, _, _⟩
      change upper.1.map (first.val + ·) ++ lower.1 = otherUpper ++ otherLower at equal
      change ∀ entry ∈ otherUpper, first.val ≤ entry at otherHigh
      change ∀ entry ∈ otherLower, entry < first.val at otherLow
      have sameUpper : otherUpper = upper.1.map (first.val + ·) := by
        rw [← recover _ _ _ otherHigh otherLow, ← equal, recover _ _ _ high low]
      have sameLower : otherLower = lower.1 := by
        exact List.append_cancel_left (by simpa only [sameUpper] using equal.symm)
      exact Prod.ext sameUpper sameLower
    refine ⟨?_, ?_, avoids⟩
    · simp only [List.length_cons, List.length_append, List.length_map, upper.2.1, lower.2.1]
      have bound := split.isLt
      omega
    · intro entry member
      simp only [List.mem_cons, List.mem_append] at member
      rcases member with rfl | member | member
      · exact first.isLt
      · obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp member
        have bound := upper.2.2.1 original originalMem
        have firstBound := first.isLt
        omega
      · have bound := low entry member
        exact bound.trans first.isLt
  have injective : Function.Injective build := by
    rintro ⟨firstLeft, splitLeft, upperLeft, lowerLeft⟩
      ⟨firstRight, splitRight, upperRight, lowerRight⟩ equal
    have sameWord := congrArg Subtype.val equal
    have sameFirst : firstLeft = firstRight := by
      apply Fin.ext
      have value := congrArg (fun word : List ℕ => word.getD 0 0) sameWord
      simpa only [build, List.getD_cons_zero] using value
    subst firstRight
    have sameTail : upperLeft.1.map (firstLeft.val + ·) ++ lowerLeft.1 =
        upperRight.1.map (firstLeft.val + ·) ++ lowerRight.1 := by
      change firstLeft.val :: _ = firstLeft.val :: _ at sameWord
      exact List.cons.inj sameWord |>.2
    have high (block : List ℕ) :
        ∀ entry ∈ block.map (firstLeft.val + ·), firstLeft.val ≤ entry := by
      intro entry member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      omega
    have mappedEqual : upperLeft.1.map (firstLeft.val + ·) =
        upperRight.1.map (firstLeft.val + ·) := by
      rw [← recover _ _ _ (high _) lowerLeft.2.2.1, sameTail,
        recover _ _ _ (high _) lowerRight.2.2.1]
    have upperEqual : upperLeft.1 = upperRight.1 := by
      have value := congrArg (List.map (· - firstLeft.val)) mappedEqual
      simpa only [unshift] using value
    have lowerEqual : lowerLeft.1 = lowerRight.1 := by
      rw [mappedEqual] at sameTail
      exact List.append_cancel_left sameTail
    have splitEqual : splitLeft = splitRight := by
      apply Fin.ext
      rw [← upperLeft.2.1, ← upperRight.2.1, upperEqual]
    subst splitRight
    have upperSubtype : upperLeft = upperRight := Subtype.ext upperEqual
    have lowerSubtype : lowerLeft = lowerRight := Subtype.ext lowerEqual
    subst upperRight
    subst lowerRight
    rfl
  have surjective : Function.Surjective build := by
    rintro ⟨word, length, bounded, avoids⟩
    cases word with
    | nil => simp at length
    | cons first tail =>
        obtain ⟨⟨upper, lower⟩, ⟨split, high, low, upperAvoids, lowerAvoids⟩, _⟩ :=
          (word_decomposition first tail).mp avoids
        have firstBound : first < alphabet := bounded first (by simp)
        have tailLength : upper.length + lower.length = size := by
          simp only [List.length_cons, split, List.length_append] at length
          omega
        let firstIndex : Fin alphabet := ⟨first, firstBound⟩
        let splitIndex : Fin (size + 1) := ⟨upper.length, by omega⟩
        have normalized : upper.map (· - first) ∈ words (alphabet - first) splitIndex := by
          refine ⟨by simp [splitIndex], ?_, ?_⟩
          · intro entry member
            obtain ⟨original, originalMem, rfl⟩ := List.mem_map.mp member
            have above := high original originalMem
            have below := bounded original (by simp [split, originalMem])
            omega
          · apply (translate first _).mp
            rw [restore first upper high]
            exact upperAvoids
        have lowerWord : lower ∈ words first (size - splitIndex) := by
          refine ⟨?_, low, lowerAvoids⟩
          change lower.length = size - upper.length
          omega
        refine ⟨⟨firstIndex, splitIndex, ⟨_, normalized⟩, ⟨lower, lowerWord⟩⟩, ?_⟩
        apply Subtype.ext
        change first :: ((upper.map (· - first)).map (first + ·) ++ lower) = first :: tail
        rw [restore first upper high, ← split]
  have cardinal := Nat.card_congr (Equiv.ofBijective build ⟨injective, surjective⟩)
  change Nat.card Pieces = Nat.card (words alphabet (size + 1)) at cardinal
  rw [← Nat.card_coe_set_eq, ← cardinal]
  change Nat.card (Σ first : Fin alphabet, Σ split : Fin (size + 1),
    words (alphabet - first) split × words first (size - split)) = _
  have (first : Fin alphabet) : Finite (Σ split : Fin (size + 1),
      words (alphabet - first) split × words first (size - split)) := by infer_instance
  rw [Nat.card_sigma]
  simp_rw [Nat.card_sigma, Nat.card_prod, Nat.card_coe_set_eq]

end D5.S3.Combinatorics.LevelSequence.LevelSequenceWordCount
