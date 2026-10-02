/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTerminal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTerminal
   mirror-E: none(waiver:last-opening-extraction)
   anchors: []
   utility: none
   digest: Extracts the last-opening terminal blocks and the mountain-case restriction. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoPartition
import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeINesting
import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeIINesting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTerminal

open NonnestingBasicOrders

theorem terminal_factorization (word : List ℕ) (pivot : ℕ) (member : pivot ∈ word)
    (double : ∀ letter ∈ word, word.count letter = 2)
    (lastOpening : ∀ letter ∈ word, word.idxOf letter ≤ word.idxOf pivot) :
    (¬ NonnestingDefs.Occurs [1, 2, 2, 1] word ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2] word ∧
      ¬ NonnestingDefs.Occurs [1, 3, 2, 2] word) ↔
    (¬ NonnestingDefs.Occurs [1, 2, 2, 1]
        (word.filter (fun letter => decide (pivot < letter))) ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2]
        (word.filter (fun letter => decide (pivot < letter))) ∧
      ¬ NonnestingDefs.Occurs [1, 3, 2, 2]
        (word.filter (fun letter => decide (pivot < letter)))) ∧
    (¬ NonnestingDefs.Occurs [1, 2, 2, 1]
        (word.filter (fun letter => decide (letter < pivot))) ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2]
        (word.filter (fun letter => decide (letter < pivot))) ∧
      ¬ NonnestingDefs.Occurs [1, 3, 2, 2]
        (word.filter (fun letter => decide (letter < pivot)))) ∧
    ∃! parameters : ℕ ⊕ (List ℕ × ℕ),
      match parameters with
      | Sum.inl cut =>
          cut ≤ (word.filter (fun letter => decide (letter < pivot))).length ∧
          word = NonnestingOneThreeTwoTwoTypeI.typeIWord
            (word.filter (fun letter => decide (pivot < letter)))
            (word.filter (fun letter => decide (letter < pivot))) pivot cut ∧
          (∀ letter ∈ word.filter (fun letter => decide (letter < pivot)),
            (word.filter (fun letter => decide (letter < pivot))).idxOf letter < cut) ∧
          word.length - word.idxOf pivot - 1 =
            (word.filter (fun letter => decide (letter < pivot))).length - cut + 1
      | Sum.inr pair =>
          word = NonnestingOneThreeTwoTwoTypeII.typeIIWord
            (word.filter (fun letter => decide (pivot < letter))) pair.1 pivot pair.2 ∧
          pair.1.Nodup ∧
          word.filter (fun letter => decide (letter < pivot)) = pair.1 ++ pair.1 ∧
          pair.2 < (word.filter (fun letter => decide (pivot < letter))).length ∧
          (∀ letter ∈ word.filter (fun letter => decide (pivot < letter)),
            (word.filter (fun letter => decide (pivot < letter))).idxOf letter < pair.2) ∧
          word.length - word.idxOf pivot - 1 =
            (word.filter (fun letter => decide (pivot < letter))).length - pair.2 +
              pair.1.length + 1 := by
  constructor
  swap
  · rintro ⟨upperGood, lowerGood, parameters, admissible, _⟩
    let upper := word.filter (fun letter => decide (pivot < letter))
    let lower := word.filter (fun letter => decide (letter < pivot))
    have upperValues : ∀ letter ∈ upper, pivot < letter := by
      intro letter present
      simpa [upper] using (List.mem_filter.mp present).2
    have lowerValues : ∀ letter ∈ lower, letter < pivot := by
      intro letter present
      simpa [lower] using (List.mem_filter.mp present).2
    have upperDouble : ∀ letter ∈ upper, upper.count letter = 2 := by
      intro letter present
      have parts := List.mem_filter.mp present
      have countEq := double letter parts.1
      simpa [upper, List.count_filter, parts.2] using countEq
    have lowerDouble : ∀ letter ∈ lower, lower.count letter = 2 := by
      intro letter present
      have parts := List.mem_filter.mp present
      have countEq := double letter parts.1
      simpa [lower, List.count_filter, parts.2] using countEq
    cases parameters with
    | inl cut =>
      have noNest := NonnestingOneThreeTwoTwoTypeINesting.typeI_nonnesting
        upper lower pivot cut upperValues lowerValues lowerDouble
        ⟨upperGood.1, upperGood.2.1⟩ ⟨lowerGood.1, lowerGood.2.1⟩ admissible.2.2.1
      have noPattern := NonnestingOneThreeTwoTwoTypeI.typeI_avoids
        upper lower pivot cut upperValues lowerValues upperDouble lowerDouble
        upperGood.2.2 lowerGood.2.2 admissible.2.2.1
      rw [admissible.2.1]
      exact ⟨noNest.1, noNest.2, noPattern⟩
    | inr pair =>
      have mountainNest : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] (pair.1 ++ pair.1) ∧
          ¬ NonnestingDefs.Occurs [2, 1, 1, 2] (pair.1 ++ pair.1) := by
        rw [← admissible.2.2.1]
        exact ⟨lowerGood.1, lowerGood.2.1⟩
      have mountainAvoid : ¬ NonnestingDefs.Occurs [1, 3, 2, 2] (pair.1 ++ pair.1) := by
        rw [← admissible.2.2.1]
        exact lowerGood.2.2
      have orderValues : ∀ letter ∈ pair.1, letter < pivot := by
        intro letter present
        apply lowerValues letter
        change letter ∈ word.filter (fun letter => decide (letter < pivot))
        rw [admissible.2.2.1]
        simp [present]
      have noNest := NonnestingOneThreeTwoTwoTypeIINesting.typeII_nonnesting
        upper pair.1 pivot pair.2 upperValues orderValues upperDouble admissible.2.1
        ⟨upperGood.1, upperGood.2.1⟩ mountainNest admissible.2.2.2.2.1
      have noPattern := NonnestingOneThreeTwoTwoTypeII.typeII_avoids
        upper pair.1 pivot pair.2 upperValues orderValues upperDouble admissible.2.1
        upperGood.2.2 mountainAvoid admissible.2.2.2.2.1
      rw [admissible.1]
      exact ⟨noNest.1, noNest.2, noPattern⟩
  rintro ⟨noAscending, noDescending, avoiding⟩
  have nonnesting := And.intro noAscending noDescending
  have restriction (pattern : List ℕ) (predicate : ℕ → Bool)
      (absent : ¬ NonnestingDefs.Occurs pattern word) :
      ¬ NonnestingDefs.Occurs pattern (word.filter predicate) := by
    rintro ⟨labels, increasing, members, subsequence, _⟩
    apply absent
    exact ⟨labels, increasing, fun index positive below =>
      List.mem_of_mem_filter (members index positive below),
      subsequence.trans List.filter_sublist, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨restriction _ _ noAscending, restriction _ _ noDescending,
      restriction _ _ avoiding⟩
  · exact ⟨restriction _ _ noAscending, restriction _ _ noDescending,
      restriction _ _ avoiding⟩
  have slots (letter : ℕ) (present : letter ∈ word) :
      word.idxOf letter < secondPos letter word ∧
      word[secondPos letter word]? = some letter ∧
      (∀ index : ℕ, word[index]? = some letter →
        index = word.idxOf letter ∨ index = secondPos letter word) := by
    obtain ⟨initial, middle, ending, absentInitial, absentMiddle, absentEnding, eq⟩ :=
      count_two_decomposition letter word (double letter present)
    have firstEq : word.idxOf letter = initial.length := by
      simp [eq, List.idxOf_append, absentInitial]
    have secondEq : secondPos letter word = initial.length + 1 + middle.length := by
      have dropInitial : initial.drop (initial.length + 1) = [] := by
        apply List.drop_eq_nil_iff.mpr
        omega
      unfold secondPos
      rw [firstEq, eq]
      simp [List.drop_append, dropInitial, List.idxOf_append, absentMiddle]
    refine ⟨by omega, ?_, ?_⟩
    · rw [secondEq, eq]
      have notInitial : ¬ initial.length + 1 + middle.length < initial.length := by omega
      have offset : initial.length + 1 + middle.length - initial.length =
          middle.length + 1 := by omega
      simp only [List.append_assoc, List.singleton_append, List.getElem?_append,
        if_neg notInitial]
      rw [offset]
      simp
    · intro index value
      rw [firstEq, secondEq]
      by_cases initialBound : index < initial.length
      · have getInitial : initial[index]? = some letter := by
          simpa [eq, List.append_assoc, List.getElem?_append, initialBound] using value
        exact (absentInitial (List.mem_of_getElem? getInitial)).elim
      by_cases firstEqual : index = initial.length
      · exact Or.inl firstEqual
      have positive : 0 < index - initial.length := by omega
      have offset : index - initial.length = (index - initial.length - 1) + 1 := by omega
      have restValue : (letter :: (middle ++ letter :: ending))[index - initial.length]? =
          some letter := by
        simpa [eq, List.append_assoc, List.getElem?_append, initialBound] using value
      rw [offset] at restValue
      have remaining : (middle ++ letter :: ending)[index - initial.length - 1]? =
          some letter := by simpa using restValue
      by_cases middleBound : index - initial.length - 1 < middle.length
      · have getMiddle : middle[index - initial.length - 1]? = some letter := by
          simpa [List.getElem?_append, middleBound] using remaining
        exact (absentMiddle (List.mem_of_getElem? getMiddle)).elim
      by_cases secondEqual : index = initial.length + 1 + middle.length
      · exact Or.inr secondEqual
      have endingOffset : index - initial.length - 1 - middle.length =
          (index - initial.length - 1 - middle.length - 1) + 1 := by omega
      have endingValue : (letter :: ending)[index - initial.length - 1 - middle.length]? =
          some letter := by
        simpa [List.getElem?_append, middleBound] using remaining
      rw [endingOffset] at endingValue
      have getEnding : ending[index - initial.length - 1 - middle.length - 1]? =
          some letter := by simpa using endingValue
      exact (absentEnding (List.mem_of_getElem? getEnding)).elim
  have orders := (nonnesting_iff_equal_orders word double).mp nonnesting
  obtain ⟨before, after, tail, absentBefore, absentAfter, absentTail, wordEq⟩ :=
    count_two_decomposition pivot word (double pivot member)
  have pivotFirst : word.idxOf pivot = before.length := by
    simp [wordEq, List.idxOf_append, absentBefore]
  have pivotSecond : secondPos pivot word = before.length + 1 + after.length := by
    have dropBefore : before.drop (before.length + 1) = [] := by
      apply List.drop_eq_nil_iff.mpr
      omega
    unfold secondPos
    rw [pivotFirst, wordEq]
    simp [List.drop_append, dropBefore, List.idxOf_append, absentAfter]
  have firstBefore (letter : ℕ) (present : letter ∈ word) (different : letter ≠ pivot) :
      word.idxOf letter < before.length := by
    have bound := lastOpening letter present
    have ne : word.idxOf letter ≠ word.idxOf pivot := by
      intro equal
      have letterValue := List.getElem?_idxOf present
      rw [equal, List.getElem?_idxOf member] at letterValue
      exact different (Option.some.inj letterValue.symm)
    omega
  have closingBefore (letter : ℕ) (present : letter ∈ word) (different : letter ≠ pivot) :
      secondPos letter word < before.length + 1 + after.length := by
    rw [← pivotSecond]
    apply orders letter present pivot member
    rw [pivotFirst]
    exact firstBefore letter present different
  have tailEmpty : tail = [] := by
    cases tail with
    | nil => rfl
    | cons letter rest =>
      have present : letter ∈ word := by simp [wordEq]
      have different : letter ≠ pivot := by
        intro equal
        apply absentTail
        simp [← equal]
      have value : word[before.length + 1 + after.length + 1]? = some letter := by
        have offset : before.length + 1 + after.length + 1 - before.length =
            after.length + 2 := by omega
        have notBefore : ¬ before.length + 1 + after.length + 1 < before.length := by
          omega
        rw [wordEq]
        simp only [List.append_assoc, List.singleton_append, List.getElem?_append,
          if_neg notBefore]
        rw [offset]
        simp
      have positions := (slots letter present).2.2 _ value
      have firstBound := firstBefore letter present different
      have secondBound := closingBefore letter present different
      rcases positions with first | second <;> omega
  subst tail
  have afterMember (letter : ℕ) (present : letter ∈ after) : letter ∈ word := by
    simp [wordEq, present]
  have beforeMember (letter : ℕ) (present : letter ∈ before) : letter ∈ word := by
    simp [wordEq, present]
  have afterDifferent (letter : ℕ) (present : letter ∈ after) : letter ≠ pivot := by
    intro equal
    exact absentAfter (equal ▸ present)
  have beforeDifferent (letter : ℕ) (present : letter ∈ before) : letter ≠ pivot := by
    intro equal
    exact absentBefore (equal ▸ present)
  have afterClosing (index letter : ℕ) (value : after[index]? = some letter) :
      secondPos letter word = before.length + 1 + index := by
    have bound := (List.getElem?_eq_some_iff.mp value).1
    have present := List.mem_of_getElem? value
    have wholeValue : word[before.length + 1 + index]? = some letter := by
      have offset : before.length + 1 + index - before.length = index + 1 := by omega
      have notBefore : ¬ before.length + 1 + index < before.length := by omega
      rw [wordEq]
      simp only [List.append_assoc, List.singleton_append, List.getElem?_append,
        if_neg notBefore]
      rw [offset]
      simpa [List.getElem?_append, bound] using value
    have possibilities := (slots letter (afterMember letter present)).2.2 _ wholeValue
    have firstBound := firstBefore letter (afterMember letter present)
      (afterDifferent letter present)
    rcases possibilities with first | second
    · omega
    · exact second.symm
  have afterDistinct : after.Nodup := by
    apply List.nodup_iff_injective_get.mpr
    intro left right equal
    have leftValue : after[left.val]? = some (after.get left) := by simp
    have rightValue : after[right.val]? = some (after.get left) := by
      simpa only [equal] using (show after[right.val]? = some (after.get right) by simp)
    have leftPosition := afterClosing _ _ leftValue
    have rightPosition := afterClosing _ _ rightValue
    apply Fin.ext
    omega
  have afterCount (letter : ℕ) (present : letter ∈ after) : before.count letter = 1 := by
    have wholeCount := double letter (afterMember letter present)
    have uniqueCount := List.count_eq_one_of_mem afterDistinct present
    have different := afterDifferent letter present
    simp [wordEq, List.count_append, Ne.symm different] at wholeCount
    omega
  have beforeEq : before = before.filter (fun letter => decide (pivot < letter)) ++
      before.filter (fun letter => decide (letter < pivot)) := by
    have eq := NonnestingOneThreeTwoTwoPartition.prefix_partition
      word pivot member double avoiding
    have takeEq : word.take (word.idxOf pivot) = before := by
      rw [pivotFirst, wordEq]
      simp
    simpa [takeEq] using eq
  have highBeforeLow (higher lower : ℕ) (highMem : higher ∈ before)
      (lowMem : lower ∈ before) (high : pivot < higher) (low : lower < pivot) :
      word.idxOf higher < word.idxOf lower := by
    have highKept : higher ∈ before.filter (fun letter => decide (pivot < letter)) := by
      simp [highMem, high]
    have lowKept : lower ∈ before.filter (fun letter => decide (letter < pivot)) := by
      simp [lowMem, low]
    have lowNotHigh : lower ∉ before.filter (fun letter => decide (pivot < letter)) := by
      simp [show ¬ pivot < lower by omega]
    have highBound := List.idxOf_lt_length_of_mem highKept
    have highEq : before.idxOf higher =
        (before.filter (fun letter => decide (pivot < letter))).idxOf higher := by
      conv_lhs => rw [beforeEq]
      simp [List.idxOf_append, highKept]
    have lowEq : before.idxOf lower =
        (before.filter (fun letter => decide (pivot < letter))).length +
        (before.filter (fun letter => decide (letter < pivot))).idxOf lower := by
      conv_lhs => rw [beforeEq]
      simp [List.idxOf_append, lowNotHigh, Nat.add_comm]
    have firstHigh : word.idxOf higher = before.idxOf higher := by
      simp [wordEq, List.append_assoc, List.idxOf_append, highMem]
    have firstLow : word.idxOf lower = before.idxOf lower := by
      simp [wordEq, List.append_assoc, List.idxOf_append, lowMem]
    omega
  have afterOrdered : ∀ first second lower higher : ℕ,
      after[first]? = some lower → after[second]? = some higher →
      lower < pivot → pivot < higher → second < first := by
    intro first second lower higher getLow getHigh low high
    have lowMem := List.mem_of_getElem? getLow
    have highMem := List.mem_of_getElem? getHigh
    have lowBefore : lower ∈ before := List.count_pos_iff.mp (by
      rw [afterCount lower lowMem]
      omega)
    have highBefore : higher ∈ before := List.count_pos_iff.mp (by
      rw [afterCount higher highMem]
      omega)
    have firstOrder := highBeforeLow higher lower highBefore lowBefore high low
    have secondOrder := orders higher (afterMember higher highMem)
      lower (afterMember lower lowMem) firstOrder
    rw [afterClosing _ _ getHigh, afterClosing _ _ getLow] at secondOrder
    omega
  have separate : ∀ sequence : List ℕ, pivot ∉ sequence →
      (∀ first second lower higher : ℕ,
        sequence[first]? = some lower → sequence[second]? = some higher →
        lower < pivot → pivot < higher → second < first) →
      sequence = sequence.filter (fun letter => decide (pivot < letter)) ++
        sequence.filter (fun letter => decide (letter < pivot)) := by
    intro sequence
    induction sequence with
    | nil => simp
    | cons head rest inductionHyp =>
      intro absent ordered
      have absentParts : pivot ≠ head ∧ pivot ∉ rest := by simpa using absent
      by_cases high : pivot < head
      · have restOrdered : ∀ first second lower higher : ℕ,
            rest[first]? = some lower → rest[second]? = some higher →
            lower < pivot → pivot < higher → second < first := by
          intro first second lower higher getLow getHigh low high
          have inequality := ordered (first + 1) (second + 1) lower higher
            (by simpa using getLow) (by simpa using getHigh) low high
          omega
        have restEq := inductionHyp absentParts.2 restOrdered
        simp [high, show ¬ head < pivot by omega, ← restEq]
      · have low : head < pivot := by omega
        have restLow : ∀ letter ∈ rest, letter < pivot := by
          intro letter present
          by_contra notLow
          have different : letter ≠ pivot := fun eq => absentParts.2 (eq ▸ present)
          have high : pivot < letter := by omega
          have inequality := ordered 0 (rest.idxOf letter + 1) head letter (by simp)
            (by simpa using List.getElem?_idxOf present) low high
          omega
        have highEmpty : rest.filter (fun letter => decide (pivot < letter)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter present
          simp [show ¬ pivot < letter by have := restLow letter present; omega]
        have lowAll : rest.filter (fun letter => decide (letter < pivot)) = rest := by
          apply List.filter_eq_self.mpr
          intro letter present
          simp [restLow letter present]
        simp [high, low, highEmpty, lowAll]
  have afterEq := separate after absentAfter afterOrdered
  have mountainDistinct : after.filter (fun letter => decide (pivot < letter)) ≠ [] →
      (before.filter (fun letter => decide (letter < pivot))).Nodup := by
    intro upperNonempty
    obtain ⟨higher, highMember⟩ := List.exists_mem_of_ne_nil _ upperNonempty
    have highParts := List.mem_filter.mp highMember
    have high : pivot < higher := by simpa using highParts.2
    have highBefore : higher ∈ before := List.count_pos_iff.mp (by
      rw [afterCount higher highParts.1]
      omega)
    apply List.nodup_iff_count_le_one.mpr
    intro lower
    by_cases low : lower < pivot
    · by_cases lowMember : lower ∈ before
      · have lowFirst := highBeforeLow higher lower highBefore lowMember high low
        have secondOrder := orders higher (afterMember higher highParts.1)
          lower (beforeMember lower lowMember) lowFirst
        have highClosing := afterClosing _ _ (List.getElem?_idxOf highParts.1)
        have lowCount := double lower (beforeMember lower lowMember)
        have different := beforeDifferent lower lowMember
        have countSum : before.count lower + after.count lower = 2 := by
          simpa [wordEq, List.count_append, Ne.symm different] using lowCount
        have lowAfter : lower ∈ after := by
          by_contra absent
          have zero := List.count_eq_zero.mpr absent
          have fullBefore : before.count lower = 2 := by omega
          obtain ⟨initial, middle, ending, absentInitial, absentMiddle, _, beforeSplit⟩ :=
            count_two_decomposition lower before fullBefore
          have firstEq : word.idxOf lower = initial.length := by
            simp [wordEq, beforeSplit, List.append_assoc, List.idxOf_append, absentInitial]
          have secondEq : secondPos lower word = initial.length + 1 + middle.length := by
            have dropInitial : initial.drop (initial.length + 1) = [] := by
              apply List.drop_eq_nil_iff.mpr
              omega
            unfold secondPos
            rw [firstEq, wordEq, beforeSplit]
            simp [List.append_assoc, List.drop_append, dropInitial,
              List.idxOf_append, absentMiddle]
          have lengthEq : before.length =
              initial.length + 1 + middle.length + 1 + ending.length := by
            simp [beforeSplit, List.length_append, Nat.add_comm, Nat.add_left_comm]
          omega
        have one := afterCount lower lowAfter
        simpa [List.count_filter, low] using Nat.le_of_eq one
      · have absent : lower ∉ before.filter (fun letter => decide (letter < pivot)) := by
          simp [lowMember]
        rw [List.count_eq_zero.mpr absent]
        omega
    · have absent : lower ∉ before.filter (fun letter => decide (letter < pivot)) := by
        simp [low]
      rw [List.count_eq_zero.mpr absent]
      omega
  let upperBefore := before.filter (fun letter => decide (pivot < letter))
  let upperAfter := after.filter (fun letter => decide (pivot < letter))
  let lowerBefore := before.filter (fun letter => decide (letter < pivot))
  let lowerAfter := after.filter (fun letter => decide (letter < pivot))
  have upperEq : word.filter (fun letter => decide (pivot < letter)) =
      upperBefore ++ upperAfter := by
    simp [wordEq, List.filter_append, upperBefore, upperAfter]
  have lowerEq : word.filter (fun letter => decide (letter < pivot)) =
      lowerBefore ++ lowerAfter := by
    simp [wordEq, List.filter_append, lowerBefore, lowerAfter]
  have wordBlocks : word = upperBefore ++ lowerBefore ++ [pivot] ++
      upperAfter ++ lowerAfter ++ [pivot] := by
    simpa [List.append_assoc, upperBefore, upperAfter, lowerBefore, lowerAfter,
      ← beforeEq, ← afterEq] using wordEq
  have tailPresent : ∀ letter ∈ lowerAfter, letter ∈ lowerBefore := by
    intro letter present
    have parts := List.mem_filter.mp present
    have firstMem : letter ∈ before := List.count_pos_iff.mp (by
      rw [afterCount letter parts.1]
      omega)
    exact List.mem_filter.mpr ⟨firstMem, parts.2⟩
  let upper := word.filter (fun letter => decide (pivot < letter))
  let lower := word.filter (fun letter => decide (letter < pivot))
  have upperHigh : ∀ letter ∈ upper, pivot < letter := by
    intro letter present
    simpa [upper] using (List.mem_filter.mp present).2
  have lowerLow : ∀ letter ∈ lower, letter < pivot := by
    intro letter present
    simpa [lower] using (List.mem_filter.mp present).2
  have pivotUpper : pivot ∉ upper := by simp [upper]
  have pivotLower : pivot ∉ lower := by simp [lower]
  have highFilter : upper.filter (fun letter => decide (pivot < letter)) = upper := by
    apply List.filter_eq_self.mpr
    intro letter present
    simp [upperHigh letter present]
  have inverseI (cut : ℕ) (bound : cut ≤ lower.length)
      (eq : word = NonnestingOneThreeTwoTwoTypeI.typeIWord upper lower pivot cut) :
      (word.take (word.idxOf pivot)).filter (fun letter => decide (pivot < letter)) =
        upper ∧ word.idxOf pivot = upper.length + cut := by
    let initial := upper ++ lower.take cut
    have initialAbsent : pivot ∉ initial := by
      simp [initial, pivotUpper,
        show pivot ∉ lower.take cut from fun present =>
          pivotLower (List.mem_of_mem_take present)]
    have eq' : word = initial ++ [pivot] ++ lower.drop cut ++ [pivot] := eq
    have firstEq : word.idxOf pivot = initial.length := by
      simp [eq', List.append_assoc, List.idxOf_append, initialAbsent]
    have takeEq : word.take (word.idxOf pivot) = initial := by
      rw [firstEq, eq']
      simp
    have takeHigh : (lower.take cut).filter (fun letter => decide (pivot < letter)) =
        [] := by
      apply List.filter_eq_nil_iff.mpr
      intro letter present
      have low := lowerLow letter (List.mem_of_mem_take present)
      simp [show ¬ pivot < letter by omega]
    constructor
    · simp [takeEq, initial, List.filter_append, highFilter, takeHigh]
    · simpa [initial, List.length_append, Nat.min_eq_left bound] using firstEq
  have inverseII (order : List ℕ) (cut : ℕ) (bound : cut < upper.length)
      (eq : word = NonnestingOneThreeTwoTwoTypeII.typeIIWord upper order pivot cut)
      (lowerEq : lower = order ++ order) :
      (word.take (word.idxOf pivot)).filter (fun letter => decide (pivot < letter)) =
        upper.take cut ∧
      (word.take (word.idxOf pivot)).filter (fun letter => decide (letter < pivot)) =
        order ∧ word.idxOf pivot = cut + order.length := by
    have orderLow : ∀ letter ∈ order, letter < pivot := by
      intro letter present
      apply lowerLow letter
      rw [lowerEq]
      simp [present]
    have pivotOrder : pivot ∉ order := by
      intro present
      have impossible := orderLow pivot present
      omega
    let initial := upper.take cut ++ order
    have initialAbsent : pivot ∉ initial := by
      simp [initial, pivotOrder,
        show pivot ∉ upper.take cut from fun present =>
          pivotUpper (List.mem_of_mem_take present)]
    have eq' : word = initial ++ [pivot] ++ upper.drop cut ++ order ++ [pivot] := eq
    have firstEq : word.idxOf pivot = initial.length := by
      simp [eq', List.append_assoc, List.idxOf_append, initialAbsent]
    have takeEq : word.take (word.idxOf pivot) = initial := by
      rw [firstEq, eq']
      simp
    have initialHigh : (upper.take cut).filter (fun letter => decide (pivot < letter)) =
        upper.take cut := by
      apply List.filter_eq_self.mpr
      intro letter present
      simp [upperHigh letter (List.mem_of_mem_take present)]
    have initialLow : (upper.take cut).filter (fun letter => decide (letter < pivot)) =
        [] := by
      apply List.filter_eq_nil_iff.mpr
      intro letter present
      have high := upperHigh letter (List.mem_of_mem_take present)
      simp [show ¬ letter < pivot by omega]
    have orderHigh : order.filter (fun letter => decide (pivot < letter)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro letter present
      simp [show ¬ pivot < letter by have := orderLow letter present; omega]
    have orderFilter : order.filter (fun letter => decide (letter < pivot)) = order := by
      apply List.filter_eq_self.mpr
      intro letter present
      simp [orderLow letter present]
    refine ⟨?_, ?_, ?_⟩
    · simp [takeEq, initial, List.filter_append, initialHigh, orderHigh]
    · simp [takeEq, initial, List.filter_append, initialLow, orderFilter]
    · simpa [initial, List.length_append, Nat.min_eq_left (Nat.le_of_lt bound)]
        using firstEq
  by_cases upperEmpty : upperAfter = []
  · have bound : lowerBefore.length ≤ lower.length := by
      simp [lower, lowerEq]
    have construction : word =
        NonnestingOneThreeTwoTwoTypeI.typeIWord upper lower pivot lowerBefore.length := by
      unfold NonnestingOneThreeTwoTwoTypeI.typeIWord upper lower
      rw [upperEq, lowerEq, wordBlocks, upperEmpty]
      simp [List.append_assoc]
    refine ⟨Sum.inl lowerBefore.length, ⟨bound, construction, ?_, ?_⟩, ?_⟩
    · intro letter present
      rw [lowerEq] at present ⊢
      have firstMem : letter ∈ lowerBefore := by
        rcases List.mem_append.mp present with initial | ending
        · exact initial
        · exact tailPresent letter ending
      rw [List.idxOf_append_of_mem firstMem]
      exact List.idxOf_lt_length_of_mem firstMem
    · have firstEq := (inverseI lowerBefore.length bound construction).2
      have lengthEq : word.length = upper.length + lower.length + 2 := by
        rw [construction]
        simp only [NonnestingOneThreeTwoTwoTypeI.typeIWord, List.length_append,
          List.length_take, List.length_drop, List.length_singleton]
        omega
      change word.length - word.idxOf pivot - 1 = lower.length - lowerBefore.length + 1
      omega
    · intro parameters admissible
      cases parameters with
      | inl cut =>
        have actual := inverseI lowerBefore.length bound construction
        have other := inverseI cut admissible.1 admissible.2.1
        have cutEq : cut = lowerBefore.length := by omega
        simp [cutEq]
      | inr pair =>
        have actual := inverseI lowerBefore.length bound construction
        have other := inverseII pair.1 pair.2 admissible.2.2.2.1
          admissible.1 admissible.2.2.1
        have prefixEq : upper = upper.take pair.2 := actual.1.symm.trans other.1
        have lengthEq := congrArg List.length prefixEq
        simp only [List.length_take] at lengthEq
        have bound := admissible.2.2.2.1
        change pair.2 < upper.length at bound
        omega
  · have lowerDistinct : lowerBefore.Nodup := mountainDistinct upperEmpty
    have lowerTailDistinct : lowerAfter.Nodup := afterDistinct.filter _
    have initialPresent : ∀ letter ∈ lowerBefore, letter ∈ lowerAfter := by
      intro letter present
      have parts := List.mem_filter.mp present
      have low : letter < pivot := by simpa using parts.2
      have firstCount := List.count_eq_one_of_mem lowerDistinct present
      have beforeCount : before.count letter = 1 := by
        simpa [lowerBefore, List.count_filter, low] using firstCount
      have wholeCount := double letter (beforeMember letter parts.1)
      have different := beforeDifferent letter parts.1
      have countSum : before.count letter + after.count letter = 2 := by
        simpa [wordEq, List.count_append, Ne.symm different] using wholeCount
      have afterCount : after.count letter = 1 := by omega
      have lastMem : letter ∈ after := List.count_pos_iff.mp (by omega)
      exact List.mem_filter.mpr ⟨lastMem, parts.2⟩
    have firstLow (letter : ℕ) (present : letter ∈ lowerBefore) :
        word.idxOf letter = upperBefore.length + lowerBefore.idxOf letter := by
      have parts := List.mem_filter.mp present
      have low : letter < pivot := by simpa using parts.2
      have absent : letter ∉ upperBefore := by
        simp [upperBefore, show ¬ pivot < letter by omega]
      have firstEq : word.idxOf letter = before.idxOf letter := by
        simp [wordEq, List.append_assoc, List.idxOf_append, parts.1]
      rw [firstEq]
      conv_lhs => rw [beforeEq]
      simp [upperBefore, lowerBefore, List.idxOf_append, absent, Nat.add_comm]
    have secondLow (letter : ℕ) (present : letter ∈ lowerAfter) :
        secondPos letter word = before.length + 1 + upperAfter.length +
          lowerAfter.idxOf letter := by
      have parts := List.mem_filter.mp present
      have low : letter < pivot := by simpa using parts.2
      have absent : letter ∉ upperAfter := by
        simp [upperAfter, show ¬ pivot < letter by omega]
      rw [afterClosing _ _ (List.getElem?_idxOf parts.1)]
      conv_lhs => rw [afterEq]
      simp [upperAfter, lowerAfter, List.idxOf_append, absent, Nat.add_comm,
        Nat.add_left_comm]
    have lowerOrdered : ∀ left ∈ lowerBefore, ∀ right ∈ lowerBefore,
        lowerBefore.idxOf left < lowerBefore.idxOf right →
        lowerAfter.idxOf left < lowerAfter.idxOf right := by
      intro left leftMem right rightMem inequality
      have firstOrder : word.idxOf left < word.idxOf right := by
        rw [firstLow left leftMem, firstLow right rightMem]
        omega
      have leftWhole := beforeMember left (List.mem_filter.mp leftMem).1
      have rightWhole := beforeMember right (List.mem_filter.mp rightMem).1
      have secondOrder := orders left leftWhole right rightWhole firstOrder
      rw [secondLow left (initialPresent left leftMem),
        secondLow right (initialPresent right rightMem)] at secondOrder
      omega
    have orderEquality : ∀ initial ending : List ℕ,
        initial.Nodup → ending.Nodup →
        (∀ letter : ℕ, letter ∈ initial ↔ letter ∈ ending) →
        (∀ left ∈ initial, ∀ right ∈ initial, initial.idxOf left < initial.idxOf right →
          ending.idxOf left < ending.idxOf right) → initial = ending := by
      intro initial
      induction initial with
      | nil =>
        intro ending _ _ sameMembers _
        symm
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro letter present
        simpa using (sameMembers letter).mpr present
      | cons head rest inductionHyp =>
        intro ending initialDistinct endingDistinct sameMembers ordered
        cases ending with
        | nil =>
          have impossible := (sameMembers head).mp (by simp)
          simp at impossible
        | cons last tail =>
          have headEq : head = last := by
            by_contra different
            have lastMem : last ∈ head :: rest := (sameMembers last).mpr (by simp)
            have earlier : (head :: rest).idxOf head < (head :: rest).idxOf last := by
              simp [List.idxOf_cons_ne _ different]
            have impossible := ordered head (by simp) last lastMem earlier
            simp [List.idxOf_cons_ne _ (Ne.symm different)] at impossible
          subst last
          have initialParts := List.nodup_cons.mp initialDistinct
          have endingParts := List.nodup_cons.mp endingDistinct
          have tailMembers : ∀ letter : ℕ, letter ∈ rest ↔ letter ∈ tail := by
            intro letter
            by_cases equal : letter = head
            · subst letter
              simp [initialParts.1, endingParts.1]
            · simpa [equal] using sameMembers letter
          have tailOrder : ∀ left ∈ rest, ∀ right ∈ rest,
              rest.idxOf left < rest.idxOf right → tail.idxOf left < tail.idxOf right := by
            intro left leftMem right rightMem inequality
            have leftNe : head ≠ left := fun equal =>
              initialParts.1 (equal ▸ leftMem)
            have rightNe : head ≠ right := fun equal =>
              initialParts.1 (equal ▸ rightMem)
            have before : (head :: rest).idxOf left < (head :: rest).idxOf right := by
              simpa [List.idxOf_cons_ne _ leftNe, List.idxOf_cons_ne _ rightNe]
                using inequality
            have after := ordered left (by simp [leftMem]) right (by simp [rightMem]) before
            simpa [List.idxOf_cons_ne _ leftNe, List.idxOf_cons_ne _ rightNe] using after
          rw [inductionHyp tail initialParts.2 endingParts.2 tailMembers tailOrder]
    have mountainEq : lowerBefore = lowerAfter := orderEquality lowerBefore lowerAfter
      lowerDistinct lowerTailDistinct (fun letter =>
        ⟨initialPresent letter, tailPresent letter⟩) lowerOrdered
    have construction : word = NonnestingOneThreeTwoTwoTypeII.typeIIWord
        upper lowerBefore pivot upperBefore.length := by
      unfold NonnestingOneThreeTwoTwoTypeII.typeIIWord upper
      rw [upperEq, wordBlocks, ← mountainEq]
      simp [List.append_assoc]
    have mountain : lower = lowerBefore ++ lowerBefore := by
      change word.filter (fun letter => decide (letter < pivot)) = _
      rw [lowerEq, ← mountainEq]
    have bound : upperBefore.length < upper.length := by
      change upperBefore.length <
        (word.filter (fun letter => decide (pivot < letter))).length
      rw [upperEq, List.length_append]
      have positive : 0 < upperAfter.length := List.length_pos_iff.mpr upperEmpty
      omega
    refine ⟨Sum.inr (lowerBefore, upperBefore.length),
      ⟨construction, lowerDistinct, mountain, bound, ?_, ?_⟩, ?_⟩
    · intro letter present
      rw [upperEq] at present ⊢
      have initialMem : letter ∈ upperBefore := by
        rcases List.mem_append.mp present with initial | ending
        · exact initial
        · have parts := List.mem_filter.mp ending
          have firstMem : letter ∈ before := List.count_pos_iff.mp (by
            rw [afterCount letter parts.1]
            omega)
          exact List.mem_filter.mpr ⟨firstMem, parts.2⟩
      rw [List.idxOf_append_of_mem initialMem]
      exact List.idxOf_lt_length_of_mem initialMem
    · have firstEq :=
        (inverseII lowerBefore upperBefore.length bound construction mountain).2.2
      have lengthEq : word.length = upper.length + 2 * lowerBefore.length + 2 := by
        rw [construction]
        simp only [NonnestingOneThreeTwoTwoTypeII.typeIIWord, List.length_append,
          List.length_take, List.length_drop, List.length_singleton]
        omega
      change word.length - word.idxOf pivot - 1 =
        upper.length - upperBefore.length + lowerBefore.length + 1
      omega
    · intro parameters admissible
      have actual := inverseII lowerBefore upperBefore.length bound construction mountain
      cases parameters with
      | inl cut =>
        have other := inverseI cut admissible.1 admissible.2.1
        have prefixEq : upper = upper.take upperBefore.length := other.1.symm.trans actual.1
        have lengthEq := congrArg List.length prefixEq
        simp only [List.length_take] at lengthEq
        omega
      | inr pair =>
        have other := inverseII pair.1 pair.2 admissible.2.2.2.1
          admissible.1 admissible.2.2.1
        have orderEq : pair.1 = lowerBefore := other.2.1.symm.trans actual.2.1
        have cutEq : pair.2 = upperBefore.length := by
          rw [orderEq] at other
          omega
        exact congrArg Sum.inr (Prod.ext orderEq cutEq)

end D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTerminal

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTerminal.terminal_factorization
