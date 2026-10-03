/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeI
   mirror-E: none(waiver:terminal-pivot-construction)
   anchors: []
   utility: none
   digest: A terminal pivot insertion in separated value blocks cannot create 1322. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeI

def typeIWord (upper lower : List ℕ) (pivot cut : ℕ) : List ℕ :=
  upper ++ lower.take cut ++ [pivot] ++ lower.drop cut ++ [pivot]

theorem typeI_avoids (upper lower : List ℕ) (pivot cut : ℕ)
    (upperValues : ∀ letter ∈ upper, pivot < letter)
    (lowerValues : ∀ letter ∈ lower, letter < pivot)
    (upperDouble : ∀ letter ∈ upper, upper.count letter = 2)
    (lowerDouble : ∀ letter ∈ lower, lower.count letter = 2)
    (upperAvoids : ¬ NonnestingDefs.Occurs [1, 3, 2, 2] upper)
    (lowerAvoids : ¬ NonnestingDefs.Occurs [1, 3, 2, 2] lower)
    (terminal : ∀ letter ∈ lower, lower.idxOf letter < cut) :
    ¬ NonnestingDefs.Occurs [1, 3, 2, 2] (typeIWord upper lower pivot cut) := by
  have prefixCriterion (w : List ℕ) (hcount : ∀ letter ∈ w, w.count letter = 2) :
      NonnestingDefs.Occurs [1, 3, 2, 2] w ↔
        ∃ smaller larger repeated first second : ℕ,
          smaller < repeated ∧ repeated < larger ∧
          first < second ∧ second < w.idxOf repeated ∧
          w[first]? = some smaller ∧ w[second]? = some larger ∧ repeated ∈ w := by
    have first_of_two : ∀ (word : List ℕ) (letter first second : ℕ),
        word.count letter = 2 → first < second →
        word[first]? = some letter → word[second]? = some letter →
        first = word.idxOf letter := by
      intro word letter first second countEq before getFirst getSecond
      obtain ⟨initial, middle, ending, absentInitial, absentMiddle, absentEnding, wordEq⟩ :=
        NonnestingBasicOrders.count_two_decomposition letter word countEq
      have firstEq : word.idxOf letter = initial.length := by
        simp [wordEq, List.idxOf_append, absentInitial]
      have slots (index : ℕ) (value : word[index]? = some letter) :
          index = initial.length ∨ index = initial.length + 1 + middle.length := by
        by_cases initialBound : index < initial.length
        · have getInitial : initial[index]? = some letter := by
            simpa [wordEq, List.append_assoc, List.getElem?_append, initialBound] using value
          exact (absentInitial (List.mem_of_getElem? getInitial)).elim
        by_cases firstEqual : index = initial.length
        · exact Or.inl firstEqual
        have offset : index - initial.length = (index - initial.length - 1) + 1 := by omega
        have restValue : (letter :: (middle ++ letter :: ending))[index - initial.length]? =
            some letter := by
          simpa [wordEq, List.append_assoc, List.getElem?_append, initialBound] using value
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
      have firstSlots := slots first getFirst
      have secondSlots := slots second getSecond
      rw [firstEq]
      rcases firstSlots with firstSlot | firstSlot <;>
        rcases secondSlots with secondSlot | secondSlot <;> omega
    constructor
    · rintro ⟨labels, increasing, members, sub, _⟩
      have lower : labels 1 < labels 2 := increasing 1 (by omega) (by
        simp [NonnestingDefs.letters])
      have upper : labels 2 < labels 3 := increasing 2 (by omega) (by
        simp [NonnestingDefs.letters])
      have repeatedMem : labels 2 ∈ w := members 2 (by omega) (by
        simp [NonnestingDefs.letters])
      have sub' : [labels 1, labels 3, labels 2, labels 2].Sublist w := by simpa using sub
      obtain ⟨embedding, getEq⟩ :=
        List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp sub'
      have values (index : Fin 4) : w[(embedding index).val]? =
          [labels 1, labels 3, labels 2, labels 2][index.val]? := by
        rw [List.getElem?_eq_getElem (embedding index).isLt,
          List.getElem?_eq_getElem index.isLt]
        exact congrArg some (getEq index).symm
      have getThird : w[(embedding 2).val]? = some (labels 2) := by simpa using values 2
      have getFourth : w[(embedding 3).val]? = some (labels 2) := by simpa using values 3
      have thirdEq := first_of_two w (labels 2) (embedding 2).val (embedding 3).val
        (hcount _ repeatedMem)
        (embedding.strictMono (by change (2 : Fin 4) < 3; decide)) getThird getFourth
      refine ⟨labels 1, labels 3, labels 2, (embedding 0).val, (embedding 1).val,
        lower, upper, embedding.strictMono (by change (0 : Fin 4) < 1; decide),
        ?_, ?_, ?_, repeatedMem⟩
      · rw [← thirdEq]
        exact embedding.strictMono (by change (1 : Fin 4) < 2; decide)
      · simpa using values 0
      · simpa using values 1
    · rintro ⟨smaller, larger, repeated, first, second, lower, upper,
        firstLt, secondLt, getFirst, getSecond, repeatedMem⟩
      obtain ⟨initial, middle, suffix, notInitial, notMiddle, _, wordEq⟩ :=
        NonnestingBasicOrders.count_two_decomposition repeated w (hcount _ repeatedMem)
      have firstRepeated : w.idxOf repeated = initial.length := by
        simp [wordEq, List.idxOf_append, notInitial]
      have getRepeated : w[w.idxOf repeated]? = some repeated := by
        rw [firstRepeated, wordEq]
        simp
      have getRepeatedAgain : w[initial.length + 1 + middle.length]? = some repeated := by
        rw [wordEq]
        have notBefore : ¬ initial.length + 1 + middle.length < initial.length := by omega
        have offset : initial.length + 1 + middle.length - initial.length =
            middle.length + 1 := by omega
        simp [List.getElem?_append, notBefore, offset]
      let positions : Fin 4 → ℕ := fun index =>
        if index = 0 then first else if index = 1 then second else
        if index = 2 then w.idxOf repeated else initial.length + 1 + middle.length
      have bounded : ∀ index : Fin 4, positions index < w.length := by
        intro index
        fin_cases index <;> simp [positions]
        · exact List.getElem?_eq_some_iff.mp getFirst |>.1
        · exact List.getElem?_eq_some_iff.mp getSecond |>.1
        · exact List.getElem?_eq_some_iff.mp getRepeated |>.1
        · exact List.getElem?_eq_some_iff.mp getRepeatedAgain |>.1
      let embedding : Fin 4 ↪o Fin w.length :=
        OrderEmbedding.ofMapLEIff (fun index => ⟨positions index, bounded index⟩) (by
          intro left right
          fin_cases left <;> fin_cases right <;> simp [positions] <;> omega)
      have sub : [smaller, larger, repeated, repeated].Sublist w := by
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨embedding, ?_⟩
        intro index
        fin_cases index
        · simpa [embedding, positions] using (List.getElem?_eq_some_iff.mp getFirst).2.symm
        · simpa [embedding, positions] using (List.getElem?_eq_some_iff.mp getSecond).2.symm
        · simpa [embedding, positions] using (List.getElem?_eq_some_iff.mp getRepeated).2.symm
        · simpa [embedding, positions] using
            (List.getElem?_eq_some_iff.mp getRepeatedAgain).2.symm
      refine ⟨(fun index => if index = 1 then smaller else
        if index = 2 then repeated else larger), ?_, ?_, ?_, by simp⟩
      · intro index positive below
        simp [NonnestingDefs.letters] at below
        have cases : index = 1 ∨ index = 2 := by omega
        rcases cases with rfl | rfl <;> simp [lower, upper]
      · intro index positive below
        simp [NonnestingDefs.letters] at below
        have cases : index = 1 ∨ index = 2 ∨ index = 3 := by omega
        rcases cases with rfl | rfl | rfl <;> simp [repeatedMem]
        · exact List.mem_of_getElem? getFirst
        · exact List.mem_of_getElem? getSecond
      · simpa using sub
  let initial := lower.take cut
  let ending := lower.drop cut
  let word := typeIWord upper lower pivot cut
  have initialValues : ∀ letter ∈ initial, letter < pivot := by
    intro letter member
    exact lowerValues letter (List.mem_of_mem_take member)
  have endingValues : ∀ letter ∈ ending, letter < pivot := by
    intro letter member
    exact lowerValues letter (List.mem_of_mem_drop member)
  have pivotUpper : pivot ∉ upper := by
    intro member
    have impossible := upperValues pivot member
    omega
  have pivotLower : pivot ∉ lower := by
    intro member
    have impossible := lowerValues pivot member
    omega
  have pivotInitial : pivot ∉ initial := fun member =>
    pivotLower (List.mem_of_mem_take member)
  have pivotEnding : pivot ∉ ending := fun member =>
    pivotLower (List.mem_of_mem_drop member)
  have members (letter : ℕ) : letter ∈ word ↔
      letter ∈ upper ∨ letter ∈ lower ∨ letter = pivot := by
    have splitLower : initial ++ ending = lower := List.take_append_drop cut lower
    simp only [word, typeIWord, List.mem_append, List.mem_singleton]
    constructor
    · rintro ((((member | member) | equal) | member) | equal)
      · exact Or.inl member
      · exact Or.inr (Or.inl (List.mem_of_mem_take member))
      · exact Or.inr (Or.inr equal)
      · exact Or.inr (Or.inl (List.mem_of_mem_drop member))
      · exact Or.inr (Or.inr equal)
    · rintro (member | member | equal)
      · exact Or.inl (Or.inl (Or.inl (Or.inl member)))
      · have splitMember : letter ∈ initial ∨ letter ∈ ending := by
          rw [← splitLower] at member
          exact List.mem_append.mp member
        rcases splitMember with member | member
        · exact Or.inl (Or.inl (Or.inl (Or.inr member)))
        · exact Or.inl (Or.inr member)
      · exact Or.inr equal
  have countWord (letter : ℕ) : word.count letter =
      upper.count letter + lower.count letter + if letter = pivot then 2 else 0 := by
    have splitLower : initial ++ ending = lower := List.take_append_drop cut lower
    have countSplit := congrArg (List.count letter) splitLower
    simp only [List.count_append] at countSplit
    change (lower.take cut).count letter + (lower.drop cut).count letter =
      lower.count letter at countSplit
    simp only [word, typeIWord, List.count_append, List.count_singleton]
    by_cases equal : letter = pivot
    · subst letter
      simp
      omega
    · simp [equal, Ne.symm equal]
      omega
  have doubleWord : ∀ letter ∈ word, word.count letter = 2 := by
    intro letter member
    rw [countWord]
    rcases (members letter).mp member with high | low | equal
    · have highValue := upperValues letter high
      have absentLow : letter ∉ lower := by
        intro low
        have lowValue := lowerValues letter low
        omega
      simp [upperDouble letter high, List.count_eq_zero.mpr absentLow,
        show letter ≠ pivot by omega]
    · have lowValue := lowerValues letter low
      have absentHigh : letter ∉ upper := by
        intro high
        have highValue := upperValues letter high
        omega
      simp [lowerDouble letter low, List.count_eq_zero.mpr absentHigh,
        show letter ≠ pivot by omega]
    · subst letter
      simp [List.count_eq_zero.mpr pivotUpper, List.count_eq_zero.mpr pivotLower]
  have wordEq : word = upper ++ initial ++ [pivot] ++ ending ++ [pivot] := rfl
  have initialMember (letter : ℕ) (member : letter ∈ lower) : letter ∈ initial := by
    exact (List.mem_take_iff_idxOf_lt member).mpr (terminal letter member)
  have firstUpper (letter : ℕ) (member : letter ∈ upper) :
      word.idxOf letter = upper.idxOf letter := by
    simp [wordEq, List.idxOf_append, member, List.append_assoc]
  have firstLower (letter : ℕ) (member : letter ∈ lower) :
      word.idxOf letter = upper.length + lower.idxOf letter := by
    have low := lowerValues letter member
    have absent : letter ∉ upper := by
      intro high
      have highValue := upperValues letter high
      omega
    have initialEq : initial.idxOf letter = lower.idxOf letter :=
      (List.take_prefix cut lower).idxOf_eq_of_mem (initialMember letter member)
    simp [wordEq, List.append_assoc, List.idxOf_append, absent,
      initialMember letter member, initialEq, Nat.add_comm]
  have firstPivot : word.idxOf pivot = upper.length + initial.length := by
    simp [wordEq, List.append_assoc, List.idxOf_append, pivotUpper, pivotInitial,
      Nat.add_comm]
  have readUpper (index letter : ℕ) (bound : index < upper.length)
      (value : word[index]? = some letter) : upper[index]? = some letter := by
    simpa [wordEq, List.append_assoc, List.getElem?_append, bound] using value
  have readInitial (index letter : ℕ) (above : upper.length ≤ index)
      (below : index < upper.length + initial.length)
      (value : word[index]? = some letter) :
      lower[index - upper.length]? = some letter := by
    have localBound : index - upper.length < initial.length := by omega
    have getInitial : initial[index - upper.length]? = some letter := by
      simpa [wordEq, List.append_assoc, List.getElem?_append,
        Nat.not_lt.mpr above, localBound] using value
    have beforeCut : index - upper.length < cut := by
      have lengthBound := List.length_take_le cut lower
      change index - upper.length < (lower.take cut).length at localBound
      omega
    simpa [initial, beforeCut] using getInitial
  intro occurrence
  obtain ⟨smaller, larger, repeated, first, second, smallLt, repeatLt,
    firstLt, secondLt, getFirst, getSecond, repeatedMem⟩ :=
      (prefixCriterion word doubleWord).mp occurrence
  rcases lt_trichotomy repeated pivot with repeatedLow | repeatedEq | repeatedHigh
  · have lowerMem : repeated ∈ lower := by
      rcases (members repeated).mp repeatedMem with high | low | equal
      · have highValue := upperValues repeated high
        omega
      · exact low
      · omega
    have repeatedBound : lower.idxOf repeated < initial.length :=
      List.idxOf_lt_length_of_mem (initialMember repeated lowerMem) |>
        (fun bound => by
          have equal := (List.take_prefix cut lower).idxOf_eq_of_mem
            (initialMember repeated lowerMem)
          simpa [← equal] using bound)
    rw [firstLower repeated lowerMem] at secondLt
    have firstNotUpper : upper.length ≤ first := by
      by_contra before
      have firstHigh := readUpper first smaller (by omega) getFirst
      have highValue := upperValues smaller (List.mem_of_getElem? firstHigh)
      omega
    have secondNotUpper : upper.length ≤ second := by omega
    have getFirstLower := readInitial first smaller firstNotUpper (by omega) getFirst
    have getSecondLower := readInitial second larger secondNotUpper (by omega) getSecond
    apply lowerAvoids
    exact (prefixCriterion lower lowerDouble).mpr
      ⟨smaller, larger, repeated, first - upper.length, second - upper.length,
        smallLt, repeatLt, by omega, by omega, getFirstLower, getSecondLower, lowerMem⟩
  · subst repeated
    rw [firstPivot] at secondLt
    have firstNotUpper : upper.length ≤ first := by
      by_contra before
      have firstHigh := readUpper first smaller (by omega) getFirst
      have highValue := upperValues smaller (List.mem_of_getElem? firstHigh)
      omega
    have secondNotUpper : upper.length ≤ second := by omega
    have getSecondLower := readInitial second larger secondNotUpper secondLt getSecond
    have lowValue := lowerValues larger (List.mem_of_getElem? getSecondLower)
    omega
  · have upperMem : repeated ∈ upper := by
      rcases (members repeated).mp repeatedMem with high | low | equal
      · exact high
      · have lowValue := lowerValues repeated low
        omega
      · omega
    rw [firstUpper repeated upperMem] at secondLt
    have repeatedBound := List.idxOf_lt_length_of_mem upperMem
    have getFirstUpper := readUpper first smaller (by omega) getFirst
    have getSecondUpper := readUpper second larger (by omega) getSecond
    apply upperAvoids
    exact (prefixCriterion upper upperDouble).mpr
      ⟨smaller, larger, repeated, first, second, smallLt, repeatLt, firstLt,
        secondLt, getFirstUpper, getSecondUpper, upperMem⟩

end D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeI

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeI.typeI_avoids
