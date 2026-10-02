/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeII
   mirror-E: none(waiver:mountain-block-interleaving)
   anchors: []
   utility: none
   digest: Interleaving a mountain block across a terminal upper cut preserves 1322 avoidance. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeII

def typeIIWord (upper order : List ℕ) (pivot cut : ℕ) : List ℕ :=
  upper.take cut ++ order ++ [pivot] ++ upper.drop cut ++ order ++ [pivot]

theorem typeII_avoids (upper order : List ℕ) (pivot cut : ℕ)
    (upperValues : ∀ letter ∈ upper, pivot < letter)
    (lowerValues : ∀ letter ∈ order, letter < pivot)
    (upperDouble : ∀ letter ∈ upper, upper.count letter = 2)
    (distinct : order.Nodup)
    (upperAvoids : ¬ NonnestingDefs.Occurs [1, 3, 2, 2] upper)
    (lowerAvoids : ¬ NonnestingDefs.Occurs [1, 3, 2, 2] (order ++ order))
    (terminal : ∀ letter ∈ upper, upper.idxOf letter < cut) :
    ¬ NonnestingDefs.Occurs [1, 3, 2, 2] (typeIIWord upper order pivot cut) := by
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
  let initial := upper.take cut
  let ending := upper.drop cut
  let word := typeIIWord upper order pivot cut
  have wordEq : word = initial ++ order ++ [pivot] ++ ending ++ order ++ [pivot] := rfl
  have initialValues : ∀ letter ∈ initial, pivot < letter := by
    intro letter member
    exact upperValues letter (List.mem_of_mem_take member)
  have pivotUpper : pivot ∉ upper := by
    intro member
    have value := upperValues pivot member
    omega
  have pivotInitial : pivot ∉ initial := fun member =>
    pivotUpper (List.mem_of_mem_take member)
  have pivotOrder : pivot ∉ order := by
    intro member
    have value := lowerValues pivot member
    omega
  have lowerNotUpper (letter : ℕ) (member : letter ∈ order) : letter ∉ upper := by
    intro upperMember
    have lower := lowerValues letter member
    have higher := upperValues letter upperMember
    omega
  have upperNotOrder (letter : ℕ) (member : letter ∈ upper) : letter ∉ order := by
    intro lowerMember
    exact lowerNotUpper letter lowerMember member
  have initialMember (letter : ℕ) (member : letter ∈ upper) : letter ∈ initial :=
    (List.mem_take_iff_idxOf_lt member).mpr (terminal letter member)
  have members (letter : ℕ) : letter ∈ word ↔
      letter ∈ upper ∨ letter ∈ order ∨ letter = pivot := by
    have splitUpper : initial ++ ending = upper := List.take_append_drop cut upper
    simp only [wordEq, List.mem_append, List.mem_singleton]
    constructor
    · rintro (((((member | member) | equal) | member) | member) | equal)
      · exact Or.inl (List.mem_of_mem_take member)
      · exact Or.inr (Or.inl member)
      · exact Or.inr (Or.inr equal)
      · exact Or.inl (List.mem_of_mem_drop member)
      · exact Or.inr (Or.inl member)
      · exact Or.inr (Or.inr equal)
    · rintro (member | member | equal)
      · rcases List.mem_append.mp (splitUpper.symm ▸ member) with before | after
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl before))))
        · exact Or.inl (Or.inl (Or.inr after))
      · exact Or.inl (Or.inr member)
      · exact Or.inr equal
  have countFormula (letter : ℕ) : word.count letter =
      upper.count letter + 2 * order.count letter + if letter = pivot then 2 else 0 := by
    have splitCount : initial.count letter + ending.count letter = upper.count letter := by
      rw [← List.count_append, List.take_append_drop]
    simp only [wordEq, List.count_append, List.count_singleton]
    by_cases equal : letter = pivot
    · subst letter
      simp only [beq_self_eq_true, if_true]
      omega
    · simp only [beq_eq_false_iff_ne.mpr (Ne.symm equal), if_false,
        Bool.false_eq_true, equal, add_zero]
      omega
  have doubleWord : ∀ letter ∈ word, word.count letter = 2 := by
    intro letter member
    rw [countFormula]
    rcases (members letter).mp member with upperMember | lowerMember | equal
    · have absent := upperNotOrder letter upperMember
      have different : letter ≠ pivot := by
        have value := upperValues letter upperMember
        omega
      simp [upperDouble letter upperMember, List.count_eq_zero.mpr absent, different]
    · have absent := lowerNotUpper letter lowerMember
      have different : letter ≠ pivot := by
        have value := lowerValues letter lowerMember
        omega
      simp [List.count_eq_zero.mpr absent,
        List.count_eq_one_of_mem distinct lowerMember, different]
    · subst letter
      simp [List.count_eq_zero.mpr pivotUpper, List.count_eq_zero.mpr pivotOrder]
  have lowerDouble : ∀ letter ∈ order ++ order, (order ++ order).count letter = 2 := by
    intro letter member
    have lowerMember : letter ∈ order := by simpa using member
    simp [List.count_eq_one_of_mem distinct lowerMember]
  have firstUpper (letter : ℕ) (member : letter ∈ upper) :
      word.idxOf letter = upper.idxOf letter := by
    have same : initial.idxOf letter = upper.idxOf letter :=
      (List.take_prefix cut upper).idxOf_eq_of_mem (initialMember letter member)
    simp [wordEq, List.append_assoc, List.idxOf_append, initialMember letter member, same]
  have firstLower (letter : ℕ) (member : letter ∈ order) :
      word.idxOf letter = initial.length + order.idxOf letter := by
    have absent : letter ∉ initial := fun memberInitial =>
      lowerNotUpper letter member (List.mem_of_mem_take memberInitial)
    simp [wordEq, List.append_assoc, List.idxOf_append, absent, member, Nat.add_comm]
  have firstPivot : word.idxOf pivot = initial.length + order.length := by
    simp [wordEq, List.append_assoc, List.idxOf_append, pivotInitial, pivotOrder, Nat.add_comm]
  have readUpper (index letter : ℕ) (bound : index < initial.length)
      (value : word[index]? = some letter) : upper[index]? = some letter := by
    have initialValue : initial[index]? = some letter := by
      simpa [wordEq, List.append_assoc, List.getElem?_append, bound] using value
    have beforeCut : index < cut := by
      have bounded := List.length_take_le cut upper
      change index < (upper.take cut).length at bound
      omega
    simpa [initial, beforeCut] using initialValue
  have readLower (index letter : ℕ) (above : initial.length ≤ index)
      (below : index < initial.length + order.length)
      (value : word[index]? = some letter) : order[index - initial.length]? = some letter := by
    have bounded : index - initial.length < order.length := by omega
    simpa [wordEq, List.append_assoc, List.getElem?_append, Nat.not_lt.mpr above, bounded]
      using value
  intro occurrence
  obtain ⟨smaller, larger, repeated, first, second, smallLt, repeatLt,
    firstLt, secondLt, getFirst, getSecond, repeatedMember⟩ :=
      (prefixCriterion word doubleWord).mp occurrence
  rcases lt_trichotomy repeated pivot with repeatedLow | repeatedEq | repeatedHigh
  · have lowerMember : repeated ∈ order := by
      rcases (members repeated).mp repeatedMember with upperMember | lowerMember | equal
      · have value := upperValues repeated upperMember
        omega
      · exact lowerMember
      · omega
    rw [firstLower repeated lowerMember] at secondLt
    have bound := List.idxOf_lt_length_of_mem lowerMember
    have firstOutside : initial.length ≤ first := by
      by_contra inside
      have value := readUpper first smaller (by omega) getFirst
      have high := upperValues smaller (List.mem_of_getElem? value)
      omega
    have getFirstLow := readLower first smaller firstOutside (by omega) getFirst
    have getSecondLow := readLower second larger (by omega) (by omega) getSecond
    have readMountain (index letter : ℕ) (bounded : index < order.length)
        (value : order[index]? = some letter) : (order ++ order)[index]? = some letter := by
      simpa [List.getElem?_append, bounded] using value
    have mountainFirst : (order ++ order).idxOf repeated = order.idxOf repeated := by
      simp [List.idxOf_append, lowerMember]
    apply lowerAvoids
    apply (prefixCriterion (order ++ order) lowerDouble).mpr
    refine ⟨smaller, larger, repeated, first - initial.length, second - initial.length,
      smallLt, repeatLt, by omega, ?_, ?_, ?_, List.mem_append_left order lowerMember⟩
    · rw [mountainFirst]
      omega
    · exact readMountain _ _ (by omega) getFirstLow
    · exact readMountain _ _ (by omega) getSecondLow
  · subst repeated
    rw [firstPivot] at secondLt
    have firstOutside : initial.length ≤ first := by
      by_contra inside
      have value := readUpper first smaller (by omega) getFirst
      have high := upperValues smaller (List.mem_of_getElem? value)
      omega
    have value := readLower second larger (by omega) secondLt getSecond
    have low := lowerValues larger (List.mem_of_getElem? value)
    omega
  · have upperMember : repeated ∈ upper := by
      rcases (members repeated).mp repeatedMember with upperMember | lowerMember | equal
      · exact upperMember
      · have value := lowerValues repeated lowerMember
        omega
      · omega
    have bound := List.idxOf_lt_length_of_mem (initialMember repeated upperMember)
    have same : initial.idxOf repeated = upper.idxOf repeated :=
      (List.take_prefix cut upper).idxOf_eq_of_mem (initialMember repeated upperMember)
    rw [firstUpper repeated upperMember] at secondLt
    have getFirstHigh := readUpper first smaller (by omega) getFirst
    have getSecondHigh := readUpper second larger (by omega) getSecond
    apply upperAvoids
    exact (prefixCriterion upper upperDouble).mpr
      ⟨smaller, larger, repeated, first, second, smallLt, repeatLt, firstLt, secondLt,
        getFirstHigh, getSecondHigh, upperMember⟩

#print axioms typeII_avoids

end D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeII
