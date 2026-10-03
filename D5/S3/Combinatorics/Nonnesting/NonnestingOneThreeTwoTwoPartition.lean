/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoPartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoPartition
   mirror-E: none(waiver:pivot-prefix-value-separation)
   anchors: []
   utility: none
   digest: Before any first opening, all higher letters precede all lower letters. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeI

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoPartition

theorem prefix_partition (word : List ℕ) (pivot : ℕ) (pivotMember : pivot ∈ word)
    (double : ∀ letter ∈ word, word.count letter = 2)
    (avoiding : ¬ NonnestingDefs.Occurs [1, 3, 2, 2] word) :
    word.take (word.idxOf pivot) =
      (word.take (word.idxOf pivot)).filter (fun letter => decide (pivot < letter)) ++
      (word.take (word.idxOf pivot)).filter (fun letter => decide (letter < pivot)) := by
  have prefixCriterion (w : List ℕ) (hcount : ∀ letter ∈ w, w.count letter = 2) :
      (∃ smaller larger repeated first second : ℕ,
          smaller < repeated ∧ repeated < larger ∧
          first < second ∧ second < w.idxOf repeated ∧
          w[first]? = some smaller ∧ w[second]? = some larger ∧ repeated ∈ w) →
        NonnestingDefs.Occurs [1, 3, 2, 2] w := by
    rintro ⟨smaller, larger, repeated, first, second, lower, upper,
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
  let before := word.take (word.idxOf pivot)
  have pivotAbsent : pivot ∉ before := by
    intro member
    have impossible := (List.mem_take_iff_idxOf_lt pivotMember).mp member
    omega
  have separated : ∀ first second smaller larger : ℕ,
      before[first]? = some smaller → before[second]? = some larger →
      smaller < pivot → pivot < larger → second < first := by
    intro first second smaller larger getFirst getSecond smallLt largeLt
    have firstBound := (List.getElem?_eq_some_iff.mp getFirst).1
    have secondBound := (List.getElem?_eq_some_iff.mp getSecond).1
    have lengthBefore : before.length = word.idxOf pivot := by
      simp [before, Nat.min_eq_left (List.idxOf_le_length (l := word) (a := pivot))]
    have firstBefore : first < word.idxOf pivot := by omega
    have secondBefore : second < word.idxOf pivot := by omega
    have firstValue : word[first]? = some smaller := by
      simpa [before, firstBefore] using getFirst
    have secondValue : word[second]? = some larger := by
      simpa [before, secondBefore] using getSecond
    by_contra notBefore
    have different : first ≠ second := by
      intro equal
      rw [equal, getSecond] at getFirst
      have equalLetters := Option.some.inj getFirst
      omega
    have firstLt : first < second := by omega
    apply avoiding
    exact prefixCriterion word double
      ⟨smaller, larger, pivot, first, second, smallLt, largeLt, firstLt,
        secondBefore, firstValue, secondValue, pivotMember⟩
  have partition : ∀ sequence : List ℕ, pivot ∉ sequence →
      (∀ first second smaller larger : ℕ,
        sequence[first]? = some smaller → sequence[second]? = some larger →
        smaller < pivot → pivot < larger → second < first) →
      sequence = sequence.filter (fun letter => decide (pivot < letter)) ++
        sequence.filter (fun letter => decide (letter < pivot)) := by
    intro sequence
    induction sequence with
    | nil => simp
    | cons head tail inductionHyp =>
      intro absent ordered
      have absentParts : pivot ≠ head ∧ pivot ∉ tail := by simpa using absent
      by_cases headHigh : pivot < head
      · have tailOrdered : ∀ first second smaller larger : ℕ,
            tail[first]? = some smaller → tail[second]? = some larger →
            smaller < pivot → pivot < larger → second < first := by
          intro first second smaller larger getFirst getSecond smallLt largeLt
          have before := ordered (first + 1) (second + 1) smaller larger
            (by simpa using getFirst) (by simpa using getSecond) smallLt largeLt
          omega
        have tailEq := inductionHyp absentParts.2 tailOrdered
        simp [headHigh, Nat.not_lt_of_ge (Nat.le_of_lt headHigh), ← tailEq]
      · have headLow : head < pivot := by omega
        have tailLow : ∀ letter ∈ tail, letter < pivot := by
          intro letter member
          by_contra notLow
          have different : letter ≠ pivot := fun equal => absentParts.2 (equal ▸ member)
          have high : pivot < letter := by omega
          have impossible := ordered 0 (tail.idxOf letter + 1) head letter (by simp)
            (by simpa using List.getElem?_idxOf member) headLow high
          omega
        have upperEmpty : tail.filter (fun letter => decide (pivot < letter)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter member
          simp [Nat.not_lt.mpr (Nat.le_of_lt (tailLow letter member))]
        have lowerAll : tail.filter (fun letter => decide (letter < pivot)) = tail := by
          apply List.filter_eq_self.mpr
          intro letter member
          simp [tailLow letter member]
        simp [headLow, headHigh, upperEmpty, lowerAll]
  exact partition before pivotAbsent separated

end D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoPartition

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoPartition.prefix_partition
