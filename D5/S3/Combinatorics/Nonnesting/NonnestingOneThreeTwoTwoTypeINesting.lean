/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeINesting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeINesting
   mirror-E: none(waiver:terminal-pivot-nonnesting)
   anchors: []
   utility: none
   digest: Terminal pivot insertion preserves nonnesting in both separated blocks. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoPartition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeINesting

open D5.S3.Combinatorics NonnestingOneThreeTwoTwoTypeI

theorem typeI_nonnesting (upper lower : List ℕ) (pivot cut : ℕ)
    (upperValues : ∀ letter ∈ upper, pivot < letter)
    (lowerValues : ∀ letter ∈ lower, letter < pivot)
    (lowerDouble : ∀ letter ∈ lower, lower.count letter = 2)
    (upperNesting : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] upper ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2] upper)
    (lowerNesting : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] lower ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2] lower)
    (terminal : ∀ letter ∈ lower, lower.idxOf letter < cut) :
    ¬ NonnestingDefs.Occurs [1, 2, 2, 1] (typeIWord upper lower pivot cut) ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2] (typeIWord upper lower pivot cut) := by
  have raw (sequence : List ℕ) :
      (¬ NonnestingDefs.Occurs [1, 2, 2, 1] sequence ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] sequence) ↔
      ∀ outer inner : ℕ, outer ≠ inner →
        ¬ [outer, inner, inner, outer].Sublist sequence := by
    constructor
    · rintro ⟨noAscending, noDescending⟩ outer inner different sub
      rcases lt_or_gt_of_ne different with ascending | descending
      · apply noAscending
        refine ⟨(fun index => if index = 1 then outer else inner), ?_, ?_, ?_, by simp⟩
        · intro index positive below
          have equal : index = 1 := by
            simp [NonnestingDefs.letters] at below
            omega
          simp [equal, ascending]
        · intro index positive below
          have cases : index = 1 ∨ index = 2 := by
            simp [NonnestingDefs.letters] at below
            omega
          rcases cases with rfl | rfl <;> simp
          · exact sub.subset (by simp)
          · exact sub.subset (by simp)
        · simpa using sub
      · apply noDescending
        refine ⟨(fun index => if index = 1 then inner else outer), ?_, ?_, ?_, by simp⟩
        · intro index positive below
          have equal : index = 1 := by
            simp [NonnestingDefs.letters] at below
            omega
          simp [equal, descending]
        · intro index positive below
          have cases : index = 1 ∨ index = 2 := by
            simp [NonnestingDefs.letters] at below
            omega
          rcases cases with rfl | rfl <;> simp
          · exact sub.subset (by simp)
          · exact sub.subset (by simp)
        · simpa using sub
    · intro noPairs
      constructor
      · rintro ⟨labels, increasing, _, sub, _⟩
        have ordered : labels 1 < labels 2 :=
          increasing 1 (by omega) (by simp [NonnestingDefs.letters])
        exact noPairs (labels 1) (labels 2) (by omega) (by simpa using sub)
      · rintro ⟨labels, increasing, _, sub, _⟩
        have ordered : labels 1 < labels 2 :=
          increasing 1 (by omega) (by simp [NonnestingDefs.letters])
        exact noPairs (labels 2) (labels 1) (by omega) (by simpa using sub)
  let initial := lower.take cut
  let ending := lower.drop cut
  let word := typeIWord upper lower pivot cut
  let start := upper.length + initial.length
  let finish := start + 1 + ending.length
  have wordEq : word = upper ++ initial ++ [pivot] ++ ending ++ [pivot] := rfl
  have wordLength : word.length = finish + 1 := by
    simp [wordEq, finish, start]
    omega
  have initialValues : ∀ letter ∈ initial, letter < pivot := by
    intro letter member
    exact lowerValues letter (List.mem_of_mem_take member)
  have endingValues : ∀ letter ∈ ending, letter < pivot := by
    intro letter member
    exact lowerValues letter (List.mem_of_mem_drop member)
  have location (index letter : ℕ) (value : word[index]? = some letter) :
      (pivot < letter → index < upper.length) ∧
      (letter < pivot → upper.length ≤ index) ∧
      (letter = pivot → index = start ∨ index = finish) := by
    have bounded := (List.getElem?_eq_some_iff.mp value).1
    rw [wordLength] at bounded
    by_cases inUpper : index < upper.length
    · have getUpper : upper[index]? = some letter := by
        simpa [wordEq, List.append_assoc, List.getElem?_append, inUpper] using value
      have high := upperValues letter (List.mem_of_getElem? getUpper)
      exact ⟨fun _ => inUpper, by omega, by omega⟩
    · by_cases inInitial : index < start
      · have initialBound : index - upper.length < initial.length := by omega
        have getInitial : initial[index - upper.length]? = some letter := by
          simpa [wordEq, List.append_assoc, List.getElem?_append, inUpper, initialBound]
            using value
        have low := initialValues letter (List.mem_of_getElem? getInitial)
        exact ⟨by omega, fun _ => by omega, by omega⟩
      · by_cases atStart : index = start
        · exact ⟨by
            have atPivot : letter = pivot := by
              have offset : index - upper.length - initial.length = 0 := by omega
              simpa [wordEq, List.getElem?_append, List.append_assoc, inUpper,
                show ¬ index - upper.length < initial.length by omega, offset] using value.symm
            omega, fun _ => by omega, fun _ => Or.inl atStart⟩
        · by_cases inEnding : index < finish
          · have endingBound : index - start - 1 < ending.length := by omega
            have getEnding : ending[index - start - 1]? = some letter := by
              have offset : index - upper.length - initial.length =
                  (index - start - 1) + 1 := by omega
              simpa [wordEq, List.append_assoc, List.getElem?_append, inUpper,
                show ¬ index - upper.length < initial.length by omega,
                offset, endingBound] using value
            have low := endingValues letter (List.mem_of_getElem? getEnding)
            exact ⟨by omega, fun _ => by omega, by omega⟩
          · have atFinish : index = finish := by omega
            have atPivot : letter = pivot := by
              have offset : index - upper.length - initial.length = ending.length + 1 := by
                omega
              simpa [wordEq, List.getElem?_append, List.append_assoc, inUpper,
                show ¬ index - upper.length < initial.length by omega, offset] using value.symm
            exact ⟨by omega, fun _ => by omega, fun _ => Or.inr atFinish⟩
  have filterUpper : word.filter (fun letter => decide (pivot < letter)) = upper := by
    have upperAll : upper.filter (fun letter => decide (pivot < letter)) = upper := by
      apply List.filter_eq_self.mpr
      intro letter member
      simp [upperValues letter member]
    have initialEmpty : initial.filter (fun letter => decide (pivot < letter)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro letter member
      simp [Nat.not_lt.mpr (Nat.le_of_lt (initialValues letter member))]
    have endingEmpty : ending.filter (fun letter => decide (pivot < letter)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro letter member
      simp [Nat.not_lt.mpr (Nat.le_of_lt (endingValues letter member))]
    simp [wordEq, List.filter_append, upperAll, initialEmpty, endingEmpty]
  have filterLower : word.filter (fun letter => decide (letter < pivot)) = lower := by
    have upperEmpty : upper.filter (fun letter => decide (letter < pivot)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro letter member
      simp [Nat.not_lt.mpr (Nat.le_of_lt (upperValues letter member))]
    have initialAll : initial.filter (fun letter => decide (letter < pivot)) = initial := by
      apply List.filter_eq_self.mpr
      intro letter member
      simp [initialValues letter member]
    have endingAll : ending.filter (fun letter => decide (letter < pivot)) = ending := by
      apply List.filter_eq_self.mpr
      intro letter member
      simp [endingValues letter member]
    simp [wordEq, List.filter_append, upperEmpty, initialAll, endingAll,
      initial, ending, List.take_append_drop]
  apply (raw word).mpr
  intro outer inner different sub
  obtain ⟨embedding, values⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp sub
  have getValue (index : Fin 4) : word[(embedding index).val]? =
      [outer, inner, inner, outer][index.val]? := by
    rw [List.getElem?_eq_getElem (embedding index).isLt,
      List.getElem?_eq_getElem index.isLt]
    exact congrArg some (values index).symm
  have outerFirst : word[(embedding 0).val]? = some outer := by simpa using getValue 0
  have innerFirst : word[(embedding 1).val]? = some inner := by simpa using getValue 1
  have innerLast : word[(embedding 2).val]? = some inner := by simpa using getValue 2
  have outerLast : word[(embedding 3).val]? = some outer := by simpa using getValue 3
  have orderedOne := embedding.strictMono (by change (0 : Fin 4) < 1; decide)
  have orderedTwo := embedding.strictMono (by change (1 : Fin 4) < 2; decide)
  have orderedThree := embedding.strictMono (by change (2 : Fin 4) < 3; decide)
  rcases lt_trichotomy outer pivot with outerLow | outerEqual | outerHigh
  · have innerLow : inner < pivot := by
      have firstBound := (location _ _ outerFirst).2.1 outerLow
      by_contra notLow
      rcases lt_or_eq_of_le (Nat.le_of_not_gt notLow) with innerHigh | innerEqual
      · have secondBound := (location _ _ innerFirst).1 innerHigh
        omega
      · have secondPosition := (location _ _ innerFirst).2.2 innerEqual.symm
        have thirdPosition := (location _ _ innerLast).2.2 innerEqual.symm
        have fourthBound := (embedding 3).isLt
        have fourthBound' : (embedding 3).val < finish + 1 := by
          simpa only [wordLength] using fourthBound
        rcases secondPosition with secondPosition | secondPosition <;>
          rcases thirdPosition with thirdPosition | thirdPosition <;> omega
    have lowerSub := sub.filter (fun letter => decide (letter < pivot))
    rw [filterLower] at lowerSub
    have preserved : [outer, inner, inner, outer].Sublist lower := by
      simpa [outerLow, innerLow] using lowerSub
    exact (raw lower).mp lowerNesting outer inner different preserved
  · subst outer
    have firstPosition := (location _ _ outerFirst).2.2 rfl
    have fourthPosition := (location _ _ outerLast).2.2 rfl
    have firstAtStart : (embedding 0).val = start := by
      rcases firstPosition with atStart | atFinish
      · exact atStart
      · rcases fourthPosition with fourthPosition | fourthPosition <;> omega
    have fourthAtFinish : (embedding 3).val = finish := by
      rcases fourthPosition with atStart | atFinish
      · omega
      · exact atFinish
    have readEnding (index : ℕ) (above : start < index) (below : index < finish)
        (value : word[index]? = some inner) :
        ending[index - start - 1]? = some inner := by
      have upperBound : ¬ index < upper.length := by omega
      have initialBound : ¬ index - upper.length < initial.length := by omega
      have offset : index - upper.length - initial.length = (index - start - 1) + 1 := by
        omega
      have endingBound : index - start - 1 < ending.length := by omega
      simpa [wordEq, List.append_assoc, List.getElem?_append, upperBound,
        initialBound, offset, endingBound] using value
    have firstEnding := readEnding (embedding 1).val (by omega) (by omega) innerFirst
    have secondEnding := readEnding (embedding 2).val (by omega) (by omega) innerLast
    have pair : [inner, inner].Sublist ending := by
      let indices : Fin 2 → ℕ := fun index =>
        if index = 0 then (embedding 1).val - start - 1 else (embedding 2).val - start - 1
      have bounded : ∀ index : Fin 2, indices index < ending.length := by
        intro index
        fin_cases index
        · exact (List.getElem?_eq_some_iff.mp firstEnding).1
        · exact (List.getElem?_eq_some_iff.mp secondEnding).1
      let selected : Fin 2 ↪o Fin ending.length :=
        OrderEmbedding.ofMapLEIff (fun index => ⟨indices index, bounded index⟩) (by
          intro left right
          fin_cases left <;> fin_cases right <;> simp [indices] <;> omega)
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      refine ⟨selected, ?_⟩
      intro index
      fin_cases index
      · exact (List.getElem?_eq_some_iff.mp firstEnding).2.symm
      · exact (List.getElem?_eq_some_iff.mp secondEnding).2.symm
    have innerMember : inner ∈ lower :=
      List.mem_of_mem_drop (List.mem_of_getElem? firstEnding)
    have initialMember : inner ∈ initial :=
      (List.mem_take_iff_idxOf_lt innerMember).mpr (terminal inner innerMember)
    have initialPositive := List.count_pos_iff.mpr initialMember
    have splitCount : initial.count inner + ending.count inner = 2 := by
      rw [← List.count_append, List.take_append_drop]
      exact lowerDouble inner innerMember
    have pairCount := pair.count_le inner
    simp only [List.count_cons_self, List.count_nil] at pairCount
    omega
  · have fourthBound := (location _ _ outerLast).1 outerHigh
    have secondBound : (embedding 1).val < upper.length := by omega
    have secondValue : upper[(embedding 1).val]? = some inner := by
      simpa [wordEq, List.append_assoc, List.getElem?_append, secondBound] using innerFirst
    have innerHigh := upperValues inner (List.mem_of_getElem? secondValue)
    have upperSub := sub.filter (fun letter => decide (pivot < letter))
    rw [filterUpper] at upperSub
    have preserved : [outer, inner, inner, outer].Sublist upper := by
      simpa [outerHigh, innerHigh] using upperSub
    exact (raw upper).mp upperNesting outer inner different preserved

end D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeINesting

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeINesting.typeI_nonnesting
