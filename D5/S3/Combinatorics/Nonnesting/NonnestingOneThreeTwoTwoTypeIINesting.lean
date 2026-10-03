/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeIINesting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTypeIINesting
   mirror-E: none(waiver:nonnesting-mountain-interleaving)
   anchors: []
   utility: none
   digest: Terminal upper suffixes and mountain orders cannot create a nested occurrence pair. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeII

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeIINesting

open NonnestingOneThreeTwoTwoTypeII

theorem typeII_nonnesting (upper order : List ℕ) (pivot cut : ℕ)
    (upperValues : ∀ letter ∈ upper, pivot < letter)
    (lowerValues : ∀ letter ∈ order, letter < pivot)
    (upperDouble : ∀ letter ∈ upper, upper.count letter = 2)
    (distinct : order.Nodup)
    (upperNesting : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] upper ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2] upper)
    (lowerNesting : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] (order ++ order) ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2] (order ++ order))
    (terminal : ∀ letter ∈ upper, upper.idxOf letter < cut) :
    ¬ NonnestingDefs.Occurs [1, 2, 2, 1] (typeIIWord upper order pivot cut) ∧
      ¬ NonnestingDefs.Occurs [2, 1, 1, 2] (typeIIWord upper order pivot cut) := by
  let initial := upper.take cut
  let ending := upper.drop cut
  let word := typeIIWord upper order pivot cut
  have splitUpper : initial ++ ending = upper := List.take_append_drop cut upper
  have wordEq : word = initial ++ order ++ [pivot] ++ ending ++ order ++ [pivot] := rfl
  have initialValues : ∀ letter ∈ initial, pivot < letter := by
    intro letter member
    exact upperValues letter (List.mem_of_mem_take member)
  have endingValues : ∀ letter ∈ ending, pivot < letter := by
    intro letter member
    exact upperValues letter (List.mem_of_mem_drop member)
  have pivotInitial : pivot ∉ initial := by
    intro member
    have value := initialValues pivot member
    omega
  have pivotEnding : pivot ∉ ending := by
    intro member
    have value := endingValues pivot member
    omega
  have pivotOrder : pivot ∉ order := by
    intro member
    have value := lowerValues pivot member
    omega
  have endingDistinct : ending.Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro letter
    by_cases member : letter ∈ ending
    · have upperMember := List.mem_of_mem_drop member
      have initialMember : letter ∈ initial :=
        (List.mem_take_iff_idxOf_lt upperMember).mpr (terminal letter upperMember)
      have positive := List.count_pos_iff.mpr initialMember
      have total : initial.count letter + ending.count letter = 2 := by
        rw [← List.count_append, splitUpper]
        exact upperDouble letter upperMember
      omega
    · simp [List.count_eq_zero.mpr member]
  have joinedDistinct : (ending ++ order).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨endingDistinct, distinct, ?_⟩
    intro left leftMember right rightMember equal
    have high := endingValues left leftMember
    have low := lowerValues right rightMember
    omega
  have skipPrefix : ∀ (prefixList suffixList rest : List ℕ) (head : ℕ),
      head ∉ prefixList → (head :: rest).Sublist (prefixList ++ suffixList) →
        (head :: rest).Sublist suffixList := by
    intro prefixList
    induction prefixList with
    | nil => simp
    | cons letter prefixList inductionHyp =>
      intro suffixList rest head absent sub
      cases sub with
      | cons _ sub =>
        exact inductionHyp suffixList rest head (fun member => absent (by simp [member])) sub
      | cons_cons _ sub => exact (absent (by simp)).elim
  have trimSuffix (left right : List ℕ) (outer inner : ℕ) (absent : outer ∉ right)
      (sub : [outer, inner, inner, outer].Sublist (left ++ right)) :
      [outer, inner, inner, outer].Sublist left := by
    have reversed : [outer, inner, inner, outer].Sublist (right.reverse ++ left.reverse) := by
      simpa [List.reverse_append] using sub.reverse
    have shortened := skipPrefix right.reverse left.reverse [inner, inner, outer] outer
      (by simpa using absent) reversed
    simpa using shortened.reverse
  have inputNoPairs (sequence : List ℕ)
      (nonnesting : ¬ NonnestingDefs.Occurs [1, 2, 2, 1] sequence ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] sequence)
      (outer inner : ℕ) (different : outer ≠ inner)
      (sub : [outer, inner, inner, outer].Sublist sequence) : False := by
    rcases lt_or_gt_of_ne different with increasing | decreasing
    · apply nonnesting.1
      refine ⟨(fun index => if index = 1 then outer else inner), ?_, ?_, ?_, by simp⟩
      · intro index positive below
        have equal : index = 1 := by
          simp [NonnestingDefs.letters] at below
          omega
        simp [equal, increasing]
      · intro index positive below
        have cases : index = 1 ∨ index = 2 := by
          simp [NonnestingDefs.letters] at below
          omega
        rcases cases with rfl | rfl
        · change outer ∈ sequence
          exact sub.subset (by simp)
        · change inner ∈ sequence
          exact sub.subset (by simp)
      · simpa using sub
    · apply nonnesting.2
      refine ⟨(fun index => if index = 1 then inner else outer), ?_, ?_, ?_, by simp⟩
      · intro index positive below
        have equal : index = 1 := by
          simp [NonnestingDefs.letters] at below
          omega
        simp [equal, decreasing]
      · intro index positive below
        have cases : index = 1 ∨ index = 2 := by
          simp [NonnestingDefs.letters] at below
          omega
        rcases cases with rfl | rfl
        · change inner ∈ sequence
          exact sub.subset (by simp)
        · change outer ∈ sequence
          exact sub.subset (by simp)
      · simpa using sub
  have upperFilter : word.filter (fun letter => decide (pivot < letter)) = upper := by
    have initialKeep : initial.filter (fun letter => decide (pivot < letter)) = initial :=
      List.filter_eq_self.mpr (fun letter member => by simp [initialValues letter member])
    have endingKeep : ending.filter (fun letter => decide (pivot < letter)) = ending :=
      List.filter_eq_self.mpr (fun letter member => by simp [endingValues letter member])
    have orderDrop : order.filter (fun letter => decide (pivot < letter)) = [] :=
      List.filter_eq_nil_iff.mpr (fun letter member => by
        have value := lowerValues letter member
        simp [Nat.not_lt.mpr (by omega : letter ≤ pivot)])
    simpa [wordEq, List.filter_append, initialKeep, endingKeep, orderDrop] using splitUpper
  have lowerFilter : word.filter (fun letter => decide (letter < pivot)) = order ++ order := by
    have initialDrop : initial.filter (fun letter => decide (letter < pivot)) = [] :=
      List.filter_eq_nil_iff.mpr (fun letter member => by
        have value := initialValues letter member
        simp [Nat.not_lt.mpr (by omega : pivot ≤ letter)])
    have endingDrop : ending.filter (fun letter => decide (letter < pivot)) = [] :=
      List.filter_eq_nil_iff.mpr (fun letter member => by
        have value := endingValues letter member
        simp [Nat.not_lt.mpr (by omega : pivot ≤ letter)])
    have orderKeep : order.filter (fun letter => decide (letter < pivot)) = order :=
      List.filter_eq_self.mpr (fun letter member => by simp [lowerValues letter member])
    simp [wordEq, List.filter_append, initialDrop, endingDrop, orderKeep]
  have noPairs (outer inner : ℕ) (different : outer ≠ inner)
      (sub : [outer, inner, inner, outer].Sublist word) : False := by
    by_cases outerPivot : outer = pivot
    · subst outer
      have absent : pivot ∉ initial ++ order := by simp [pivotInitial, pivotOrder]
      have pairSuffix : [pivot, inner, inner, pivot].Sublist
          ([pivot] ++ ending ++ order ++ [pivot]) := by
        apply skipPrefix (initial ++ order) _ [inner, inner, pivot] pivot absent
        simpa [wordEq, List.append_assoc] using sub
      have countLe := pairSuffix.count_le inner
      have bounded := List.nodup_iff_count_le_one.mp joinedDistinct inner
      simp [List.count_append, Ne.symm different, different] at countLe
      simp only [List.count_append] at bounded
      omega
    by_cases innerPivot : inner = pivot
    · subst inner
      have pairPrefix : [outer, pivot, pivot, outer].Sublist
          (initial ++ order ++ [pivot] ++ ending ++ order) := by
        apply trimSuffix _ [pivot] outer pivot (by simpa using outerPivot)
        exact sub
      have countLe := pairPrefix.count_le pivot
      simp [List.count_append, List.count_eq_zero.mpr pivotInitial,
        List.count_eq_zero.mpr pivotEnding, List.count_eq_zero.mpr pivotOrder,
        outerPivot] at countLe
    rcases lt_or_gt_of_ne outerPivot with outerLow | outerHigh
    · rcases lt_or_gt_of_ne innerPivot with innerLow | innerHigh
      · have filtered := sub.filter (fun letter => decide (letter < pivot))
        have lowPair : [outer, inner, inner, outer].Sublist (order ++ order) := by
          simpa [outerLow, innerLow, lowerFilter] using filtered
        exact inputNoPairs _ lowerNesting outer inner different lowPair
      · have absent : outer ∉ initial := by
          intro member
          have value := initialValues outer member
          omega
        have pairSuffix : [outer, inner, inner, outer].Sublist
            (order ++ [pivot] ++ ending ++ order ++ [pivot]) := by
          apply skipPrefix initial _ [inner, inner, outer] outer absent
          simpa [wordEq, List.append_assoc] using sub
        have innerNotOrder : inner ∉ order := by
          intro member
          have value := lowerValues inner member
          omega
        have countLe := pairSuffix.count_le inner
        have bounded := List.nodup_iff_count_le_one.mp endingDistinct inner
        simp [List.count_append, List.count_eq_zero.mpr innerNotOrder,
          different, Ne.symm different, Ne.symm innerPivot] at countLe
        omega
    · rcases lt_or_gt_of_ne innerPivot with innerLow | innerHigh
      · have absent : outer ∉ order ++ [pivot] := by
          simp only [List.mem_append, List.mem_singleton, not_or]
          refine ⟨?_, outerPivot⟩
          intro member
          have value := lowerValues outer member
          omega
        have pairPrefix : [outer, inner, inner, outer].Sublist
            (initial ++ order ++ [pivot] ++ ending) := by
          apply trimSuffix _ (order ++ [pivot]) outer inner absent
          simpa [wordEq, List.append_assoc] using sub
        have innerNotInitial : inner ∉ initial := by
          intro member
          have value := initialValues inner member
          omega
        have innerNotEnding : inner ∉ ending := by
          intro member
          have value := endingValues inner member
          omega
        have countLe := pairPrefix.count_le inner
        have bounded := List.nodup_iff_count_le_one.mp distinct inner
        simp [List.count_append, List.count_eq_zero.mpr innerNotInitial,
          List.count_eq_zero.mpr innerNotEnding, different, Ne.symm different,
          Ne.symm innerPivot] at countLe
        omega
      · have filtered := sub.filter (fun letter => decide (pivot < letter))
        have highPair : [outer, inner, inner, outer].Sublist upper := by
          simpa [outerHigh, innerHigh, upperFilter] using filtered
        exact inputNoPairs _ upperNesting outer inner different highPair
  constructor
  · rintro ⟨labels, increasing, _, sub, _⟩
    have ordered : labels 1 < labels 2 :=
      increasing 1 (by omega) (by simp [NonnestingDefs.letters])
    exact noPairs (labels 1) (labels 2) (by omega) (by simpa using sub)
  · rintro ⟨labels, increasing, _, sub, _⟩
    have ordered : labels 1 < labels 2 :=
      increasing 1 (by omega) (by simp [NonnestingDefs.letters])
    exact noPairs (labels 2) (labels 1) (by omega) (by simpa using sub)

#print axioms typeII_nonnesting

end D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoTypeIINesting
