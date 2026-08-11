/- GID: D5/S1/Words/ReturnWords/GoldenReturnWordsExact
   generality: I
   mirror-B: none(waiver:formal-kernel-return-word-exactness)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden factors of every positive length have exactly two return words. -/

import D5.S1.Words.ReturnWords.GoldenReturnItinerary

namespace D5.S1.Words

open Set

private theorem adjacent_golden_occurrences_iff {n : Nat} {w : List Bool} {i j : Nat} :
    AdjacentGoldenOccurrences n w i j ↔
      i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
        (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅ := by
  change decide (i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
    (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅) = true ↔ _
  simp

/-- Occurrence gaps are exactly the lengths attained by return words. -/
theorem golden_occurrence_gap_set_eq_length_image (n : Nat) (w : List Bool) :
    goldenOccurrenceGapSet n w = List.length '' goldenReturnWords n w := by
  ext d
  constructor
  · rintro ⟨i, j, hadj, rfl⟩
    refine ⟨goldenFactor (j - i) i, ⟨i, j, hadj, rfl⟩, ?_⟩
    simp [goldenFactor]
  · rintro ⟨r, ⟨i, j, hadj, rfl⟩, hr⟩
    exact ⟨i, j, hadj, by simpa [goldenFactor] using hr.symm⟩


/-- Length bijects return words with adjacent-occurrence gaps at positive factor length. -/
theorem golden_return_words_length_bijOn {n : Nat} (hn : 0 < n) (w : List Bool) :
    Set.BijOn List.length (goldenReturnWords n w) (goldenOccurrenceGapSet n w) := by
  refine ⟨?_, golden_return_words_length_injOn hn w, ?_⟩
  · intro r hr
    rw [golden_occurrence_gap_set_eq_length_image]
    exact ⟨r, hr, rfl⟩
  · intro d hd
    rw [golden_occurrence_gap_set_eq_length_image] at hd
    obtain ⟨r, hr, hlength⟩ := hd
    exact ⟨r, hr, hlength⟩

/-- Every occurring positive-length golden factor has exactly two return words. -/
theorem golden_return_words_encard_eq_two_of_pos {n : Nat} (hn : 0 < n)
    {w : List Bool} (hw : w ∈ goldenFactorSet n) :
    (goldenReturnWords n w).encard = 2 := by
  obtain ⟨i, hi⟩ := mem_goldenFactorSet.mp hw
  calc
    (goldenReturnWords n w).encard =
        (List.length '' goldenReturnWords n w).encard :=
      (golden_return_words_length_injOn hn w).encard_image.symm
    _ = (goldenOccurrenceGapSet n w).encard := by rw [golden_occurrence_gap_set_eq_length_image]
    _ = 2 := golden_occurrence_gap_set_encard_eq_two hn hi.symm

private theorem goldenWord_no_false_false (i : Nat) :
    ¬(goldenWord i = false ∧ goldenWord (i + 1) = false) := by
  rintro ⟨hi, hi1⟩
  have hzero : goldenWindowTrueCount i 2 = 0 := by
    rw [goldenWindowTrueCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk htrue
    simp only [Finset.mem_range] at hk
    interval_cases k <;> simp_all
  have htwo : goldenWindowTrueCount 2 2 = 2 := by decide
  have hbalanced := goldenWord_balanced_one i 2 2
  rw [hzero, htwo] at hbalanced
  norm_num at hbalanced

private theorem goldenWord_no_true_true_true (i : Nat) :
    ¬(goldenWord i = true ∧ goldenWord (i + 1) = true ∧
      goldenWord (i + 2) = true) := by
  rintro ⟨hi, hi1, hi2⟩
  have hthree : goldenWindowTrueCount i 3 = 3 := by
    rw [goldenWindowTrueCount]
    have hfilter :
        (Finset.range 3).filter (fun k => goldenWord (i + k) = true) =
          Finset.range 3 := by
      apply Finset.filter_eq_self.mpr
      intro k hk
      simp only [Finset.mem_range] at hk
      interval_cases k <;> simp_all
    rw [hfilter]
    decide
  have hone : goldenWindowTrueCount 4 3 = 1 := by decide
  have hbalanced := goldenWord_balanced_one i 4 3
  rw [hthree, hone] at hbalanced
  norm_num at hbalanced

private theorem golden_factor_two_words {i : Nat} {a b : Bool}
    (h : goldenFactor 2 i = [a, b]) :
    goldenWord i = a ∧ goldenWord (i + 1) = b := by
  simpa [goldenFactor, List.ofFn_inj] using h

private theorem return_word_two_true_false_cases {r : List Bool}
    (hr : r ∈ goldenReturnWords 2 [true, false]) :
    r = [true, false] ∨ r = [true, false, true] := by
  obtain ⟨i, j, hadj, rfl⟩ := hr
  have hs := adjacent_golden_occurrences_iff.mp hadj
  have hgap : j - i = 2 ∨ j - i = 3 := by
    have hmem : j - i ∈ goldenOccurrenceGapSet 2 [true, false] :=
      ⟨i, j, hadj, rfl⟩
    rw [golden_occurrence_gap_set_two_true_false] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  rcases hgap with hgap | hgap
  · left
    simpa [hgap] using hs.2.1
  · right
    have hbits := golden_factor_two_words hs.2.1
    have hthird : goldenWord (i + 2) = true := by
      cases h : goldenWord (i + 2)
      · exact (goldenWord_no_false_false (i + 1)
          ⟨hbits.2, by simpa [Nat.add_assoc] using h⟩).elim
      · rfl
    simp [hgap, goldenFactor, hbits.1, hbits.2, hthird]

private theorem return_word_two_false_true_cases {r : List Bool}
    (hr : r ∈ goldenReturnWords 2 [false, true]) :
    r = [false, true] ∨ r = [false, true, true] := by
  obtain ⟨i, j, hadj, rfl⟩ := hr
  have hs := adjacent_golden_occurrences_iff.mp hadj
  have hgap : j - i = 2 ∨ j - i = 3 := by
    have hmem : j - i ∈ goldenOccurrenceGapSet 2 [false, true] :=
      ⟨i, j, hadj, rfl⟩
    rw [golden_occurrence_gap_set_two_false_true] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  rcases hgap with hgap | hgap
  · left
    simpa [hgap] using hs.2.1
  · right
    have hbits := golden_factor_two_words hs.2.1
    have hjbits := golden_factor_two_words hs.2.2.1
    have hji : j = i + 3 := by omega
    have hthird : goldenWord (i + 2) = true := by
      cases h : goldenWord (i + 2)
      · exact (goldenWord_no_false_false (i + 2)
          ⟨h, by simpa [hji, Nat.add_assoc] using hjbits.1⟩).elim
      · rfl
    simp [hgap, goldenFactor, hbits.1, hbits.2, hthird]

private theorem return_word_two_true_true_cases {r : List Bool}
    (hr : r ∈ goldenReturnWords 2 [true, true]) :
    r = [true, true, false] ∨ r = [true, true, false, true, false] := by
  obtain ⟨i, j, hadj, rfl⟩ := hr
  have hs := adjacent_golden_occurrences_iff.mp hadj
  have hgap : j - i = 3 ∨ j - i = 5 := by
    have hmem : j - i ∈ goldenOccurrenceGapSet 2 [true, true] :=
      ⟨i, j, hadj, rfl⟩
    rw [golden_occurrence_gap_set_two_true_true] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hbits := golden_factor_two_words hs.2.1
  have hthird : goldenWord (i + 2) = false := by
    cases h : goldenWord (i + 2)
    · rfl
    · exact (goldenWord_no_true_true_true i ⟨hbits.1, hbits.2, h⟩).elim
  rcases hgap with hgap | hgap
  · left
    simp [hgap, goldenFactor, hbits.1, hbits.2, hthird]
  · right
    have hjbits := golden_factor_two_words hs.2.2.1
    have hji : j = i + 5 := by omega
    have hfourth : goldenWord (i + 3) = true := by
      cases h : goldenWord (i + 3)
      · exact (goldenWord_no_false_false (i + 2)
          ⟨hthird, by simpa [Nat.add_assoc] using h⟩).elim
      · rfl
    have hfifth : goldenWord (i + 4) = false := by
      cases h : goldenWord (i + 4)
      · rfl
      · exact (goldenWord_no_true_true_true (i + 3)
          ⟨hfourth, h, by simpa [hji, Nat.add_assoc] using hjbits.1⟩).elim
    simp [hgap, goldenFactor, hbits.1, hbits.2, hthird, hfourth, hfifth]

/-- The return words to `TF` are exactly `TF` and `TFT`. -/
theorem golden_return_words_two_true_false :
    goldenReturnWords 2 [true, false] = {[true, false], [true, false, true]} := by
  ext r
  constructor
  · intro hr
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      return_word_two_true_false_cases hr
  · intro hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact ⟨3, 5, by decide, by decide⟩
    · exact ⟨0, 3, by decide, by decide⟩

/-- The return words to `FT` are exactly `FT` and `FTT`. -/
theorem golden_return_words_two_false_true :
    goldenReturnWords 2 [false, true] = {[false, true], [false, true, true]} := by
  ext r
  constructor
  · intro hr
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      return_word_two_false_true_cases hr
  · intro hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact ⟨4, 6, by decide, by decide⟩
    · exact ⟨1, 4, by decide, by decide⟩

/-- The return words to `TT` are exactly `TTF` and `TTFTF`. -/
theorem golden_return_words_two_true_true :
    goldenReturnWords 2 [true, true] =
      {[true, true, false], [true, true, false, true, false]} := by
  ext r
  constructor
  · intro hr
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      return_word_two_true_true_cases hr
  · intro hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact ⟨7, 10, by decide, by decide⟩
    · exact ⟨2, 7, by decide, by decide⟩

private theorem golden_factor_set_two_recheck :
    goldenFactorSet 2 = {[true, false], [false, true], [true, true]} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact mem_goldenFactorSet.mpr ⟨0, by decide⟩
    · exact mem_goldenFactorSet.mpr ⟨1, by decide⟩
    · exact mem_goldenFactorSet.mpr ⟨2, by decide⟩
  · rw [golden_factor_complexity]
    decide

/-- Every occurring length-two golden factor has exactly two return words. -/
theorem golden_return_words_two_encard_eq_two {w : List Bool}
    (hw : w ∈ goldenFactorSet 2) : (goldenReturnWords 2 w).encard = 2 := by
  rw [golden_factor_set_two_recheck] at hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · rw [golden_return_words_two_true_false]
    exact Set.encard_pair (by decide)
  · rw [golden_return_words_two_false_true]
    exact Set.encard_pair (by decide)
  · rw [golden_return_words_two_true_true]
    exact Set.encard_pair (by decide)

private theorem golden_return_words_zero_readout :
    goldenReturnWords 0 [] = {([true] : List Bool), [false]} := by
  ext r
  constructor
  · rintro ⟨i, j, hadj, rfl⟩
    have hgapMem : j - i ∈ goldenOccurrenceGapSet 0 [] := ⟨i, j, hadj, rfl⟩
    rw [golden_occurrence_gap_set_zero] at hgapMem
    have hgap : j - i = 1 := by simpa using hgapMem
    cases hword : goldenWord i <;>
      simp [hgap, goldenFactor, hword]
  · intro hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact ⟨2, 3, by decide, by decide⟩
    · exact ⟨1, 2, by decide, by decide⟩

private theorem golden_return_words_zero_length_not_injOn :
    ¬Set.InjOn List.length (goldenReturnWords 0 []) := by
  rw [golden_return_words_zero_readout]
  intro hinj
  have htrue : ([true] : List Bool) ∈
      ({([true] : List Bool), [false]} : Set (List Bool)) := by simp
  have hfalse : ([false] : List Bool) ∈
      ({([true] : List Bool), [false]} : Set (List Bool)) := by simp
  have heq := hinj htrue hfalse (by decide)
  exact (by decide : ([true] : List Bool) ≠ [false]) heq

private theorem golden_return_words_one_recheck :
    goldenReturnWords 1 [true] = {[true], [true, false]} ∧
      goldenReturnWords 1 [false] = {[false, true], [false, true, true]} :=
  ⟨golden_return_words_true, golden_return_words_false⟩


#print axioms golden_occurrence_gap_set_eq_length_image
#print axioms golden_return_words_length_bijOn
#print axioms golden_return_words_encard_eq_two_of_pos
#print axioms golden_return_words_two_true_false
#print axioms golden_return_words_two_false_true
#print axioms golden_return_words_two_true_true
#print axioms golden_return_words_two_encard_eq_two

end D5.S1.Words

