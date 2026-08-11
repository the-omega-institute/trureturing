/- GID: D5/S1/Words/ReturnWords/GoldenReturnWords
   generality: I
   mirror-B: D5/B/S1/Words/ReturnWords/GoldenReturnWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden factors have return words, with exactly two at length one. -/

import D5.S1.Words.GoldenSubstFixed
import D5.S1.Words.GoldenUniformRecurrence

namespace D5.S1.Words

open D5.S0.Tower.GoldenGapWord
open Set

private def adjacentGoldenOccurrencesBool (n : Nat) (w : List Bool) (i j : Nat) : Bool :=
  decide (i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
    (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅)

/-- Two occurrences of `w` with no occurrence starting strictly between them. -/
def AdjacentGoldenOccurrences (n : Nat) (w : List Bool) (i j : Nat) : Prop :=
  adjacentGoldenOccurrencesBool n w i j = true

instance (n : Nat) (w : List Bool) (i j : Nat) :
    Decidable (AdjacentGoldenOccurrences n w i j) :=
  inferInstanceAs (Decidable (adjacentGoldenOccurrencesBool n w i j = true))

private theorem adjacentGoldenOccurrences_iff {n : Nat} {w : List Bool} {i j : Nat} :
    AdjacentGoldenOccurrences n w i j ↔
      i < j ∧ goldenFactor n i = w ∧ goldenFactor n j = w ∧
        (Finset.Ioo i j).filter (fun k => goldenFactor n k = w) = ∅ := by
  simp [AdjacentGoldenOccurrences, adjacentGoldenOccurrencesBool]

/-- A return word is the golden-word block between adjacent starts of the same factor. -/
def IsGoldenReturnWord (n : Nat) (w r : List Bool) : Prop :=
  ∃ i j, AdjacentGoldenOccurrences n w i j ∧ r = goldenFactor (j - i) i

/-- The set of return words to `w` among length-`n` golden factors. -/
def goldenReturnWords (n : Nat) (w : List Bool) : Set (List Bool) :=
  {r | IsGoldenReturnWord n w r}

private theorem factor_ne_of_adjacent_between {n : Nat} {w : List Bool} {i j k : Nat}
    (h : AdjacentGoldenOccurrences n w i j) (hik : i < k) (hkj : k < j) :
    goldenFactor n k ≠ w := by
  have hs := adjacentGoldenOccurrences_iff.mp h
  intro hfactor
  have hmem : k ∈ (Finset.Ioo i j).filter (fun l => goldenFactor n l = w) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hik, hkj⟩, hfactor⟩
  rw [hs.2.2.2] at hmem
  simp at hmem

/-- Every factor that occurs has at least one return word. -/
theorem golden_return_words_nonempty {n : Nat} {w : List Bool}
    (hw : w ∈ goldenFactorSet n) : (goldenReturnWords n w).Nonempty := by
  obtain ⟨i, hi⟩ := mem_goldenFactorSet.mp hw
  have hexists : ∃ j, i < j ∧ goldenFactor n j = w := by
    obtain ⟨j, hij, hj⟩ := golden_factor_recurrent hw i
    exact ⟨j, hij, hj.symm⟩
  let j := Nat.find hexists
  have hj : i < j ∧ goldenFactor n j = w := Nat.find_spec hexists
  refine ⟨goldenFactor (j - i) i, i, j, ?_, rfl⟩
  apply adjacentGoldenOccurrences_iff.mpr
  refine ⟨hj.1, hi.symm, hj.2, Finset.filter_eq_empty_iff.mpr ?_⟩
  intro k hk hfactor
  exact Nat.find_min hexists (Finset.mem_Ioo.mp hk).2
    ⟨(Finset.mem_Ioo.mp hk).1, hfactor⟩

private theorem goldenFactor_one (i : Nat) : goldenFactor 1 i = [goldenWord i] := by
  simp [goldenFactor]

private theorem goldenWord_no_false_false (i : Nat) :
    ¬ (goldenWord i = false ∧ goldenWord (i + 1) = false) := by
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
    ¬ (goldenWord i = true ∧ goldenWord (i + 1) = true ∧
      goldenWord (i + 2) = true) := by
  rintro ⟨hi, hi1, hi2⟩
  have hthree : goldenWindowTrueCount i 3 = 3 := by
    rw [goldenWindowTrueCount]
    have hfilter :
        (Finset.range 3).filter (fun k => goldenWord (i + k) = true) = Finset.range 3 := by
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

private theorem true_return_word_cases {r : List Bool}
    (hr : r ∈ goldenReturnWords 1 [true]) : r = [true] ∨ r = [true, false] := by
  obtain ⟨i, j, hadj, rfl⟩ := hr
  have hadj := adjacentGoldenOccurrences_iff.mp hadj
  have hij : i < j := hadj.1
  have hi : goldenWord i = true := by
    simpa [goldenFactor_one] using hadj.2.1
  have hgap : j - i = 1 ∨ j - i = 2 := by
    have hle : j ≤ i + 2 := by
      by_contra hnot
      have hij1 : i < i + 1 := by omega
      have hij2 : i + 1 < j := by omega
      have hij3 : i + 2 < j := by omega
      have hne1 := factor_ne_of_adjacent_between (k := i + 1)
        (adjacentGoldenOccurrences_iff.mpr hadj) hij1 hij2
      have hne2 := factor_ne_of_adjacent_between (k := i + 2)
        (adjacentGoldenOccurrences_iff.mpr hadj) (by omega) hij3
      have hfalse1 : goldenWord (i + 1) = false := by
        cases h : goldenWord (i + 1) <;> simp_all [goldenFactor_one]
      have hfalse2 : goldenWord (i + 2) = false := by
        cases h : goldenWord (i + 2) <;> simp_all [goldenFactor_one]
      exact goldenWord_no_false_false (i + 1) ⟨hfalse1, by simpa [Nat.add_assoc] using hfalse2⟩
    omega
  rcases hgap with hgap | hgap
  · left
    simpa [hgap] using hadj.2.1
  · right
    have hmiddle := factor_ne_of_adjacent_between (k := i + 1)
      (adjacentGoldenOccurrences_iff.mpr hadj) (by omega) (by omega)
    have hfalse : goldenWord (i + 1) = false := by
      cases h : goldenWord (i + 1) <;> simp_all [goldenFactor_one]
    simp [hgap, goldenFactor, hi, hfalse]

private theorem false_return_word_cases {r : List Bool}
    (hr : r ∈ goldenReturnWords 1 [false]) :
    r = [false, true] ∨ r = [false, true, true] := by
  obtain ⟨i, j, hadj, rfl⟩ := hr
  have hadj := adjacentGoldenOccurrences_iff.mp hadj
  have hij : i < j := hadj.1
  have hi : goldenWord i = false := by
    simpa [goldenFactor_one] using hadj.2.1
  have hgap : j - i = 2 ∨ j - i = 3 := by
    have hne_one : j - i ≠ 1 := by
      intro hgap
      have hj : goldenWord j = false := by
        simpa [goldenFactor_one] using hadj.2.2.1
      apply goldenWord_no_false_false i
      constructor
      · exact hi
      · have hji : j = i + 1 := by omega
        rw [← hji]
        exact hj
    have hle : j ≤ i + 3 := by
      by_contra hnot
      have htrue1 : goldenWord (i + 1) = true := by
        have hne := factor_ne_of_adjacent_between (k := i + 1)
          (adjacentGoldenOccurrences_iff.mpr hadj) (by omega) (by omega)
        cases h : goldenWord (i + 1) <;> simp_all [goldenFactor_one]
      have htrue2 : goldenWord (i + 2) = true := by
        have hne := factor_ne_of_adjacent_between (k := i + 2)
          (adjacentGoldenOccurrences_iff.mpr hadj) (by omega) (by omega)
        cases h : goldenWord (i + 2) <;> simp_all [goldenFactor_one]
      have htrue3 : goldenWord (i + 3) = true := by
        have hne := factor_ne_of_adjacent_between (k := i + 3)
          (adjacentGoldenOccurrences_iff.mpr hadj) (by omega) (by omega)
        cases h : goldenWord (i + 3) <;> simp_all [goldenFactor_one]
      exact goldenWord_no_true_true_true (i + 1)
        ⟨htrue1, by simpa [Nat.add_assoc] using htrue2,
          by simpa [Nat.add_assoc] using htrue3⟩
    omega
  rcases hgap with hgap | hgap
  · left
    have hmiddle := factor_ne_of_adjacent_between (k := i + 1)
      (adjacentGoldenOccurrences_iff.mpr hadj) (by omega) (by omega)
    have htrue : goldenWord (i + 1) = true := by
      cases h : goldenWord (i + 1) <;> simp_all [goldenFactor_one]
    simp [hgap, goldenFactor, hi, htrue]
  · right
    have hmiddle1 := factor_ne_of_adjacent_between (k := i + 1)
      (adjacentGoldenOccurrences_iff.mpr hadj) (by omega) (by omega)
    have hmiddle2 := factor_ne_of_adjacent_between (k := i + 2)
      (adjacentGoldenOccurrences_iff.mpr hadj) (by omega) (by omega)
    have htrue1 : goldenWord (i + 1) = true := by
      cases h : goldenWord (i + 1) <;> simp_all [goldenFactor_one]
    have htrue2 : goldenWord (i + 2) = true := by
      cases h : goldenWord (i + 2) <;> simp_all [goldenFactor_one]
    simp [hgap, goldenFactor, hi, htrue1, htrue2]

/-- The return words to the one-letter true factor are exactly `T` and `TF`. -/
theorem golden_return_words_true :
    goldenReturnWords 1 [true] = {[true], [true, false]} := by
  ext r
  constructor
  · intro hr
    simpa only [mem_insert_iff, mem_singleton_iff] using true_return_word_cases hr
  · intro hr
    simp only [mem_insert_iff, mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact ⟨2, 3, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide⟩

/-- The return words to the one-letter false factor are exactly `FT` and `FTT`. -/
theorem golden_return_words_false :
    goldenReturnWords 1 [false] = {[false, true], [false, true, true]} := by
  ext r
  constructor
  · intro hr
    simpa only [mem_insert_iff, mem_singleton_iff] using false_return_word_cases hr
  · intro hr
    simp only [mem_insert_iff, mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact ⟨4, 6, by decide, by decide⟩
    · exact ⟨1, 4, by decide, by decide⟩

/-- Every length-one golden factor has exactly two return words. -/
theorem golden_return_words_encard_eq_two {w : List Bool} (hw : w ∈ goldenFactorSet 1) :
    (goldenReturnWords 1 w).encard = 2 := by
  have hlength := length_eq_of_mem_goldenFactorSet hw
  cases w with
  | nil => simp at hlength
  | cons b tail =>
      cases tail with
      | nil =>
          cases b
          · rw [golden_return_words_false]
            exact Set.encard_pair (by decide)
          · rw [golden_return_words_true]
            exact Set.encard_pair (by decide)
      | cons c tail => simp at hlength

/-- Substitution sends seed return words to return words of their synchronized image marker. -/
theorem seed_return_word_subst_mem {b : Bool} {r : List Bool}
    (hr : r ∈ goldenReturnWords 1 [b]) :
    r.flatMap subst ∈ goldenReturnWords 2 (if b then [true, false] else [true, true]) := by
  cases b with
  | false =>
      rcases false_return_word_cases hr with rfl | rfl
      · exact ⟨7, 10, by decide, by decide⟩
      · exact ⟨2, 7, by decide, by decide⟩
  | true =>
      rcases true_return_word_cases hr with rfl | rfl
      · exact ⟨3, 5, by decide, by decide⟩
      · exact ⟨0, 3, by decide, by decide⟩

private def goldenReturnWordsBelow (n : Nat) (w : List Bool) (bound : Nat) :
    Finset (List Bool) :=
  (((Finset.range bound).product (Finset.range bound)).filter fun (p : Nat × Nat) =>
      AdjacentGoldenOccurrences n w p.1 p.2).image fun (p : Nat × Nat) =>
        goldenFactor (p.2 - p.1) p.1

private theorem golden_return_words_small_cases :
    goldenReturnWordsBelow 1 [true] 16 = {[true], [true, false]} ∧
      goldenReturnWordsBelow 1 [false] 16 = {[false, true], [false, true, true]} ∧
      goldenReturnWordsBelow 2 [true, false] 16 =
        {[true, false], [true, false, true]} ∧
      goldenReturnWordsBelow 2 [false, true] 16 =
        {[false, true], [false, true, true]} ∧
      goldenReturnWordsBelow 2 [true, true] 16 =
        {[true, true, false], [true, true, false, true, false]} := by
  decide

#print axioms golden_return_words_nonempty
#print axioms golden_return_words_encard_eq_two
#print axioms seed_return_word_subst_mem

end D5.S1.Words
