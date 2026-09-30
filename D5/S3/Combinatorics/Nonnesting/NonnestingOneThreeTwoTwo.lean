/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo
   mirror-E: none(waiver:lagrange-inversion-counting)
   anchors: []
   utility: none
   digest: Proves the all-size 1322 binomial enumeration by strong-inductive Lagrange inversion. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoCount
import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwoKernel
import Mathlib

namespace D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo

open D5.S3.Combinatorics.Nonnesting NonnestingOneThreeTwoTwoCount PowerSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
theorem result : NonnestingDefs.claim1322 := by
  classical
  have counting_recurrence (degree : ℕ) (positive : 1 ≤ degree) :
      (NonnestingDefs.avoiders degree [[1, 3, 2, 2]]).ncard =
        (∑ index ∈ Finset.Icc 1 (degree - 1),
          (NonnestingDefs.avoiders index [[1, 3, 2, 2]]).ncard *
            (NonnestingDefs.avoiders (degree - index) [[1, 3, 2, 2]]).ncard) +
        ∑ outer ∈ Finset.HasAntidiagonal.antidiagonal (degree - 1),
          ∑ inner ∈ Finset.HasAntidiagonal.antidiagonal outer.1,
            (NonnestingDefs.avoiders inner.1 [[1, 3, 2, 2]]).ncard *
              (NonnestingDefs.avoiders inner.2 [[1, 3, 2, 2]]).ncard *
              (NonnestingDefs.avoiders outer.2 [[1, 3, 2, 2]]).ncard := by
    classical
    let words := fun labels : List ℕ =>
      ((labels.flatMap fun letter => [letter, letter]).permutations.toFinset).filter
        fun word => ¬ NonnestingDefs.Occurs [1, 2, 2, 1] word ∧
          ¬ NonnestingDefs.Occurs [2, 1, 1, 2] word ∧
          ¬ NonnestingDefs.Occurs [1, 3, 2, 2] word
    let terminal := fun word : List ℕ =>
      word.length - word.toFinset.sup (fun letter => word.idxOf letter) - 1
    let counts := fun degree => ((words (List.range' 1 degree)).card : ℚ)
    let weighted := fun degree =>
      ∑ word ∈ words (List.range' 1 degree), (Polynomial.X : Polynomial ℚ) ^ terminal word
    have weightedRecurrence (size : ℕ) :
        (1 - Polynomial.X) * weighted (size + 1) =
          ∑ lower ∈ Finset.range (size + 1),
            (Polynomial.C (counts (size - lower)) *
              (Polynomial.X * Polynomial.C (counts lower) - Polynomial.X ^ 2 * weighted lower) +
            Polynomial.C (catalan lower : ℚ) * Polynomial.X ^ (lower + 2) *
              (Polynomial.C (counts (size - lower)) - weighted (size - lower))) := by
      have wordMember (labels word : List ℕ) : word ∈ words labels ↔
          word.Perm (labels.flatMap fun letter => [letter, letter]) ∧
            ¬ NonnestingDefs.Occurs [1, 2, 2, 1] word ∧
            ¬ NonnestingDefs.Occurs [2, 1, 1, 2] word ∧
            ¬ NonnestingDefs.Occurs [1, 3, 2, 2] word := by
        simp [words, List.mem_permutations]
      have occurrenceShift (pattern word : List ℕ) (offset : ℕ) :
          NonnestingDefs.Occurs pattern (word.map fun letter => letter + offset) ↔
            NonnestingDefs.Occurs pattern word := by
        unfold NonnestingDefs.Occurs D5.S3.Combinatorics.ArrowWilfDefs.Contains
        constructor
        · rintro ⟨values, increasing, members, subword, arrows⟩
          refine ⟨fun index => values index - offset, ?_, ?_, ?_, by simp⟩
          · intro index positive bounded
            obtain ⟨left, _, leftEq⟩ := List.mem_map.mp (members index positive (by omega))
            obtain ⟨right, _, rightEq⟩ :=
              List.mem_map.mp (members (index + 1) (by omega) (by omega))
            have := increasing index positive bounded
            change values index - offset < values (index + 1) - offset
            omega
          · intro index positive bounded
            obtain ⟨letter, present, equal⟩ := List.mem_map.mp (members index positive bounded)
            have : values index - offset = letter := by omega
            simpa [this] using present
          · have mapped := subword.map (fun letter => letter - offset)
            simpa [List.map_map, Function.comp_def] using mapped
        · rintro ⟨values, increasing, members, subword, arrows⟩
          refine ⟨fun index => values index + offset, ?_, ?_, ?_, by simp⟩
          · intro index positive bounded
            exact Nat.add_lt_add_right (increasing index positive bounded) offset
          · intro index positive bounded
            exact List.mem_map_of_mem (members index positive bounded)
          · simpa [List.map_map, Function.comp_def] using
              subword.map (fun letter => letter + offset)
      have shiftedDouble (labels : List ℕ) (offset : ℕ) :
          (labels.flatMap fun letter => [letter, letter]).map (fun letter => letter + offset) =
            (labels.map fun letter => letter + offset).flatMap fun letter => [letter, letter] := by
        induction labels with
        | nil => simp
        | cons letter labels inductionHypothesis => simp [inductionHypothesis]
      have shiftedIndex (word : List ℕ) (letter offset : ℕ) :
          (word.map fun letter => letter + offset).idxOf (letter + offset) = word.idxOf letter := by
        induction word with
        | nil => simp
        | cons entry word inductionHypothesis =>
          by_cases equal : entry = letter
          · simp [equal]
          · have shiftedNe : entry + offset ≠ letter + offset := by omega
            simp [equal, inductionHypothesis]
      have shiftedTerminal (word : List ℕ) (offset : ℕ) :
          terminal (word.map fun letter => letter + offset) = terminal word := by
        have supEq :
            (word.map fun letter => letter + offset).toFinset.sup
              (fun letter => (word.map fun letter => letter + offset).idxOf letter) =
                word.toFinset.sup (fun letter => word.idxOf letter) := by
          apply le_antisymm
          · apply Finset.sup_le
            intro letter present
            obtain ⟨entry, member, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
            rw [shiftedIndex]
            exact Finset.le_sup (f := fun letter => word.idxOf letter)
              (List.mem_toFinset.mpr member)
          · apply Finset.sup_le
            intro letter present
            rw [← shiftedIndex word letter offset]
            exact Finset.le_sup
              (f := fun letter => (word.map fun letter => letter + offset).idxOf letter)
              (List.mem_toFinset.mpr
              (List.mem_map_of_mem (List.mem_toFinset.mp present)))
        simp only [terminal, List.length_map, supEq]
      have shiftedSums (labels : List ℕ) (offset : ℕ) (weight : ℕ → Polynomial ℚ) :
          (∑ word ∈ words (labels.map fun letter => letter + offset), weight (terminal word)) =
            ∑ word ∈ words labels, weight (terminal word) := by
        symm
        apply Finset.sum_bij
          (fun word _ => word.map fun letter => letter + offset)
        · intro word present
          have properties := (wordMember labels word).mp present
          apply (wordMember _ _).mpr
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [← shiftedDouble]
            exact properties.1.map _
          · simpa only [occurrenceShift] using properties.2.1
          · simpa only [occurrenceShift] using properties.2.2.1
          · simpa only [occurrenceShift] using properties.2.2.2
        · intro left leftPresent right rightPresent equal
          have mapped := congrArg (List.map fun letter => letter - offset) equal
          simpa [List.map_map, Function.comp_def] using mapped
        · intro word present
          have properties := (wordMember _ word).mp present
          have restore : (word.map fun letter => letter - offset).map
              (fun letter => letter + offset) = word := by
            rw [List.map_map]
            calc
              _ = word.map id := by
                apply List.map_congr_left
                intro letter member
                have baseMember := properties.1.mem_iff.mp member
                obtain ⟨entry, entryPresent, letterPresent⟩ := List.mem_flatMap.mp baseMember
                have letterEq : letter = entry := by simpa using letterPresent
                obtain ⟨original, _, shiftedEq⟩ := List.mem_map.mp entryPresent
                dsimp only [Function.comp_apply, id_eq]
                omega
              _ = word := List.map_id word
          refine ⟨word.map (fun letter => letter - offset), ?_, restore⟩
          apply (wordMember _ _).mpr
          refine ⟨?_, ?_, ?_, ?_⟩
          · have permutation := properties.1.map (fun letter => letter - offset)
            rw [← shiftedDouble, List.map_map] at permutation
            simpa [Function.comp_def] using permutation
          · have equivalence := occurrenceShift [1, 2, 2, 1]
              (word.map fun letter => letter - offset) offset
            rw [restore] at equivalence
            exact fun forbidden => properties.2.1 (equivalence.mpr forbidden)
          · have equivalence := occurrenceShift [2, 1, 1, 2]
              (word.map fun letter => letter - offset) offset
            rw [restore] at equivalence
            exact fun forbidden => properties.2.2.1 (equivalence.mpr forbidden)
          · have equivalence := occurrenceShift [1, 3, 2, 2]
              (word.map fun letter => letter - offset) offset
            rw [restore] at equivalence
            exact fun forbidden => properties.2.2.2 (equivalence.mpr forbidden)
        · intro word present
          rw [shiftedTerminal]
      have cutSums (word : List ℕ) (extra : ℕ) :
          (∑ cut ∈ (Finset.range (word.length + 1)).filter
            (fun cut => ∀ letter ∈ word, word.idxOf letter < cut),
              (1 - Polynomial.X) * (Polynomial.X : Polynomial ℚ) ^
                (word.length - cut + extra + 1)) =
              Polynomial.X ^ (extra + 1) - Polynomial.X ^ (extra + terminal word + 2) ∧
          (∑ cut ∈ (Finset.range word.length).filter
            (fun cut => ∀ letter ∈ word, word.idxOf letter < cut),
              (1 - Polynomial.X) * (Polynomial.X : Polynomial ℚ) ^
                (word.length - cut + extra + 1)) =
              Polynomial.X ^ (extra + 2) - Polynomial.X ^ (extra + terminal word + 2) := by
        have geometric (length start : ℕ) :
            (∑ index ∈ Finset.range length,
              (1 - Polynomial.X) * (Polynomial.X : Polynomial ℚ) ^ (start + index)) =
                Polynomial.X ^ start - Polynomial.X ^ (start + length) := by
          induction length with
          | zero => simp
          | succ length inductionHypothesis =>
            rw [Finset.sum_range_succ, inductionHypothesis]
            simp only [pow_succ, Nat.add_succ]
            ring
        by_cases empty : word = []
        · subst word
          simp [terminal, pow_succ]
          ring
        have positive : 0 < word.length := List.length_pos_iff_ne_nil.mpr empty
        let lastOpening := word.toFinset.sup (fun letter => word.idxOf letter)
        have openingBound : lastOpening < word.length := by
          apply (Finset.sup_lt_iff positive).mpr
          intro letter member
          exact List.idxOf_lt_length_of_mem (List.mem_toFinset.mp member)
        have cutCondition (cut : ℕ) :
            (∀ letter ∈ word, word.idxOf letter < cut) ↔ lastOpening < cut := by
          constructor
          · intro condition
            have cutPositive : 0 < cut := by
              obtain ⟨letter, member⟩ := List.exists_mem_of_ne_nil word empty
              exact (Nat.zero_le _).trans_lt (condition letter member)
            exact (Finset.sup_lt_iff cutPositive).mpr
              (fun letter present => condition letter (List.mem_toFinset.mp present))
          · intro bound letter present
            exact (Finset.le_sup (f := fun letter => word.idxOf letter)
              (List.mem_toFinset.mpr present)).trans_lt bound
        have terminalEq : terminal word = word.length - lastOpening - 1 := rfl
        constructor
        · rw [show extra + terminal word + 2 = extra + 1 + (terminal word + 1) by omega,
            ← geometric (terminal word + 1) (extra + 1)]
          apply Finset.sum_bij (fun cut _ => word.length - cut)
          · intro cut present
            have bounds := Finset.mem_filter.mp present
            have : cut ≤ word.length := by simpa using bounds.1
            have := (cutCondition cut).mp bounds.2
            simp only [Finset.mem_range, terminalEq]
            omega
          · intro left leftPresent right rightPresent equal
            have leftBound := (Finset.mem_filter.mp leftPresent).1
            have rightBound := (Finset.mem_filter.mp rightPresent).1
            simp only [Finset.mem_range] at leftBound rightBound
            omega
          · intro index present
            refine ⟨word.length - index, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_range.mpr (by omega), (cutCondition _).mpr ?_⟩
              simp only [Finset.mem_range, terminalEq] at present
              omega
            · simp only [Finset.mem_range, terminalEq] at present
              omega
          · intro cut present
            congr 2
            omega
        · rw [show extra + terminal word + 2 = extra + 2 + terminal word by omega,
            ← geometric (terminal word) (extra + 2)]
          apply Finset.sum_bij (fun cut _ => word.length - cut - 1)
          · intro cut present
            have bounds := Finset.mem_filter.mp present
            have : cut < word.length := Finset.mem_range.mp bounds.1
            have := (cutCondition cut).mp bounds.2
            simp only [Finset.mem_range, terminalEq]
            omega
          · intro left leftPresent right rightPresent equal
            have leftBound := (Finset.mem_filter.mp leftPresent).1
            have rightBound := (Finset.mem_filter.mp rightPresent).1
            simp only [Finset.mem_range] at leftBound rightBound
            omega
          · intro index present
            refine ⟨word.length - index - 1, ?_, ?_⟩
            · apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_range.mpr (by omega), (cutCondition _).mpr ?_⟩
              simp only [Finset.mem_range, terminalEq] at present
              omega
            · simp only [Finset.mem_range, terminalEq] at present
              omega
          · intro cut present
            have bound := Finset.mem_range.mp (Finset.mem_filter.mp present).1
            congr 2
            omega
      have firstCuts (labels : List ℕ) :
          (∑ word ∈ words labels,
            ∑ cut ∈ (Finset.range (word.length + 1)).filter
              (fun cut => ∀ letter ∈ word, word.idxOf letter < cut),
                (1 - Polynomial.X) * (Polynomial.X : Polynomial ℚ) ^ (word.length - cut + 1)) =
            Polynomial.X * ((words labels).card : Polynomial ℚ) -
              Polynomial.X ^ 2 * ∑ word ∈ words labels, Polynomial.X ^ terminal word := by
        have perWord (word : List ℕ) :
            (∑ cut ∈ (Finset.range (word.length + 1)).filter
              (fun cut => ∀ letter ∈ word, word.idxOf letter < cut),
                (1 - Polynomial.X) * (Polynomial.X : Polynomial ℚ) ^ (word.length - cut + 1)) =
              Polynomial.X - Polynomial.X ^ 2 * Polynomial.X ^ terminal word := by
          have equation := (cutSums word 0).1
          simpa [show terminal word + 2 = 2 + terminal word by omega, pow_add] using equation
        simp_rw [perWord, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [nsmul_eq_mul, mul_comm]
      have secondCuts (labels : List ℕ) (extra : ℕ) :
          (∑ word ∈ words labels,
            ∑ cut ∈ (Finset.range word.length).filter
              (fun cut => ∀ letter ∈ word, word.idxOf letter < cut),
                (1 - Polynomial.X) * (Polynomial.X : Polynomial ℚ) ^
                  (word.length - cut + extra + 1)) =
            Polynomial.X ^ (extra + 2) *
              (((words labels).card : Polynomial ℚ) -
                ∑ word ∈ words labels, Polynomial.X ^ terminal word) := by
        have perWord (word : List ℕ) :
            (∑ cut ∈ (Finset.range word.length).filter
              (fun cut => ∀ letter ∈ word, word.idxOf letter < cut),
                (1 - Polynomial.X) * (Polynomial.X : Polynomial ℚ) ^
                  (word.length - cut + extra + 1)) =
              Polynomial.X ^ (extra + 2) -
                Polynomial.X ^ (extra + 2) * Polynomial.X ^ terminal word := by
          have equation := (cutSums word extra).2
          simpa [show extra + terminal word + 2 = extra + 2 + terminal word by omega,
            pow_add] using equation
        simp_rw [perWord, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [nsmul_eq_mul, mul_sub, mul_comm]
      have rangeParts (lower : ℕ) (bound : lower ≤ size) :
          (List.range' 1 (size + 1)).filter (fun letter => decide (letter < lower + 1)) =
            List.range' 1 lower ∧
          (List.range' 1 (size + 1)).filter (fun letter => decide (lower + 1 < letter)) =
            (List.range' 1 (size - lower)).map (fun letter => letter + (lower + 1)) := by
        have split : List.range' 1 (size + 1) =
            List.range' 1 lower ++ (lower + 1) :: List.range' (lower + 2) (size - lower) := by
          have equation := List.range'_append_1 (s := 1) (m := lower)
            (n := size - lower + 1)
          rw [show lower + (size - lower + 1) = size + 1 by omega] at equation
          simpa [List.range', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using equation.symm
        have lowerKept : (List.range' 1 lower).filter
            (fun letter => decide (letter < lower + 1)) = List.range' 1 lower := by
          apply List.filter_eq_self.mpr
          intro letter present
          have := List.mem_range'.mp present
          simpa using (show letter < lower + 1 by omega)
        have upperRemoved : (List.range' (lower + 2) (size - lower)).filter
            (fun letter => decide (letter < lower + 1)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter present
          have := List.mem_range'.mp present
          simpa using (show ¬ letter < lower + 1 by omega)
        have lowerRemoved : (List.range' 1 lower).filter
            (fun letter => decide (lower + 1 < letter)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter present
          have := List.mem_range'.mp present
          simpa using (show ¬ lower + 1 < letter by omega)
        have upperKept : (List.range' (lower + 2) (size - lower)).filter
            (fun letter => decide (lower + 1 < letter)) =
              List.range' (lower + 2) (size - lower) := by
          apply List.filter_eq_self.mpr
          intro letter present
          have := List.mem_range'.mp present
          simpa using (show lower + 1 < letter by omega)
        constructor
        · simp only [split, List.filter_append, List.filter_cons, lt_self_iff_false,
            decide_false, Bool.false_eq_true, ↓reduceIte, lowerKept, upperRemoved,
            List.append_nil]
        · simp only [split, List.filter_append, List.filter_cons, lt_self_iff_false,
            decide_false, Bool.false_eq_true, ↓reduceIte, lowerRemoved, upperKept,
            List.nil_append]
          have shift := List.map_add_range' (a := lower + 1) 1 (size - lower) 1
          rw [show lower + 1 + 1 = lower + 2 by omega] at shift
          simpa only [Nat.add_comm] using shift.symm
      have enumeration := weighted_decomposition (List.range' 1 (size + 1))
        (List.nodup_range' 1) (by simp) (fun length =>
          (1 - Polynomial.X) * (Polynomial.X : Polynomial ℚ) ^ length)
      change (∑ word ∈ words (List.range' 1 (size + 1)),
        (1 - Polynomial.X) * Polynomial.X ^ terminal word) = _ at enumeration
      rw [← Finset.mul_sum] at enumeration
      change (1 - Polynomial.X) * weighted (size + 1) = _ at enumeration
      rw [enumeration]
      apply Finset.sum_bij (fun pivot _ => pivot - 1)
      · intro pivot present
        have bounds := List.mem_range'.mp (List.mem_toFinset.mp present)
        apply Finset.mem_range.mpr
        omega
      · intro left leftPresent right rightPresent equal
        have leftBound : 1 ≤ left := by
          obtain ⟨index, _, equal⟩ := List.mem_range'.mp (List.mem_toFinset.mp leftPresent)
          omega
        have rightBound : 1 ≤ right := by
          obtain ⟨index, _, equal⟩ := List.mem_range'.mp (List.mem_toFinset.mp rightPresent)
          omega
        omega
      · intro lower present
        have bound := Finset.mem_range.mp present
        refine ⟨lower + 1,
          List.mem_toFinset.mpr (List.mem_range'.mpr ⟨lower, bound, by omega⟩), by omega⟩
      · intro pivot present
        have bounds := List.mem_range'.mp (List.mem_toFinset.mp present)
        have lowerBound : pivot - 1 ≤ size := by omega
        have pivotEq : pivot = pivot - 1 + 1 := by omega
        have parts := rangeParts (pivot - 1) lowerBound
        rw [pivotEq, parts.1, parts.2]
        simp only [List.length_range']
        rw [firstCuts, secondCuts]
        simp only [Finset.sum_const, nsmul_eq_mul]
        have upperWeight := shiftedSums (List.range' 1 (size - (pivot - 1)))
          (pivot - 1 + 1) (fun length => Polynomial.X ^ length)
        have upperCount := shiftedSums (List.range' 1 (size - (pivot - 1)))
          (pivot - 1 + 1) (fun _ => (1 : Polynomial ℚ))
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at upperCount
        rw [upperWeight, upperCount]
        simp only [counts, weighted, map_natCast, Nat.add_sub_cancel]
        ring
    have emptyOccurrence (pattern : List ℕ) (hasLetter : 1 ≤ NonnestingDefs.letters pattern) :
        ¬ NonnestingDefs.Occurs pattern [] := by
      rintro ⟨values, increasing, members, subword, arrows⟩
      have impossible := members 1 (by omega) hasLetter
      simp at impossible
    have emptyWords : words [] = {[]} := by
      have first := emptyOccurrence [1, 2, 2, 1] (by decide)
      have second := emptyOccurrence [2, 1, 1, 2] (by decide)
      have third := emptyOccurrence [1, 3, 2, 2] (by decide)
      simp [words, first, second, third]
    have emptyCount : counts 0 = 1 := by simp [counts, emptyWords]
    have emptyWeight : weighted 0 = 1 := by simp [weighted, emptyWords, terminal]
    let series : PowerSeries ℚ := mk counts
    let bivariate : PowerSeries (Polynomial ℚ) := mk weighted
    let lifted := series.map Polynomial.C
    let catalan := rescale Polynomial.X
      ((catalanSeries.map (Nat.castRingHom ℚ)).map Polynomial.C)
    let marker : PowerSeries (Polynomial ℚ) := C Polynomial.X
    have catalanCoeff (index : ℕ) : coeff index catalan =
        Polynomial.X ^ index * Polynomial.C (_root_.catalan index : ℚ) := by
      simp [catalan, coeff_rescale, coeff_map]
    have liftedCoeff (index : ℕ) : coeff index lifted = Polynomial.C (counts index) := by
      simp [lifted, series]
    have constantSeries : constantCoeff series = 1 := emptyCount
    have coefficientEquation :
        (1 - marker) * bivariate = C (1 - Polynomial.X) +
          X * ((marker * lifted - marker ^ 2 * bivariate) * lifted +
            marker ^ 2 * catalan * (lifted - bivariate)) := by
      have markerOne : 1 - marker = (C (1 - Polynomial.X) :
          PowerSeries (Polynomial ℚ)) := by simp [marker]
      rw [markerOne]
      apply PowerSeries.ext
      intro index
      cases index with
      | zero => simp [bivariate, marker, series, lifted, emptyWeight]
      | succ index =>
        simp only [coeff_C_mul, bivariate, coeff_mk, map_add,
          coeff_succ_C, coeff_succ_X_mul, zero_add]
        rw [weightedRecurrence]
        rw [coeff_mul, coeff_mul]
        simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Nat.succ_eq_add_one, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro lower member
        simp only [map_sub, marker, ← map_pow C, coeff_C_mul, liftedCoeff,
          catalanCoeff, coeff_mk]
        ring
    have equation :
        (1 - marker + X * marker ^ 2 * (lifted + catalan)) * bivariate =
          1 - marker + X * marker * lifted ^ 2 + X * marker ^ 2 * catalan * lifted := by
      have constantEq : (C (1 - Polynomial.X) : PowerSeries (Polynomial ℚ)) = 1 - marker := by
        simp [marker]
      rw [constantEq] at coefficientEquation
      linear_combination coefficientEquation
    have recurrence := NonnestingOneThreeTwoTwoKernel.catalytic_recurrence
      series constantSeries bivariate equation degree positive
    have actualCounts (index : ℕ) : coeff index series =
        ((NonnestingDefs.avoiders index [[1, 3, 2, 2]]).ncard : ℚ) := by
      have sets : (↑(words (List.range' 1 index)) : Set (List ℕ)) =
          NonnestingDefs.avoiders index [[1, 3, 2, 2]] := by
        ext word
        simp [words, NonnestingDefs.avoiders, List.mem_permutations]
      have cardinality := congrArg Set.ncard sets
      simp only [Set.ncard_coe_finset] at cardinality
      simp [series, counts, cardinality]
    simp_rw [actualCounts] at recurrence
    exact_mod_cast recurrence
  have emptyOccurrence (pattern : List ℕ) (hasLetter : 1 ≤ NonnestingDefs.letters pattern) :
      ¬ NonnestingDefs.Occurs pattern [] := by
    rintro ⟨values, increasing, members, subword, arrows⟩
    have impossible := members 1 (by omega) hasLetter
    simp at impossible
  have emptyAvoiders : NonnestingDefs.avoiders 0 [[1, 3, 2, 2]] = {[]} := by
    have first := emptyOccurrence [1, 2, 2, 1] (by decide)
    have second := emptyOccurrence [2, 1, 1, 2] (by decide)
    have third := emptyOccurrence [1, 3, 2, 2] (by decide)
    ext word
    simp only [NonnestingDefs.avoiders, List.range'_zero, List.flatMap_nil,
      Set.mem_ofPred_eq, List.perm_nil, Set.mem_singleton_iff]
    constructor
    · exact fun member => member.1
    · rintro rfl
      simp [first, second, third]
  let series : PowerSeries ℚ := mk fun degree =>
    ((NonnestingDefs.avoiders degree [[1, 3, 2, 2]]).ncard : ℚ)
  have constant : constantCoeff series = 1 := by
    simp [series, emptyAvoiders]
  let root := series - 1
  have positiveCoefficient (index : ℕ) (nonzero : 0 < index) :
      coeff index root = coeff index series := by
    simp only [root, map_sub, coeff_one, if_neg (Nat.ne_of_gt nonzero), sub_zero]
  have zeroCoefficient : coeff 0 root = 0 := by
    simp [root, coeff_zero_eq_constantCoeff, constant]
  have squareCoefficient (degree : ℕ) (positive : 1 ≤ degree) : coeff degree (root ^ 2) =
      ∑ index ∈ Finset.Icc 1 (degree - 1),
        coeff index series * coeff (degree - index) series := by
    rw [pow_two, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun left right => coeff left root * coeff right root) degree]
    have inclusion : Finset.Icc 1 (degree - 1) ⊆ Finset.range (degree + 1) := by
      intro index member
      have bounds := Finset.mem_Icc.mp member
      simp only [Finset.mem_range]
      omega
    calc
      (∑ index ∈ Finset.range (degree + 1),
          coeff index root * coeff (degree - index) root) =
          ∑ index ∈ Finset.Icc 1 (degree - 1),
            coeff index root * coeff (degree - index) root := by
        apply (Finset.sum_subset inclusion ?_).symm
        intro index member excluded
        have bound := Finset.mem_range.mp member
        have endpoints : index = 0 ∨ index = degree := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at excluded
          omega
        rcases endpoints with rfl | rfl <;> simp [zeroCoefficient]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index member
        have bounds := Finset.mem_Icc.mp member
        rw [positiveCoefficient index (by omega),
          positiveCoefficient (degree - index) (by omega)]
  have cubeCoefficient (degree : ℕ) : coeff (degree - 1) (series ^ 3) =
      ∑ outer ∈ Finset.HasAntidiagonal.antidiagonal (degree - 1),
        ∑ inner ∈ Finset.HasAntidiagonal.antidiagonal outer.1,
          coeff inner.1 series * coeff inner.2 series * coeff outer.2 series := by
    rw [show series ^ 3 = (series * series) * series by ring, coeff_mul]
    simp only [coeff_mul, Finset.sum_mul]
  have zero : constantCoeff root = 0 := by simp [root, constant]
  have functionalEquation : root - root ^ 2 = X * series ^ 3 := by
    apply PowerSeries.ext
    intro degree
    cases degree with
    | zero => simp [coeff_zero_eq_constantCoeff, zero]
    | succ degree =>
      have recurrence : coeff (degree + 1) series =
          (∑ index ∈ Finset.Icc 1 degree,
            coeff index series * coeff (degree + 1 - index) series) +
          ∑ outer ∈ Finset.HasAntidiagonal.antidiagonal degree,
            ∑ inner ∈ Finset.HasAntidiagonal.antidiagonal outer.1,
              coeff inner.1 series * coeff inner.2 series * coeff outer.2 series := by
        simp only [series, coeff_mk]
        exact_mod_cast counting_recurrence
          (degree + 1) (by omega)
      rw [map_sub, positiveCoefficient _ (by omega), squareCoefficient _ (by omega),
        coeff_succ_X_mul, show degree = degree + 1 - 1 by omega, cubeCoefficient]
      simp only [Nat.add_sub_cancel] at *
      linear_combination recurrence
  let factor : PowerSeries ℚ := (1 + X) ^ 3 * mk 1
  have substitution : HasSubst root := HasSubst.of_constantCoeff_zero' zero
  have factorSubstitution : subst root factor =
      (1 + root) ^ 3 * subst root (mk 1 : PowerSeries ℚ) := by
    simp only [factor, subst_mul substitution, subst_pow substitution,
      subst_add substitution, ← coe_substAlgHom substitution, map_one, substAlgHom_X]
  have geometric : subst root (mk 1 : PowerSeries ℚ) * (1 - root) = 1 := by
    have mapped := congrArg (substAlgHom substitution) (mk_one_mul_one_sub_eq_one ℚ)
    simpa only [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom] using mapped
  have equation : root = X * subst root factor := by
    have rootEquation : root * (1 - root) = X * (1 + root) ^ 3 := by
      dsimp only [root] at *
      linear_combination functionalEquation
    calc
      root = root * (subst root (mk 1 : PowerSeries ℚ) * (1 - root)) := by rw [geometric]; simp
      _ = (root * (1 - root)) * subst root (mk 1 : PowerSeries ℚ) := by ring
      _ = (X * (1 + root) ^ 3) * subst root (mk 1 : PowerSeries ℚ) := by rw [rootEquation]
      _ = X * subst root factor := by rw [factorSubstitution]; ring
  have lagrange (root factor : PowerSeries ℚ) (zero : constantCoeff root = 0)
    (equation : root = X * subst root factor) :
    ∀ degree power : ℕ, 1 ≤ power → power ≤ degree →
      (degree : ℚ) * coeff degree (root ^ power) =
        (power : ℚ) * coeff (degree - power) (factor ^ degree) := by
    classical
    have substitution : HasSubst root := HasSubst.of_constantCoeff_zero' zero
    have vanishes (degree power : ℕ) (bound : degree < power) :
        coeff degree (root ^ power) = 0 := by
      apply coeff_of_lt_order
      exact (show (degree : ENat) < (power : ENat) by exact_mod_cast bound).trans_le
        (le_order_pow_of_constantCoeff_eq_zero power zero)
    have finiteSubstitution (source : PowerSeries ℚ) (degree : ℕ) :
        coeff degree (subst root source) =
          ∑ power ∈ Finset.range (degree + 1),
            coeff power source * coeff degree (root ^ power) := by
      rw [coeff_subst' substitution]
      simp only [smul_eq_mul]
      apply finsum_eq_sum_of_support_subset
      intro power supported
      apply Finset.mem_range.mpr
      by_contra unbounded
      have vanish := vanishes degree power (by omega)
      exact supported (by simp [vanish])
    have shifted (degree power : ℕ) (bound : power ≤ degree) :
        coeff degree (root ^ power) = coeff (degree - power) (subst root (factor ^ power)) := by
      have powers : root ^ power = X ^ power * subst root (factor ^ power) := by
        rw [subst_pow substitution, ← mul_pow, ← equation]
      rw [powers, coeff_X_pow_mul', if_pos bound]
    have derivativeCoefficients (source : PowerSeries ℚ) (degree : ℕ) :
        coeff degree (X * derivative ℚ source) = (degree : ℚ) * coeff degree source := by
      cases degree with
      | zero => simp
      | succ degree =>
        rw [coeff_succ_X_mul, coeff_derivative]
        push_cast
        ring
    intro degree
    induction degree using Nat.strong_induction_on with
    | h degree inductionHypothesis =>
      intro power positive bounded
      by_cases equal : degree = power
      · subst degree
        rw [shifted power power le_rfl]
        simp only [Nat.sub_self]
        rw [finiteSubstitution]
        simp
      have differencePositive : 0 < degree - power := by omega
      have differenceSmaller : degree - power < degree := by omega
      have weighted : (degree - power : ℕ) * coeff degree (root ^ power) =
          coeff (degree - power)
            (X * derivative ℚ (factor ^ power) * factor ^ (degree - power)) := by
        rw [shifted degree power bounded, finiteSubstitution, Finset.mul_sum]
        rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_congr rfl
        intro index member
        have indexBound : index ≤ degree - power := by simpa using Finset.mem_range.mp member
        rw [derivativeCoefficients]
        by_cases indexZero : index = 0
        · subst index
          simp [coeff_one, Nat.ne_of_gt differencePositive]
        have inductionResult := inductionHypothesis (degree - power) differenceSmaller index
          (by omega) indexBound
        linear_combination coeff index (factor ^ power) * inductionResult
      have derivativeIdentity :
          (degree : PowerSeries ℚ) *
              (X * derivative ℚ (factor ^ power) * factor ^ (degree - power)) =
            (power : PowerSeries ℚ) * (X * derivative ℚ (factor ^ degree)) := by
        rw [derivative_pow, derivative_pow]
        have exponent : power - 1 + (degree - power) = degree - 1 := by omega
        rw [← exponent, pow_add]
        ring
      have coefficientIdentity := congrArg (coeff (degree - power)) derivativeIdentity
      simp only [← map_natCast C, coeff_C_mul, derivativeCoefficients] at coefficientIdentity
      have nonzero : (degree - power : ℕ) ≠ 0 := by omega
      apply mul_left_cancel₀ (show ((degree - power : ℕ) : ℚ) ≠ 0 by exact_mod_cast nonzero)
      linear_combination (degree : ℚ) * weighted + coefficientIdentity
  intro degree positive
  have coefficient := lagrange root factor zero equation degree 1 (by omega) positive
  have positiveRoot : coeff degree root = coeff degree series :=
    positiveCoefficient degree (by omega)
  simp only [pow_one, Nat.cast_one, one_mul, positiveRoot] at coefficient
  have binomialCoefficient (exponent index : ℕ) :
      coeff index ((1 + X : PowerSeries ℚ) ^ exponent) = (exponent.choose index : ℚ) := by
    have polynomial : ((1 + X : PowerSeries ℚ) ^ exponent) =
        ((1 + Polynomial.X : Polynomial ℚ) ^ exponent : Polynomial ℚ) := by simp
    rw [polynomial, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  have geometricPower : (mk 1 : PowerSeries ℚ) ^ degree =
      mk (fun index => ((degree - 1 + index).choose (degree - 1) : ℚ)) := by
    have powerEquation := mk_one_pow_eq_mk_choose_add ℚ (degree - 1)
    simpa only [Nat.sub_add_cancel positive] using powerEquation
  have factorPower : factor ^ degree =
      (1 + X) ^ (3 * degree) * (mk 1 : PowerSeries ℚ) ^ degree := by
    simp only [factor, mul_pow, pow_mul]
  have expanded : coeff (degree - 1) (factor ^ degree) =
      ∑ index ∈ Finset.range degree,
        ((3 * degree).choose index : ℚ) *
          ((2 * degree - index - 2).choose (degree - 1) : ℚ) := by
    rw [factorPower, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, geometricPower]
    rw [show (degree - 1).succ = degree by omega]
    apply Finset.sum_congr rfl
    intro index member
    simp only [binomialCoefficient, coeff_mk]
    have bound := Finset.mem_range.mp member
    rw [show degree - 1 + (degree - 1 - index) = 2 * degree - index - 2 by omega]
  rw [expanded] at coefficient
  simp only [series, coeff_mk] at coefficient
  exact_mod_cast coefficient

end D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo
