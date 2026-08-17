/- GID: D5/S0/Tower/NonPisot/GapCountInstances
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisot/GapCountInstances
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three further finite beta13 gap counts and the exact ten-digit model boundary. -/

import D5.S0.Tower.NonPisot.GapCounts

namespace D5.S0.Tower.NonPisot.GapCountInstances

/-- The exact normalized internal adjacent-gap spectrum has three types at level three. -/
theorem beta13_normalized_gap_type_count_three :
    (D5.S0.Tower.NonPisot.GapCounts.beta13NormalizedGapSpectrum 3).card = 3 := by
  rw [D5.S0.Tower.NonPisot.GapCounts.beta13NormalizedGapSpectrum,
    Finset.card_image_of_injective _
      D5.S0.Tower.NonPisot.GapCounts.beta13_gap_code_value_injective]
  decide

/-- The exact normalized internal adjacent-gap spectrum has four types at level four. -/
theorem beta13_normalized_gap_type_count_four :
    (D5.S0.Tower.NonPisot.GapCounts.beta13NormalizedGapSpectrum 4).card = 4 := by
  rw [D5.S0.Tower.NonPisot.GapCounts.beta13NormalizedGapSpectrum,
    Finset.card_image_of_injective _
      D5.S0.Tower.NonPisot.GapCounts.beta13_gap_code_value_injective]
  decide

/-- The exact normalized internal adjacent-gap spectrum has five types at level five. -/
theorem beta13_normalized_gap_type_count_five :
    (D5.S0.Tower.NonPisot.GapCounts.beta13NormalizedGapSpectrum 5).card = 5 := by
  rw [D5.S0.Tower.NonPisot.GapCounts.beta13NormalizedGapSpectrum,
    Finset.card_image_of_injective _
      D5.S0.Tower.NonPisot.GapCounts.beta13_gap_code_value_injective]
  decide

/-- The certified next greedy digit is zero, but the frozen ten-digit prefix predicate rejects
that eleven-digit greedy prefix and hence the frozen name generator omits it. -/
theorem beta13_frozen_prefix_rejects_actual_eleven_digit_prefix :
    let actualPrefix := D5.S0.Tower.NonPisot.GapCounts.beta13GreedyDigits ++ [0]
    D5.S0.Tower.NonPisot.GapCounts.beta13RemainderCodes[10]? = some (21, -9) ∧
      ⌊D5.S0.Tower.NonPisot.Beta13.beta13 *
          D5.S0.Tower.NonPisot.GapCounts.beta13GapCodeValue (21, -9)⌋ = 0 ∧
      D5.S0.Tower.NonPisot.GapCounts.beta13BelowGreedyPrefix actualPrefix = false ∧
      actualPrefix ∉ D5.S0.Tower.NonPisot.GapCounts.beta13Names 11 := by
  dsimp only
  have hsqrt : Real.sqrt (13 : Real) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 <= Real.sqrt (13 : Real) := Real.sqrt_nonneg 13
  have hsqrtLower : (7 : Real) / 2 < Real.sqrt 13 := by nlinarith
  have hsqrtUpper : Real.sqrt 13 < (11 : Real) / 3 := by nlinarith
  constructor
  · decide
  · constructor
    · apply Int.floor_eq_iff.mpr
      constructor <;>
        norm_num [D5.S0.Tower.NonPisot.GapCounts.beta13GapCodeValue,
          D5.S0.Tower.NonPisot.Beta13.beta13] <;>
        nlinarith
    · constructor
      · decide
      · intro hword
        have generated_name_passes_full_test
            (Q : Nat) (word : List Nat)
            (hmem : word ∈ D5.S0.Tower.NonPisot.GapCounts.beta13Names (Q + 1)) :
            D5.S0.Tower.NonPisot.GapCounts.beta13BelowGreedyPrefix word = true := by
          simp only [D5.S0.Tower.NonPisot.GapCounts.beta13Names, List.mem_flatMap,
            List.mem_cons, List.mem_filterMap] at hmem
          obtain ⟨digit, _hdigit, tail, _htail, hif⟩ := hmem
          split at hif <;> rename_i htest
          · have hwordEq : digit :: tail = word := Option.some.inj hif
            subst word
            exact htest
          · cases hif
        have hpasses := generated_name_passes_full_test 10 _ hword
        rw [show D5.S0.Tower.NonPisot.GapCounts.beta13BelowGreedyPrefix
          (D5.S0.Tower.NonPisot.GapCounts.beta13GreedyDigits ++ [0]) = false by decide]
          at hpasses
        exact Bool.noConfusion hpasses

end D5.S0.Tower.NonPisot.GapCountInstances
